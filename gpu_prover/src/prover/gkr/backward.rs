use std::cell::UnsafeCell;
use std::collections::{BTreeMap, VecDeque};
use std::mem::align_of;
use std::ptr::{null, null_mut};
use std::slice;

use cs::definitions::{
    gkr::AddressSpaceType, GKRAddress, PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
};
use cs::gkr_compiler::{
    GKRCircuitArtifact, GKRLayerDescription, InitsOrTeardownsTimestampAndValue, NoFieldGKRRelation,
    NoFieldMaxQuadraticConstraintsGKRRelation, NoFieldMaxQuadraticGKRRelation, OutputType,
};
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::memory::{memory_copy_async, memory_set_async};
use era_cudart::paste::paste;
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSlice, CudaSliceMut, DeviceSlice};
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use field::{Field, FieldExtension, PrimeField};
use prover::gkr::high_bits_offset_for_inits_and_teardowns;
use prover::gkr::prover::dimension_reduction::forward::DimensionReducingInputOutput;
use prover::gkr::prover::transcript_utils::draw_random_field_els;
use prover::gkr::prover::GKRExternalChallenges;
use prover::gkr::sumcheck::evaluation_kernels::{
    BaseFieldCopyGKRRelation, BatchedGKRKernel, ExtensionCopyGKRRelation, GKRInputs,
    LookupBaseExtMinusBaseExtGKRRelation, LookupBaseMinusMultiplicityByBaseGKRRelation,
    LookupBasePairGKRRelation, LookupExtensionMinusMultiplicityByExtensionGKRRelation,
    LookupExtensionPairGKRRelation, LookupPairGKRRelation,
    LookupRationalPairWithUnbalancedBaseGKRRelation,
    LookupRationalPairWithUnbalancedExtensionGKRRelation, MaskIntoIdentityProductGKRRelation,
    SameSizeProductGKRRelation,
};
use prover::gkr::sumcheck::{
    evaluate_eq_poly, evaluate_small_univariate_poly, output_univariate_monomial_form_max_quadratic,
};
use prover::transcript::Seed;

use super::backward_kernels::GpuBackwardSumcheckRoundUpdateKernel;
pub(crate) use super::backward_kernels::*;
use super::transform::normalize_compiled_circuit_for_gpu;
use super::{
    alloc_host_and_schedule_copy, GpuBaseFieldPoly, GpuBaseFieldPolySource,
    GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor,
    GpuBaseFieldPolySourceAfterTwoFoldingsLaunchDescriptor,
    GpuExtensionFieldPolyContinuingLaunchDescriptor, GpuExtensionFieldPolyInitialSource,
    GpuGKRStorage, GpuSumcheckRound0HostLaunchDescriptors, GpuSumcheckRound0LaunchDescriptors,
    GpuSumcheckRound0ScheduledLaunchDescriptors, GpuSumcheckRound1HostLaunchDescriptors,
    GpuSumcheckRound1PreparedStorage, GpuSumcheckRound1ScheduledLaunchDescriptors,
    GpuSumcheckRound2HostLaunchDescriptors, GpuSumcheckRound2PreparedStorage,
    GpuSumcheckRound2ScheduledLaunchDescriptors, GpuSumcheckRound3AndBeyondHostLaunchDescriptors,
    GpuSumcheckRound3AndBeyondPreparedStorage,
    GpuSumcheckRound3AndBeyondScheduledLaunchDescriptors,
};
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::blake2s::STATE_SIZE;
use crate::ops::cub::device_reduce::{
    batch_reduce, get_batch_reduce_temp_storage_bytes, get_reduce_temp_storage_bytes, reduce,
    Reduce, ReduceOperation,
};
use crate::ops::cub::CUB_TEMP_STORAGE_EXTRA_ALIGNMENT_LOG2;
use crate::ops::immediate_factors::{
    ImmediateFactorRecipeStructural, IMMEDIATE_FACTOR_ADDITIVE_PART_IDX,
};
use crate::ops::simple::{mul_into_y, BinaryOp, Mul};
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{
    DeviceAllocation, HostAllocation, ProverContext, SchedulerHostAllocation, UnsafeAccessor,
    UnsafeMutAccessor,
};
use crate::primitives::device_structures::{DeviceMatrix, DeviceVectorChunk, DeviceVectorChunkMut};
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E4};
use crate::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
use crate::prover::proof_layout::ProofLayout;

fn remap_constraint_input(
    mapping: &mut BTreeMap<GKRAddress, usize>,
    inputs: &mut Vec<GKRAddress>,
    address: GKRAddress,
) -> usize {
    if let Some(idx) = mapping.get(&address).copied() {
        idx
    } else {
        let idx = mapping.len();
        mapping.insert(address, idx);
        inputs.push(address);
        idx
    }
}

#[derive(Clone)]
struct ImmediateCoeff<E> {
    value: E,
    recipe: ImmediateFactorRecipeStructural,
}

impl<E: Field + FieldExtension<BF>> ImmediateCoeff<E> {
    fn zero() -> Self {
        Self {
            value: E::ZERO,
            recipe: ImmediateFactorRecipeStructural::zero(),
        }
    }

    fn from_base(coeff: BF) -> Self {
        Self {
            value: E::from_base(coeff),
            recipe: ImmediateFactorRecipeStructural::from_base(coeff),
        }
    }

    fn challenge(idx: u8, value: E) -> Self {
        Self {
            value,
            recipe: ImmediateFactorRecipeStructural::challenge(idx),
        }
    }

    fn challenge_scaled(idx: u8, value: E, coeff: BF) -> Self {
        let mut value = value;
        value.mul_assign_by_base(&coeff);
        Self {
            value,
            recipe: ImmediateFactorRecipeStructural::challenge_scaled(idx, coeff),
        }
    }

    fn add_assign(&mut self, other: &Self) {
        self.value.add_assign(&other.value);
        self.recipe = self.recipe.add(&other.recipe);
    }

    fn mul(&self, other: &Self) -> Self {
        let mut value = self.value;
        value.mul_assign(&other.value);
        Self {
            value,
            recipe: self.recipe.mul(&other.recipe),
        }
    }
}

pub(crate) fn canonical_inits_and_teardowns_top_bits(sets_count: usize) -> Vec<u32> {
    (0..sets_count as u32).collect()
}

fn fill_round0_eq_pair_values<E: Field>(dst: &mut [E], claim_point: &[E]) {
    assert_eq!(
        dst.len(),
        round0_eq_pair_values_len(claim_point.len()),
        "round-0 eq pair buffer must match the claim-point suffix length"
    );
    for (pair, challenge) in dst
        .chunks_exact_mut(2)
        .zip(claim_point.iter().skip(1).copied())
    {
        let mut one_minus = E::ONE;
        one_minus.sub_assign(&challenge);
        pair[0] = one_minus;
        pair[1] = challenge;
    }
}

fn make_round0_eq_pair_values<E: Field>(claim_point: &[E]) -> Vec<E> {
    let mut result = vec![E::ZERO; round0_eq_pair_values_len(claim_point.len())];
    fill_round0_eq_pair_values(&mut result, claim_point);
    result
}

fn alloc_scheduler_host_and_upload<T: Copy>(
    context: &ProverContext,
    values: &[T],
    placement: AllocationPlacement,
) -> CudaResult<(Option<SchedulerHostAllocation<[T]>>, DeviceAllocation<T>)> {
    let mut device = context.alloc(values.len().max(1), placement)?;
    if values.is_empty() {
        return Ok((None, device));
    }
    let host = context.scheduler_host_from_slice(values)?;
    memory_copy_async(
        &mut device[..values.len()],
        &host,
        context.get_exec_stream(),
    )?;
    Ok((Some(host), device))
}

fn memory_query_as_flattened_relation<E: Field + FieldExtension<BF>>(
    rel: &cs::gkr_compiler::NoFieldSpecialMemoryContributionRelation,
    external_challenges: &GKRExternalChallenges<BF, E>,
) -> (BTreeMap<GKRAddress, ImmediateCoeff<E>>, ImmediateCoeff<E>) {
    let mut result = BTreeMap::new();
    let mut constant_term = ImmediateCoeff {
        value: external_challenges.permutation_argument_additive_part,
        recipe: ImmediateFactorRecipeStructural::challenge(IMMEDIATE_FACTOR_ADDITIVE_PART_IDX),
    };

    match rel.address_space {
        cs::gkr_compiler::CompiledAddressSpaceRelationStrict::Constant(c) => {
            assert!(c < (1u32 << 16));
            constant_term.add_assign(&ImmediateCoeff::from_base(BF::from_u32_unchecked(c)));
        }
        cs::gkr_compiler::CompiledAddressSpaceRelationStrict::IsRam(offset) => {
            assert_eq!(AddressSpaceType::RAM as u8, 1);
            assert!(result
                .insert(
                    GKRAddress::BaseLayerMemory(offset),
                    ImmediateCoeff::from_base(BF::ONE),
                )
                .is_none());
        }
        cs::gkr_compiler::CompiledAddressSpaceRelationStrict::IsRegister(offset) => {
            assert_eq!(AddressSpaceType::Register as u8, 0);
            assert!(result
                .insert(
                    GKRAddress::BaseLayerMemory(offset),
                    ImmediateCoeff::from_base(BF::MINUS_ONE),
                )
                .is_none());
            constant_term.add_assign(&ImmediateCoeff::from_base(BF::ONE));
        }
    }

    match &rel.address {
        cs::gkr_compiler::CompiledAddressStrict::ConstantU16(c) => {
            let idx = PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX;
            let challenge = ImmediateCoeff::challenge_scaled(
                idx as u8,
                external_challenges.permutation_argument_linearization_challenges[idx],
                BF::from_u32_unchecked(*c as u32),
            );
            constant_term.add_assign(&challenge);
        }
        cs::gkr_compiler::CompiledAddressStrict::Constant(c) => {
            assert!(*c < (1u32 << 16));
            let idx = PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX;
            let challenge = ImmediateCoeff::challenge_scaled(
                idx as u8,
                external_challenges.permutation_argument_linearization_challenges[idx],
                BF::from_u32_unchecked(*c),
            );
            constant_term.add_assign(&challenge);
        }
        cs::gkr_compiler::CompiledAddressStrict::U16Space(offset) => {
            let idx = PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX;
            let challenge = ImmediateCoeff::challenge(
                idx as u8,
                external_challenges.permutation_argument_linearization_challenges[idx],
            );
            assert!(result
                .insert(GKRAddress::BaseLayerMemory(*offset), challenge)
                .is_none());
        }
        cs::gkr_compiler::CompiledAddressStrict::U32Space([low, high]) => {
            for (idx, offset) in [
                (PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX, *low),
                (
                    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
                    *high,
                ),
            ] {
                let challenge = ImmediateCoeff::challenge(
                    idx as u8,
                    external_challenges.permutation_argument_linearization_challenges[idx],
                );
                assert!(result
                    .insert(GKRAddress::BaseLayerMemory(offset), challenge)
                    .is_none());
            }
        }
        cs::gkr_compiler::CompiledAddressStrict::U32SpaceGeneric(..) => {
            todo!();
        }
        cs::gkr_compiler::CompiledAddressStrict::U32SpaceSpecialIndirect {
            low_base,
            low_dynamic_offset,
            low_offset,
            high,
        } => {
            if let Some((c, offset)) = *low_dynamic_offset {
                let idx = PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX;
                let challenge = ImmediateCoeff::challenge_scaled(
                    idx as u8,
                    external_challenges.permutation_argument_linearization_challenges[idx],
                    BF::from_u32_unchecked(c as u32),
                );
                assert!(result
                    .insert(GKRAddress::BaseLayerMemory(offset), challenge)
                    .is_none());
            }
            {
                let idx = PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX;
                let challenge = ImmediateCoeff::challenge(
                    idx as u8,
                    external_challenges.permutation_argument_linearization_challenges[idx],
                );
                assert!(result
                    .insert(GKRAddress::BaseLayerMemory(*low_base), challenge.clone())
                    .is_none());
                let offset_challenge = ImmediateCoeff::challenge_scaled(
                    idx as u8,
                    external_challenges.permutation_argument_linearization_challenges[idx],
                    BF::from_u32_unchecked(*low_offset as u32),
                );
                constant_term.add_assign(&offset_challenge);
            }
            {
                let idx = PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX;
                let challenge = ImmediateCoeff::challenge(
                    idx as u8,
                    external_challenges.permutation_argument_linearization_challenges[idx],
                );
                assert!(result
                    .insert(GKRAddress::BaseLayerMemory(*high), challenge)
                    .is_none());
            }
        }
    }

    match rel.timestamp {
        cs::gkr_compiler::CompiledMemoryTimestamp::Zero => {}
        cs::gkr_compiler::CompiledMemoryTimestamp::Normal(ts) => {
            {
                let idx = PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX;
                let challenge = ImmediateCoeff::challenge(
                    idx as u8,
                    external_challenges.permutation_argument_linearization_challenges[idx],
                );
                assert!(result
                    .insert(GKRAddress::BaseLayerMemory(ts[0]), challenge.clone())
                    .is_none());
                let offset_challenge = ImmediateCoeff::challenge_scaled(
                    idx as u8,
                    external_challenges.permutation_argument_linearization_challenges[idx],
                    BF::from_u32_unchecked(rel.timestamp_offset as u32),
                );
                constant_term.add_assign(&offset_challenge);
            }
            {
                let idx = PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX;
                let challenge = ImmediateCoeff::challenge(
                    idx as u8,
                    external_challenges.permutation_argument_linearization_challenges[idx],
                );
                assert!(result
                    .insert(GKRAddress::BaseLayerMemory(ts[1]), challenge)
                    .is_none());
            }
        }
    }

    match rel.value {
        cs::definitions::gkr::RamWordRepresentation::Zero => {}
        cs::definitions::gkr::RamWordRepresentation::U16Limbs(read_value) => {
            for (idx, offset) in [
                (
                    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
                    read_value[0],
                ),
                (
                    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
                    read_value[1],
                ),
            ] {
                let challenge = ImmediateCoeff::challenge(
                    idx as u8,
                    external_challenges.permutation_argument_linearization_challenges[idx],
                );
                assert!(result
                    .insert(GKRAddress::BaseLayerMemory(offset), challenge)
                    .is_none());
            }
        }
        cs::definitions::gkr::RamWordRepresentation::U8Limbs(read_value_bytes) => {
            let byte_shift = BF::from_u32_unchecked(1u32 << 8);
            for (idx, offset_low, offset_high) in [
                (
                    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
                    read_value_bytes[0],
                    read_value_bytes[1],
                ),
                (
                    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
                    read_value_bytes[2],
                    read_value_bytes[3],
                ),
            ] {
                let challenge = ImmediateCoeff::challenge(
                    idx as u8,
                    external_challenges.permutation_argument_linearization_challenges[idx],
                );
                assert!(result
                    .insert(GKRAddress::BaseLayerMemory(offset_low), challenge.clone())
                    .is_none());
                let high_challenge = ImmediateCoeff::challenge_scaled(
                    idx as u8,
                    external_challenges.permutation_argument_linearization_challenges[idx],
                    byte_shift,
                );
                assert!(result
                    .insert(GKRAddress::BaseLayerMemory(offset_high), high_challenge)
                    .is_none());
            }
        }
    }

    (result, constant_term)
}

fn single_column_lookup_as_flattened_relation<
    E: Field + FieldExtension<BF>,
    const WITH_ADDITIVE_PART: bool,
>(
    rel: &cs::definitions::gkr::NoFieldSingleColumnLookupRelation,
    lookup_challenges_additive_part: E,
) -> (BTreeMap<GKRAddress, E>, E) {
    let mut result = BTreeMap::new();
    let mut constant_term = if WITH_ADDITIVE_PART {
        lookup_challenges_additive_part
    } else {
        E::ZERO
    };

    for (coeff, address) in rel.input.linear_terms.iter() {
        assert!(result
            .insert(*address, E::from_base(BF::from_u32_unchecked(*coeff)))
            .is_none());
    }
    constant_term.add_assign_base(&BF::from_u32_unchecked(rel.input.constant));

    (result, constant_term)
}

fn vector_lookup_as_flattened_relation<
    E: Field + FieldExtension<BF>,
    const WITH_ADDITIVE_PART: bool,
>(
    rel: &cs::definitions::gkr::NoFieldVectorLookupRelation,
    lookup_challenges_multiplicative_part: E,
    lookup_challenges_additive_part: E,
) -> (BTreeMap<GKRAddress, E>, E) {
    let mut result = BTreeMap::new();
    let mut constant_term = if WITH_ADDITIVE_PART {
        lookup_challenges_additive_part
    } else {
        E::ZERO
    };

    let mut challenge = E::ONE;
    for column in rel.columns.iter() {
        for (coeff, address) in column.linear_terms.iter() {
            let mut t = challenge;
            t.mul_assign_by_base(&BF::from_u32_unchecked(*coeff));
            assert!(result.insert(*address, t).is_none());
        }
        let mut t = challenge;
        t.mul_assign_by_base(&BF::from_u32_unchecked(column.constant));
        constant_term.add_assign(&t);
        challenge.mul_assign(&lookup_challenges_multiplicative_part);
    }

    (result, constant_term)
}

fn lookup_constraint_term(
    coeff: u32,
    source: GpuGKRMainLayerDeferredChallengeSource,
    power: u32,
) -> GpuGKRMainLayerConstraintChallengeTerm {
    GpuGKRMainLayerConstraintChallengeTerm {
        coeff: BF::from_u32_unchecked(coeff),
        source,
        power,
    }
}

fn single_column_lookup_as_flattened_relation_template<const WITH_ADDITIVE_PART: bool>(
    rel: &cs::definitions::gkr::NoFieldSingleColumnLookupRelation,
) -> (
    BTreeMap<GKRAddress, Vec<GpuGKRMainLayerConstraintChallengeTerm>>,
    Vec<GpuGKRMainLayerConstraintChallengeTerm>,
) {
    let mut result = BTreeMap::new();
    let mut constant_terms = Vec::new();
    if WITH_ADDITIVE_PART {
        constant_terms.push(lookup_constraint_term(
            1,
            GpuGKRMainLayerDeferredChallengeSource::LookupAdditive,
            1,
        ));
    }
    if rel.input.constant != 0 {
        constant_terms.push(lookup_constraint_term(
            rel.input.constant,
            GpuGKRMainLayerDeferredChallengeSource::LookupAdditive,
            0,
        ));
    }

    for (coeff, address) in rel.input.linear_terms.iter() {
        assert!(result
            .insert(
                *address,
                vec![lookup_constraint_term(
                    *coeff,
                    GpuGKRMainLayerDeferredChallengeSource::LookupAdditive,
                    0,
                )],
            )
            .is_none());
    }

    (result, constant_terms)
}

fn vector_lookup_as_flattened_relation_template<const WITH_ADDITIVE_PART: bool>(
    rel: &cs::definitions::gkr::NoFieldVectorLookupRelation,
) -> (
    BTreeMap<GKRAddress, Vec<GpuGKRMainLayerConstraintChallengeTerm>>,
    Vec<GpuGKRMainLayerConstraintChallengeTerm>,
) {
    let mut result = BTreeMap::new();
    let mut constant_terms = Vec::new();
    if WITH_ADDITIVE_PART {
        constant_terms.push(lookup_constraint_term(
            1,
            GpuGKRMainLayerDeferredChallengeSource::LookupAdditive,
            1,
        ));
    }

    for (idx, column) in rel.columns.iter().enumerate() {
        let power = idx as u32;
        for (coeff, address) in column.linear_terms.iter() {
            assert!(result
                .insert(
                    *address,
                    vec![lookup_constraint_term(
                        *coeff,
                        GpuGKRMainLayerDeferredChallengeSource::LookupMultiplicative,
                        power,
                    )],
                )
                .is_none());
        }
        if column.constant != 0 {
            constant_terms.push(lookup_constraint_term(
                column.constant,
                GpuGKRMainLayerDeferredChallengeSource::LookupMultiplicative,
                power,
            ));
        }
    }

    (result, constant_terms)
}

fn flatten_inits_or_teardowns_relation<E: Field + FieldExtension<BF>>(
    timestamps_and_values: Option<([GKRAddress; 2], [GKRAddress; 2])>,
    setup: [GKRAddress; 2],
    address_high_bits: u32,
    address_high_bits_shift: u32,
    external_challenges: &GKRExternalChallenges<BF, E>,
) -> (BTreeMap<GKRAddress, ImmediateCoeff<E>>, ImmediateCoeff<E>) {
    let mut result = BTreeMap::new();
    let mut constant_term = ImmediateCoeff {
        value: external_challenges.permutation_argument_additive_part,
        recipe: ImmediateFactorRecipeStructural::challenge(IMMEDIATE_FACTOR_ADDITIVE_PART_IDX),
    };
    constant_term.add_assign(&ImmediateCoeff::from_base(BF::from_u32_unchecked(
        AddressSpaceType::RAM as u32,
    )));

    {
        let idx = PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX;
        let challenge = ImmediateCoeff::challenge(
            idx as u8,
            external_challenges.permutation_argument_linearization_challenges[idx],
        );
        assert!(result.insert(setup[0], challenge).is_none());
    }
    {
        let idx = PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX;
        let challenge = ImmediateCoeff::challenge(
            idx as u8,
            external_challenges.permutation_argument_linearization_challenges[idx],
        );
        assert!(result.insert(setup[1], challenge.clone()).is_none());
        let shifted = ImmediateCoeff::challenge_scaled(
            idx as u8,
            external_challenges.permutation_argument_linearization_challenges[idx],
            BF::from_u32_unchecked(address_high_bits << address_high_bits_shift),
        );
        constant_term.add_assign(&shifted);
    }

    if let Some((timestamps, values)) = timestamps_and_values {
        for (idx, address) in [
            (
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
                timestamps[0],
            ),
            (
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
                timestamps[1],
            ),
            (
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
                values[0],
            ),
            (
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
                values[1],
            ),
        ] {
            let challenge = ImmediateCoeff::challenge(
                idx as u8,
                external_challenges.permutation_argument_linearization_challenges[idx],
            );
            assert!(result.insert(address, challenge).is_none());
        }
    }

    (result, constant_term)
}

pub(crate) fn build_inits_and_teardowns_initial_pair_inputs_and_metadata<
    E: Field + FieldExtension<BF>,
>(
    timestamp_and_value: &InitsOrTeardownsTimestampAndValue,
    setup: [GKRAddress; 2],
    output: GKRAddress,
    address_high_bits: [u32; 2],
    address_high_bits_shift: u32,
    external_challenges: &GKRExternalChallenges<BF, E>,
) -> (GKRInputs, GpuGKRMainLayerConstraintHostMetadata<E>) {
    let lhs_timestamps_and_values = match timestamp_and_value {
        InitsOrTeardownsTimestampAndValue::Init => None,
        InitsOrTeardownsTimestampAndValue::Teardown {
            lhs_timestamp,
            lhs_value,
            ..
        } => Some((
            lhs_timestamp.map(GKRAddress::BaseLayerMemory),
            lhs_value.map(GKRAddress::BaseLayerMemory),
        )),
    };
    let rhs_timestamps_and_values = match timestamp_and_value {
        InitsOrTeardownsTimestampAndValue::Init => None,
        InitsOrTeardownsTimestampAndValue::Teardown {
            rhs_timestamp,
            rhs_value,
            ..
        } => Some((
            rhs_timestamp.map(GKRAddress::BaseLayerMemory),
            rhs_value.map(GKRAddress::BaseLayerMemory),
        )),
    };
    let (lhs_terms, lhs_constant) = flatten_inits_or_teardowns_relation(
        lhs_timestamps_and_values,
        setup,
        address_high_bits[0],
        address_high_bits_shift,
        external_challenges,
    );
    let (rhs_terms, rhs_constant) = flatten_inits_or_teardowns_relation(
        rhs_timestamps_and_values,
        setup,
        address_high_bits[1],
        address_high_bits_shift,
        external_challenges,
    );

    let mut mapping = BTreeMap::new();
    let mut inputs = Vec::new();
    let mut quadratic_terms = Vec::new();
    for (&lhs_address, lhs_challenge) in lhs_terms.iter() {
        let lhs_idx = remap_constraint_input(&mut mapping, &mut inputs, lhs_address);
        for (&rhs_address, rhs_challenge) in rhs_terms.iter() {
            let rhs_idx = remap_constraint_input(&mut mapping, &mut inputs, rhs_address);
            let challenge = lhs_challenge.mul(rhs_challenge);
            quadratic_terms.push(GpuGKRMainLayerConstraintQuadraticTerm {
                lhs: lhs_idx as u32,
                rhs: rhs_idx as u32,
                challenge: challenge.value,
                immediate_recipe: challenge.recipe,
            });
        }
    }

    let mut linear_acc = BTreeMap::new();
    for (&address, challenge) in lhs_terms.iter() {
        let idx = remap_constraint_input(&mut mapping, &mut inputs, address);
        let linear = challenge.mul(&rhs_constant);
        linear_acc
            .entry(idx)
            .and_modify(|acc: &mut ImmediateCoeff<E>| {
                acc.add_assign(&linear);
            })
            .or_insert(linear);
    }
    for (&address, challenge) in rhs_terms.iter() {
        let idx = remap_constraint_input(&mut mapping, &mut inputs, address);
        let linear = challenge.mul(&lhs_constant);
        linear_acc
            .entry(idx)
            .and_modify(|acc: &mut ImmediateCoeff<E>| {
                acc.add_assign(&linear);
            })
            .or_insert(linear);
    }

    let linear_terms = linear_acc
        .into_iter()
        .map(|(input, challenge)| GpuGKRMainLayerConstraintLinearTerm {
            input: input as u32,
            challenge: challenge.value,
            immediate_recipe: challenge.recipe,
        })
        .collect();
    let constant_offset = lhs_constant.mul(&rhs_constant);

    (
        GKRInputs {
            inputs_in_base: inputs,
            inputs_in_extension: Vec::new(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: vec![output],
        },
        GpuGKRMainLayerConstraintHostMetadata {
            quadratic_terms,
            linear_terms,
            constant_offset: constant_offset.value,
            constant_offset_recipe: constant_offset.recipe,
        },
    )
}

pub(crate) fn build_single_max_quadratic_constraint_inputs_and_metadata<
    E: Field + FieldExtension<BF>,
>(
    relation: &NoFieldMaxQuadraticGKRRelation,
) -> (GKRInputs, GpuGKRMainLayerConstraintHostMetadata<E>) {
    let mut mapping = BTreeMap::new();
    let mut inputs = Vec::new();
    let mut quadratic_terms = Vec::new();
    let mut linear_terms = Vec::new();

    for (lhs, rhs_terms) in relation.quadratic_terms.iter() {
        let lhs_idx = remap_constraint_input(&mut mapping, &mut inputs, *lhs);
        for (coeff, rhs) in rhs_terms.iter() {
            let coeff = BF::from_u32_with_reduction(*coeff);
            let rhs_idx = if *lhs == *rhs {
                lhs_idx
            } else {
                remap_constraint_input(&mut mapping, &mut inputs, *rhs)
            };
            quadratic_terms.push(GpuGKRMainLayerConstraintQuadraticTerm {
                lhs: lhs_idx as u32,
                rhs: rhs_idx as u32,
                challenge: E::from_base(coeff),
                immediate_recipe: ImmediateFactorRecipeStructural::from_base(coeff),
            });
        }
    }

    for (coeff, input) in relation.linear_terms.iter() {
        let coeff = BF::from_u32_with_reduction(*coeff);
        let input_idx = remap_constraint_input(&mut mapping, &mut inputs, *input);
        linear_terms.push(GpuGKRMainLayerConstraintLinearTerm {
            input: input_idx as u32,
            challenge: E::from_base(coeff),
            immediate_recipe: ImmediateFactorRecipeStructural::from_base(coeff),
        });
    }
    let constant = BF::from_u32_with_reduction(relation.constant);

    (
        GKRInputs {
            inputs_in_base: inputs,
            inputs_in_extension: Vec::new(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: Vec::new(),
        },
        GpuGKRMainLayerConstraintHostMetadata {
            quadratic_terms,
            linear_terms,
            constant_offset: E::from_base(constant),
            constant_offset_recipe: ImmediateFactorRecipeStructural::from_base(constant),
        },
    )
}

/// Builds blueprint inputs and metadata for the value-producing
/// `NoFieldGKRRelation::MaxQuadratic { input, output }` form. Reuses the
/// constraint-only helper for input remapping and metadata, then attaches the
/// scratch-backed output as `outputs_in_base`. The kernel kind is the
/// dedicated `MaxQuadraticBaseOutput` (a `LinearBaseOutput`-shaped emit with
/// the constraint's quadratic terms layered on top).
pub(crate) fn build_max_quadratic_relation_inputs_and_metadata<E: Field + FieldExtension<BF>>(
    relation: &NoFieldMaxQuadraticGKRRelation,
    output: GKRAddress,
) -> (GKRInputs, GpuGKRMainLayerConstraintHostMetadata<E>) {
    let (mut gkr_inputs, metadata) =
        build_single_max_quadratic_constraint_inputs_and_metadata::<E>(relation);
    gkr_inputs.outputs_in_base = vec![output];
    (gkr_inputs, metadata)
}

fn build_linear_base_kernel_inputs_and_metadata<E: Field + FieldExtension<BF>>(
    relation: &cs::definitions::gkr::NoFieldLinearRelation,
    output: GKRAddress,
) -> (GKRInputs, GpuGKRMainLayerConstraintHostMetadata<E>) {
    let mut mapping = BTreeMap::new();
    let mut inputs = Vec::new();
    let mut linear_terms = Vec::new();

    for (coeff, input) in relation.linear_terms.iter() {
        let coeff = BF::from_u32_with_reduction(*coeff);
        let input_idx = remap_constraint_input(&mut mapping, &mut inputs, *input);
        linear_terms.push(GpuGKRMainLayerConstraintLinearTerm {
            input: input_idx as u32,
            challenge: E::from_base(coeff),
            immediate_recipe: ImmediateFactorRecipeStructural::from_base(coeff),
        });
    }
    let constant = BF::from_u32_with_reduction(relation.constant);

    (
        GKRInputs {
            inputs_in_base: inputs,
            inputs_in_extension: Vec::new(),
            outputs_in_base: vec![output],
            outputs_in_extension: Vec::new(),
        },
        GpuGKRMainLayerConstraintHostMetadata {
            quadratic_terms: Vec::new(),
            linear_terms,
            constant_offset: E::from_base(constant),
            constant_offset_recipe: ImmediateFactorRecipeStructural::from_base(constant),
        },
    )
}

const NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL: u32 = u32::MAX;

fn remap_no_cache_base_input(
    mapping: &mut BTreeMap<GKRAddress, usize>,
    inputs: &mut Vec<GKRAddress>,
    address: GKRAddress,
) -> usize {
    remap_constraint_input(mapping, inputs, address)
}

fn remap_no_cache_linear_form_inputs<E>(
    mapping: &mut BTreeMap<GKRAddress, usize>,
    inputs: &mut Vec<GKRAddress>,
    terms: &BTreeMap<GKRAddress, E>,
) {
    for address in terms.keys().copied() {
        remap_no_cache_base_input(mapping, inputs, address);
    }
}

fn collect_no_cache_linear_form_inputs<E>(
    forms: &[&BTreeMap<GKRAddress, E>],
) -> (BTreeMap<GKRAddress, usize>, Vec<GKRAddress>) {
    let mut mapping = BTreeMap::new();
    let mut inputs = Vec::new();
    for terms in forms.iter().copied() {
        remap_no_cache_linear_form_inputs(&mut mapping, &mut inputs, terms);
    }
    (mapping, inputs)
}

fn remap_no_cache_linear_form_template_inputs(
    mapping: &mut BTreeMap<GKRAddress, usize>,
    inputs: &mut Vec<GKRAddress>,
    terms: &BTreeMap<GKRAddress, Vec<GpuGKRMainLayerConstraintChallengeTerm>>,
) {
    for address in terms.keys().copied() {
        remap_no_cache_base_input(mapping, inputs, address);
    }
}

fn collect_no_cache_linear_form_template_inputs(
    forms: &[&BTreeMap<GKRAddress, Vec<GpuGKRMainLayerConstraintChallengeTerm>>],
) -> (BTreeMap<GKRAddress, usize>, Vec<GKRAddress>) {
    let mut mapping = BTreeMap::new();
    let mut inputs = Vec::new();
    for terms in forms.iter().copied() {
        remap_no_cache_linear_form_template_inputs(&mut mapping, &mut inputs, terms);
    }
    (mapping, inputs)
}

fn encode_linear_form_as_quadratic_terms<E: Field>(
    mapping: &BTreeMap<GKRAddress, usize>,
    terms: &BTreeMap<GKRAddress, E>,
    constant: E,
) -> Vec<GpuGKRMainLayerConstraintQuadraticTerm<E>> {
    let mut encoded = terms
        .iter()
        .map(
            |(address, challenge)| GpuGKRMainLayerConstraintQuadraticTerm {
                lhs: mapping[address] as u32,
                rhs: 0,
                challenge: *challenge,
                immediate_recipe: ImmediateFactorRecipeStructural::zero(),
            },
        )
        .collect::<Vec<_>>();
    if !constant.is_zero() {
        encoded.push(GpuGKRMainLayerConstraintQuadraticTerm {
            lhs: NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL,
            rhs: 0,
            challenge: constant,
            immediate_recipe: ImmediateFactorRecipeStructural::zero(),
        });
    }
    encoded
}

fn encode_immediate_linear_form_as_quadratic_terms<E: Field>(
    mapping: &BTreeMap<GKRAddress, usize>,
    terms: &BTreeMap<GKRAddress, ImmediateCoeff<E>>,
    constant: ImmediateCoeff<E>,
) -> Vec<GpuGKRMainLayerConstraintQuadraticTerm<E>> {
    let mut encoded = terms
        .iter()
        .map(
            |(address, challenge)| GpuGKRMainLayerConstraintQuadraticTerm {
                lhs: mapping[address] as u32,
                rhs: 0,
                challenge: challenge.value,
                immediate_recipe: challenge.recipe.clone(),
            },
        )
        .collect::<Vec<_>>();
    if !constant.value.is_zero() {
        encoded.push(GpuGKRMainLayerConstraintQuadraticTerm {
            lhs: NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL,
            rhs: 0,
            challenge: constant.value,
            immediate_recipe: constant.recipe,
        });
    }
    encoded
}

fn encode_linear_form_as_linear_terms<E: Field>(
    mapping: &BTreeMap<GKRAddress, usize>,
    terms: &BTreeMap<GKRAddress, E>,
    constant: E,
) -> Vec<GpuGKRMainLayerConstraintLinearTerm<E>> {
    let mut encoded = terms
        .iter()
        .map(|(address, challenge)| GpuGKRMainLayerConstraintLinearTerm {
            input: mapping[address] as u32,
            challenge: *challenge,
            immediate_recipe: ImmediateFactorRecipeStructural::zero(),
        })
        .collect::<Vec<_>>();
    if !constant.is_zero() {
        encoded.push(GpuGKRMainLayerConstraintLinearTerm {
            input: NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL,
            challenge: constant,
            immediate_recipe: ImmediateFactorRecipeStructural::zero(),
        });
    }
    encoded
}

fn encode_immediate_linear_form_as_linear_terms<E: Field>(
    mapping: &BTreeMap<GKRAddress, usize>,
    terms: &BTreeMap<GKRAddress, ImmediateCoeff<E>>,
    constant: ImmediateCoeff<E>,
) -> Vec<GpuGKRMainLayerConstraintLinearTerm<E>> {
    let mut encoded = terms
        .iter()
        .map(|(address, challenge)| GpuGKRMainLayerConstraintLinearTerm {
            input: mapping[address] as u32,
            challenge: challenge.value,
            immediate_recipe: challenge.recipe.clone(),
        })
        .collect::<Vec<_>>();
    if !constant.value.is_zero() {
        encoded.push(GpuGKRMainLayerConstraintLinearTerm {
            input: NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL,
            challenge: constant.value,
            immediate_recipe: constant.recipe,
        });
    }
    encoded
}

fn encode_linear_form_as_quadratic_templates(
    mapping: &BTreeMap<GKRAddress, usize>,
    terms: &BTreeMap<GKRAddress, Vec<GpuGKRMainLayerConstraintChallengeTerm>>,
    constant_terms: &[GpuGKRMainLayerConstraintChallengeTerm],
) -> Vec<GpuGKRMainLayerConstraintQuadraticTemplate> {
    let mut encoded = terms
        .iter()
        .map(
            |(address, challenge_terms)| GpuGKRMainLayerConstraintQuadraticTemplate {
                lhs: mapping[address] as u32,
                rhs: 0,
                challenge_terms: challenge_terms.clone(),
            },
        )
        .collect::<Vec<_>>();
    if !constant_terms.is_empty() {
        encoded.push(GpuGKRMainLayerConstraintQuadraticTemplate {
            lhs: NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL,
            rhs: 0,
            challenge_terms: constant_terms.to_vec(),
        });
    }
    encoded
}

fn encode_linear_form_as_linear_templates(
    mapping: &BTreeMap<GKRAddress, usize>,
    terms: &BTreeMap<GKRAddress, Vec<GpuGKRMainLayerConstraintChallengeTerm>>,
    constant_terms: &[GpuGKRMainLayerConstraintChallengeTerm],
) -> Vec<GpuGKRMainLayerConstraintLinearTemplate> {
    let mut encoded = terms
        .iter()
        .map(
            |(address, challenge_terms)| GpuGKRMainLayerConstraintLinearTemplate {
                input: mapping[address] as u32,
                challenge_terms: challenge_terms.clone(),
            },
        )
        .collect::<Vec<_>>();
    if !constant_terms.is_empty() {
        encoded.push(GpuGKRMainLayerConstraintLinearTemplate {
            input: NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL,
            challenge_terms: constant_terms.to_vec(),
        });
    }
    encoded
}

fn validate_no_cache_linear_form_metadata<E: Field>(
    metadata: &GpuGKRMainLayerConstraintHostMetadata<E>,
    tail_inputs_len: usize,
) {
    let tail_inputs_len = tail_inputs_len as u32;
    for term in metadata.quadratic_terms.iter() {
        assert!(
            term.lhs == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL || term.lhs < tail_inputs_len,
            "no-cache quadratic term lhs {} exceeds tail input count {}",
            term.lhs,
            tail_inputs_len,
        );
    }
    for term in metadata.linear_terms.iter() {
        assert!(
            term.input == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL || term.input < tail_inputs_len,
            "no-cache linear term input {} exceeds tail input count {}",
            term.input,
            tail_inputs_len,
        );
    }
}

pub(crate) fn build_initial_grand_product_without_caches_inputs_and_metadata<
    E: Field + FieldExtension<BF>,
>(
    input: &[cs::gkr_compiler::NoFieldSpecialMemoryContributionRelation; 2],
    output: GKRAddress,
    external_challenges: &GKRExternalChallenges<BF, E>,
) -> (GKRInputs, GpuGKRMainLayerConstraintHostMetadata<E>) {
    let (lhs_terms, lhs_constant) =
        memory_query_as_flattened_relation::<E>(&input[0], external_challenges);
    let (rhs_terms, rhs_constant) =
        memory_query_as_flattened_relation::<E>(&input[1], external_challenges);
    let (mapping, inputs) = collect_no_cache_linear_form_inputs(&[&lhs_terms, &rhs_terms]);

    let metadata = GpuGKRMainLayerConstraintHostMetadata {
        quadratic_terms: encode_immediate_linear_form_as_quadratic_terms(
            &mapping,
            &lhs_terms,
            lhs_constant,
        ),
        linear_terms: encode_immediate_linear_form_as_linear_terms(
            &mapping,
            &rhs_terms,
            rhs_constant,
        ),
        constant_offset: E::ZERO,
        constant_offset_recipe: ImmediateFactorRecipeStructural::zero(),
    };
    validate_no_cache_linear_form_metadata(&metadata, inputs.len());

    (
        GKRInputs {
            inputs_in_base: inputs,
            inputs_in_extension: Vec::new(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: vec![output],
        },
        metadata,
    )
}

pub(crate) fn build_materialize_grand_product_term_expression_inputs_and_metadata<
    E: Field + FieldExtension<BF>,
>(
    relation: &cs::gkr_compiler::NoFieldSpecialMemoryContributionRelation,
    output: GKRAddress,
    external_challenges: &GKRExternalChallenges<BF, E>,
) -> (GKRInputs, GpuGKRMainLayerConstraintHostMetadata<E>) {
    let (terms, constant) = memory_query_as_flattened_relation::<E>(relation, external_challenges);
    let (mapping, inputs) = collect_no_cache_linear_form_inputs(&[&terms]);

    let metadata = GpuGKRMainLayerConstraintHostMetadata {
        quadratic_terms: Vec::new(),
        linear_terms: encode_immediate_linear_form_as_linear_terms(&mapping, &terms, constant),
        constant_offset: E::ZERO,
        constant_offset_recipe: ImmediateFactorRecipeStructural::zero(),
    };
    validate_no_cache_linear_form_metadata(&metadata, inputs.len());

    (
        GKRInputs {
            inputs_in_base: inputs,
            inputs_in_extension: Vec::new(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: vec![output],
        },
        metadata,
    )
}

fn flatten_lookup_setup_relation<E: Field>(
    setup: &[GKRAddress],
    lookup_multiplicative_challenge: E,
    lookup_additive_challenge: E,
) -> (BTreeMap<GKRAddress, E>, E) {
    let mut terms = BTreeMap::new();
    let mut challenge = E::ONE;
    for address in setup.iter().copied() {
        assert!(terms.insert(address, challenge).is_none());
        challenge.mul_assign(&lookup_multiplicative_challenge);
    }
    (terms, lookup_additive_challenge)
}

fn flatten_lookup_setup_relation_template(
    setup: &[GKRAddress],
) -> (
    BTreeMap<GKRAddress, Vec<GpuGKRMainLayerConstraintChallengeTerm>>,
    Vec<GpuGKRMainLayerConstraintChallengeTerm>,
) {
    let mut terms = BTreeMap::new();
    for (idx, address) in setup.iter().copied().enumerate() {
        assert!(terms
            .insert(
                address,
                vec![lookup_constraint_term(
                    1,
                    GpuGKRMainLayerDeferredChallengeSource::LookupMultiplicative,
                    idx as u32,
                )],
            )
            .is_none());
    }
    (
        terms,
        vec![lookup_constraint_term(
            1,
            GpuGKRMainLayerDeferredChallengeSource::LookupAdditive,
            1,
        )],
    )
}

pub(crate) fn build_lookup_pair_from_base_inputs_inputs_and_metadata<
    E: Field + FieldExtension<BF>,
>(
    input: &[cs::definitions::gkr::NoFieldSingleColumnLookupRelation; 2],
    output: [GKRAddress; 2],
    lookup_additive_challenge: E,
) -> (GKRInputs, GpuGKRMainLayerConstraintHostMetadata<E>) {
    let (lhs_terms, lhs_constant) =
        single_column_lookup_as_flattened_relation::<E, true>(&input[0], lookup_additive_challenge);
    let (rhs_terms, rhs_constant) =
        single_column_lookup_as_flattened_relation::<E, true>(&input[1], lookup_additive_challenge);
    let (mapping, inputs) = collect_no_cache_linear_form_inputs(&[&lhs_terms, &rhs_terms]);

    let metadata = GpuGKRMainLayerConstraintHostMetadata {
        quadratic_terms: encode_linear_form_as_quadratic_terms(&mapping, &lhs_terms, lhs_constant),
        linear_terms: encode_linear_form_as_linear_terms(&mapping, &rhs_terms, rhs_constant),
        constant_offset: E::ZERO,
        constant_offset_recipe: ImmediateFactorRecipeStructural::zero(),
    };
    validate_no_cache_linear_form_metadata(&metadata, inputs.len());

    (
        GKRInputs {
            inputs_in_base: inputs,
            inputs_in_extension: Vec::new(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: output.to_vec(),
        },
        metadata,
    )
}

pub(crate) fn build_lookup_pair_from_base_inputs_inputs_and_template(
    input: &[cs::definitions::gkr::NoFieldSingleColumnLookupRelation; 2],
    output: [GKRAddress; 2],
) -> (GKRInputs, GpuGKRMainLayerConstraintTemplate) {
    let (lhs_terms, lhs_constant_terms) =
        single_column_lookup_as_flattened_relation_template::<true>(&input[0]);
    let (rhs_terms, rhs_constant_terms) =
        single_column_lookup_as_flattened_relation_template::<true>(&input[1]);
    let (mapping, inputs) = collect_no_cache_linear_form_template_inputs(&[&lhs_terms, &rhs_terms]);

    (
        GKRInputs {
            inputs_in_base: inputs,
            inputs_in_extension: Vec::new(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: output.to_vec(),
        },
        GpuGKRMainLayerConstraintTemplate {
            quadratic_terms: encode_linear_form_as_quadratic_templates(
                &mapping,
                &lhs_terms,
                &lhs_constant_terms,
            ),
            linear_terms: encode_linear_form_as_linear_templates(
                &mapping,
                &rhs_terms,
                &rhs_constant_terms,
            ),
            constant_terms: Vec::new(),
        },
    )
}

pub(crate) fn build_lookup_pair_from_vector_inputs_inputs_and_metadata<
    E: Field + FieldExtension<BF>,
>(
    input: &[cs::definitions::gkr::NoFieldVectorLookupRelation; 2],
    output: [GKRAddress; 2],
    lookup_multiplicative_challenge: E,
    lookup_additive_challenge: E,
) -> (GKRInputs, GpuGKRMainLayerConstraintHostMetadata<E>) {
    let (lhs_terms, lhs_constant) = vector_lookup_as_flattened_relation::<E, true>(
        &input[0],
        lookup_multiplicative_challenge,
        lookup_additive_challenge,
    );
    let (rhs_terms, rhs_constant) = vector_lookup_as_flattened_relation::<E, true>(
        &input[1],
        lookup_multiplicative_challenge,
        lookup_additive_challenge,
    );
    let (mapping, inputs) = collect_no_cache_linear_form_inputs(&[&lhs_terms, &rhs_terms]);

    let metadata = GpuGKRMainLayerConstraintHostMetadata {
        quadratic_terms: encode_linear_form_as_quadratic_terms(&mapping, &lhs_terms, lhs_constant),
        linear_terms: encode_linear_form_as_linear_terms(&mapping, &rhs_terms, rhs_constant),
        constant_offset: E::ZERO,
        constant_offset_recipe: ImmediateFactorRecipeStructural::zero(),
    };
    validate_no_cache_linear_form_metadata(&metadata, inputs.len());

    (
        GKRInputs {
            inputs_in_base: inputs,
            inputs_in_extension: Vec::new(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: output.to_vec(),
        },
        metadata,
    )
}

pub(crate) fn build_lookup_pair_from_vector_inputs_inputs_and_template(
    input: &[cs::definitions::gkr::NoFieldVectorLookupRelation; 2],
    output: [GKRAddress; 2],
) -> (GKRInputs, GpuGKRMainLayerConstraintTemplate) {
    let (lhs_terms, lhs_constant_terms) =
        vector_lookup_as_flattened_relation_template::<true>(&input[0]);
    let (rhs_terms, rhs_constant_terms) =
        vector_lookup_as_flattened_relation_template::<true>(&input[1]);
    let (mapping, inputs) = collect_no_cache_linear_form_template_inputs(&[&lhs_terms, &rhs_terms]);

    (
        GKRInputs {
            inputs_in_base: inputs,
            inputs_in_extension: Vec::new(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: output.to_vec(),
        },
        GpuGKRMainLayerConstraintTemplate {
            quadratic_terms: encode_linear_form_as_quadratic_templates(
                &mapping,
                &lhs_terms,
                &lhs_constant_terms,
            ),
            linear_terms: encode_linear_form_as_linear_templates(
                &mapping,
                &rhs_terms,
                &rhs_constant_terms,
            ),
            constant_terms: Vec::new(),
        },
    )
}

pub(crate) fn build_materialized_vector_lookup_input_inputs_and_metadata<
    E: Field + FieldExtension<BF>,
>(
    input: &cs::definitions::gkr::NoFieldVectorLookupRelation,
    output: GKRAddress,
    lookup_multiplicative_challenge: E,
) -> (GKRInputs, GpuGKRMainLayerConstraintHostMetadata<E>) {
    let (terms, constant) = vector_lookup_as_flattened_relation::<E, false>(
        input,
        lookup_multiplicative_challenge,
        E::ZERO,
    );
    let (mapping, inputs) = collect_no_cache_linear_form_inputs(&[&terms]);
    let metadata = GpuGKRMainLayerConstraintHostMetadata {
        quadratic_terms: Vec::new(),
        linear_terms: encode_linear_form_as_linear_terms(&mapping, &terms, constant),
        constant_offset: E::ZERO,
        constant_offset_recipe: ImmediateFactorRecipeStructural::zero(),
    };
    validate_no_cache_linear_form_metadata(&metadata, inputs.len());

    (
        GKRInputs {
            inputs_in_base: inputs,
            inputs_in_extension: Vec::new(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: vec![output],
        },
        metadata,
    )
}

pub(crate) fn build_materialized_vector_lookup_input_inputs_and_template(
    input: &cs::definitions::gkr::NoFieldVectorLookupRelation,
    output: GKRAddress,
) -> (GKRInputs, GpuGKRMainLayerConstraintTemplate) {
    let (terms, constant_terms) = vector_lookup_as_flattened_relation_template::<false>(input);
    let (mapping, inputs) = collect_no_cache_linear_form_template_inputs(&[&terms]);

    (
        GKRInputs {
            inputs_in_base: inputs,
            inputs_in_extension: Vec::new(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: vec![output],
        },
        GpuGKRMainLayerConstraintTemplate {
            quadratic_terms: Vec::new(),
            linear_terms: encode_linear_form_as_linear_templates(&mapping, &terms, &constant_terms),
            constant_terms: Vec::new(),
        },
    )
}

pub(crate) fn build_lookup_with_dens_and_setup_expressions_inputs_and_metadata<
    E: Field + FieldExtension<BF>,
>(
    input: &(
        GKRAddress,
        cs::definitions::gkr::NoFieldVectorLookupRelation,
    ),
    setup: &(GKRAddress, Box<[GKRAddress]>),
    output: [GKRAddress; 2],
    lookup_multiplicative_challenge: E,
    lookup_additive_challenge: E,
) -> (GKRInputs, GpuGKRMainLayerConstraintHostMetadata<E>) {
    let (input_terms, input_constant) = vector_lookup_as_flattened_relation::<E, true>(
        &input.1,
        lookup_multiplicative_challenge,
        lookup_additive_challenge,
    );
    let (setup_terms, setup_constant) = flatten_lookup_setup_relation(
        setup.1.as_ref(),
        lookup_multiplicative_challenge,
        lookup_additive_challenge,
    );
    let (tail_mapping, tail_inputs) =
        collect_no_cache_linear_form_inputs(&[&input_terms, &setup_terms]);
    let inputs = std::iter::once(input.0)
        .chain(std::iter::once(setup.0))
        .chain(tail_inputs.iter().copied())
        .collect::<Vec<_>>();

    let metadata = GpuGKRMainLayerConstraintHostMetadata {
        quadratic_terms: encode_linear_form_as_quadratic_terms(
            &tail_mapping,
            &input_terms,
            input_constant,
        ),
        linear_terms: encode_linear_form_as_linear_terms(
            &tail_mapping,
            &setup_terms,
            setup_constant,
        ),
        constant_offset: E::ZERO,
        constant_offset_recipe: ImmediateFactorRecipeStructural::zero(),
    };
    validate_no_cache_linear_form_metadata(&metadata, tail_inputs.len());

    (
        GKRInputs {
            inputs_in_base: inputs,
            inputs_in_extension: Vec::new(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: output.to_vec(),
        },
        metadata,
    )
}

pub(crate) fn build_lookup_with_dens_and_setup_expressions_inputs_and_template(
    input: &(
        GKRAddress,
        cs::definitions::gkr::NoFieldVectorLookupRelation,
    ),
    setup: &(GKRAddress, Box<[GKRAddress]>),
    output: [GKRAddress; 2],
) -> (GKRInputs, GpuGKRMainLayerConstraintTemplate) {
    let (input_terms, input_constant_terms) =
        vector_lookup_as_flattened_relation_template::<true>(&input.1);
    let (setup_terms, setup_constant_terms) =
        flatten_lookup_setup_relation_template(setup.1.as_ref());
    let (tail_mapping, tail_inputs) =
        collect_no_cache_linear_form_template_inputs(&[&input_terms, &setup_terms]);
    let inputs = std::iter::once(input.0)
        .chain(std::iter::once(setup.0))
        .chain(tail_inputs.iter().copied())
        .collect::<Vec<_>>();

    (
        GKRInputs {
            inputs_in_base: inputs,
            inputs_in_extension: Vec::new(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: output.to_vec(),
        },
        GpuGKRMainLayerConstraintTemplate {
            quadratic_terms: encode_linear_form_as_quadratic_templates(
                &tail_mapping,
                &input_terms,
                &input_constant_terms,
            ),
            linear_terms: encode_linear_form_as_linear_templates(
                &tail_mapping,
                &setup_terms,
                &setup_constant_terms,
            ),
            constant_terms: Vec::new(),
        },
    )
}

pub(crate) fn build_lookup_from_vector_input_with_setup_inputs_and_metadata<
    E: Field + FieldExtension<BF>,
>(
    input: &cs::definitions::gkr::NoFieldVectorLookupRelation,
    setup: &(GKRAddress, Box<[GKRAddress]>),
    output: [GKRAddress; 2],
    lookup_multiplicative_challenge: E,
    lookup_additive_challenge: E,
) -> (GKRInputs, GpuGKRMainLayerConstraintHostMetadata<E>) {
    let (input_terms, input_constant) = vector_lookup_as_flattened_relation::<E, true>(
        input,
        lookup_multiplicative_challenge,
        lookup_additive_challenge,
    );
    let (setup_terms, setup_constant) = flatten_lookup_setup_relation(
        setup.1.as_ref(),
        lookup_multiplicative_challenge,
        lookup_additive_challenge,
    );
    let (tail_mapping, tail_inputs) =
        collect_no_cache_linear_form_inputs(&[&input_terms, &setup_terms]);
    let inputs = std::iter::once(setup.0)
        .chain(tail_inputs.iter().copied())
        .collect::<Vec<_>>();

    let metadata = GpuGKRMainLayerConstraintHostMetadata {
        quadratic_terms: encode_linear_form_as_quadratic_terms(
            &tail_mapping,
            &input_terms,
            input_constant,
        ),
        linear_terms: encode_linear_form_as_linear_terms(
            &tail_mapping,
            &setup_terms,
            setup_constant,
        ),
        constant_offset: E::ZERO,
        constant_offset_recipe: ImmediateFactorRecipeStructural::zero(),
    };
    validate_no_cache_linear_form_metadata(&metadata, tail_inputs.len());

    (
        GKRInputs {
            inputs_in_base: inputs,
            inputs_in_extension: Vec::new(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: output.to_vec(),
        },
        metadata,
    )
}

pub(crate) fn build_lookup_from_vector_input_with_setup_inputs_and_template(
    input: &cs::definitions::gkr::NoFieldVectorLookupRelation,
    setup: &(GKRAddress, Box<[GKRAddress]>),
    output: [GKRAddress; 2],
) -> (GKRInputs, GpuGKRMainLayerConstraintTemplate) {
    let (input_terms, input_constant_terms) =
        vector_lookup_as_flattened_relation_template::<true>(input);
    let (setup_terms, setup_constant_terms) =
        flatten_lookup_setup_relation_template(setup.1.as_ref());
    let (tail_mapping, tail_inputs) =
        collect_no_cache_linear_form_template_inputs(&[&input_terms, &setup_terms]);
    let inputs = std::iter::once(setup.0)
        .chain(tail_inputs.iter().copied())
        .collect::<Vec<_>>();

    (
        GKRInputs {
            inputs_in_base: inputs,
            inputs_in_extension: Vec::new(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: output.to_vec(),
        },
        GpuGKRMainLayerConstraintTemplate {
            quadratic_terms: encode_linear_form_as_quadratic_templates(
                &tail_mapping,
                &input_terms,
                &input_constant_terms,
            ),
            linear_terms: encode_linear_form_as_linear_templates(
                &tail_mapping,
                &setup_terms,
                &setup_constant_terms,
            ),
            constant_terms: Vec::new(),
        },
    )
}

pub(crate) fn build_lookup_unbalanced_pair_with_vector_inputs_inputs_and_metadata<
    E: Field + FieldExtension<BF>,
>(
    input: [GKRAddress; 2],
    remainder: &cs::definitions::gkr::NoFieldVectorLookupRelation,
    output: [GKRAddress; 2],
    lookup_multiplicative_challenge: E,
    lookup_additive_challenge: E,
) -> (GKRInputs, GpuGKRMainLayerConstraintHostMetadata<E>) {
    let (remainder_terms, remainder_constant) = vector_lookup_as_flattened_relation::<E, true>(
        remainder,
        lookup_multiplicative_challenge,
        lookup_additive_challenge,
    );
    let (mapping, base_inputs) = collect_no_cache_linear_form_inputs(&[&remainder_terms]);

    let metadata = GpuGKRMainLayerConstraintHostMetadata {
        quadratic_terms: Vec::new(),
        linear_terms: encode_linear_form_as_linear_terms(
            &mapping,
            &remainder_terms,
            remainder_constant,
        ),
        constant_offset: E::ZERO,
        constant_offset_recipe: ImmediateFactorRecipeStructural::zero(),
    };
    validate_no_cache_linear_form_metadata(&metadata, base_inputs.len());

    (
        GKRInputs {
            inputs_in_base: base_inputs,
            inputs_in_extension: input.to_vec(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: output.to_vec(),
        },
        metadata,
    )
}

pub(crate) fn build_lookup_unbalanced_pair_with_vector_inputs_inputs_and_template(
    input: [GKRAddress; 2],
    remainder: &cs::definitions::gkr::NoFieldVectorLookupRelation,
    output: [GKRAddress; 2],
) -> (GKRInputs, GpuGKRMainLayerConstraintTemplate) {
    let (remainder_terms, remainder_constant_terms) =
        vector_lookup_as_flattened_relation_template::<true>(remainder);
    let (mapping, base_inputs) = collect_no_cache_linear_form_template_inputs(&[&remainder_terms]);

    (
        GKRInputs {
            inputs_in_base: base_inputs,
            inputs_in_extension: input.to_vec(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: output.to_vec(),
        },
        GpuGKRMainLayerConstraintTemplate {
            quadratic_terms: Vec::new(),
            linear_terms: encode_linear_form_as_linear_templates(
                &mapping,
                &remainder_terms,
                &remainder_constant_terms,
            ),
            constant_terms: Vec::new(),
        },
    )
}

fn build_dimension_reducing_kernel_blueprints<E: Field>(
    layer: &BTreeMap<OutputType, DimensionReducingInputOutput>,
    batch_challenge_base: E,
) -> Vec<DimensionReducingKernelBlueprint<E>> {
    let mut current_batch_challenge = E::ONE;
    let mut next_batch_challenge_offset = 0usize;
    let mut get_challenge = || {
        let challenge = current_batch_challenge;
        current_batch_challenge.mul_assign(&batch_challenge_base);
        challenge
    };

    let mut blueprints = Vec::new();
    for (output_type, reduced_io) in layer.iter() {
        match *output_type {
            OutputType::PermutationProduct => {
                for (input, output) in reduced_io.inputs.iter().zip(reduced_io.output.iter()) {
                    let batch_challenge_offset = next_batch_challenge_offset;
                    next_batch_challenge_offset += 1;
                    blueprints.push(DimensionReducingKernelBlueprint {
                        kind: GpuGKRDimensionReducingKernelKind::Pairwise,
                        inputs: GKRInputs {
                            inputs_in_base: Vec::new(),
                            inputs_in_extension: vec![*input],
                            outputs_in_base: Vec::new(),
                            outputs_in_extension: vec![*output],
                        },
                        batch_challenge_offset,
                        batch_challenge_count: 1,
                        batch_challenges: vec![get_challenge()],
                    });
                }
            }
            OutputType::Lookup16Bits | OutputType::LookupTimestamps | OutputType::GenericLookup => {
                let inputs: [GKRAddress; 2] = reduced_io
                    .inputs
                    .clone()
                    .try_into()
                    .expect("dimension-reducing lookup kernels expect exactly two inputs");
                let outputs: [GKRAddress; 2] = reduced_io
                    .output
                    .clone()
                    .try_into()
                    .expect("dimension-reducing lookup kernels expect exactly two outputs");
                let batch_challenge_offset = next_batch_challenge_offset;
                next_batch_challenge_offset += 2;
                blueprints.push(DimensionReducingKernelBlueprint {
                    kind: GpuGKRDimensionReducingKernelKind::Lookup,
                    inputs: GKRInputs {
                        inputs_in_base: Vec::new(),
                        inputs_in_extension: inputs.to_vec(),
                        outputs_in_base: Vec::new(),
                        outputs_in_extension: outputs.to_vec(),
                    },
                    batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: vec![get_challenge(), get_challenge()],
                });
            }
        }
    }

    blueprints
}

fn build_dimension_reducing_kernel_blueprints_static<E: Field>(
    layer: &BTreeMap<OutputType, DimensionReducingInputOutput>,
) -> Vec<DimensionReducingKernelBlueprint<E>> {
    let mut next_batch_challenge_offset = 0usize;
    let mut blueprints = Vec::new();
    for (output_type, reduced_io) in layer.iter() {
        match *output_type {
            OutputType::PermutationProduct => {
                for (input, output) in reduced_io.inputs.iter().zip(reduced_io.output.iter()) {
                    let batch_challenge_offset = next_batch_challenge_offset;
                    next_batch_challenge_offset += 1;
                    blueprints.push(DimensionReducingKernelBlueprint {
                        kind: GpuGKRDimensionReducingKernelKind::Pairwise,
                        inputs: GKRInputs {
                            inputs_in_base: Vec::new(),
                            inputs_in_extension: vec![*input],
                            outputs_in_base: Vec::new(),
                            outputs_in_extension: vec![*output],
                        },
                        batch_challenge_offset,
                        batch_challenge_count: 1,
                        batch_challenges: Vec::new(),
                    });
                }
            }
            OutputType::Lookup16Bits | OutputType::LookupTimestamps | OutputType::GenericLookup => {
                let inputs: [GKRAddress; 2] = reduced_io
                    .inputs
                    .clone()
                    .try_into()
                    .expect("dimension-reducing lookup kernels expect exactly two inputs");
                let outputs: [GKRAddress; 2] = reduced_io
                    .output
                    .clone()
                    .try_into()
                    .expect("dimension-reducing lookup kernels expect exactly two outputs");
                let batch_challenge_offset = next_batch_challenge_offset;
                next_batch_challenge_offset += 2;
                blueprints.push(DimensionReducingKernelBlueprint {
                    kind: GpuGKRDimensionReducingKernelKind::Lookup,
                    inputs: GKRInputs {
                        inputs_in_base: Vec::new(),
                        inputs_in_extension: inputs.to_vec(),
                        outputs_in_base: Vec::new(),
                        outputs_in_extension: outputs.to_vec(),
                    },
                    batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: Vec::new(),
                });
            }
        }
    }

    blueprints
}

fn resolve_main_layer_auxiliary_challenge<E: Copy>(
    source: GpuGKRMainLayerAuxiliaryChallengeSource<E>,
    lookup_additive_challenge: E,
) -> E {
    match source {
        GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(value) => value,
        GpuGKRMainLayerAuxiliaryChallengeSource::LookupAdditive => lookup_additive_challenge,
    }
}

pub(super) fn evaluate_constraint_prefactor<E: Field + FieldExtension<BF>>(
    challenge_terms: &[GpuGKRMainLayerConstraintChallengeTerm],
    lookup_multiplicative_challenge: E,
    lookup_additive_challenge: E,
) -> E {
    let mut total = E::ZERO;
    for term in challenge_terms.iter() {
        let challenge = match term.source {
            GpuGKRMainLayerDeferredChallengeSource::LookupMultiplicative => {
                lookup_multiplicative_challenge
            }
            GpuGKRMainLayerDeferredChallengeSource::LookupAdditive => lookup_additive_challenge,
        };
        let mut contribution = challenge.pow(term.power);
        contribution.mul_assign_by_base(&term.coeff);
        total.add_assign(&contribution);
    }
    total
}

fn resolve_main_layer_constraint_metadata<E: Field + FieldExtension<BF>>(
    source: Option<GpuGKRMainLayerConstraintMetadataSource<E>>,
) -> Option<GpuGKRMainLayerConstraintHostMetadata<E>> {
    match source {
        None => None,
        Some(GpuGKRMainLayerConstraintMetadataSource::Immediate(metadata)) => Some(metadata),
        Some(GpuGKRMainLayerConstraintMetadataSource::Deferred(_template)) => {
            unreachable!("static main-layer constraint metadata should be materialized eagerly")
        }
    }
}

fn summarize_main_layer_constraint_metadata_source<E: Field>(
    source: Option<&GpuGKRMainLayerConstraintMetadataSource<E>>,
) -> Option<(usize, usize, E)> {
    match source {
        None => None,
        Some(GpuGKRMainLayerConstraintMetadataSource::Immediate(metadata)) => Some((
            metadata.quadratic_terms.len(),
            metadata.linear_terms.len(),
            metadata.constant_offset,
        )),
        Some(GpuGKRMainLayerConstraintMetadataSource::Deferred(template)) => Some((
            template.quadratic_terms.len(),
            template.linear_terms.len(),
            E::ZERO,
        )),
    }
}

struct PreparedMainLayerKernelStaticData<E: Copy> {
    kind: GpuGKRMainLayerKernelKind,
    auxiliary_challenge: E,
    constraint_metadata: Option<GpuGKRMainLayerConstraintHostMetadata<E>>,
    round0_descriptors: GpuSumcheckRound0LaunchDescriptors<BF, E>,
    round1_descriptors: GpuSumcheckRound1HostLaunchDescriptors<BF, E>,
    round2_descriptors: GpuSumcheckRound2HostLaunchDescriptors<BF, E>,
    round3_descriptors: Vec<GpuGKRMainLayerRound3HostDescriptors<E>>,
}

fn build_main_layer_kernel_blueprints<E: Field + FieldExtension<BF>>(
    layer: &GKRLayerDescription,
    layer_idx: usize,
    storage: &GpuGKRStorage<BF, E>,
    external_challenges: &GKRExternalChallenges<BF, E>,
    inits_and_teardowns_top_bits: &[u32],
    inits_and_teardowns_address_high_bits_shift: u32,
    batch_challenge_base: E,
    lookup_multiplicative_challenge: E,
    lookup_additive_challenge: E,
    num_base_layer_memory_polys: usize,
    num_base_layer_witness_polys: usize,
) -> Vec<GpuGKRMainLayerKernelBlueprint<E>> {
    let mut current_batch_challenge = E::ONE;
    let mut next_batch_challenge_offset = 0usize;
    let mut get_challenge = || {
        let challenge = current_batch_challenge;
        current_batch_challenge.mul_assign(&batch_challenge_base);
        challenge
    };

    let mut blueprints = Vec::new();
    for gate in layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
    {
        let push_challenges = |count: usize,
                               next_batch_challenge_offset: &mut usize,
                               get_challenge: &mut dyn FnMut() -> E| {
            let batch_challenge_offset = *next_batch_challenge_offset;
            *next_batch_challenge_offset += count;
            let batch_challenges = (0..count).map(|_| get_challenge()).collect::<Vec<_>>();
            (batch_challenge_offset, batch_challenges)
        };
        match &gate.enforced_relation {
            NoFieldGKRRelation::CopyInBaseField { input, output }
            | NoFieldGKRRelation::CopyInExtensionField { input, output } => {
                let (batch_challenge_offset, batch_challenges) =
                    push_challenges(1, &mut next_batch_challenge_offset, &mut get_challenge);
                if storage.layers[layer_idx]
                    .base_field_inputs
                    .contains_key(input)
                {
                    let relation = BaseFieldCopyGKRRelation {
                        input: *input,
                        output: *output,
                    };
                    blueprints.push(GpuGKRMainLayerKernelBlueprint {
                        kind: GpuGKRMainLayerKernelKind::BaseCopy,
                        inputs: <BaseFieldCopyGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                            &relation,
                        ),
                        batch_challenge_offset,
                        batch_challenge_count: 1,
                        batch_challenges,
                        auxiliary_challenge_source:
                            GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(E::ZERO),
                        constraint_metadata_source: None,
                    });
                } else {
                    let relation = ExtensionCopyGKRRelation {
                        input: *input,
                        output: *output,
                    };
                    blueprints.push(GpuGKRMainLayerKernelBlueprint {
                        kind: GpuGKRMainLayerKernelKind::ExtCopy,
                        inputs: <ExtensionCopyGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                            &relation,
                        ),
                        batch_challenge_offset,
                        batch_challenge_count: 1,
                        batch_challenges,
                        auxiliary_challenge_source:
                            GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(E::ZERO),
                        constraint_metadata_source: None,
                    });
                }
            }
            NoFieldGKRRelation::InitialGrandProductFromCaches { input, output }
            | NoFieldGKRRelation::TrivialProduct { input, output } => {
                let relation = SameSizeProductGKRRelation {
                    inputs: *input,
                    output: *output,
                };
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::Product,
                    inputs: <SameSizeProductGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                        &relation,
                    ),
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 1,
                    batch_challenges: {
                        next_batch_challenge_offset += 1;
                        vec![get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::InitialGrandProductWithoutCaches { input, output } => {
                let (inputs, constraint_metadata) =
                    build_initial_grand_product_without_caches_inputs_and_metadata(
                        input,
                        *output,
                        external_challenges,
                    );
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::InitialGrandProductWithoutCaches,
                    inputs,
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 1,
                    batch_challenges: {
                        next_batch_challenge_offset += 1;
                        vec![get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::MaskIntoIdentityProduct {
                input,
                mask,
                output,
            } => {
                let relation = MaskIntoIdentityProductGKRRelation {
                    input: *input,
                    mask: *mask,
                    output: *output,
                };
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::MaskIdentity,
                    inputs:
                        <MaskIntoIdentityProductGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                            &relation,
                        ),
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 1,
                    batch_challenges: {
                        next_batch_challenge_offset += 1;
                        vec![get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::AggregateLookupRationalPair { input, output } => {
                let relation = LookupPairGKRRelation {
                    inputs: *input,
                    outputs: *output,
                };
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupPair,
                    inputs: <LookupPairGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                        &relation,
                    ),
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: {
                        next_batch_challenge_offset += 2;
                        vec![get_challenge(), get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs { input, output } => {
                let relation = LookupBasePairGKRRelation::<BF, E> {
                    inputs: *input,
                    outputs: *output,
                    lookup_additive_challenge: E::ZERO,
                    _marker: core::marker::PhantomData,
                };
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupBasePair,
                    inputs:
                        <LookupBasePairGKRRelation<BF, E> as BatchedGKRKernel<BF, E>>::get_inputs(
                            &relation,
                        ),
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: {
                        next_batch_challenge_offset += 2;
                        vec![get_challenge(), get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        lookup_additive_challenge,
                    ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::LookupPairFromBaseInputs { input, output, .. } => {
                let (inputs, constraint_metadata) =
                    build_lookup_pair_from_base_inputs_inputs_and_metadata(
                        input,
                        *output,
                        lookup_additive_challenge,
                    );
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupPairFromBaseInputs,
                    inputs,
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: {
                        next_batch_challenge_offset += 2;
                        vec![get_challenge(), get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::LookupFromMaterializedBaseInputWithSetup {
                input,
                setup,
                output,
            } => {
                let relation = LookupBaseMinusMultiplicityByBaseGKRRelation::<BF, E> {
                    input: *input,
                    setup: *setup,
                    outputs: *output,
                    lookup_additive_challenge: E::ZERO,
                    _marker: core::marker::PhantomData,
                };
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupBaseMinusMultiplicityByBase,
                    inputs:
                        <LookupBaseMinusMultiplicityByBaseGKRRelation<BF, E> as BatchedGKRKernel<
                            BF,
                            E,
                        >>::get_inputs(&relation),
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: {
                        next_batch_challenge_offset += 2;
                        vec![get_challenge(), get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        lookup_additive_challenge,
                    ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::LookupWithDensAndSetupExpressions {
                input,
                setup,
                output,
            } => {
                let (inputs, constraint_metadata) =
                    build_lookup_with_dens_and_setup_expressions_inputs_and_metadata(
                        input,
                        setup,
                        *output,
                        lookup_multiplicative_challenge,
                        lookup_additive_challenge,
                    );
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupWithDensAndSetupExpressions,
                    inputs,
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: {
                        next_batch_challenge_offset += 2;
                        vec![get_challenge(), get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::LookupFromMaterializedVectorInputWithSetup {
                input,
                setup,
                output,
            } => {
                let relation = LookupExtensionMinusMultiplicityByExtensionGKRRelation::<BF, E> {
                    input: *input,
                    setup: *setup,
                    outputs: *output,
                    lookup_additive_challenge: E::ZERO,
                    _marker: core::marker::PhantomData,
                };
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupExtMinusMultiplicityByExt,
                    inputs: <LookupExtensionMinusMultiplicityByExtensionGKRRelation<BF, E> as BatchedGKRKernel<
                        BF,
                        E,
                    >>::get_inputs(&relation),
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: {
                        next_batch_challenge_offset += 2;
                        vec![get_challenge(), get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        lookup_additive_challenge,
                    ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::LookupPairFromMaterializedVectorInputs { input, output }
            | NoFieldGKRRelation::LookupPairFromCachedVectorInputs { input, output } => {
                let relation = LookupExtensionPairGKRRelation::<BF, E> {
                    inputs: *input,
                    outputs: *output,
                    lookup_additive_challenge: E::ZERO,
                    _marker: core::marker::PhantomData,
                };
                blueprints.push(
                    GpuGKRMainLayerKernelBlueprint {
                        kind: GpuGKRMainLayerKernelKind::LookupExtPair,
                        inputs: <LookupExtensionPairGKRRelation<BF, E> as BatchedGKRKernel<
                            BF,
                            E,
                        >>::get_inputs(&relation),
                        batch_challenge_offset: next_batch_challenge_offset,
                        batch_challenge_count: 2,
                        batch_challenges: {
                            next_batch_challenge_offset += 2;
                            vec![get_challenge(), get_challenge()]
                        },
                        auxiliary_challenge_source:
                            GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                                lookup_additive_challenge,
                            ),
                        constraint_metadata_source: None,
                    },
                );
            }
            NoFieldGKRRelation::LookupPairFromVectorInputs { input, output } => {
                let (inputs, constraint_metadata) =
                    build_lookup_pair_from_vector_inputs_inputs_and_metadata(
                        input,
                        *output,
                        lookup_multiplicative_challenge,
                        lookup_additive_challenge,
                    );
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupPairFromVectorInputs,
                    inputs,
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: {
                        next_batch_challenge_offset += 2;
                        vec![get_challenge(), get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedBaseInputs {
                input,
                remainder,
                output,
            } => {
                let relation = LookupRationalPairWithUnbalancedBaseGKRRelation::<BF, E> {
                    inputs: *input,
                    remainder: *remainder,
                    outputs: *output,
                    lookup_additive_challenge: E::ZERO,
                    _marker: core::marker::PhantomData,
                };
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupUnbalanced,
                    inputs: <LookupRationalPairWithUnbalancedBaseGKRRelation<BF, E> as BatchedGKRKernel<BF, E>>::get_inputs(
                        &relation,
                    ),
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: {
                        next_batch_challenge_offset += 2;
                        vec![get_challenge(), get_challenge()]
                    },
                    auxiliary_challenge_source:
                        GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                            lookup_additive_challenge,
                        ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedVectorInputs {
                input,
                remainder,
                output,
            } => {
                let relation = LookupRationalPairWithUnbalancedExtensionGKRRelation::<BF, E> {
                    inputs: *input,
                    remainder: *remainder,
                    outputs: *output,
                    lookup_additive_challenge: E::ZERO,
                    _marker: core::marker::PhantomData,
                };
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupUnbalancedExtension,
                    inputs: <LookupRationalPairWithUnbalancedExtensionGKRRelation<BF, E> as BatchedGKRKernel<BF, E>>::get_inputs(
                        &relation,
                    ),
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: {
                        next_batch_challenge_offset += 2;
                        vec![get_challenge(), get_challenge()]
                    },
                    auxiliary_challenge_source:
                        GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                            lookup_additive_challenge,
                        ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::MaterializedVectorLookupInput { input, output } => {
                let (inputs, constraint_metadata) =
                    build_materialized_vector_lookup_input_inputs_and_metadata(
                        input,
                        *output,
                        lookup_multiplicative_challenge,
                    );
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::MaterializeGrandProductTermExpression,
                    inputs,
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 1,
                    batch_challenges: {
                        next_batch_challenge_offset += 1;
                        vec![get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithVectorInputs {
                input,
                remainder,
                output,
            } => {
                let (inputs, constraint_metadata) =
                    build_lookup_unbalanced_pair_with_vector_inputs_inputs_and_metadata(
                        *input,
                        remainder,
                        *output,
                        lookup_multiplicative_challenge,
                        lookup_additive_challenge,
                    );
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupUnbalancedPairWithVectorInputs,
                    inputs,
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: {
                        next_batch_challenge_offset += 2;
                        vec![get_challenge(), get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::LookupWithCachedDensAndSetup {
                input,
                setup,
                output,
            } => {
                let relation = LookupBaseExtMinusBaseExtGKRRelation::<BF, E> {
                    nums: [input[0], setup[0]],
                    dens: [input[1], setup[1]],
                    outputs: *output,
                    lookup_additive_challenge: E::ZERO,
                    _marker: core::marker::PhantomData,
                };
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupWithCachedDensAndSetup,
                    inputs: <LookupBaseExtMinusBaseExtGKRRelation<BF, E> as BatchedGKRKernel<
                        BF,
                        E,
                    >>::get_inputs(&relation),
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: {
                        next_batch_challenge_offset += 2;
                        vec![get_challenge(), get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        lookup_additive_challenge,
                    ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::EnforceConstraintsMaxQuadratic { .. } => {
                unreachable!(
                    "batched max-quadratic constraints not supported on GPU; cs/ must emit EnforceSingleMaxQuadraticConstraint (USE_BATCHING=false)"
                );
            }
            NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint { input } => {
                let (inputs, constraint_metadata) =
                    build_single_max_quadratic_constraint_inputs_and_metadata::<E>(input);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic,
                    inputs,
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 1,
                    batch_challenges: {
                        next_batch_challenge_offset += 1;
                        vec![get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::MaterializeSingleLookupInput { input, output, .. } => {
                let (inputs, constraint_metadata) =
                    build_linear_base_kernel_inputs_and_metadata::<E>(&input.input, *output);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LinearBaseOutput,
                    inputs,
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 1,
                    batch_challenges: {
                        next_batch_challenge_offset += 1;
                        vec![get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::LookupFromVectorInputWithSetup {
                input,
                setup,
                output,
            } => {
                let (inputs, constraint_metadata) =
                    build_lookup_from_vector_input_with_setup_inputs_and_metadata(
                        input,
                        setup,
                        *output,
                        lookup_multiplicative_challenge,
                        lookup_additive_challenge,
                    );
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupFromVectorInputWithSetup,
                    inputs,
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: {
                        next_batch_challenge_offset += 2;
                        vec![get_challenge(), get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::MaterializeGrandProductTermExpression { input, output } => {
                let (inputs, constraint_metadata) =
                    build_materialize_grand_product_term_expression_inputs_and_metadata(
                        input,
                        *output,
                        external_challenges,
                    );
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::MaterializeGrandProductTermExpression,
                    inputs,
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 1,
                    batch_challenges: {
                        next_batch_challenge_offset += 1;
                        vec![get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::LinearBaseFieldRelation { input, output } => {
                let (inputs, constraint_metadata) =
                    build_linear_base_kernel_inputs_and_metadata::<E>(input, *output);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LinearBaseOutput,
                    inputs,
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 1,
                    batch_challenges: {
                        next_batch_challenge_offset += 1;
                        vec![get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::InitsOrTeardownsInitialPair {
                timestamp_and_value,
                setup,
                output,
                set_idxes,
            } => {
                let (inputs, constraint_metadata) =
                    build_inits_and_teardowns_initial_pair_inputs_and_metadata(
                        timestamp_and_value,
                        *setup,
                        *output,
                        set_idxes.map(|idx| inits_and_teardowns_top_bits[idx]),
                        inits_and_teardowns_address_high_bits_shift,
                        external_challenges,
                    );
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::InitsAndTeardownsInitialPair,
                    inputs,
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 1,
                    batch_challenges: {
                        next_batch_challenge_offset += 1;
                        vec![get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::MaxQuadratic { input, output } => {
                let (inputs, constraint_metadata) =
                    build_max_quadratic_relation_inputs_and_metadata::<E>(input, *output);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::MaxQuadraticBaseOutput,
                    inputs,
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 1,
                    batch_challenges: {
                        next_batch_challenge_offset += 1;
                        vec![get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::UnbalancedGrandProductWithCache { .. } => {
                unimplemented!(
                    "unsupported GPU main-layer relation: {:?}",
                    gate.enforced_relation
                )
            }
        }
    }

    blueprints
}

pub(crate) fn build_main_layer_kernel_blueprints_static<E: Field + FieldExtension<BF>>(
    layer: &GKRLayerDescription,
    _layer_idx: usize,
    is_base_field_at_layer: &dyn Fn(&GKRAddress) -> bool,
    external_challenges: &GKRExternalChallenges<BF, E>,
    inits_and_teardowns_top_bits: &[u32],
    inits_and_teardowns_address_high_bits_shift: u32,
    _num_base_layer_memory_polys: usize,
    _num_base_layer_witness_polys: usize,
) -> Vec<GpuGKRMainLayerKernelBlueprint<E>> {
    let mut next_batch_challenge_offset = 0usize;
    let mut blueprints = Vec::new();
    for gate in layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
    {
        let push_empty = |count: usize, next_batch_challenge_offset: &mut usize| {
            let batch_challenge_offset = *next_batch_challenge_offset;
            *next_batch_challenge_offset += count;
            (batch_challenge_offset, count)
        };
        match &gate.enforced_relation {
            NoFieldGKRRelation::CopyInBaseField { input, output }
            | NoFieldGKRRelation::CopyInExtensionField { input, output } => {
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(1, &mut next_batch_challenge_offset);
                if is_base_field_at_layer(input) {
                    let relation = BaseFieldCopyGKRRelation {
                        input: *input,
                        output: *output,
                    };
                    blueprints.push(GpuGKRMainLayerKernelBlueprint {
                        kind: GpuGKRMainLayerKernelKind::BaseCopy,
                        inputs: <BaseFieldCopyGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                            &relation,
                        ),
                        batch_challenge_offset,
                        batch_challenge_count,
                        batch_challenges: Vec::new(),
                        auxiliary_challenge_source:
                            GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(E::ZERO),
                        constraint_metadata_source: None,
                    });
                } else {
                    let relation = ExtensionCopyGKRRelation {
                        input: *input,
                        output: *output,
                    };
                    blueprints.push(GpuGKRMainLayerKernelBlueprint {
                        kind: GpuGKRMainLayerKernelKind::ExtCopy,
                        inputs: <ExtensionCopyGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                            &relation,
                        ),
                        batch_challenge_offset,
                        batch_challenge_count,
                        batch_challenges: Vec::new(),
                        auxiliary_challenge_source:
                            GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(E::ZERO),
                        constraint_metadata_source: None,
                    });
                }
            }
            NoFieldGKRRelation::InitialGrandProductFromCaches { input, output }
            | NoFieldGKRRelation::TrivialProduct { input, output } => {
                let relation = SameSizeProductGKRRelation {
                    inputs: *input,
                    output: *output,
                };
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(1, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::Product,
                    inputs: <SameSizeProductGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                        &relation,
                    ),
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::InitialGrandProductWithoutCaches { input, output } => {
                let (inputs, constraint_metadata) =
                    build_initial_grand_product_without_caches_inputs_and_metadata(
                        input,
                        *output,
                        external_challenges,
                    );
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(1, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::InitialGrandProductWithoutCaches,
                    inputs,
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::MaskIntoIdentityProduct {
                input,
                mask,
                output,
            } => {
                let relation = MaskIntoIdentityProductGKRRelation {
                    input: *input,
                    mask: *mask,
                    output: *output,
                };
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(1, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::MaskIdentity,
                    inputs:
                        <MaskIntoIdentityProductGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                            &relation,
                        ),
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::AggregateLookupRationalPair { input, output } => {
                let relation = LookupPairGKRRelation {
                    inputs: *input,
                    outputs: *output,
                };
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupPair,
                    inputs: <LookupPairGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                        &relation,
                    ),
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs { input, output } => {
                let relation = LookupBasePairGKRRelation::<BF, E> {
                    inputs: *input,
                    outputs: *output,
                    lookup_additive_challenge: E::ZERO,
                    _marker: core::marker::PhantomData,
                };
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupBasePair,
                    inputs:
                        <LookupBasePairGKRRelation<BF, E> as BatchedGKRKernel<BF, E>>::get_inputs(
                            &relation,
                        ),
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source:
                        GpuGKRMainLayerAuxiliaryChallengeSource::LookupAdditive,
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::LookupPairFromBaseInputs { input, output, .. } => {
                let (inputs, constraint_metadata) =
                    build_lookup_pair_from_base_inputs_inputs_and_template(input, *output);
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupPairFromBaseInputs,
                    inputs,
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Deferred(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::LookupFromMaterializedBaseInputWithSetup {
                input,
                setup,
                output,
            } => {
                let relation = LookupBaseMinusMultiplicityByBaseGKRRelation::<BF, E> {
                    input: *input,
                    setup: *setup,
                    outputs: *output,
                    lookup_additive_challenge: E::ZERO,
                    _marker: core::marker::PhantomData,
                };
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupBaseMinusMultiplicityByBase,
                    inputs:
                        <LookupBaseMinusMultiplicityByBaseGKRRelation<BF, E> as BatchedGKRKernel<
                            BF,
                            E,
                        >>::get_inputs(&relation),
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source:
                        GpuGKRMainLayerAuxiliaryChallengeSource::LookupAdditive,
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::LookupWithDensAndSetupExpressions {
                input,
                setup,
                output,
            } => {
                let (inputs, constraint_metadata) =
                    build_lookup_with_dens_and_setup_expressions_inputs_and_template(
                        input, setup, *output,
                    );
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupWithDensAndSetupExpressions,
                    inputs,
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Deferred(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::LookupFromMaterializedVectorInputWithSetup {
                input,
                setup,
                output,
            } => {
                let relation = LookupExtensionMinusMultiplicityByExtensionGKRRelation::<BF, E> {
                    input: *input,
                    setup: *setup,
                    outputs: *output,
                    lookup_additive_challenge: E::ZERO,
                    _marker: core::marker::PhantomData,
                };
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupExtMinusMultiplicityByExt,
                    inputs: <LookupExtensionMinusMultiplicityByExtensionGKRRelation<BF, E> as BatchedGKRKernel<
                        BF,
                        E,
                    >>::get_inputs(&relation),
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source:
                        GpuGKRMainLayerAuxiliaryChallengeSource::LookupAdditive,
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::LookupPairFromMaterializedVectorInputs { input, output }
            | NoFieldGKRRelation::LookupPairFromCachedVectorInputs { input, output } => {
                let relation = LookupExtensionPairGKRRelation::<BF, E> {
                    inputs: *input,
                    outputs: *output,
                    lookup_additive_challenge: E::ZERO,
                    _marker: core::marker::PhantomData,
                };
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(
                    GpuGKRMainLayerKernelBlueprint {
                        kind: GpuGKRMainLayerKernelKind::LookupExtPair,
                        inputs: <LookupExtensionPairGKRRelation<BF, E> as BatchedGKRKernel<
                            BF,
                            E,
                        >>::get_inputs(&relation),
                        batch_challenge_offset,
                        batch_challenge_count,
                        batch_challenges: Vec::new(),
                        auxiliary_challenge_source:
                            GpuGKRMainLayerAuxiliaryChallengeSource::LookupAdditive,
                        constraint_metadata_source: None,
                    },
                );
            }
            NoFieldGKRRelation::LookupPairFromVectorInputs { input, output } => {
                let (inputs, constraint_metadata) =
                    build_lookup_pair_from_vector_inputs_inputs_and_template(input, *output);
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupPairFromVectorInputs,
                    inputs,
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Deferred(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedBaseInputs {
                input,
                remainder,
                output,
            } => {
                let relation = LookupRationalPairWithUnbalancedBaseGKRRelation::<BF, E> {
                    inputs: *input,
                    remainder: *remainder,
                    outputs: *output,
                    lookup_additive_challenge: E::ZERO,
                    _marker: core::marker::PhantomData,
                };
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupUnbalanced,
                    inputs: <LookupRationalPairWithUnbalancedBaseGKRRelation<BF, E> as BatchedGKRKernel<BF, E>>::get_inputs(
                        &relation,
                    ),
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source:
                        GpuGKRMainLayerAuxiliaryChallengeSource::LookupAdditive,
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedVectorInputs {
                input,
                remainder,
                output,
            } => {
                let relation = LookupRationalPairWithUnbalancedExtensionGKRRelation::<BF, E> {
                    inputs: *input,
                    remainder: *remainder,
                    outputs: *output,
                    lookup_additive_challenge: E::ZERO,
                    _marker: core::marker::PhantomData,
                };
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupUnbalancedExtension,
                    inputs: <LookupRationalPairWithUnbalancedExtensionGKRRelation<BF, E> as BatchedGKRKernel<BF, E>>::get_inputs(
                        &relation,
                    ),
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source:
                        GpuGKRMainLayerAuxiliaryChallengeSource::LookupAdditive,
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::MaterializedVectorLookupInput { input, output } => {
                let (inputs, constraint_metadata) =
                    build_materialized_vector_lookup_input_inputs_and_template(input, *output);
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(1, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::MaterializeGrandProductTermExpression,
                    inputs,
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Deferred(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithVectorInputs {
                input,
                remainder,
                output,
            } => {
                let (inputs, constraint_metadata) =
                    build_lookup_unbalanced_pair_with_vector_inputs_inputs_and_template(
                        *input, remainder, *output,
                    );
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupUnbalancedPairWithVectorInputs,
                    inputs,
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Deferred(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::LookupWithCachedDensAndSetup {
                input,
                setup,
                output,
            } => {
                let relation = LookupBaseExtMinusBaseExtGKRRelation::<BF, E> {
                    nums: [input[0], setup[0]],
                    dens: [input[1], setup[1]],
                    outputs: *output,
                    lookup_additive_challenge: E::ZERO,
                    _marker: core::marker::PhantomData,
                };
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupWithCachedDensAndSetup,
                    inputs: <LookupBaseExtMinusBaseExtGKRRelation<BF, E> as BatchedGKRKernel<
                        BF,
                        E,
                    >>::get_inputs(&relation),
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source:
                        GpuGKRMainLayerAuxiliaryChallengeSource::LookupAdditive,
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::EnforceConstraintsMaxQuadratic { .. } => {
                unreachable!(
                    "batched max-quadratic constraints not supported on GPU; cs/ must emit EnforceSingleMaxQuadraticConstraint (USE_BATCHING=false)"
                );
            }
            NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint { input } => {
                let (inputs, constraint_metadata) =
                    build_single_max_quadratic_constraint_inputs_and_metadata::<E>(input);
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(1, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic,
                    inputs,
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::MaterializeSingleLookupInput { input, output, .. } => {
                let (inputs, constraint_metadata) =
                    build_linear_base_kernel_inputs_and_metadata::<E>(&input.input, *output);
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(1, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LinearBaseOutput,
                    inputs,
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::LookupFromVectorInputWithSetup {
                input,
                setup,
                output,
            } => {
                let (inputs, constraint_metadata) =
                    build_lookup_from_vector_input_with_setup_inputs_and_template(
                        input, setup, *output,
                    );
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupFromVectorInputWithSetup,
                    inputs,
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Deferred(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::MaterializeGrandProductTermExpression { input, output } => {
                let (inputs, constraint_metadata) =
                    build_materialize_grand_product_term_expression_inputs_and_metadata(
                        input,
                        *output,
                        external_challenges,
                    );
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(1, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::MaterializeGrandProductTermExpression,
                    inputs,
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::LinearBaseFieldRelation { input, output } => {
                let (inputs, constraint_metadata) =
                    build_linear_base_kernel_inputs_and_metadata::<E>(input, *output);
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(1, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LinearBaseOutput,
                    inputs,
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::InitsOrTeardownsInitialPair {
                timestamp_and_value,
                setup,
                output,
                set_idxes,
            } => {
                let (inputs, constraint_metadata) =
                    build_inits_and_teardowns_initial_pair_inputs_and_metadata(
                        timestamp_and_value,
                        *setup,
                        *output,
                        set_idxes.map(|idx| inits_and_teardowns_top_bits[idx]),
                        inits_and_teardowns_address_high_bits_shift,
                        external_challenges,
                    );
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(1, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::InitsAndTeardownsInitialPair,
                    inputs,
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::MaxQuadratic { input, output } => {
                let (inputs, constraint_metadata) =
                    build_max_quadratic_relation_inputs_and_metadata::<E>(input, *output);
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(1, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::MaxQuadraticBaseOutput,
                    inputs,
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::UnbalancedGrandProductWithCache { .. } => {
                unimplemented!(
                    "unsupported GPU main-layer relation: {:?}",
                    gate.enforced_relation
                )
            }
        }
    }

    blueprints
}

/// Collects, per main layer, the sorted unique set of input addresses that
/// `schedule_execute_main_layer_from_workflow_state` will eventually observe
/// in `final_evaluation_sources_for_last_step` — i.e. the keys of the
/// `BTreeMap<GKRAddress, Vec<E>>` stored in
/// `SumcheckIntermediateProofValues::final_step_evaluations` for that layer.
///
/// Implementation: run `build_main_layer_kernel_blueprints_static` for each
/// layer at prove() start (after forward has populated `storage`), collect the
/// union of `inputs_in_base` + `inputs_in_extension` from every blueprint's
/// `GKRInputs`, deduplicate through a `BTreeSet<GKRAddress>` to get the same
/// order the scheduler's `final_evaluation_sources_for_last_step` produces.
///
/// Result is indexed by natural `layer_idx` (0-based position in
/// `compiled_circuit.layers`), not by backward-scheduler slot. Callers that
/// build `ProofLayoutInputs.backward_layers` in scheduler order (high-to-low
/// layer_idx after dim-reducing) index into the returned Vec accordingly.
pub(crate) fn collect_main_layer_input_addresses_per_layer<E>(
    compiled_circuit: &GKRCircuitArtifact<BF>,
    external_challenges: &GKRExternalChallenges<BF, E>,
    storage: &GpuGKRStorage<BF, E>,
) -> Vec<Vec<GKRAddress>>
where
    E: Field + FieldExtension<BF>,
{
    let inits_and_teardowns_top_bits =
        canonical_inits_and_teardowns_top_bits(compiled_circuit.memory_layout.teardown_sets.len());
    let inits_and_teardowns_address_high_bits_shift =
        if compiled_circuit.memory_layout.teardown_sets.is_empty() {
            0
        } else {
            high_bits_offset_for_inits_and_teardowns::<2>(compiled_circuit.trace_len)
        };
    let num_base_layer_memory_polys = compiled_circuit.memory_layout.total_width;
    let num_base_layer_witness_polys = compiled_circuit.witness_layout.total_width;
    let mut per_layer = Vec::with_capacity(compiled_circuit.layers.len());
    for (layer_idx, layer) in compiled_circuit.layers.iter().enumerate() {
        let blueprints = build_main_layer_kernel_blueprints_static::<E>(
            layer,
            layer_idx,
            &|addr| {
                if matches!(
                    addr,
                    GKRAddress::BaseLayerWitness(_)
                        | GKRAddress::BaseLayerMemory(_)
                        | GKRAddress::Setup(_)
                        | GKRAddress::ScratchSpace(_)
                ) {
                    return true;
                }
                storage.layers[layer_idx]
                    .base_field_inputs
                    .contains_key(addr)
            },
            external_challenges,
            &inits_and_teardowns_top_bits,
            inits_and_teardowns_address_high_bits_shift,
            num_base_layer_memory_polys,
            num_base_layer_witness_polys,
        );
        let mut addresses: std::collections::BTreeSet<GKRAddress> =
            std::collections::BTreeSet::new();
        for kernel in blueprints.iter() {
            for addr in kernel
                .inputs
                .inputs_in_base
                .iter()
                .chain(kernel.inputs.inputs_in_extension.iter())
            {
                if *addr == GKRAddress::placeholder() {
                    continue;
                }
                addresses.insert(*addr);
            }
        }
        per_layer.push(addresses.into_iter().collect());
    }
    per_layer
}

/// Structural variant of [`collect_main_layer_input_addresses_per_layer`]: walks
/// `compiled_circuit` directly without consulting `GpuGKRStorage`. Produces an
/// identical address set for every layer.
///
/// The storage-aware version reads `storage.layers[layer_idx].base_field_inputs.contains_key(input)`
/// only to choose between the BaseCopy and ExtCopy kernel kinds for `CopyInBaseField` /
/// `CopyInExtensionField` relations. The collected `inputs_in_base ∪ inputs_in_extension`
/// set is invariant across that branch — both `BaseFieldCopyGKRRelation::get_inputs`
/// (`prover/.../copy.rs:28`) and `ExtensionCopyGKRRelation::get_inputs` (`copy.rs:218`)
/// emit `{relation.input}` (only `inputs_in_base` vs `inputs_in_extension` differs,
/// and the loop at lines 3101–3107 chains both). Every other relation variant ignores
/// `storage` entirely. We delegate to the storage-aware function with an empty stub
/// storage that has the right number of (default-empty) layer slots; the storage check
/// always returns `false` and the ExtCopy branch is taken, but the collected address
/// set is identical to the storage-aware result.
pub(crate) fn collect_main_layer_input_addresses_per_layer_structural<E>(
    compiled_circuit: &GKRCircuitArtifact<BF>,
    external_challenges: &GKRExternalChallenges<BF, E>,
) -> Vec<Vec<GKRAddress>>
where
    E: Field + FieldExtension<BF>,
{
    let mut stub_storage = GpuGKRStorage::<BF, E>::default();
    stub_storage
        .layers
        .resize_with(compiled_circuit.layers.len(), Default::default);
    collect_main_layer_input_addresses_per_layer(
        compiled_circuit,
        external_challenges,
        &stub_storage,
    )
}

/// Sibling of [`collect_main_layer_input_addresses_per_layer`] that collects
/// the deduplicated `outputs_in_base ∪ outputs_in_extension` per layer. These
/// are the addresses that each layer's kernels claim about — i.e., the
/// addresses looked up via `claim_layout.claim_idx` in the desc_pairs build
/// inside `schedule_execute_main_layer_from_workflow_state`.
///
/// Result is indexed by natural `layer_idx` (0-based position in
/// `compiled_circuit.layers`), matching the inputs-side helper.
pub(crate) fn collect_main_layer_kernel_output_addresses_per_layer<E>(
    compiled_circuit: &GKRCircuitArtifact<BF>,
    external_challenges: &GKRExternalChallenges<BF, E>,
    storage: &GpuGKRStorage<BF, E>,
) -> Vec<Vec<GKRAddress>>
where
    E: Field + FieldExtension<BF>,
{
    let inits_and_teardowns_top_bits =
        canonical_inits_and_teardowns_top_bits(compiled_circuit.memory_layout.teardown_sets.len());
    let inits_and_teardowns_address_high_bits_shift =
        if compiled_circuit.memory_layout.teardown_sets.is_empty() {
            0
        } else {
            high_bits_offset_for_inits_and_teardowns::<2>(compiled_circuit.trace_len)
        };
    let num_base_layer_memory_polys = compiled_circuit.memory_layout.total_width;
    let num_base_layer_witness_polys = compiled_circuit.witness_layout.total_width;
    let mut per_layer = Vec::with_capacity(compiled_circuit.layers.len());
    for (layer_idx, layer) in compiled_circuit.layers.iter().enumerate() {
        let blueprints = build_main_layer_kernel_blueprints_static::<E>(
            layer,
            layer_idx,
            &|addr| {
                if matches!(
                    addr,
                    GKRAddress::BaseLayerWitness(_)
                        | GKRAddress::BaseLayerMemory(_)
                        | GKRAddress::Setup(_)
                        | GKRAddress::ScratchSpace(_)
                ) {
                    return true;
                }
                storage.layers[layer_idx]
                    .base_field_inputs
                    .contains_key(addr)
            },
            external_challenges,
            &inits_and_teardowns_top_bits,
            inits_and_teardowns_address_high_bits_shift,
            num_base_layer_memory_polys,
            num_base_layer_witness_polys,
        );
        let mut addresses: std::collections::BTreeSet<GKRAddress> =
            std::collections::BTreeSet::new();
        for kernel in blueprints.iter() {
            for addr in kernel
                .inputs
                .outputs_in_base
                .iter()
                .chain(kernel.inputs.outputs_in_extension.iter())
            {
                if *addr == GKRAddress::placeholder() {
                    continue;
                }
                addresses.insert(*addr);
            }
        }
        per_layer.push(addresses.into_iter().collect());
    }
    per_layer
}

/// Structural variant of [`collect_main_layer_kernel_output_addresses_per_layer`].
/// Same rationale as
/// [`collect_main_layer_input_addresses_per_layer_structural`]: the
/// `storage`-derived branch in `build_main_layer_kernel_blueprints_static`
/// only affects BaseCopy/ExtCopy classification, which preserves the
/// `outputs_in_*` set.
pub(crate) fn collect_main_layer_kernel_output_addresses_per_layer_structural<E>(
    compiled_circuit: &GKRCircuitArtifact<BF>,
    external_challenges: &GKRExternalChallenges<BF, E>,
) -> Vec<Vec<GKRAddress>>
where
    E: Field + FieldExtension<BF>,
{
    let mut stub_storage = GpuGKRStorage::<BF, E>::default();
    stub_storage
        .layers
        .resize_with(compiled_circuit.layers.len(), Default::default);
    collect_main_layer_kernel_output_addresses_per_layer(
        compiled_circuit,
        external_challenges,
        &stub_storage,
    )
}

/// Computes per-layer "orphan" output addresses, indexed by the layer at
/// which the prover **evaluates** them (= the main-layer scheduler that
/// emits them into its slot's `extra_evaluations` slab range).
///
/// Concretely: at scheduler for main layer `L`, we have just folded down
/// to a single random point and produced `last_evaluations[L]` (= layer
/// `L`'s last-round kernel inputs). The next layer scheduled is `L - 1`,
/// whose `desc_pairs` build looks up each of its kernels' output
/// addresses in the IN claim layout. Any layer-`(L - 1)` kernel output
/// address that is not in `last_evaluations[L]` is an "orphan" — its
/// claim must be computed explicitly at `L`'s folding point and inserted
/// into `L`'s next claim layout (and its slot's slab `extra_evaluations`
/// range) so that `L - 1`'s scheduler sees it.
///
/// Returned vector layout: `per_layer[L]` =
/// `outputs_per_layer[L - 1] − inputs_per_layer[L]`, sorted by
/// `BTreeSet`. `per_layer[0]` is always empty (no main layer below 0
/// produces outputs that need bridging into 0's IN claim layout).
///
/// On CPU this is bridged by
/// `extra_evaluations_from_caching_relations` ([sumcheck_loop/mod.rs:293-395](prover/src/gkr/prover/sumcheck_loop/mod.rs#L293-L395));
/// the GPU port mirrors this via on-device explicit evaluation at the
/// random folding point and a dedicated per-layer-slot proof-slab range.
pub(crate) fn compute_main_layer_orphan_output_addresses_per_layer<E>(
    inputs_per_layer: &[Vec<GKRAddress>],
    outputs_per_layer: &[Vec<GKRAddress>],
) -> Vec<Vec<GKRAddress>>
where
    E: Field + FieldExtension<BF>,
{
    assert_eq!(
        inputs_per_layer.len(),
        outputs_per_layer.len(),
        "inputs and outputs per-layer arrays must have matching length",
    );
    let num_layers = inputs_per_layer.len();
    let mut per_layer: Vec<Vec<GKRAddress>> = Vec::with_capacity(num_layers);
    for layer_idx in 0..num_layers {
        // Bottom main layer (layer_idx == 0) has no layer-(-1) below to
        // produce orphan outputs; its IN claim layout is fully populated
        // from layer 1's transcript inputs and there is nothing to bridge.
        if layer_idx == 0 {
            per_layer.push(Vec::new());
            continue;
        }
        let child_layer_idx = layer_idx - 1;
        let this_inputs: std::collections::BTreeSet<GKRAddress> =
            inputs_per_layer[layer_idx].iter().copied().collect();
        // BTreeSet keeps deterministic ordering and dedupes simultaneously;
        // downstream code relies on `BTreeMap::keys()`-equivalent iteration
        // order on the addresses produced here.
        let orphans: std::collections::BTreeSet<GKRAddress> = outputs_per_layer[child_layer_idx]
            .iter()
            .copied()
            .filter(|addr| !this_inputs.contains(addr))
            .collect();
        per_layer.push(orphans.into_iter().collect());
    }
    per_layer
}

/// Stream-ordered keepalive for the main-layer extras eval scratch
/// buffers. The held allocations and Arc-clones outlive every
/// `exec_stream` op scheduled by `schedule_main_layer_extras_eval`; the
/// pool defers underlying free until exec_stream has progressed past the
/// last write that uses these buffers.
pub(crate) struct MainLayerExtrasKeepalive<B, E> {
    _eq_group_tables: DeviceAllocation<E>,
    _eq_values: DeviceAllocation<E>,
    _block_partials: DeviceAllocation<E>,
    _reduction_temp: DeviceAllocation<u8>,
    /// Per-orphan resolved views over the consolidated
    /// `base_class_backings`. Holding the views keeps the underlying
    /// `Arc<DeviceAllocation<B>>` backings alive until kernels reading
    /// from them have been scheduled and the pool drop is safe.
    _orphan_views: Vec<GpuBaseFieldPoly<B>>,
}

/// Schedules the on-device evaluation of `orphan_addresses` at the
/// folding point `[r_0..r_{folding_steps - 1}]` of length
/// `folding_steps`. For each orphan, computes
/// `inner_product(orphan_poly, eq_values)` and writes one `E` value into:
/// (a) `extras_dst_ptr[i]`, the tail of the caller's `device_new_claims`
///     buffer (so the next layer's IN claim buffer carries the orphan
///     claim), and
/// (b) `proof_layout.backward[layer_slot].extra_evaluations`, the slab
///     range (so the verifier can read the explicit at-point evals).
///
/// Mirrors the CPU's
/// `extra_evaluations_from_caching_relations` mechanism (see
/// [`prover/src/gkr/prover/sumcheck_loop/mod.rs:293-395`]). Returns a
/// keepalive that the caller drops at the end of the scheduler — the
/// keepalive owns the temporaries (`eq_values`, `block_partials`,
/// `reduction_temp`) and the orphan view Arc-clones.
///
/// Operates entirely on `exec_stream`. No host blocking. Compatible
/// with the GPU scheduling contract (`gpu_prover/docs/gpu_scheduling_contract.md`).
#[allow(clippy::too_many_arguments)]
pub(crate) fn schedule_main_layer_extras_eval<E>(
    layer_idx: usize,
    orphan_addresses: &[GKRAddress],
    storage: &GpuGKRStorage<BF, E>,
    folding_point_ptr: *const E,
    folding_steps: usize,
    trace_len: usize,
    extras_dst_ptr: *mut E,
    proof_slab: Option<&DeviceAllocation<E4>>,
    proof_layout: &ProofLayout,
    layer_slot: usize,
    context: &ProverContext,
) -> CudaResult<MainLayerExtrasKeepalive<BF, E>>
where
    E: GpuDimensionReducingKernelSet + Field + FieldExtension<BF> + Reduce + 'static,
{
    let orphan_count = orphan_addresses.len();
    assert!(
        orphan_count > 0,
        "schedule_main_layer_extras_eval should only be called with at least one orphan"
    );
    assert_eq!(
        trace_len,
        1usize << folding_steps,
        "trace_len must equal 2^folding_steps for full-folding-point eq build",
    );
    assert!(trace_len <= u32::MAX as usize);
    let stream = context.get_exec_stream();

    // 1. Build the full-folding-point `eq_values` of length `trace_len`
    //    from the just-produced folding point in `device_claim_point_out`.
    //    The dim-reducing eq builder is reused: it derives `eq_values`
    //    over the entire hypercube of size `2^challenge_count` from a
    //    single contiguous challenge slab — exactly what we need here.
    let mut eq_group_tables: DeviceAllocation<E> = context.alloc(
        eq_group_tables_len(folding_steps).max(1),
        AllocationPlacement::Top,
    )?;
    let mut eq_values: DeviceAllocation<E> = context.alloc(trace_len, AllocationPlacement::Top)?;
    launch_build_eq_values_from_point(
        folding_point_ptr,
        0,
        folding_steps,
        eq_group_tables.as_mut_ptr(),
        eq_values.as_mut_ptr(),
        trace_len,
        context,
    )?;

    // 2. Resolve each orphan to its `(backing, offset, len)` view via
    //    the storage layout. Non-mutating — no fresh allocations
    //    triggered. The Arc clones held in `orphan_views` are the
    //    keepalive that ties this scheduler's lifetime to the backings.
    let orphan_views: Vec<GpuBaseFieldPoly<BF>> = orphan_addresses
        .iter()
        .map(|addr| {
            let view = storage.resolve_base_view_or_panic(layer_idx, *addr);
            assert_eq!(
                view.len(),
                trace_len,
                "orphan poly length must match trace_len (address {addr:?})"
            );
            view
        })
        .collect();

    // 3. Per-orphan partial-sum reduction → `block_partials[orphan_count, blocks_count]`
    //    matrix, then `batch_reduce` over rows to produce `[orphan_count]`
    //    scalar inner products written straight into `extras_dst_ptr`.
    let blocks_count = context.get_device_properties().sm_count;
    assert!(blocks_count > 0, "device must expose at least one SM");
    assert!(blocks_count <= u32::MAX as usize);
    let mut block_partials: DeviceAllocation<E> =
        context.alloc(orphan_count * blocks_count, AllocationPlacement::Top)?;
    let reduction_temp_bytes = get_batch_reduce_temp_storage_bytes::<E>(
        ReduceOperation::Sum,
        orphan_count as i32,
        blocks_count as i32,
    )?;
    let mut reduction_temp = context
        .alloc_with_extra_alignment::<u8, CUB_TEMP_STORAGE_EXTRA_ALIGNMENT_LOG2>(
            reduction_temp_bytes,
            AllocationPlacement::Top,
        )?;

    for (orphan_i, view) in orphan_views.iter().enumerate() {
        // SAFETY: block_partials buffer is sized [orphan_count *
        // blocks_count]; the kernel writes exactly `blocks_count`
        // contiguous slots starting at this pointer (since we pass
        // `column_start = 0`, `chunk_cols = 1`).
        let row_partials_ptr = unsafe { block_partials.as_mut_ptr().add(orphan_i * blocks_count) };
        launch_trace_holder_block_partials::<E>(
            view.as_ptr(),
            eq_values.as_ptr(),
            row_partials_ptr,
            trace_len,
            0,
            1,
            blocks_count,
            context,
        )?;
    }

    let block_partials_matrix = DeviceMatrix::new(&block_partials, blocks_count);
    // SAFETY: `extras_dst_ptr` is a tail slot in `device_new_claims`,
    // sized to fit `orphan_count` `E` values by the caller.
    let extras_dst_slice = unsafe { DeviceSlice::from_raw_parts_mut(extras_dst_ptr, orphan_count) };
    let reduction_temp_slice = unsafe {
        DeviceSlice::from_raw_parts_mut(reduction_temp.as_mut_ptr(), reduction_temp.len())
    };
    batch_reduce(
        ReduceOperation::Sum,
        reduction_temp_slice,
        &block_partials_matrix,
        extras_dst_slice,
        stream,
    )?;

    // 4. Production slab path: copy the orphan claim values from the
    //    `device_new_claims` tail into the slab's per-layer-slot
    //    `extra_evaluations` range so the verifier can parse them
    //    alongside `final_step_evaluations`. Test paths (no slab)
    //    skip this — the values still live in the claims buffer for
    //    the next layer's consumption.
    if let Some(slab) = proof_slab {
        // SAFETY: E = E4 in every instantiation; the slab range was
        // sized at `extra_evaluations_addresses.len()` E4 by the
        // proof-layout builder.
        let (slab_dst_ptr, slab_dst_len) = unsafe {
            proof_layout.backward_extra_evaluations_device_mut(slab.as_ptr() as *mut u8, layer_slot)
        };
        debug_assert_eq!(
            slab_dst_len, orphan_count,
            "slab extra_evaluations range must match orphan_count for layer {layer_slot}",
        );
        let slab_dst_slice =
            unsafe { DeviceSlice::from_raw_parts_mut(slab_dst_ptr as *mut E, orphan_count) };
        let extras_src_slice =
            unsafe { DeviceSlice::from_raw_parts(extras_dst_ptr as *const E, orphan_count) };
        memory_copy_async(slab_dst_slice, extras_src_slice, stream)?;
    }

    Ok(MainLayerExtrasKeepalive {
        _eq_group_tables: eq_group_tables,
        _eq_values: eq_values,
        _block_partials: block_partials,
        _reduction_temp: reduction_temp,
        _orphan_views: orphan_views,
    })
}

/// Structural variant of [`schedule_dimension_reduction_forward`]'s
/// `dimension_reduction_description` output: replicates the address-only
/// portion of the per-round lowering at
/// `gpu_prover/src/prover/gkr/forward.rs:1965-2074` without scheduling any GPU work.
///
/// Address-assignment rules (matched exactly):
/// - Each round walks `layer_inputs.iter()` (BTreeMap → ordered by `OutputType`).
/// - Both `PermutationProduct` and `Lookup*` arg types emit two output addresses
///   per slot (`InnerLayer { layer: output_layer, offset: output_idx }` then
///   `output_idx += 1`), so the offset assignment is purely positional.
/// - Round 0's `layer_inputs` is `compiled_circuit.global_output_map`; subsequent
///   rounds chain from the previous round's `output`.
///
/// Used by [`crate::prover::proof_layout::build_proof_layout_inputs_structural`]
/// to size the proof slab before forward runs.
pub(crate) fn derive_dimension_reducing_inputs_structural(
    initial_layer_idx: usize,
    initial_output_map: &BTreeMap<OutputType, Vec<GKRAddress>>,
    initial_trace_log_2: usize,
    final_trace_log_2: usize,
) -> BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>> {
    let mut result: BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>> =
        BTreeMap::new();
    let total_rounds = initial_trace_log_2.saturating_sub(final_trace_log_2);
    if total_rounds == 0 {
        return result;
    }
    let mut current_layer_idx = initial_layer_idx;
    let mut layer_inputs: BTreeMap<OutputType, Vec<GKRAddress>> = initial_output_map.clone();

    for _round in 0..total_rounds {
        let output_layer = current_layer_idx + 1;
        let mut output_idx = 0usize;
        let mut layer_description: BTreeMap<OutputType, DimensionReducingInputOutput> =
            BTreeMap::new();

        for (arg_type, inputs) in layer_inputs.iter() {
            assert_eq!(
                inputs.len(),
                2,
                "dim reduction expects 2 inputs per slot for {:?}",
                arg_type,
            );
            let out_a = GKRAddress::InnerLayer {
                layer: output_layer,
                offset: output_idx,
            };
            output_idx += 1;
            let out_b = GKRAddress::InnerLayer {
                layer: output_layer,
                offset: output_idx,
            };
            output_idx += 1;
            layer_description.insert(
                *arg_type,
                DimensionReducingInputOutput {
                    inputs: inputs.clone(),
                    output: vec![out_a, out_b],
                },
            );
        }

        layer_inputs = layer_description
            .iter()
            .map(|(k, v)| (*k, v.output.clone()))
            .collect();

        result.insert(current_layer_idx, layer_description);
        current_layer_idx += 1;
    }
    result
}

impl<B, E> GpuGKRDimensionReducingBackwardState<B, E> {
    pub(super) fn new(
        forward_tracing_ranges: Vec<Range>,
        storage: GpuGKRStorage<B, E>,
        initial_layer_for_sumcheck: usize,
        dimension_reducing_inputs: BTreeMap<
            usize,
            BTreeMap<OutputType, DimensionReducingInputOutput>,
        >,
    ) -> Self {
        let first_output_addr = dimension_reducing_inputs[&initial_layer_for_sumcheck]
            .values()
            .next()
            .and_then(|io| io.output.first())
            .copied()
            .expect("dimension-reducing backward state requires at least one reduced output");
        let next_trace_len_after_reduction = storage.get_ext_poly(first_output_addr).len();
        let pending_layers = dimension_reducing_inputs.into_iter().rev().collect();

        Self {
            forward_tracing_ranges,
            storage,
            pending_layers,
            next_trace_len_after_reduction,
        }
    }

    pub(crate) fn storage(&self) -> &GpuGKRStorage<B, E> {
        &self.storage
    }

    pub(crate) fn purge_up_to_layer(&mut self, layer: usize) {
        self.storage.purge_up_to_layer(layer);
    }
}

impl<E: Field + FieldExtension<BF>> GpuGKRDimensionReducingBackwardState<BF, E> {
    pub(crate) fn into_main_layer_backward_state(
        self,
        compiled_circuit: GKRCircuitArtifact<BF>,
        external_challenges: GKRExternalChallenges<BF, E>,
        lookup_multiplicative_challenge: E,
        lookup_additive_challenge: E,
        is_delegation: bool,
    ) -> GpuGKRMainLayerBackwardState<E> {
        let compiled_circuit = normalize_compiled_circuit_for_gpu(compiled_circuit);
        assert!(
            self.pending_layers.is_empty(),
            "main-layer handoff requires dimension-reducing layers to be exhausted"
        );
        GpuGKRMainLayerBackwardState {
            forward_tracing_ranges: self.forward_tracing_ranges,
            storage: self.storage,
            pending_layers: compiled_circuit
                .layers
                .into_iter()
                .enumerate()
                .rev()
                .collect(),
            trace_len: compiled_circuit.trace_len,
            external_challenges,
            inits_and_teardowns_top_bits: canonical_inits_and_teardowns_top_bits(
                compiled_circuit.memory_layout.teardown_sets.len(),
            ),
            inits_and_teardowns_address_high_bits_shift: if compiled_circuit
                .memory_layout
                .teardown_sets
                .is_empty()
            {
                0
            } else {
                high_bits_offset_for_inits_and_teardowns::<2>(compiled_circuit.trace_len)
            },
            lookup_multiplicative_challenge,
            lookup_additive_challenge,
            num_base_layer_memory_polys: compiled_circuit.memory_layout.total_width,
            num_base_layer_witness_polys: compiled_circuit.witness_layout.total_width,
            is_delegation,
        }
    }

    pub(crate) fn into_main_layer_backward_state_static(
        self,
        compiled_circuit: GKRCircuitArtifact<BF>,
        external_challenges: GKRExternalChallenges<BF, E>,
        is_delegation: bool,
    ) -> GpuGKRMainLayerBackwardState<E> {
        self.into_main_layer_backward_state(
            compiled_circuit,
            external_challenges,
            E::ZERO,
            E::ZERO,
            is_delegation,
        )
    }
}

impl<B: 'static, E: Field + Reduce> GpuGKRDimensionReducingBackwardState<B, E> {
    fn prepare_layer_from_blueprints(
        &mut self,
        layer_idx: usize,
        blueprints: Vec<DimensionReducingKernelBlueprint<E>>,
        batch_challenge_base: Option<E>,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRDimensionReducingSumcheckLayerPlan<B, E>> {
        let trace_len_after_reduction = self.next_trace_len_after_reduction;
        assert!(trace_len_after_reduction.is_power_of_two());
        let folding_steps = trace_len_after_reduction.trailing_zeros() as usize;
        assert!(folding_steps >= 2);
        assert!(
            blueprints.len() <= GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER,
            "fused dimension-reducing backward supports at most {} kernels per layer, got {}",
            GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER,
            blueprints.len()
        );
        let batch_challenge_count = blueprints
            .iter()
            .map(|blueprint| blueprint.batch_challenge_count)
            .sum::<usize>();
        assert!(
            batch_challenge_count <= GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN,
            "fused dimension-reducing backward supports at most {} batch challenges per layer, got {}",
            GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN,
            batch_challenge_count
        );

        // Pre-allocate one consolidated ext-folding backing for this layer so
        // every per-blueprint `prepare_for_sumcheck_round_*` call slices a
        // view into it instead of allocating per-poly. Phase B kernel-arg
        // compaction will index into this single Arc via a u16 source
        // descriptor + per-launch bases table.
        let dim_reducing_ext_inputs: std::collections::BTreeSet<GKRAddress> = blueprints
            .iter()
            .flat_map(|bp| bp.inputs.inputs_in_extension.iter().copied())
            .filter(|addr| *addr != GKRAddress::placeholder())
            .collect();
        self.storage.register_dim_reducing_inputs_for_layer(
            layer_idx,
            &dim_reducing_ext_inputs,
            context,
        )?;

        let mut round1_prepared_all = Vec::with_capacity(blueprints.len());
        for blueprint in blueprints.iter() {
            round1_prepared_all.push(self.storage.prepare_for_sumcheck_round_1(
                &blueprint.inputs,
                layer_idx,
                context,
            )?);
        }

        let mut round2_prepared_all = Vec::with_capacity(blueprints.len());
        for blueprint in blueprints.iter() {
            round2_prepared_all.push(if folding_steps >= 3 {
                Some(self.storage.prepare_for_sumcheck_round_2(
                    &blueprint.inputs,
                    layer_idx,
                    context,
                )?)
            } else {
                None
            });
        }

        let mut round3_prepared_all: Vec<Vec<GpuGKRDimensionReducingRound3Prepared<E>>> =
            Vec::with_capacity(blueprints.len());
        round3_prepared_all.resize_with(blueprints.len(), Vec::new);
        for step in 3..folding_steps {
            for (prepared_for_kernel, blueprint) in
                round3_prepared_all.iter_mut().zip(blueprints.iter())
            {
                let prepared = self.storage.prepare_for_sumcheck_round_3_and_beyond(
                    &blueprint.inputs,
                    layer_idx,
                    step,
                    context,
                )?;
                prepared_for_kernel.push(GpuGKRDimensionReducingRound3Prepared { step, prepared });
            }
        }

        let kernel_plans: Vec<GpuGKRDimensionReducingKernelPlan<B, E>> = blueprints
            .iter()
            .zip(round1_prepared_all.into_iter())
            .zip(round2_prepared_all.into_iter())
            .zip(round3_prepared_all.into_iter())
            .map(
                |(((blueprint, round1_prepared), round2_prepared), round3_and_beyond_prepared)| {
                    GpuGKRDimensionReducingKernelPlan {
                        kind: blueprint.kind,
                        inputs: blueprint.inputs.clone(),
                        batch_challenge_offset: blueprint.batch_challenge_offset,
                        batch_challenge_count: blueprint.batch_challenge_count,
                        batch_challenges: blueprint.batch_challenges.clone(),
                        round1_prepared,
                        round2_prepared,
                        round3_and_beyond_prepared,
                    }
                },
            )
            .collect();

        let round0_batch_template_compact =
            crate::prover::gkr::backward_compact_encoder::build_round0_batch_compact(
                &blueprints,
                &self.storage,
            );
        let round1_batch_template_compact =
            crate::prover::gkr::backward_compact_encoder::build_round1_batch_compact(
                &blueprints,
                &self.storage,
            );
        let continuation_batch_template_compact =
            crate::prover::gkr::backward_compact_encoder::build_continuation_batch_compact(
                &blueprints,
                &self.storage,
            );

        let max_acc_size = trace_len_after_reduction / 2;
        let reduction_temp_storage_bytes =
            get_reduce_temp_storage_bytes::<E>(ReduceOperation::Sum, max_acc_size as i32)?;

        let round_scratch = GpuGKRDimensionReducingRoundScratch {
            claim_point: context.alloc(folding_steps + 1, AllocationPlacement::Top)?,
            eq_pair_values: context.alloc(
                round0_eq_pair_values_len(folding_steps).max(1),
                AllocationPlacement::Top,
            )?,
            eq_group_tables: context.alloc(
                round0_eq_group_tables_len(folding_steps).max(1),
                AllocationPlacement::Top,
            )?,
            eq_values: context.alloc(max_acc_size.max(1), AllocationPlacement::Top)?,
            accumulator: context.alloc(max_acc_size * 2, AllocationPlacement::Top)?,
            reduction_output: context.alloc(2, AllocationPlacement::Top)?,
            reduction_temp_storage: context
                .alloc_with_extra_alignment::<u8, CUB_TEMP_STORAGE_EXTRA_ALIGNMENT_LOG2>(
                    reduction_temp_storage_bytes,
                    AllocationPlacement::Top,
                )?,
        };

        self.next_trace_len_after_reduction *= 2;

        Ok(GpuGKRDimensionReducingSumcheckLayerPlan {
            layer_idx,
            trace_len_after_reduction,
            folding_steps,
            batch_challenge_base,
            kernel_plans,
            round0_batch_template_compact,
            round1_batch_template_compact,
            continuation_batch_template_compact,
            round_scratch,
            batch_challenge_base_override_ptr: None,
        })
    }

    pub(crate) fn prepare_next_layer(
        &mut self,
        batch_challenge_base: E,
        context: &ProverContext,
    ) -> CudaResult<Option<GpuGKRDimensionReducingSumcheckLayerPlan<B, E>>> {
        let Some((layer_idx, layer)) = self.pending_layers.pop_front() else {
            return Ok(None);
        };
        let blueprints = build_dimension_reducing_kernel_blueprints(&layer, batch_challenge_base);
        Ok(Some(self.prepare_layer_from_blueprints(
            layer_idx,
            blueprints,
            Some(batch_challenge_base),
            context,
        )?))
    }

    pub(crate) fn prepare_next_layer_static(
        &mut self,
        context: &ProverContext,
    ) -> CudaResult<Option<GpuGKRDimensionReducingSumcheckLayerPlan<B, E>>> {
        let Some((layer_idx, layer)) = self.pending_layers.pop_front() else {
            return Ok(None);
        };
        let blueprints = build_dimension_reducing_kernel_blueprints_static::<E>(&layer);
        Ok(Some(self.prepare_layer_from_blueprints(
            layer_idx, blueprints, None, context,
        )?))
    }
}

impl<E: Field + FieldExtension<BF>> GpuGKRMainLayerBackwardState<E> {
    pub(crate) fn storage(&self) -> &GpuGKRStorage<BF, E> {
        &self.storage
    }

    pub(crate) fn purge_up_to_layer(&mut self, layer: usize) {
        self.storage.purge_up_to_layer(layer);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct FlatContinuationLaunchSizes {
    fold_stride: u32,
    next_layer_size: u32,
}

impl FlatContinuationLaunchSizes {
    fn from_sizes(fold_stride: usize, next_layer_size: usize) -> Self {
        assert!(
            fold_stride <= u32::MAX as usize && next_layer_size <= u32::MAX as usize,
            "flat continuation: fold sizes overflow u32 (fold_stride={fold_stride}, next_layer_size={next_layer_size})",
        );
        Self {
            fold_stride: fold_stride as u32,
            next_layer_size: next_layer_size as u32,
        }
    }

    fn from_acc_size(acc_size: usize) -> Self {
        Self::from_sizes(acc_size, acc_size)
    }
}

#[derive(Clone, Copy, Debug)]
struct FlatContinuationSizeCheck {
    sizes: Option<FlatContinuationLaunchSizes>,
    has_sources: bool,
    consistent: bool,
}

impl FlatContinuationSizeCheck {
    fn empty() -> Self {
        Self {
            sizes: None,
            has_sources: false,
            consistent: true,
        }
    }

    fn resolve(&self, acc_size: usize) -> Option<FlatContinuationLaunchSizes> {
        if !self.consistent {
            return None;
        }
        Some(
            self.sizes
                .unwrap_or_else(|| FlatContinuationLaunchSizes::from_acc_size(acc_size)),
        )
    }
}

impl<E: Field + FieldExtension<BF> + Reduce> GpuGKRMainLayerBackwardState<E> {
    fn prepare_layer_from_blueprints(
        &mut self,
        layer_idx: usize,
        blueprints: Vec<GpuGKRMainLayerKernelBlueprint<E>>,
        batch_challenge_base: Option<E>,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRMainLayerSumcheckLayerPlan<E>> {
        let folding_steps = self.trace_len.trailing_zeros() as usize;
        assert!(
            blueprints.len() <= GKR_BACKWARD_MAX_KERNELS_PER_LAYER,
            "fused main-layer backward supports at most {} kernels per layer, got {}",
            GKR_BACKWARD_MAX_KERNELS_PER_LAYER,
            blueprints.len()
        );

        let mut round0_descriptors = Vec::with_capacity(blueprints.len());
        for blueprint in blueprints.iter() {
            round0_descriptors.push(self.storage.get_for_sumcheck_round_0(&blueprint.inputs));
        }

        // Pre-allocate consolidated folding backings per
        // `(layer, AddressClass)` so per-blueprint
        // `prepare_for_sumcheck_round_*` calls slice views into them
        // instead of allocating per-poly. Phase C round-1+ kernel-arg
        // compaction indexes into these Arcs via a u16 source descriptor +
        // per-launch bases table.
        //
        // - Base inputs route through `register_flat_base_folding_for_layer`
        //   (Phase A2-flat-base). `VirtualSetup` polys are excluded — no
        //   layout slot; they fall back to per-poly allocation.
        // - Ext inputs route through `register_dim_reducing_inputs_for_layer`
        //   (the same Phase B mechanism the dim-reducing path uses; the
        //   function name is historical, the consolidation shape is
        //   identical for main-layer artifact layers).
        let flat_base_inputs: std::collections::BTreeSet<GKRAddress> = blueprints
            .iter()
            .flat_map(|bp| bp.inputs.inputs_in_base.iter().copied())
            .filter(|addr| *addr != GKRAddress::placeholder())
            .collect();
        self.storage
            .register_flat_base_folding_for_layer(layer_idx, &flat_base_inputs, context)?;
        let flat_ext_inputs: std::collections::BTreeSet<GKRAddress> = blueprints
            .iter()
            .flat_map(|bp| bp.inputs.inputs_in_extension.iter().copied())
            .filter(|addr| *addr != GKRAddress::placeholder())
            .collect();
        if !flat_ext_inputs.is_empty() {
            self.storage.register_dim_reducing_inputs_for_layer(
                layer_idx,
                &flat_ext_inputs,
                context,
            )?;
        }

        let mut round1_prepared_all = Vec::with_capacity(blueprints.len());
        for blueprint in blueprints.iter() {
            round1_prepared_all.push(self.storage.prepare_for_sumcheck_round_1(
                &blueprint.inputs,
                layer_idx,
                context,
            )?);
        }

        let mut round2_prepared_all = Vec::with_capacity(blueprints.len());
        for blueprint in blueprints.iter() {
            round2_prepared_all.push(self.storage.prepare_for_sumcheck_round_2(
                &blueprint.inputs,
                layer_idx,
                context,
            )?);
        }

        let mut round3_prepared_all = Vec::with_capacity(blueprints.len());
        round3_prepared_all.resize_with(blueprints.len(), Vec::new);
        for step in 3..folding_steps {
            for (prepared_for_kernel, blueprint) in
                round3_prepared_all.iter_mut().zip(blueprints.iter())
            {
                let prepared = self.storage.prepare_for_sumcheck_round_3_and_beyond(
                    &blueprint.inputs,
                    layer_idx,
                    step,
                    context,
                )?;
                prepared_for_kernel.push(GpuGKRMainLayerRound3Prepared { step, prepared });
            }
        }

        let mut static_data = Vec::with_capacity(blueprints.len());
        let mut kernel_plans = Vec::with_capacity(blueprints.len());
        for (
            (((blueprint, round0_descriptors_for_kernel), round1_prepared), round2_prepared),
            round3_and_beyond_prepared,
        ) in blueprints
            .into_iter()
            .zip(round0_descriptors.iter().cloned())
            .zip(round1_prepared_all.into_iter())
            .zip(round2_prepared_all.into_iter())
            .zip(round3_prepared_all.into_iter())
        {
            let auxiliary_challenge = if batch_challenge_base.is_some() {
                resolve_main_layer_auxiliary_challenge(
                    blueprint.auxiliary_challenge_source,
                    self.lookup_additive_challenge,
                )
            } else {
                match blueprint.auxiliary_challenge_source {
                    GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(value) => value,
                    GpuGKRMainLayerAuxiliaryChallengeSource::LookupAdditive => E::ZERO,
                }
            };
            let constraint_metadata = if batch_challenge_base.is_some() {
                resolve_main_layer_constraint_metadata(blueprint.constraint_metadata_source.clone())
            } else {
                match blueprint.constraint_metadata_source.as_ref() {
                    None => None,
                    Some(GpuGKRMainLayerConstraintMetadataSource::Immediate(metadata)) => {
                        Some(metadata.clone())
                    }
                    Some(GpuGKRMainLayerConstraintMetadataSource::Deferred(_)) => None,
                }
            };
            let constraint_metadata_summary = summarize_main_layer_constraint_metadata_source(
                blueprint.constraint_metadata_source.as_ref(),
            );
            let round1_descriptors = round1_prepared.build_launch_descriptors();
            let round2_descriptors = round2_prepared.build_launch_descriptors();
            let round3_descriptors = round3_and_beyond_prepared
                .iter()
                .map(|round3| GpuGKRMainLayerRound3HostDescriptors {
                    step: round3.step,
                    descriptors: round3.prepared.build_launch_descriptors(),
                })
                .collect();

            static_data.push(PreparedMainLayerKernelStaticData {
                kind: blueprint.kind,
                auxiliary_challenge,
                constraint_metadata: constraint_metadata.clone(),
                round0_descriptors: round0_descriptors_for_kernel,
                round1_descriptors,
                round2_descriptors,
                round3_descriptors,
            });
            kernel_plans.push(GpuGKRMainLayerKernelPlan {
                kind: blueprint.kind,
                inputs: blueprint.inputs,
                batch_challenge_offset: blueprint.batch_challenge_offset,
                batch_challenge_count: blueprint.batch_challenge_count,
                batch_challenges: blueprint.batch_challenges,
                auxiliary_challenge_source: blueprint.auxiliary_challenge_source,
                constraint_metadata_source: blueprint.constraint_metadata_source,
                constraint_metadata_summary,
                round1_prepared,
                round2_prepared,
                round3_and_beyond_prepared,
            });
        }

        // Build the flat round 0 plan in compact form directly. The builder
        // resolves each gate's source pointers against the per-(layer, class)
        // consolidated storage backings and emits packed `u16` source
        // descriptors as it walks the gates.
        let flat_round0_template_compact: Option<
            super::backward_flat_compact::FlatRound0BuildPlanCompact<E>,
        > = {
            let gates: Vec<_> = static_data
                .iter()
                .zip(kernel_plans.iter())
                .map(|(sd, kp)| super::backward_flat::PreparedGateForFlatPlan {
                    kind: sd.kind,
                    round0: &sd.round0_descriptors,
                    batch_challenge_power_offset: kp.batch_challenge_offset as u32,
                    constraint_source: kp.constraint_metadata_source.as_ref(),
                })
                .collect();
            Some(super::backward_flat::build_flat_round0_plan(
                &gates,
                &self.storage,
            ))
        };

        // Compile one inline descriptor for the round-0 eval-recipes launch.
        let mut recipe_callbacks = Callbacks::new();
        let (flat_recipe_desc, flat_recipe_count, flat_coeff_device_buf, flat_use_constant) =
            if let Some(ref plan) = flat_round0_template_compact {
                let total = plan.total_coefficients();
                if total > 0 {
                    let compiled = super::backward_flat::compile_recipes_for_device(&plan.recipes);
                    let use_constant = !self.is_delegation || layer_idx != 0;
                    if use_constant {
                        assert!(
                            total <= super::backward_flat::FLAT_ROUND0_CONST_MAX,
                            "flat round 0: {} coefficients exceeds __constant__ limit of {}",
                            total,
                            super::backward_flat::FLAT_ROUND0_CONST_MAX,
                        );
                    }
                    let coeff_buf = if use_constant {
                        None // eval_recipes writes directly to __constant__ symbol
                    } else {
                        Some(context.alloc(total, AllocationPlacement::BestFit)?)
                    };
                    (
                        Some(compiled.desc),
                        compiled.num_recipes,
                        coeff_buf,
                        use_constant,
                    )
                } else {
                    (None, 0, None, true)
                }
            } else {
                (None, 0, None, true)
            };
        // Restored — no diagnostic override

        let max_acc_size = self.trace_len / 2;
        let reduction_temp_storage_bytes =
            get_reduce_temp_storage_bytes::<E>(ReduceOperation::Sum, max_acc_size as i32)?;
        let round_scratch = GpuGKRMainLayerRoundScratch {
            claim_point: context.alloc(folding_steps + 1, AllocationPlacement::Top)?,
            eq_pair_values: context.alloc(
                round0_eq_pair_values_len(folding_steps).max(1),
                AllocationPlacement::Top,
            )?,
            eq_group_tables: context.alloc(
                round0_eq_group_tables_len(folding_steps).max(1),
                AllocationPlacement::Top,
            )?,
            eq_values: context.alloc(max_acc_size.max(1), AllocationPlacement::Top)?,
            accumulator: context.alloc(max_acc_size * 2, AllocationPlacement::Top)?,
            reduction_output: context.alloc(2, AllocationPlacement::Top)?,
            reduction_temp_storage: context
                .alloc_with_extra_alignment::<u8, CUB_TEMP_STORAGE_EXTRA_ALIGNMENT_LOG2>(
                    reduction_temp_storage_bytes,
                    AllocationPlacement::Top,
                )?,
        };

        // --- Build flat continuation plan for rounds 1+ ---
        let (
            flat_continuation_plan,
            flat_continuation_per_step_sources,
            flat_cont_recipe_desc,
            flat_cont_recipe_count,
            cont_recipe_callbacks,
        ) = self.build_flat_continuation_artifacts(
            &static_data,
            &kernel_plans,
            folding_steps,
            layer_idx,
            context,
        )?;
        recipe_callbacks.extend(cont_recipe_callbacks);

        let flat_round1_desc =
            Self::build_flat_round1_desc(flat_continuation_plan.as_ref(), &kernel_plans);
        let flat_round2_desc =
            Self::build_flat_round2_desc(flat_continuation_plan.as_ref(), &kernel_plans);

        // Phase C compact descriptors: each fused builder takes the static
        // desc + plan + storage and produces the compact unified desc in
        // one pass (source pointers resolve to compact `(slot, poly_idx)`
        // records and term/tile/fold metadata builds inline).
        // Phase A2-flat-base provides the per-(layer, class) consolidated
        // base-folding backings; Phase B's per-(layer, class)
        // `intermediate_folding_consolidated` covers the ext side.
        let flat_round1_unified_desc_compact = if let (Some(ref r1_desc), Some(plan)) =
            (&flat_round1_desc, flat_continuation_plan.as_ref())
        {
            Some(
                super::backward_flat_compact::build_flat_round1_unified_desc_compact::<E>(
                    r1_desc,
                    plan,
                    &self.storage,
                ),
            )
        } else {
            None
        };
        let flat_round2_unified_desc_compact = if let (Some(ref r2_desc), Some(plan)) =
            (&flat_round2_desc, flat_continuation_plan.as_ref())
        {
            Some(
                super::backward_flat_compact::build_flat_round2_unified_desc_compact::<E>(
                    r2_desc,
                    plan,
                    &self.storage,
                ),
            )
        } else {
            None
        };
        let flat_continuation_unified_descs_compact: Vec<(
            usize,
            Box<super::backward_flat_compact::GpuFlatContinuationUnifiedDescCompact>,
        )> = if let Some(ref plan) = flat_continuation_plan {
            flat_continuation_per_step_sources
                .iter()
                .map(|(step, sources)| {
                    let compact =
                        super::backward_flat_compact::build_flat_continuation_unified_desc_compact(
                            sources,
                            plan,
                            &self.storage,
                        );
                    (*step, compact)
                })
                .collect()
        } else {
            Vec::new()
        };

        if std::env::var("GPU_PROVER_DUMP_FLAT_PLAN").is_ok() {
            super::backward_flat::dump_flat_round1_plan(
                layer_idx,
                flat_round1_desc.as_deref(),
                flat_continuation_plan.as_ref(),
                &kernel_plans,
            );
        }

        Ok(GpuGKRMainLayerSumcheckLayerPlan {
            layer_idx,
            trace_len: self.trace_len,
            folding_steps,
            batch_challenge_base,
            lookup_multiplicative_challenge: self.lookup_multiplicative_challenge,
            lookup_additive_challenge: self.lookup_additive_challenge,
            external_challenges_flat: {
                let mut values = self
                    .external_challenges
                    .permutation_argument_linearization_challenges
                    .to_vec();
                values.push(self.external_challenges.permutation_argument_additive_part);
                values
            },
            kernel_plans,
            round0_descriptors,
            flat_round0_template_compact,
            flat_recipe_desc,
            flat_recipe_count,
            flat_coeff_device_buf,
            flat_use_constant,
            flat_continuation_plan,
            flat_cont_recipe_desc,
            flat_cont_recipe_count,
            flat_continuation_unified_descs_compact,
            flat_round1_unified_desc_compact,
            flat_round2_unified_desc_compact,
            round_scratch,
            recipe_upload_callbacks: recipe_callbacks,
            batch_challenge_base_override_ptr: None,
        })
    }

    /// Build round-1 fused-source data from the continuation plan and round 1 prepared storage.
    fn build_flat_round1_desc(
        plan: Option<&super::backward_flat::FlatContinuationBuildPlan<E>>,
        kernel_plans: &[GpuGKRMainLayerKernelPlan<E>],
    ) -> Option<Box<super::backward_flat::Round1FusedSources>> {
        use super::backward_flat::{
            GpuFlatBaseAfterOneSourceEntry, GpuFlatContinuingSourceEntry, Round1FusedSources,
            FLAT_CONT_EXT_SOURCE_BIT, FLAT_CONT_MAX_BASE_SOURCES, FLAT_CONT_MAX_EXT_SOURCES,
        };

        let plan = plan?;
        let mut desc = Box::new(Round1FusedSources::default());

        // Build a key→source index map using round3 prepared cache pointers (same as plan).
        let round3_prepared = kernel_plans
            .iter()
            .map(|kp| {
                kp.round3_and_beyond_prepared
                    .iter()
                    .find(|r| r.step == 3)
                    .unwrap_or_else(|| panic!("missing round 3 prepared for step 3"))
            })
            .collect::<Vec<_>>();
        let mut key_map: std::collections::HashMap<(usize, bool), u32> =
            std::collections::HashMap::new();
        for assignment in &plan.source_assignments {
            let r3 = round3_prepared[assignment.gate_idx];
            let cache_ptr = if assignment.is_ext {
                r3.prepared.extension_field_inputs[assignment.input_idx].this_layer_start as usize
            } else {
                r3.prepared.base_field_inputs[assignment.input_idx].this_layer_start as usize
            };
            let key = (cache_ptr, assignment.is_ext);
            if let Some(prev) = key_map.insert(key, assignment.source_table_idx) {
                debug_assert_eq!(
                    prev, assignment.source_table_idx,
                    "flat round1: inconsistent source index for key"
                );
            }
        }

        // Aggregate first_access across *all* gate inputs that map to the same source table idx.
        let mut source_first_access = vec![false; plan.term_desc.num_sources as usize];
        for (gate_idx, kp) in kernel_plans.iter().enumerate() {
            let r3 = round3_prepared[gate_idx];
            for (input_idx, src) in kp.round1_prepared.base_field_inputs.iter().enumerate() {
                let key = (
                    r3.prepared.base_field_inputs[input_idx].this_layer_start as usize,
                    false,
                );
                if let Some(&idx) = key_map.get(&key) {
                    if src.first_access {
                        source_first_access[idx as usize] = true;
                    }
                }
            }
            for (input_idx, src) in kp.round1_prepared.extension_field_inputs.iter().enumerate() {
                let key = (
                    r3.prepared.extension_field_inputs[input_idx].this_layer_start as usize,
                    true,
                );
                if let Some(&idx) = key_map.get(&key) {
                    if src.first_access {
                        source_first_access[idx as usize] = true;
                    }
                }
            }
        }

        // Populate sources. Base sources come from round1_prepared, ext sources from round1_prepared.
        // Source assignments map (gate_idx, is_ext, input_idx) → source_table_idx.
        // For round 1/2, the source index encoding uses the high bit:
        //   base → low indices (unchanged), ext → high bit set.
        // We need to remap: the continuation plan assigned indices into a single flat array,
        // but round 1/2 use split arrays with the high-bit tag.
        let mut base_count = 0u32;
        let mut ext_count = 0u32;
        const UNASSIGNED: u16 = u16::MAX;
        // Map from continuation source_table_idx → round1 tagged index.
        let mut idx_remap = vec![UNASSIGNED; plan.term_desc.num_sources as usize];

        for assignment in &plan.source_assignments {
            let remap_slot = &mut idx_remap[assignment.source_table_idx as usize];
            if *remap_slot != UNASSIGNED {
                debug_assert_eq!(
                    (*remap_slot & FLAT_CONT_EXT_SOURCE_BIT) != 0,
                    assignment.is_ext,
                    "flat round1: inconsistent base/ext mapping for source {}",
                    assignment.source_table_idx,
                );
                continue;
            }
            let kp = &kernel_plans[assignment.gate_idx];
            let combined_first_access = source_first_access[assignment.source_table_idx as usize];
            if assignment.is_ext {
                let src = &kp.round1_prepared.extension_field_inputs[assignment.input_idx];
                let tagged_idx = ext_count as u16 | FLAT_CONT_EXT_SOURCE_BIT;
                assert!(
                    (ext_count as usize) < FLAT_CONT_MAX_EXT_SOURCES,
                    "flat round1: ext source overflow ({ext_count} >= {FLAT_CONT_MAX_EXT_SOURCES})",
                );
                *remap_slot = tagged_idx;
                desc.ext_sources[ext_count as usize] = GpuFlatContinuingSourceEntry {
                    previous_layer_start: if combined_first_access {
                        src.previous_layer_start as *const u8
                    } else {
                        std::ptr::null()
                    },
                    this_layer_cache_start: src.this_layer_start as *mut u8,
                };
                ext_count += 1;
            } else {
                let src = &kp.round1_prepared.base_field_inputs[assignment.input_idx];
                let tagged_idx = base_count as u16;
                assert!(
                    (base_count as usize) < FLAT_CONT_MAX_BASE_SOURCES,
                    "flat round1: base source overflow ({base_count} >= {FLAT_CONT_MAX_BASE_SOURCES})",
                );
                *remap_slot = tagged_idx;
                desc.base_sources[base_count as usize] = GpuFlatBaseAfterOneSourceEntry {
                    base_layer_half_size: src.base_layer_half_size,
                    next_layer_size: src.next_layer_size,
                    base_input_start: src.base_input_start as *const u8,
                    this_layer_cache_start: src.this_layer_cache_start as *mut u8,
                    first_access: combined_first_access,
                    source_kind: src.source_kind,
                };
                base_count += 1;
            }
        }
        desc.num_base_sources = base_count;
        desc.num_ext_sources = ext_count;
        desc.idx_remap = idx_remap;

        Some(desc)
    }

    /// Build round-2 fused-source data from the continuation plan and round 2 prepared storage.
    fn build_flat_round2_desc(
        plan: Option<&super::backward_flat::FlatContinuationBuildPlan<E>>,
        kernel_plans: &[GpuGKRMainLayerKernelPlan<E>],
    ) -> Option<Box<super::backward_flat::Round2FusedSources>> {
        use super::backward_flat::{
            GpuFlatBaseAfterTwoSourceEntry, GpuFlatContinuingSourceEntry, Round2FusedSources,
            FLAT_CONT_EXT_SOURCE_BIT, FLAT_CONT_MAX_BASE_SOURCES, FLAT_CONT_MAX_EXT_SOURCES,
        };

        let plan = plan?;
        let mut desc = Box::new(Round2FusedSources::default());

        // Build a key→source index map using round3 prepared cache pointers (same as plan).
        let round3_prepared = kernel_plans
            .iter()
            .map(|kp| {
                kp.round3_and_beyond_prepared
                    .iter()
                    .find(|r| r.step == 3)
                    .unwrap_or_else(|| panic!("missing round 3 prepared for step 3"))
            })
            .collect::<Vec<_>>();
        let mut key_map: std::collections::HashMap<(usize, bool), u32> =
            std::collections::HashMap::new();
        for assignment in &plan.source_assignments {
            let r3 = round3_prepared[assignment.gate_idx];
            let cache_ptr = if assignment.is_ext {
                r3.prepared.extension_field_inputs[assignment.input_idx].this_layer_start as usize
            } else {
                r3.prepared.base_field_inputs[assignment.input_idx].this_layer_start as usize
            };
            let key = (cache_ptr, assignment.is_ext);
            if let Some(prev) = key_map.insert(key, assignment.source_table_idx) {
                debug_assert_eq!(
                    prev, assignment.source_table_idx,
                    "flat round2: inconsistent source index for key"
                );
            }
        }

        // Aggregate first_access across *all* gate inputs that map to the same source table idx.
        let mut source_first_access = vec![false; plan.term_desc.num_sources as usize];
        for (gate_idx, kp) in kernel_plans.iter().enumerate() {
            let r3 = round3_prepared[gate_idx];
            for (input_idx, src) in kp.round2_prepared.base_field_inputs.iter().enumerate() {
                let key = (
                    r3.prepared.base_field_inputs[input_idx].this_layer_start as usize,
                    false,
                );
                if let Some(&idx) = key_map.get(&key) {
                    if src.first_access {
                        source_first_access[idx as usize] = true;
                    }
                }
            }
            for (input_idx, src) in kp.round2_prepared.extension_field_inputs.iter().enumerate() {
                let key = (
                    r3.prepared.extension_field_inputs[input_idx].this_layer_start as usize,
                    true,
                );
                if let Some(&idx) = key_map.get(&key) {
                    if src.first_access {
                        source_first_access[idx as usize] = true;
                    }
                }
            }
        }

        let mut base_count = 0u32;
        let mut ext_count = 0u32;
        const UNASSIGNED: u16 = u16::MAX;
        let mut idx_remap = vec![UNASSIGNED; plan.term_desc.num_sources as usize];

        for assignment in &plan.source_assignments {
            let remap_slot = &mut idx_remap[assignment.source_table_idx as usize];
            if *remap_slot != UNASSIGNED {
                debug_assert_eq!(
                    (*remap_slot & FLAT_CONT_EXT_SOURCE_BIT) != 0,
                    assignment.is_ext,
                    "flat round2: inconsistent base/ext mapping for source {}",
                    assignment.source_table_idx,
                );
                continue;
            }
            let kp = &kernel_plans[assignment.gate_idx];
            let combined_first_access = source_first_access[assignment.source_table_idx as usize];
            if assignment.is_ext {
                let src = &kp.round2_prepared.extension_field_inputs[assignment.input_idx];
                let tagged_idx = ext_count as u16 | FLAT_CONT_EXT_SOURCE_BIT;
                assert!(
                    (ext_count as usize) < FLAT_CONT_MAX_EXT_SOURCES,
                    "flat round2: ext source overflow ({ext_count} >= {FLAT_CONT_MAX_EXT_SOURCES})",
                );
                *remap_slot = tagged_idx;
                desc.ext_sources[ext_count as usize] = GpuFlatContinuingSourceEntry {
                    previous_layer_start: if combined_first_access {
                        src.previous_layer_start as *const u8
                    } else {
                        std::ptr::null()
                    },
                    this_layer_cache_start: src.this_layer_start as *mut u8,
                };
                ext_count += 1;
            } else {
                let src = &kp.round2_prepared.base_field_inputs[assignment.input_idx];
                let tagged_idx = base_count as u16;
                assert!(
                    (base_count as usize) < FLAT_CONT_MAX_BASE_SOURCES,
                    "flat round2: base source overflow ({base_count} >= {FLAT_CONT_MAX_BASE_SOURCES})",
                );
                *remap_slot = tagged_idx;
                desc.base_sources[base_count as usize] = GpuFlatBaseAfterTwoSourceEntry {
                    base_input_start: src.base_input_start as *const u8,
                    this_layer_cache_start: src.this_layer_cache_start as *mut u8,
                    base_layer_half_size: src.base_layer_half_size,
                    base_quarter_size: src.base_quarter_size,
                    next_layer_size: src.next_layer_size,
                    first_access: combined_first_access,
                    source_kind: src.source_kind,
                };
                base_count += 1;
            }
        }
        desc.num_base_sources = base_count;
        desc.num_ext_sources = ext_count;
        desc.idx_remap = idx_remap;

        Some(desc)
    }

    /// Build flat continuation artifacts for round 3+ kernel dispatch.
    #[allow(clippy::type_complexity)]
    fn build_flat_continuation_artifacts(
        &self,
        static_data: &[PreparedMainLayerKernelStaticData<E>],
        kernel_plans: &[GpuGKRMainLayerKernelPlan<E>],
        folding_steps: usize,
        _layer_idx: usize,
        _context: &ProverContext,
    ) -> CudaResult<(
        Option<super::backward_flat::FlatContinuationBuildPlan<E>>,
        Vec<(
            usize,
            Box<
                [super::backward_flat::GpuFlatContinuingSourceEntry;
                    super::backward_flat::FLAT_CONT_MAX_SOURCES],
            >,
        )>,
        Option<Box<crate::ops::eval_recipes::GpuFlatRecipeEvalDesc>>,
        usize,
        Callbacks<'static>,
    )> {
        use super::backward_flat::{
            build_flat_continuation_plan, compile_recipes_for_device, GpuFlatContinuingSourceEntry,
            PreparedGateForFlatContinuationPlan, FLAT_CONT_CONST_MAX, FLAT_CONT_MAX_SOURCES,
        };

        // Use the first round 3 step's prepared storage to build the term arrays.
        // The term structure (which gates reference which sources) is the same across steps;
        // only the source pointers change per step.
        let first_step = 3;
        let gates: Vec<_> = kernel_plans
            .iter()
            .enumerate()
            .map(|(gate_idx, kp)| {
                let round3 = kp
                    .round3_and_beyond_prepared
                    .iter()
                    .find(|r| r.step == first_step)
                    .unwrap_or_else(|| panic!("missing round 3 prepared for step {first_step}"));
                PreparedGateForFlatContinuationPlan {
                    kind: kp.kind,
                    gate_idx,
                    base_inputs: &round3.prepared.base_field_inputs,
                    ext_inputs: &round3.prepared.extension_field_inputs,
                    batch_challenge_power_offset: kp.batch_challenge_offset as u32,
                    constraint_source: kp.constraint_metadata_source.as_ref(),
                }
            })
            .collect();
        let plan = build_flat_continuation_plan(&gates);
        let total = plan.total_coefficients();
        if total == 0 {
            return Ok((Some(plan), vec![], None, 0, Callbacks::new()));
        }

        // Compile one inline descriptor for the continuation eval-recipes launch.
        let compiled = compile_recipes_for_device(&plan.recipes);
        let mut cont_recipe_callbacks = Callbacks::new();
        assert!(
            total <= FLAT_CONT_CONST_MAX,
            "flat continuation: {} coefficients exceeds __constant__ limit of {}",
            total,
            FLAT_CONT_CONST_MAX,
        );

        // Build a key→source index map using round3 prepared cache pointers (same as plan).
        let round3_prepared = kernel_plans
            .iter()
            .map(|kp| {
                kp.round3_and_beyond_prepared
                    .iter()
                    .find(|r| r.step == first_step)
                    .unwrap_or_else(|| panic!("missing round 3 prepared for step {first_step}"))
            })
            .collect::<Vec<_>>();
        let mut key_map: std::collections::HashMap<(usize, bool), u32> =
            std::collections::HashMap::new();
        for assignment in &plan.source_assignments {
            let r3 = round3_prepared[assignment.gate_idx];
            let cache_ptr = if assignment.is_ext {
                r3.prepared.extension_field_inputs[assignment.input_idx].this_layer_start as usize
            } else {
                r3.prepared.base_field_inputs[assignment.input_idx].this_layer_start as usize
            };
            let key = (cache_ptr, assignment.is_ext);
            if let Some(prev) = key_map.insert(key, assignment.source_table_idx) {
                debug_assert_eq!(
                    prev, assignment.source_table_idx,
                    "flat round3: inconsistent source index for key"
                );
            }
        }

        // Build per-step source tables.
        let mut per_step_sources: Vec<(
            usize,
            Box<[GpuFlatContinuingSourceEntry; FLAT_CONT_MAX_SOURCES]>,
        )> = Vec::new();
        for step in first_step..folding_steps {
            let mut sources: Box<[GpuFlatContinuingSourceEntry; FLAT_CONT_MAX_SOURCES]> =
                Box::new([GpuFlatContinuingSourceEntry::default(); FLAT_CONT_MAX_SOURCES]);
            let mut source_first_access = vec![false; plan.term_desc.num_sources as usize];
            for (gate_idx, kp) in kernel_plans.iter().enumerate() {
                let round3 = kp
                    .round3_and_beyond_prepared
                    .iter()
                    .find(|r| r.step == step)
                    .unwrap_or_else(|| panic!("missing round 3 prepared for step {step}"));
                let r3_key = round3_prepared[gate_idx];
                for (input_idx, src) in round3.prepared.base_field_inputs.iter().enumerate() {
                    let key = (
                        r3_key.prepared.base_field_inputs[input_idx].this_layer_start as usize,
                        false,
                    );
                    if let Some(&idx) = key_map.get(&key) {
                        if src.first_access {
                            source_first_access[idx as usize] = true;
                        }
                    }
                }
                for (input_idx, src) in round3.prepared.extension_field_inputs.iter().enumerate() {
                    let key = (
                        r3_key.prepared.extension_field_inputs[input_idx].this_layer_start as usize,
                        true,
                    );
                    if let Some(&idx) = key_map.get(&key) {
                        if src.first_access {
                            source_first_access[idx as usize] = true;
                        }
                    }
                }
            }
            // Populate source entries for this step.
            for assignment in &plan.source_assignments {
                let round3 = kernel_plans[assignment.gate_idx]
                    .round3_and_beyond_prepared
                    .iter()
                    .find(|r| r.step == step)
                    .unwrap_or_else(|| panic!("missing round 3 prepared for step {step}"));
                let src_plan = if assignment.is_ext {
                    &round3.prepared.extension_field_inputs[assignment.input_idx]
                } else {
                    &round3.prepared.base_field_inputs[assignment.input_idx]
                };
                let combined_first_access =
                    source_first_access[assignment.source_table_idx as usize];
                sources[assignment.source_table_idx as usize] = GpuFlatContinuingSourceEntry {
                    previous_layer_start: if combined_first_access {
                        src_plan.previous_layer_start as *const u8
                    } else {
                        std::ptr::null()
                    },
                    this_layer_cache_start: src_plan.this_layer_start as *mut u8,
                };
            }
            per_step_sources.push((step, sources));
        }

        Ok((
            Some(plan),
            per_step_sources,
            Some(compiled.desc),
            compiled.num_recipes,
            cont_recipe_callbacks,
        ))
    }

    pub(crate) fn prepare_next_layer(
        &mut self,
        batch_challenge_base: E,
        context: &ProverContext,
    ) -> CudaResult<Option<GpuGKRMainLayerSumcheckLayerPlan<E>>> {
        let Some((layer_idx, layer)) = self.pending_layers.pop_front() else {
            return Ok(None);
        };

        assert!(self.trace_len.is_power_of_two());
        let folding_steps = self.trace_len.trailing_zeros() as usize;
        assert!(folding_steps >= 4);

        let blueprints = build_main_layer_kernel_blueprints(
            &layer,
            layer_idx,
            &self.storage,
            &self.external_challenges,
            &self.inits_and_teardowns_top_bits,
            self.inits_and_teardowns_address_high_bits_shift,
            batch_challenge_base,
            self.lookup_multiplicative_challenge,
            self.lookup_additive_challenge,
            self.num_base_layer_memory_polys,
            self.num_base_layer_witness_polys,
        );
        let plan = self.prepare_layer_from_blueprints(
            layer_idx,
            blueprints,
            Some(batch_challenge_base),
            context,
        )?;
        Ok(Some(plan))
    }

    pub(crate) fn prepare_next_layer_static(
        &mut self,
        context: &ProverContext,
    ) -> CudaResult<Option<GpuGKRMainLayerSumcheckLayerPlan<E>>> {
        let Some((layer_idx, layer)) = self.pending_layers.pop_front() else {
            return Ok(None);
        };

        assert!(self.trace_len.is_power_of_two());
        let folding_steps = self.trace_len.trailing_zeros() as usize;
        assert!(folding_steps >= 4);

        let blueprints = build_main_layer_kernel_blueprints_static(
            &layer,
            layer_idx,
            &|addr| {
                // Universally base-field address kinds (trace-holder /
                // scratch / setup) classify as base regardless of which
                // logical layer the kernel runs at; the layout-driven
                // storage path (and forward-pass scratch hydration)
                // populates them at canonical layer 0 / their `layer`
                // field, not at the requesting `layer_idx`. Without
                // this, a `CopyIn{Base,Extension}Field` whose input got
                // rewritten to `ScratchSpace(K)` by
                // `normalize_compiled_circuit_for_gpu` would fall into
                // the ExtCopy branch and panic in
                // `get_for_sumcheck_round_0`'s extension lookup at line
                // 1973 (the value lives in `base_field_inputs`).
                if matches!(
                    addr,
                    GKRAddress::BaseLayerWitness(_)
                        | GKRAddress::BaseLayerMemory(_)
                        | GKRAddress::Setup(_)
                        | GKRAddress::ScratchSpace(_)
                ) {
                    return true;
                }
                self.storage.layers[layer_idx]
                    .base_field_inputs
                    .contains_key(addr)
            },
            &self.external_challenges,
            &self.inits_and_teardowns_top_bits,
            self.inits_and_teardowns_address_high_bits_shift,
            self.num_base_layer_memory_polys,
            self.num_base_layer_witness_polys,
        );
        Ok(Some(self.prepare_layer_from_blueprints(
            layer_idx, blueprints, None, context,
        )?))
    }
}

impl<B, E> GpuGKRDimensionReducingSumcheckLayerPlan<B, E> {
    pub(crate) fn kernel_plans(&self) -> &[GpuGKRDimensionReducingKernelPlan<B, E>] {
        &self.kernel_plans
    }
}

impl<E> GpuGKRMainLayerSumcheckLayerPlan<E> {
    pub(crate) fn kernel_plans(&self) -> &[GpuGKRMainLayerKernelPlan<E>] {
        &self.kernel_plans
    }

    pub(crate) fn round0_descriptors(&self) -> &[GpuSumcheckRound0LaunchDescriptors<BF, E>] {
        &self.round0_descriptors
    }

    fn update_flat_cont_sizes_from_source(
        sizes: &mut Option<FlatContinuationLaunchSizes>,
        consistent: &mut bool,
        src: &super::GpuExtensionFieldPolyContinuingSourcePlan<E>,
    ) {
        if src.this_layer_size == 0 || src.next_layer_size == 0 {
            return;
        }
        let candidate =
            FlatContinuationLaunchSizes::from_sizes(src.this_layer_size, src.next_layer_size);
        match sizes {
            None => *sizes = Some(candidate),
            Some(prev) => {
                if *prev != candidate {
                    *consistent = false;
                }
            }
        }
    }

    fn flat_round1_size_check(&self) -> FlatContinuationSizeCheck {
        let Some(plan) = self.flat_continuation_plan.as_ref() else {
            return FlatContinuationSizeCheck::empty();
        };
        let mut sizes = None;
        let mut has_sources = false;
        let mut consistent = true;
        for assignment in plan.source_assignments.iter() {
            if !assignment.is_ext {
                continue;
            }
            let src = &self.kernel_plans[assignment.gate_idx]
                .round1_prepared
                .extension_field_inputs[assignment.input_idx];
            if src.this_layer_size == 0 || src.next_layer_size == 0 {
                continue;
            }
            has_sources = true;
            Self::update_flat_cont_sizes_from_source(&mut sizes, &mut consistent, src);
            if !consistent {
                break;
            }
        }
        FlatContinuationSizeCheck {
            sizes,
            has_sources,
            consistent: consistent && (!has_sources || sizes.is_some()),
        }
    }

    fn flat_round2_size_check(&self) -> FlatContinuationSizeCheck {
        let Some(plan) = self.flat_continuation_plan.as_ref() else {
            return FlatContinuationSizeCheck::empty();
        };
        let mut sizes = None;
        let mut has_sources = false;
        let mut consistent = true;
        for assignment in plan.source_assignments.iter() {
            if !assignment.is_ext {
                continue;
            }
            let src = &self.kernel_plans[assignment.gate_idx]
                .round2_prepared
                .extension_field_inputs[assignment.input_idx];
            if src.this_layer_size == 0 || src.next_layer_size == 0 {
                continue;
            }
            has_sources = true;
            Self::update_flat_cont_sizes_from_source(&mut sizes, &mut consistent, src);
            if !consistent {
                break;
            }
        }
        FlatContinuationSizeCheck {
            sizes,
            has_sources,
            consistent: consistent && (!has_sources || sizes.is_some()),
        }
    }

    fn flat_round3_size_check(&self, step: usize) -> FlatContinuationSizeCheck {
        let Some(plan) = self.flat_continuation_plan.as_ref() else {
            return FlatContinuationSizeCheck::empty();
        };
        let mut sizes = None;
        let mut has_sources = false;
        let mut consistent = true;
        for assignment in plan.source_assignments.iter() {
            let round3 = self.kernel_plans[assignment.gate_idx]
                .round3_and_beyond_prepared
                .iter()
                .find(|r| r.step == step);
            let Some(round3) = round3 else {
                continue;
            };
            let src = if assignment.is_ext {
                &round3.prepared.extension_field_inputs[assignment.input_idx]
            } else {
                &round3.prepared.base_field_inputs[assignment.input_idx]
            };
            if src.this_layer_size == 0 || src.next_layer_size == 0 {
                continue;
            }
            has_sources = true;
            Self::update_flat_cont_sizes_from_source(&mut sizes, &mut consistent, src);
            if !consistent {
                break;
            }
        }
        FlatContinuationSizeCheck {
            sizes,
            has_sources,
            consistent: consistent && (!has_sources || sizes.is_some()),
        }
    }
}

const fn main_layer_kind_batch_challenge_count(kind: GpuGKRMainLayerKernelKind) -> usize {
    match kind {
        GpuGKRMainLayerKernelKind::LookupPair
        | GpuGKRMainLayerKernelKind::LookupBasePair
        | GpuGKRMainLayerKernelKind::LookupBaseMinusMultiplicityByBase
        | GpuGKRMainLayerKernelKind::LookupExtMinusMultiplicityByExt
        | GpuGKRMainLayerKernelKind::LookupUnbalanced
        | GpuGKRMainLayerKernelKind::LookupWithCachedDensAndSetup
        | GpuGKRMainLayerKernelKind::LookupPairFromBaseInputs
        | GpuGKRMainLayerKernelKind::LookupWithDensAndSetupExpressions
        | GpuGKRMainLayerKernelKind::LookupPairFromVectorInputs
        | GpuGKRMainLayerKernelKind::LookupFromVectorInputWithSetup
        | GpuGKRMainLayerKernelKind::LookupUnbalancedPairWithVectorInputs
        | GpuGKRMainLayerKernelKind::LookupExtPair
        | GpuGKRMainLayerKernelKind::LookupUnbalancedExtension => 2,
        _ => 1,
    }
}

fn packed_main_layer_batch_challenge_len<E>(
    kernel_plans: &[GpuGKRMainLayerKernelPlan<E>],
) -> usize {
    kernel_plans
        .iter()
        .map(|kernel| {
            let count = main_layer_kind_batch_challenge_count(kernel.kind);
            assert_eq!(
                kernel.batch_challenge_count, count,
                "kernel {:?} has unexpected batch-challenge count",
                kernel.kind
            );
            count
        })
        .sum()
}

fn fill_packed_main_layer_batch_challenges<E: Field>(
    kernel_plans: &[GpuGKRMainLayerKernelPlan<E>],
    batch_challenge_base: E,
    dst: &mut [E],
) {
    assert_eq!(
        dst.len(),
        packed_main_layer_batch_challenge_len(kernel_plans)
    );
    let mut packed_offset = 0usize;
    for kernel in kernel_plans.iter() {
        let count = main_layer_kind_batch_challenge_count(kernel.kind);
        assert_eq!(
            kernel.batch_challenge_offset, packed_offset,
            "main-layer batch challenges must stay densely packed in record order"
        );
        let dst_slice = &mut dst[packed_offset..packed_offset + count];
        if kernel.batch_challenges.is_empty() {
            let mut challenge = field_pow(batch_challenge_base, kernel.batch_challenge_offset);
            for dst in dst_slice.iter_mut() {
                *dst = challenge;
                challenge.mul_assign(&batch_challenge_base);
            }
        } else {
            assert_eq!(
                kernel.batch_challenges.len(),
                count,
                "kernel {:?} materialized unexpected batch-challenge count",
                kernel.kind
            );
            dst_slice.copy_from_slice(&kernel.batch_challenges);
        }
        packed_offset += count;
    }
}

impl<E: Field + 'static> GpuGKRMainLayerSumcheckLayerPlan<E> {
    pub(crate) fn schedule_round_1(
        &self,
        callbacks: &mut Callbacks<'static>,
        context: &ProverContext,
    ) -> CudaResult<Vec<GpuSumcheckRound1ScheduledLaunchDescriptors<BF, E>>> {
        self.kernel_plans
            .iter()
            .map(|kernel| {
                kernel
                    .round1_prepared
                    .schedule_upload_launch_descriptors(context, callbacks)
            })
            .collect()
    }

    pub(crate) fn schedule_round_2(
        &self,
        callbacks: &mut Callbacks<'static>,
        context: &ProverContext,
    ) -> CudaResult<Vec<GpuSumcheckRound2ScheduledLaunchDescriptors<BF, E>>> {
        self.kernel_plans
            .iter()
            .map(|kernel| {
                kernel
                    .round2_prepared
                    .schedule_upload_launch_descriptors(context, callbacks)
            })
            .collect()
    }

    pub(crate) fn schedule_round_3_and_beyond(
        &self,
        step: usize,
        callbacks: &mut Callbacks<'static>,
        context: &ProverContext,
    ) -> CudaResult<Vec<GpuSumcheckRound3AndBeyondScheduledLaunchDescriptors<E>>> {
        self.kernel_plans
            .iter()
            .map(|kernel| {
                kernel
                    .round3_and_beyond_prepared
                    .iter()
                    .find(|prepared| prepared.step == step)
                    .unwrap_or_else(|| panic!("missing prepared round 3+ storage for step {step}"))
                    .prepared
                    .schedule_upload_launch_descriptors(context, callbacks)
            })
            .collect()
    }
}

impl<B: 'static, E: 'static> GpuGKRDimensionReducingSumcheckLayerPlan<B, E>
where
    E: Field
        + FieldExtension<BF>
        + Reduce
        + GpuDimensionReducingKernelSet
        + GpuBackwardSumcheckRoundUpdateKernel,
    Mul: BinaryOp<E, E, E>,
    [(); E::DEGREE]: Sized,
{
    fn compute_combined_claim(&self, output_claims: &BTreeMap<GKRAddress, E>) -> E {
        let mut result = E::ZERO;
        for kernel in self.kernel_plans.iter() {
            for (output, challenge) in kernel
                .inputs
                .outputs_in_extension
                .iter()
                .zip(kernel.batch_challenges.iter())
            {
                let mut term = output_claims
                    .get(output)
                    .copied()
                    .unwrap_or_else(|| panic!("missing output claim for {output:?}"));
                term.mul_assign(challenge);
                result.add_assign(&term);
            }
        }

        result
    }

    fn batch_challenge_base_ptr(&self) -> *const E {
        if let Some(ptr) = self.batch_challenge_base_override_ptr {
            return ptr;
        }
        unsafe {
            self.round_scratch
                .claim_point
                .as_ptr()
                .add(self.folding_steps)
        }
    }

    fn build_round0_eq_values(
        &mut self,
        eq_pair_values_host: &HostAllocation<[E]>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let challenge_count = self.folding_steps.saturating_sub(1);
        let acc_size = 1usize << challenge_count;
        memory_copy_async(
            &mut self.round_scratch.eq_pair_values[..eq_pair_values_host.len()],
            eq_pair_values_host,
            context.get_exec_stream(),
        )?;
        launch_build_round0_eq_values_from_pairs(
            self.round_scratch.eq_pair_values.as_ptr(),
            challenge_count,
            self.round_scratch.eq_group_tables.as_mut_ptr(),
            self.round_scratch.eq_values.as_mut_ptr(),
            acc_size,
            context,
        )
    }

    fn fold_eq_values_for_next_round(
        &mut self,
        acc_size: usize,
        context: &ProverContext,
    ) -> CudaResult<()> {
        debug_assert!(acc_size.is_power_of_two());
        debug_assert!(acc_size >= 2);
        launch_fold_eq_values_in_place(
            self.round_scratch.eq_values.as_mut_ptr(),
            acc_size / 2,
            context,
        )
    }

    fn launch_round0_kernels(
        &mut self,
        acc_size: usize,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let mut batch = self.round0_batch_template_compact;
        batch.eq_values = self.round_scratch.eq_values.as_ptr();
        batch.contributions = self.round_scratch.accumulator.as_mut_ptr();
        launch_dim_reducing_round0_batched_compact(&batch, acc_size, context)
    }

    fn launch_round1_kernels_from_symbol(
        &mut self,
        acc_size: usize,
        explicit_form: bool,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let mut batch = self.round1_batch_template_compact;
        batch.eq_values = self.round_scratch.eq_values.as_ptr();
        batch.contributions = self.round_scratch.accumulator.as_mut_ptr();
        batch.explicit_form = explicit_form;
        launch_dim_reducing_round1_batched_compact(&batch, null(), acc_size, context)
    }

    fn launch_continuation_kernels_from_symbol(
        &mut self,
        step: usize,
        acc_size: usize,
        explicit_form: bool,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let mut batch = self.continuation_batch_template_compact;
        batch.eq_values = self.round_scratch.eq_values.as_ptr();
        batch.contributions = self.round_scratch.accumulator.as_mut_ptr();
        batch.explicit_form = explicit_form;
        launch_dim_reducing_continuation_batched_compact(&batch, null(), acc_size, step, context)
    }

    /// Runs the two CUB reductions for a round's sumcheck accumulator without
    /// copying the result back to the host. Used by the on-device per-round
    /// update path where the reduction output stays on the GPU and is consumed
    /// by `launch_backward_sumcheck_round_update` directly.
    fn run_round_coefficients_reduction_device(
        &mut self,
        step: usize,
        acc_size: usize,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let challenge_count = self.folding_steps - step - 1;
        assert_eq!(acc_size, 1usize << challenge_count);
        let stream = context.get_exec_stream();
        let reduction_temp = unsafe {
            DeviceSlice::from_raw_parts_mut(
                self.round_scratch.reduction_temp_storage.as_mut_ptr(),
                self.round_scratch.reduction_temp_storage.len(),
            )
        };
        {
            let low_half = DeviceVectorChunk::new(&self.round_scratch.accumulator, 0, acc_size);
            reduce(
                ReduceOperation::Sum,
                reduction_temp,
                &low_half,
                &mut self.round_scratch.reduction_output[0],
                stream,
            )?;
        }
        {
            let high_half =
                DeviceVectorChunk::new(&self.round_scratch.accumulator, acc_size, acc_size);
            reduce(
                ReduceOperation::Sum,
                reduction_temp,
                &high_half,
                &mut self.round_scratch.reduction_output[1],
                stream,
            )?;
        }
        Ok(())
    }

    fn final_evaluation_sources_for_last_step(
        &self,
        last_step: usize,
    ) -> BTreeMap<GKRAddress, *const E> {
        let mut result = BTreeMap::new();
        for kernel in self.kernel_plans.iter() {
            let sources = match last_step {
                1 => &kernel.round1_prepared.extension_field_inputs,
                2 => {
                    &kernel
                        .round2_prepared
                        .as_ref()
                        .expect("round 2 storage must be prepared")
                        .extension_field_inputs
                }
                step => {
                    &kernel
                        .round3_and_beyond_prepared
                        .iter()
                        .find(|prepared| prepared.step == step)
                        .unwrap_or_else(|| {
                            panic!("missing prepared round 3+ storage for step {step}")
                        })
                        .prepared
                        .extension_field_inputs
                }
            };
            for (address, source) in kernel.inputs.inputs_in_extension.iter().zip(sources.iter()) {
                if *address == GKRAddress::placeholder() || result.contains_key(address) {
                    continue;
                }
                result.insert(*address, source.this_layer_start.cast_const());
            }
        }

        result
    }

    pub(crate) fn schedule_execute_dimension_reducing_layer_from_workflow_state(
        &mut self,
        workflow_state: ScheduledBackwardWorkflowStateHandle<E>,
        mut device_seed: DeviceAllocation<u32>,
        device_claim_point_in: DeviceClaimPointAndBatching<E>,
        device_claims_in: DeviceAllocation<E>,
        claim_layout: &ClaimBufferLayout,
        // When `Some` (production), per-round kernels write coeffs directly
        // into the slab's `internal_round_coefficients` range for `layer_slot`
        // and the per-address gather writes directly into
        // `final_step_evaluations` (B1 + B2). When `None` (test paths with
        // placeholder layouts), per-layer fallback device buffers are
        // allocated so the kernels still have valid destinations.
        proof_slab: Option<&DeviceAllocation<E4>>,
        proof_layout: &ProofLayout,
        layer_slot: usize,
        mirror_layer_to_host: bool,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRDimensionReducingScheduledLayerExecution<B, E>> {
        const DIMENSION_REDUCING_LAYER_RANGE_MIN_FOLDING_STEPS: usize = 19;

        let stream = context.get_exec_stream();
        let mut tracing_ranges = Vec::new();
        let last_step = self.folding_steps - 1;
        let mut layer_range = if self.folding_steps
            >= DIMENSION_REDUCING_LAYER_RANGE_MIN_FOLDING_STEPS
        {
            let layer_name = format!("gkr.backward.dimension_reducing.layer.{}", self.layer_idx);
            let range = Range::new(layer_name)?;
            range.start(stream)?;
            Some(range)
        } else {
            None
        };
        // Compute the per-layer combined_claim `(exp, claim_idx)` descriptor
        // consumed by `build_combined_claim`. Passed inline as kernel-arg
        // (`__grid_constant__`) — no device buffer, no per-layer H2D. The
        // audit-locked ceiling `GKR_COMBINED_CLAIM_MAX_PAIRS` is enforced
        // inside `build_combined_claim`.
        let mut desc_pairs: Vec<u32> = Vec::with_capacity(
            self.kernel_plans
                .iter()
                .map(|kernel| kernel.inputs.outputs_in_extension.len() * 2)
                .sum(),
        );
        for kernel in self.kernel_plans.iter() {
            for (j, output) in kernel.inputs.outputs_in_extension.iter().enumerate() {
                desc_pairs.push((kernel.batch_challenge_offset + j) as u32);
                desc_pairs.push(claim_layout.claim_idx(output));
            }
        }
        let mut shared_state = Box::new(ScheduledDimensionReducingLayerExecutionState {
            seed: Seed::default(),
            claim: E::ZERO,
            eq_prefactor: E::ONE,
            folding_challenges: Vec::with_capacity(self.folding_steps + 1),
            result: None,
        });
        let shared_state_handle =
            crate::primitives::context::UnsafeMutAccessor::new(shared_state.as_mut());

        // `device_seed` is owned by the orchestrator across all backward
        // layers (initialized from the post-forward device seed produced in
        // proof.rs). The fused per-round kernel and the end-of-layer device
        // transcript work mutate it in place; the scheduler returns it via
        // `Execution::device_seed` so the next layer can thread it in.
        let mut device_claim: DeviceAllocation<E> = context.alloc(1, AllocationPlacement::Top)?;
        let mut device_eq_prefactor: DeviceAllocation<E> =
            context.alloc(1, AllocationPlacement::Top)?;
        let coeffs_total_len = last_step * 4;
        // B1: per-round kernels write coeffs straight into the slab range for
        // this layer when `proof_slab` is provided — no standalone allocation
        // and no post-loop slab D2D. The kernels are stream-ordered against
        // the terminal D2H of the slab in `prove()`, so the slab is
        // self-consistent on `exec_stream`. Test paths fall back to a
        // per-layer device buffer.
        let mut fallback_device_coeffs: Option<DeviceAllocation<E>> = None;
        let coeffs_buffer_ptr: *mut E = if let Some(slab) = proof_slab {
            if coeffs_total_len > 0 {
                let (dst_ptr, dst_len) = unsafe {
                    proof_layout
                        .backward_internal_coeffs_device_mut(slab.as_ptr() as *mut u8, layer_slot)
                };
                debug_assert_eq!(
                    dst_len, coeffs_total_len,
                    "slab internal_round_coefficients range must match layer's coeffs_total_len",
                );
                dst_ptr as *mut E
            } else {
                null_mut()
            }
        } else {
            let alloc: DeviceAllocation<E> =
                context.alloc(coeffs_total_len.max(1), AllocationPlacement::Top)?;
            let ptr = alloc.as_ptr() as *mut E;
            fallback_device_coeffs = Some(alloc);
            ptr
        };

        // The `[claim_point || batching_challenge]` input is consumed
        // directly from `device_claim_point_in` — no D2D into a per-layer
        // `round_scratch.claim_point` buffer. Per-round kernels read it for
        // `prev_coord_slice`; `launch_build_eq_values_from_point` reads the
        // suffix `[1..folding_steps]`. The launch_round*_kernels path reads
        // the batching challenge slot via `batch_challenge_base_ptr()`, so
        // point that at `device_claim_point_in[folding_steps]` for the
        // duration of this layer's scheduling.
        let claim_point_and_batching_len = self.folding_steps + 1;
        assert_eq!(
            device_claim_point_in.len(),
            claim_point_and_batching_len,
            "device claim_point input size must match this layer's folding_steps + 1",
        );
        self.batch_challenge_base_override_ptr =
            Some(unsafe { device_claim_point_in.as_ptr().add(self.folding_steps) });
        schedule_dim_reducing_batch_challenge_table_prelude(
            self.batch_challenge_base_ptr() as *const E4,
            context,
        )?;
        // Build `eq_group_tables` + `eq_values` directly from the device
        // claim_point (using coords `[1..folding_steps]` — the suffix that
        // `fill_round0_eq_pair_values` used to expand on host). Replaces the
        // `eq_pair_values_host` H2D + `build_round0_eq_values_from_pairs`
        // kernel chain with a single on-device builder.
        let challenge_count = self.folding_steps.saturating_sub(1);
        let acc_size = 1usize << challenge_count;
        launch_build_eq_values_from_point(
            device_claim_point_in.as_ptr(),
            1,
            challenge_count,
            self.round_scratch.eq_group_tables.as_mut_ptr(),
            self.round_scratch.eq_values.as_mut_ptr(),
            acc_size,
            context,
        )?;

        assert_eq!(
            device_claims_in.len(),
            claim_layout.len(),
            "device claims buffer must match claim layout length",
        );

        {
            let claims_e4: &era_cudart::slice::DeviceSlice<E4> =
                unsafe { device_claims_in[..claim_layout.len()].transmute::<E4>() };
            let batching_slice = unsafe { device_claim_point_in.slice(self.folding_steps, 1) };
            let batching_e4: &era_cudart::slice::DeviceSlice<E4> =
                unsafe { batching_slice.transmute::<E4>() };
            let claim_out_e4: &mut era_cudart::slice::DeviceSlice<E4> =
                unsafe { device_claim[..].transmute_mut::<E4>() };
            let eq_out_e4: &mut era_cudart::slice::DeviceSlice<E4> =
                unsafe { device_eq_prefactor[..].transmute_mut::<E4>() };
            crate::ops::blake2s::build_combined_claim(
                claims_e4,
                batching_e4,
                &desc_pairs,
                claim_out_e4,
                eq_out_e4,
                stream,
            )?;
        }

        // Hoisted: `device_claim_point_out` holds the next layer's
        // `[claim_point || batching_challenge]` buffer. Slots `[0..folding_steps - 1]`
        // are written in-place by the per-round update kernels (replacing
        // the old `round_challenge_storage` + post-loop D2D pack), and
        // slots `[folding_steps - 1..folding_steps + 2]` are written by the
        // post-loop transcript squeeze (replacing the old `d_layer_challenges`
        // allocation + post-loop D2D pack).
        let next_claim_point_and_batching_len = self.folding_steps + 2;
        assert!(
            next_claim_point_and_batching_len <= MAX_DIM_REDUCING_LAYER_CLAIM_POINT_LEN,
            "dim-reducing layer claim point length {} exceeds __constant__ symbol capacity {}",
            next_claim_point_and_batching_len,
            MAX_DIM_REDUCING_LAYER_CLAIM_POINT_LEN
        );
        let mut device_claim_point_out = unsafe {
            DeviceClaimPointAndBatching::from_raw_symbol_parts(
                get_dim_reducing_layer_claim_point_device_ptr() as *mut E,
                next_claim_point_and_batching_len,
            )
        };
        let mut reduction_states = Vec::with_capacity(last_step);

        for step in 0..last_step {
            let acc_size = 1usize << (self.folding_steps - step - 1);
            if step == 0 {
                self.launch_round0_kernels(acc_size, context)?;
            } else {
                match step {
                    1 => self.launch_round1_kernels_from_symbol(acc_size, false, context)?,
                    step => self
                        .launch_continuation_kernels_from_symbol(step, acc_size, false, context)?,
                }
            }

            // Device-only reduction: sums accumulator halves into
            // `round_scratch.reduction_output` (2 E4 values) without any D2H.
            self.run_round_coefficients_reduction_device(step, acc_size, context)?;
            self.fold_eq_values_for_next_round(acc_size, context)?;

            // Fused on-device per-round update: reads the reduction output and
            // current (seed, claim, eq_prefactor) state, derives the 4
            // univariate coefficients, commits them to the transcript, extracts
            // the next folding challenge, and folds claim/eq_prefactor — all in
            // one single-thread kernel. The challenge lands directly in
            // `device_claim_point_out[step]`, ready for the next round's
            // kernel to read and for the next layer to consume.
            let prev_coord_slice = unsafe { device_claim_point_in.slice(step, 1) };
            // SAFETY: `coeffs_buffer_ptr` points either into `proof_slab`
            // (held alive by `_proof_slab` keepalive in `prove()`) or into
            // `fallback_device_coeffs` (dropped at end of this function,
            // after every kernel that writes through this pointer is
            // scheduled). The 4-element window is in-bounds for both
            // (`coeffs_total_len = last_step * 4`).
            let coeffs_round_slice =
                unsafe { DeviceSlice::from_raw_parts_mut(coeffs_buffer_ptr.add(step * 4), 4) };
            let challenge_slice = unsafe { device_claim_point_out.slice_mut(step, 1) };
            E::launch_backward_sumcheck_round_update(
                &self.round_scratch.reduction_output,
                prev_coord_slice,
                &mut device_seed,
                &mut device_claim,
                &mut device_eq_prefactor,
                coeffs_round_slice,
                challenge_slice,
                stream,
            )?;

            // Empty reduction_state retained for struct ABI compatibility — the
            // kernel-driven path no longer has per-round host callbacks.
            reduction_states.push(ScheduledDimensionReducingReductionState {
                callbacks: Callbacks::new(),
                _phantom: std::marker::PhantomData,
            });
        }

        match last_step {
            1 => self.launch_round1_kernels_from_symbol(1, true, context)?,
            step => self.launch_continuation_kernels_from_symbol(step, 1, true, context)?,
        }

        // B1: coeffs already landed in the slab via the per-round kernels
        // (or in `fallback_device_coeffs` for test paths). No post-loop
        // slab D2D needed.

        // Device-side inter-layer transcript: pack the flattened last-round
        // evaluations into a packed E buffer (D2D from each address's 4-E
        // source slot) — written **directly into the slab** via B2 in the
        // production path, with the same flat layout the previous
        // `d_layer_transcript_inputs` buffer used. Absorbed into device_seed
        // via transcript_commit, then squeezed into 3 E4 challenges
        // `[r_before_last, r_last, next_batching_challenge]` via
        // transcript_squeeze_e4. The same packed buffer feeds the on-device
        // `backward_new_claims_two_var` kernel (Phase G) — replacing the N
        // per-address `schedule_last_evaluations_readback` D2Hs and the host
        // `evaluate_with_two_variable_eq_ext` loop that used to run inside
        // the final readback callback.
        let transcript_input_sources = self.final_evaluation_sources_for_last_step(last_step);
        let num_addresses = transcript_input_sources.len();
        let transcript_inputs_len = num_addresses * 4;
        let transcript_input_addresses: Vec<GKRAddress> =
            transcript_input_sources.keys().copied().collect();
        // B2: per-address gather writes straight into the slab's
        // `final_step_evaluations` range when `proof_slab` is provided. Test
        // paths fall back to a per-layer device buffer. The flat layout (4 E
        // per address, in BTreeMap key order from
        // `final_evaluation_sources_for_last_step`) matches what
        // `build_proof_layout_inputs` stored in
        // `ProofLayout.backward[slot].final_step_eval_addresses`.
        let mut fallback_d_layer_transcript_inputs: Option<DeviceAllocation<E>> = None;
        let transcript_inputs_buffer_ptr: *mut E = if let Some(slab) = proof_slab {
            if transcript_inputs_len > 0 {
                let (dst_ptr, dst_len) = unsafe {
                    proof_layout
                        .backward_final_step_evals_device_mut(slab.as_ptr() as *mut u8, layer_slot)
                };
                debug_assert_eq!(
                    dst_len, transcript_inputs_len,
                    "slab final_step_evaluations range must match layer's transcript_inputs_len",
                );
                dst_ptr as *mut E
            } else {
                null_mut()
            }
        } else {
            let alloc: DeviceAllocation<E> =
                context.alloc(transcript_inputs_len.max(1), AllocationPlacement::Top)?;
            let ptr = alloc.as_ptr() as *mut E;
            fallback_d_layer_transcript_inputs = Some(alloc);
            ptr
        };
        // B7: per-address gather kernel — single launch replaces the
        // num_addresses-element D2D loop. Source pointers are scheduling-
        // time-known and now ride inline in the kernel-arg struct
        // (`GpuGatherEAddressesDesc`), so the previous SchedulerHostAllocation
        // + per-launch H2D of the pointer table is gone. The slab/fallback
        // `transcript_inputs_e_slice` below is still held alive by
        // `_proof_slab` (slab path) or `fallback_d_layer_transcript_inputs`
        // (test path) for the duration of the gather launch.
        if num_addresses > 0 {
            let src_ptrs: Vec<u64> = transcript_input_sources
                .values()
                .map(|p| *p as u64)
                .collect();
            let dst = unsafe {
                DeviceSlice::from_raw_parts_mut(
                    transcript_inputs_buffer_ptr as *mut E4,
                    transcript_inputs_len,
                )
            };
            crate::ops::blake2s::gather_e_addresses(&src_ptrs, dst, 4, stream)?;
        }

        // SAFETY: E = E4 in every instantiation of this scheduler; the u32
        // view matches the host `commit_field_els::<BF, E4>` byte layout
        // (covered by `ops::blake2s::tests::transcript_squeeze_e4_parity_*`).
        // The slab/fallback memory is alive through the kernel launch, and
        // `transcript_commit` only reads from this slice.
        let transcript_inputs_e_slice = unsafe {
            DeviceSlice::from_raw_parts(
                transcript_inputs_buffer_ptr as *const E,
                transcript_inputs_len,
            )
        };
        let d_transcript_inputs_u32 = unsafe { transcript_inputs_e_slice.transmute::<u32>() };
        crate::ops::blake2s::transcript_commit(&mut device_seed, d_transcript_inputs_u32, stream)?;

        // Squeeze the 3 layer challenges directly into the tail of
        // `device_claim_point_out` — slots
        // `[last_step..last_step + 3] = [r_before_last, r_last, next_batching_challenge]`.
        // SAFETY: `last_step + 3 = folding_steps + 2 = next_claim_point_and_batching_len`,
        // so the range is in-bounds, and only this scheduling site writes
        // it (see write-exclusivity below).
        {
            let layer_challenges_dst = unsafe { device_claim_point_out.slice_mut(last_step, 3) };
            // SAFETY: E = E4 in every instantiation; the transmute is a no-op at
            // the byte level and matches host `draw_random_field_els::<BF, E4>`.
            let layer_challenges_dst_e4 = unsafe { layer_challenges_dst.transmute_mut::<E4>() };
            crate::ops::blake2s::transcript_squeeze_e4(
                &mut device_seed,
                layer_challenges_dst_e4,
                stream,
            )?;
        }

        // Device-side per-address `new_claims` evaluator. Consumes the packed
        // last-round evaluations (4 E per address) and the just-squeezed
        // `[r_before_last, r_last]` to produce N E per-address next-layer
        // claims. Replaces the host loop inside the final readback callback.
        // The kernel is stream-ordered after the transcript squeeze and
        // before the subsequent D2H of the result.
        let mut device_new_claims: DeviceAllocation<E> =
            context.alloc(num_addresses.max(1), AllocationPlacement::Top)?;
        if num_addresses > 0 {
            // SAFETY: E = E4 in every instantiation; the transmutes match the
            // kernel's `e4` view of both the packed evals and the challenges.
            // The packed evals slab/fallback memory is alive through the
            // kernel launch.
            let transcript_inputs_e_view = unsafe {
                DeviceSlice::from_raw_parts(
                    transcript_inputs_buffer_ptr as *const E,
                    transcript_inputs_len,
                )
            };
            let transcript_inputs_e4: &era_cudart::slice::DeviceSlice<E4> =
                unsafe { transcript_inputs_e_view.transmute::<E4>() };
            // SAFETY: layer-challenge tail lives at
            // `claim_point_out[last_step..last_step + 3]`; reading the first
            // two (`r_before_last`, `r_last`) for the kernel.
            let challenges_view = unsafe {
                DeviceSlice::from_raw_parts(device_claim_point_out.as_ptr().add(last_step), 2)
            };
            let challenges_e4: &era_cudart::slice::DeviceSlice<E4> =
                unsafe { challenges_view.transmute::<E4>() };
            let new_claims_e4: &mut era_cudart::slice::DeviceSlice<E4> =
                unsafe { device_new_claims[..num_addresses].transmute_mut::<E4>() };
            crate::ops::blake2s::backward_new_claims_two_var(
                transcript_inputs_e4,
                challenges_e4,
                new_claims_e4,
                stream,
            )?;
        }

        // `device_claim_point_out` is already populated in place — slots
        // `[0..last_step]` by the per-round update kernels and slots
        // `[last_step..last_step + 3]` by the transcript squeeze. No post-loop
        // pack copies needed.

        let next_claim_layout =
            ClaimBufferLayout::from_addresses(transcript_input_addresses.clone());
        let callback_addresses = next_claim_layout.addresses.clone();
        let mut final_readback_callbacks = Callbacks::new();
        if mirror_layer_to_host {
            // Fork exec -> d2h: every D2H source below has been written on exec by this point
            // (d_layer_challenges via `transcript_squeeze_e4`, device_new_claims via
            // `backward_new_claims_two_var`, device_seed/round_challenge_storage from earlier
            // work in this layer; coeffs and packed last-evals are now slab-direct via B1/B2
            // and not D2H'd here). A single fork event covers all of them; the matching join
            // is recorded after the last D2H below.
            let layer_src_ready = era_cudart::event::CudaEvent::create_with_flags(
                era_cudart::event::CudaEventCreateFlags::DISABLE_TIMING,
            )?;
            layer_src_ready.record(stream)?;
            let d2h_stream = context.get_d2h_stream();
            d2h_stream.wait_event(
                &layer_src_ready,
                era_cudart::stream::CudaStreamWaitEventFlags::DEFAULT,
            )?;

            let mut layer_challenges_host: HostAllocation<[E]> =
                unsafe { context.alloc_host_uninit_slice(3) };
            let layer_challenges_accessor = layer_challenges_host.get_accessor();
            // SAFETY: `[last_step..last_step + 3]` was just written by the
            // transcript squeeze on `stream` and the d2h_stream waits on
            // `layer_src_ready` before this read.
            let layer_challenges_src = unsafe {
                DeviceSlice::from_raw_parts(device_claim_point_out.as_ptr().add(last_step), 3)
            };
            memory_copy_async(&mut layer_challenges_host, layer_challenges_src, d2h_stream)?;

            // Single D2H of device-computed new_claims. Replaces N per-address D2Hs
            // (one per address × 4 E) + the host `evaluate_with_two_variable_eq_ext` loop.
            let mut new_claims_host: HostAllocation<[E]> =
                unsafe { context.alloc_host_uninit_slice(num_addresses.max(1)) };
            let new_claims_accessor = new_claims_host.get_accessor();
            if num_addresses > 0 {
                memory_copy_async(
                    &mut new_claims_host,
                    &device_new_claims[..num_addresses],
                    d2h_stream,
                )?;
            }

            // Bulk D2H the on-device per-layer state that the final readback
            // callback needs to advance the workflow (seed + folding challenges for
            // WHIR host setup; coeffs and packed last-evaluations stay on device
            // and flow through the proof slab via B1/B2). Copies continue on
            // `d2h_stream` within the same fork/join window as the D2Hs above.
            let mut final_seed_host = unsafe { context.alloc_host_uninit_slice(STATE_SIZE) };
            let final_seed_accessor = final_seed_host.get_accessor();
            memory_copy_async(&mut final_seed_host, &device_seed, d2h_stream)?;

            let mut final_folding_challenges_host: HostAllocation<[E]> =
                unsafe { context.alloc_host_uninit_slice(last_step.max(1)) };
            let final_folding_challenges_accessor = final_folding_challenges_host.get_accessor();
            if last_step > 0 {
                // SAFETY: `[0..last_step]` are written in-place by the
                // per-round update kernels. The d2h_stream waits on
                // `layer_src_ready` before this read.
                let folding_src = unsafe {
                    DeviceSlice::from_raw_parts(device_claim_point_out.as_ptr(), last_step)
                };
                memory_copy_async(&mut final_folding_challenges_host, folding_src, d2h_stream)?;
            }

            // Join d2h -> exec: the per-layer D2Hs above are fully scheduled. Exec waits on this
            // event before the final readback callback (which reads the host slabs) is scheduled,
            // and before any downstream drop of the source allocations at the end of this function.
            let layer_d2h_done = era_cudart::event::CudaEvent::create_with_flags(
                era_cudart::event::CudaEventCreateFlags::DISABLE_TIMING,
            )?;
            layer_d2h_done.record(d2h_stream)?;
            stream.wait_event(
                &layer_d2h_done,
                era_cudart::stream::CudaStreamWaitEventFlags::DEFAULT,
            )?;

            let shared_state_for_callback = shared_state_handle;
            let workflow_state_for_callback = workflow_state;
            let layer_idx = self.layer_idx;
            final_readback_callbacks.schedule(
                move || unsafe {
                    // Populate the rolling state from the D2H'd device state. The
                    // seed captured here is already post-commit+squeeze (advanced
                    // on-device), so no host `commit_field_els`/`draw_random_field_els`
                    // is needed — the 3 challenges live in `layer_challenges_host`.
                    let state = shared_state_for_callback.get_mut();
                    state.seed = Seed(
                        <&[u32; STATE_SIZE]>::try_from(final_seed_accessor.get())
                            .expect("seed readback has STATE_SIZE words")
                            .to_owned(),
                    );
                    state.folding_challenges.clear();
                    if last_step > 0 {
                        state.folding_challenges.extend_from_slice(
                            &final_folding_challenges_accessor.get()[..last_step],
                        );
                    }

                    let [r_before_last, r_last, next_batching_challenge]: [E; 3] =
                        layer_challenges_accessor
                            .get()
                            .try_into()
                            .expect("layer challenges D2H has length 3");
                    let mut new_claim_point = state.folding_challenges.clone();
                    new_claim_point.push(r_before_last);
                    new_claim_point.push(r_last);

                    // Rebuild `new_claims` from the D2H'd device-computed per-
                    // address buffer + the same address list. The host loop that
                    // used to evaluate `eq_ext(values, r_before_last, r_last)` per
                    // address is gone — the kernel already did it.
                    let new_claims_slice = new_claims_accessor.get();
                    let new_claims: BTreeMap<GKRAddress, E> = callback_addresses
                        .iter()
                        .enumerate()
                        .map(|(i, addr)| (*addr, new_claims_slice[i]))
                        .collect();

                    {
                        let workflow_state = workflow_state_for_callback.get_mut();
                        workflow_state.current_claims = new_claims.clone();
                        workflow_state.current_claim_point = new_claim_point.clone();
                        workflow_state.current_batching_challenge = next_batching_challenge;
                        workflow_state.seed = state.seed;
                        workflow_state
                            .claims_for_layers
                            .insert(layer_idx, new_claims.clone());
                        workflow_state
                            .points_for_claims_at_layer
                            .insert(layer_idx, new_claim_point.clone());
                    }

                    state.result = Some(GpuGKRDimensionReducingLayerExecution {
                        new_claims,
                        new_claim_point,
                        next_batching_challenge,
                        updated_seed: state.seed,
                    });
                },
                stream,
            )?;
        }
        if let Some(layer_range) = layer_range.take() {
            layer_range.end(stream)?;
            tracing_ranges.push(layer_range);
        }

        drop(fallback_d_layer_transcript_inputs);
        drop(device_claim);
        drop(device_eq_prefactor);
        drop(fallback_device_coeffs);
        drop(device_claim_point_in);
        drop(device_claims_in);
        Ok(GpuGKRDimensionReducingScheduledLayerExecution {
            tracing_ranges,
            start_callbacks: Callbacks::new(),
            reduction_states,
            final_readback: ScheduledDimensionReducingFinalReadback {
                callbacks: final_readback_callbacks,
                _phantom: std::marker::PhantomData,
            },
            shared_state,
            device_seed: Some(device_seed),
            device_claim_point_for_next_layer: Some(device_claim_point_out),
            device_claims_for_next_layer: Some(device_new_claims),
            claim_layout_for_next_layer: Some(next_claim_layout),
            _phantom: std::marker::PhantomData,
        })
    }
}

impl<B, E: FieldExtension<BF> + Field> GpuGKRDimensionReducingScheduledLayerExecution<B, E> {
    pub(crate) fn into_host_keepalive(self) -> GpuGKRDimensionReducingHostKeepalive<B, E> {
        let Self {
            tracing_ranges,
            start_callbacks,
            reduction_states,
            final_readback,
            shared_state,
            device_seed: _,
            device_claim_point_for_next_layer: _,
            device_claims_for_next_layer: _,
            claim_layout_for_next_layer: _,
            _phantom: _,
        } = self;
        GpuGKRDimensionReducingHostKeepalive {
            tracing_ranges,
            start_callbacks,
            reduction_states,
            final_readback,
            shared_state,
            _phantom: std::marker::PhantomData,
        }
    }

    pub(crate) fn into_execution(self) -> GpuGKRDimensionReducingLayerExecution<E> {
        let Self {
            mut shared_state, ..
        } = self;
        shared_state
            .result
            .take()
            .expect("dimension-reducing layer execution is not ready yet")
    }
}

impl<E: 'static> GpuGKRMainLayerSumcheckLayerPlan<E>
where
    E: Field
        + FieldExtension<BF>
        + Reduce
        + GpuDimensionReducingKernelSet
        + GpuBackwardSumcheckRoundUpdateKernel
        + super::backward_flat_compact::GpuFlatRound0CompactKernelSet
        + super::backward_flat_compact::GpuFlatRound0ConstantCompactKernelSet
        + super::backward_flat_compact::GpuFlatRound1UnifiedCompactKernelSet
        + super::backward_flat_compact::GpuFlatRound2UnifiedCompactKernelSet
        + super::backward_flat_compact::GpuFlatRound3UnifiedCompactKernelSet,
    Mul: BinaryOp<E, E, E>,
    [(); E::DEGREE]: Sized,
{
    fn compute_combined_claim(&self, output_claims: &BTreeMap<GKRAddress, E>) -> E {
        let mut result = E::ZERO;
        for kernel in self.kernel_plans.iter() {
            if kernel.kind == GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic {
                continue;
            }
            for (output, challenge) in kernel
                .inputs
                .outputs_in_base
                .iter()
                .chain(kernel.inputs.outputs_in_extension.iter())
                .zip(kernel.batch_challenges.iter())
            {
                let mut term = output_claims
                    .get(output)
                    .copied()
                    .unwrap_or_else(|| panic!("missing output claim for {output:?}"));
                term.mul_assign(challenge);
                result.add_assign(&term);
            }
        }

        result
    }

    fn schedule_batch_challenge_buffer_on_device(
        &self,
        device_claim_point_in: &DeviceClaimPointAndBatching<E>,
        context: &ProverContext,
    ) -> CudaResult<(ScheduledChallengeStorage<E>, ScheduledChallengeBuffer<E>)> {
        let len = packed_main_layer_batch_challenge_len(&self.kernel_plans);
        assert!(
            len > 0,
            "main-layer batched execution requires at least one packed batch challenge"
        );
        // Static-blueprint main-layer plans never pre-populate `batch_challenges`;
        // every packed slot is `base^(offset + k)` for the single device-resident
        // batching challenge `base`. Assert so callers can't silently lose
        // pre-drawn values.
        assert!(
            self.kernel_plans
                .iter()
                .all(|k| k.batch_challenges.is_empty()),
            "schedule_batch_challenge_buffer_on_device requires static-blueprint specs",
        );
        let mut storage =
            ScheduledChallengeStorage::new(context.alloc(len, AllocationPlacement::Top)?);
        // Fill the packed buffer with powers of the device-resident batching
        // challenge — the last slot of the orchestrator-owned
        // `device_claim_point_in`.
        let batching_slice = unsafe { device_claim_point_in.slice(self.folding_steps, 1) };
        // SAFETY: `storage.device` was just allocated with capacity `len` and
        // no other view into it exists yet; the `&mut DeviceSlice` is dropped
        // before `storage.device_accessor()` is called below. The subsequent
        // `get_powers_by_ref` launch is stream-ordered on `exec_stream`, so the
        // buffer is populated before any downstream consumer reads it.
        unsafe {
            let dst_slice = storage.device.slice_mut(0, len);
            let dst_e4 = dst_slice.transmute_mut::<E4>();
            let batching_e4 = batching_slice.transmute::<E4>();
            crate::ops::powers::get_powers_by_ref::<E4>(
                &batching_e4[0],
                0,
                false,
                dst_e4,
                context.get_exec_stream(),
            )?;
        }
        let buffer = ScheduledChallengeBuffer {
            device: storage.device_accessor(),
            offset: 0,
            len,
        };
        Ok((storage, buffer))
    }

    fn build_round0_eq_values(
        &mut self,
        eq_pair_values_host: &HostAllocation<[E]>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let challenge_count = self.folding_steps.saturating_sub(1);
        let acc_size = 1usize << challenge_count;
        memory_copy_async(
            &mut self.round_scratch.eq_pair_values[..eq_pair_values_host.len()],
            eq_pair_values_host,
            context.get_exec_stream(),
        )?;
        launch_build_round0_eq_values_from_pairs(
            self.round_scratch.eq_pair_values.as_ptr(),
            challenge_count,
            self.round_scratch.eq_group_tables.as_mut_ptr(),
            self.round_scratch.eq_values.as_mut_ptr(),
            acc_size,
            context,
        )
    }

    fn fold_eq_values_for_next_round(
        &mut self,
        acc_size: usize,
        context: &ProverContext,
    ) -> CudaResult<()> {
        debug_assert!(acc_size.is_power_of_two());
        debug_assert!(acc_size >= 2);
        launch_fold_eq_values_in_place(
            self.round_scratch.eq_values.as_mut_ptr(),
            acc_size / 2,
            context,
        )
    }

    fn launch_round0_kernels(
        &mut self,
        acc_size: usize,
        context: &ProverContext,
    ) -> CudaResult<()> {
        assert!(
            self.flat_recipe_desc.is_some(),
            "flat round 0 recipe descriptor must be scheduled"
        );
        let plan_compact = self
            .flat_round0_template_compact
            .as_ref()
            .expect("compact flat round 0 plan must be built");
        if self.flat_use_constant {
            super::backward_flat_compact::launch_main_round0_flat_constant_compact(
                &plan_compact.static_desc,
                self.round_scratch.eq_values.as_ptr(),
                self.round_scratch.accumulator.as_mut_ptr(),
                acc_size as u32,
                context,
            )
        } else {
            super::backward_flat_compact::launch_main_round0_flat_compact(
                &plan_compact.static_desc,
                self.flat_coeff_device_buf.as_ref().unwrap().as_ptr(),
                self.round_scratch.eq_values.as_ptr(),
                self.round_scratch.accumulator.as_mut_ptr(),
                acc_size as u32,
                context,
            )
        }
    }

    fn launch_round1_kernels_from_symbol(
        &mut self,
        acc_size: usize,
        context: &ProverContext,
    ) -> CudaResult<()> {
        assert!(
            self.flat_cont_recipe_desc.is_some(),
            "flat continuation recipe descriptor must be scheduled"
        );
        let sizes = self
            .flat_round1_size_check()
            .resolve(acc_size)
            .expect("flat round 1 size check must be consistent");
        let compact_desc = self
            .flat_round1_unified_desc_compact
            .as_ref()
            .expect("flat round 1 compact desc must be built");
        super::backward_flat_compact::launch_main_round1_flat_constant_compact_unified_compact(
            compact_desc,
            null(),
            sizes.fold_stride,
            sizes.next_layer_size,
            self.round_scratch.eq_values.as_ptr(),
            self.round_scratch.accumulator.as_mut_ptr(),
            acc_size as u32,
            context,
        )
    }

    fn launch_round2_kernels_from_symbol(
        &mut self,
        acc_size: usize,
        context: &ProverContext,
    ) -> CudaResult<()> {
        assert!(
            self.flat_cont_recipe_desc.is_some(),
            "flat continuation recipe descriptor must be scheduled"
        );
        let sizes = self
            .flat_round2_size_check()
            .resolve(acc_size)
            .expect("flat round 2 size check must be consistent");
        let compact_desc = self
            .flat_round2_unified_desc_compact
            .as_ref()
            .expect("flat round 2 compact desc must be built");
        super::backward_flat_compact::launch_main_round2_flat_constant_compact_unified_compact(
            compact_desc,
            super::backward_flat_compact::get_main_layer_claim_point_device_ptr() as *const E,
            sizes.fold_stride,
            sizes.next_layer_size,
            self.round_scratch.eq_values.as_ptr(),
            self.round_scratch.accumulator.as_mut_ptr(),
            acc_size as u32,
            context,
        )
    }

    fn launch_round3_kernels_from_symbol(
        &mut self,
        step: usize,
        acc_size: usize,
        explicit_form: bool,
        context: &ProverContext,
    ) -> CudaResult<()> {
        assert!(
            self.flat_cont_recipe_desc.is_some(),
            "flat continuation recipe descriptor must be scheduled"
        );
        let sizes = self
            .flat_round3_size_check(step)
            .resolve(acc_size)
            .unwrap_or_else(|| {
                panic!("flat round 3 size check must be consistent for step {step}")
            });
        let (_, compact_desc) = self
            .flat_continuation_unified_descs_compact
            .iter()
            .find(|(s, _)| *s == step)
            .unwrap_or_else(|| {
                panic!("flat continuation compact desc must be built for step {step}")
            });
        super::backward_flat_compact::launch_main_round3_flat_constant_unified_compact(
            compact_desc,
            null(),
            sizes.fold_stride,
            sizes.next_layer_size,
            (step - 1) as u32,
            self.round_scratch.eq_values.as_ptr(),
            self.round_scratch.accumulator.as_mut_ptr(),
            acc_size as u32,
            explicit_form,
            context,
        )
    }

    /// Main-layer variant of the device-only sumcheck accumulator reduction.
    fn run_round_coefficients_reduction_device(
        &mut self,
        step: usize,
        acc_size: usize,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let challenge_offset = step + 1;
        let challenge_count = self.folding_steps - step - 1;
        assert_eq!(acc_size, 1usize << challenge_count);
        let _ = (challenge_offset, challenge_count);
        let stream = context.get_exec_stream();
        let reduction_temp = unsafe {
            DeviceSlice::from_raw_parts_mut(
                self.round_scratch.reduction_temp_storage.as_mut_ptr(),
                self.round_scratch.reduction_temp_storage.len(),
            )
        };
        {
            let low_half = DeviceVectorChunk::new(&self.round_scratch.accumulator, 0, acc_size);
            reduce(
                ReduceOperation::Sum,
                reduction_temp,
                &low_half,
                &mut self.round_scratch.reduction_output[0],
                stream,
            )?;
        }
        {
            let high_half =
                DeviceVectorChunk::new(&self.round_scratch.accumulator, acc_size, acc_size);
            reduce(
                ReduceOperation::Sum,
                reduction_temp,
                &high_half,
                &mut self.round_scratch.reduction_output[1],
                stream,
            )?;
        }
        Ok(())
    }

    /// Schedule eval_recipes on the GPU. Each challenge is read from its own
    /// existing device-resident pointer:
    ///   - batch_base = `device_claim_point_in[folding_steps]` (last slot,
    ///     advanced on-device by the previous layer's end-of-round squeeze);
    ///   - lookup_mul = `device_lookup_and_constraint_ptr[0]`;
    ///   - lookup_add = `device_lookup_and_constraint_ptr[1]`.
    /// Replaces the prior per-layer 3-element scratch buffer + 2 D2Ds; the
    /// kernel now reads each scalar through its own pointer.
    fn schedule_flat_eval_recipes(
        &mut self,
        device_claim_point_in: &DeviceClaimPointAndBatching<E>,
        device_lookup_and_constraint_ptr: *const E,
        external_challenges_ptr: *const E,
        context: &ProverContext,
    ) -> CudaResult<Callbacks<'static>> {
        let desc = match self.flat_recipe_desc {
            Some(ref desc) => desc,
            None => return Ok(Callbacks::new()),
        };
        let stream = context.get_exec_stream();

        // SAFETY: `device_claim_point_in` outlives this scheduling call (held
        // by the orchestrator across the full layer); `device_lookup_and_constraint_ptr`
        // points to 2 device-resident `E` scalars owned by the workflow scope
        // and stays allocated until all scheduled reads have completed on GPU.
        let batch_base_ptr =
            unsafe { device_claim_point_in.as_ptr().add(self.folding_steps) } as *const E4;
        let lookup_mul_ptr = device_lookup_and_constraint_ptr as *const E4;
        let lookup_add_ptr = unsafe { device_lookup_and_constraint_ptr.add(1) } as *const E4;
        let external_challenges_ptr = external_challenges_ptr as *const E4;

        // Determine output pointer for eval_recipes.
        let coeff_out_ptr: *mut E4 = if self.flat_use_constant {
            super::backward_flat::get_constant_coefficients_device_ptr()
        } else {
            self.flat_coeff_device_buf
                .as_mut()
                .unwrap()
                .as_mut_ptr()
                .cast()
        };

        crate::ops::eval_recipes::eval_recipes_e4(
            batch_base_ptr,
            lookup_mul_ptr,
            lookup_add_ptr,
            external_challenges_ptr,
            desc,
            self.flat_recipe_count,
            coeff_out_ptr,
            stream,
        )?;

        Ok(Callbacks::new())
    }

    /// Schedule eval_recipes for continuation coefficients (rounds 3+).
    /// Reuses the round 0 challenges buffer (same 4 challenge values).
    /// Must be called AFTER schedule_flat_eval_recipes so the challenges
    /// buffer is already populated on the stream.
    fn schedule_flat_continuation_eval_recipes(
        &mut self,
        batch_base_ptr: *const E4,
        lookup_mul_ptr: *const E4,
        lookup_add_ptr: *const E4,
        external_challenges_ptr: *const E4,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let desc = match self.flat_cont_recipe_desc {
            Some(ref desc) => desc,
            None => return Ok(()),
        };

        let coeff_out_ptr: *mut E4 =
            super::backward_flat::get_constant_continuation_coefficients_device_ptr();

        super::backward_flat::eval_continuation_recipes_e4(
            batch_base_ptr,
            lookup_mul_ptr,
            lookup_add_ptr,
            external_challenges_ptr,
            desc,
            self.flat_cont_recipe_count,
            coeff_out_ptr,
            context.get_exec_stream(),
        )?;

        Ok(())
    }

    fn final_evaluation_sources_for_last_step(
        &self,
        last_step: usize,
    ) -> BTreeMap<GKRAddress, *const E> {
        assert!(last_step >= 3, "main-layer final step must be in round 3+");
        let mut result = BTreeMap::new();
        for kernel in self.kernel_plans.iter() {
            let prepared = &kernel
                .round3_and_beyond_prepared
                .iter()
                .find(|prepared| prepared.step == last_step)
                .unwrap_or_else(|| panic!("missing round 3+ prepared storage for step {last_step}"))
                .prepared;
            for (address, source) in kernel
                .inputs
                .inputs_in_base
                .iter()
                .zip(prepared.base_field_inputs.iter())
            {
                if *address == GKRAddress::placeholder() || result.contains_key(address) {
                    continue;
                }
                result.insert(*address, source.this_layer_start.cast_const());
            }
            for (address, source) in kernel
                .inputs
                .inputs_in_extension
                .iter()
                .zip(prepared.extension_field_inputs.iter())
            {
                if *address == GKRAddress::placeholder() || result.contains_key(address) {
                    continue;
                }
                result.insert(*address, source.this_layer_start.cast_const());
            }
        }

        result
    }

    pub(crate) fn schedule_execute_main_layer_from_workflow_state(
        &mut self,
        workflow_state: ScheduledBackwardWorkflowStateHandle<E>,
        mut device_seed: DeviceAllocation<u32>,
        device_claim_point_in: DeviceClaimPointAndBatching<E>,
        device_claims_in: DeviceAllocation<E>,
        claim_layout: &ClaimBufferLayout,
        device_lookup_and_constraint_ptr: *const E,
        device_external_challenges_ptr: *const E,
        // Same pattern as the dim-reducing scheduler — when `Some` (production),
        // per-round kernels write coeffs directly into the slab's
        // `internal_round_coefficients` range and the per-address gather
        // writes directly into `final_step_evaluations` (B1 + B2). When
        // `None` (test paths), per-layer fallback device buffers are used.
        proof_slab: Option<&DeviceAllocation<E4>>,
        proof_layout: &ProofLayout,
        layer_slot: usize,
        mirror_layer_to_host: bool,
        // Read-only handle to the consolidated GKR storage. Used by the
        // main-layer extras eval path to resolve orphan output addresses
        // (`outputs[layer-1] − inputs[layer]`) to their backing
        // pointers without forcing additional allocations. Test paths
        // that don't exercise extras can pass `None` to skip extras work
        // entirely; production callers always pass `Some`.
        storage: Option<&GpuGKRStorage<BF, E>>,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRMainLayerScheduledLayerExecution<E>> {
        let stream = context.get_exec_stream();
        let mut tracing_ranges = Vec::new();
        let layer_name = format!("gkr.backward.main.layer.{}", self.layer_idx);
        let layer_range = Range::new(layer_name.clone())?;
        layer_range.start(stream)?;
        let last_step = self.folding_steps - 1;
        assert!(last_step >= 3);
        // Compute the per-layer combined_claim `(exp, claim_idx)` descriptor
        // consumed by `build_combined_claim`. Passed inline as kernel-arg
        // (`__grid_constant__`) — no device buffer, no per-layer H2D.
        // `EnforceConstraintsMaxQuadratic` kernels contribute no term (see
        // `compute_combined_claim`).
        let mut desc_pairs: Vec<u32> = Vec::new();
        for kernel in self.kernel_plans.iter() {
            if kernel.kind == GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic {
                continue;
            }
            for (j, output) in kernel
                .inputs
                .outputs_in_base
                .iter()
                .chain(kernel.inputs.outputs_in_extension.iter())
                .enumerate()
            {
                desc_pairs.push((kernel.batch_challenge_offset + j) as u32);
                desc_pairs.push(claim_layout.claim_idx(output));
            }
        }
        let mut shared_state = Box::new(ScheduledMainLayerExecutionState {
            seed: Seed::default(),
            claim: E::ZERO,
            eq_prefactor: E::ONE,
            folding_challenges: Vec::with_capacity(self.folding_steps),
            result: None,
        });
        let shared_state_handle =
            crate::primitives::context::UnsafeMutAccessor::new(shared_state.as_mut());

        // `device_seed` is owned by the orchestrator across all backward
        // layers; the fused per-round kernel + end-of-layer device transcript
        // mutate it in place. Returned via `Execution::device_seed` for the
        // next layer.
        let mut device_claim: DeviceAllocation<E> = context.alloc(1, AllocationPlacement::Top)?;
        let mut device_eq_prefactor: DeviceAllocation<E> =
            context.alloc(1, AllocationPlacement::Top)?;
        let coeffs_total_len = last_step * 4;
        // B1: per-round kernels write coeffs straight into the slab's
        // `internal_round_coefficients` range for this layer when `proof_slab`
        // is provided — no standalone allocation, no post-loop slab D2D. Test
        // paths fall back to a per-layer buffer.
        let mut fallback_device_coeffs: Option<DeviceAllocation<E>> = None;
        let coeffs_buffer_ptr: *mut E = if let Some(slab) = proof_slab {
            if coeffs_total_len > 0 {
                let (dst_ptr, dst_len) = unsafe {
                    proof_layout
                        .backward_internal_coeffs_device_mut(slab.as_ptr() as *mut u8, layer_slot)
                };
                debug_assert_eq!(
                    dst_len, coeffs_total_len,
                    "slab internal_round_coefficients range must match main-layer coeffs_total_len",
                );
                dst_ptr as *mut E
            } else {
                null_mut()
            }
        } else {
            let alloc: DeviceAllocation<E> =
                context.alloc(coeffs_total_len.max(1), AllocationPlacement::Top)?;
            let ptr = alloc.as_ptr() as *mut E;
            fallback_device_coeffs = Some(alloc);
            ptr
        };
        // Consume `[claim_point || batching_challenge]` directly from the
        // orchestrator-owned `device_claim_point_in`; build `eq_group_tables`
        // + `eq_values` from it (offset 1, count folding_steps - 1) — same
        // pattern as the dim-reducing twin.
        let claim_point_and_batching_len = self.folding_steps + 1;
        assert_eq!(
            device_claim_point_in.len(),
            claim_point_and_batching_len,
            "device claim_point input size must match this layer's folding_steps + 1",
        );
        let challenge_count = self.folding_steps.saturating_sub(1);
        let acc_size = 1usize << challenge_count;
        launch_build_eq_values_from_point(
            device_claim_point_in.as_ptr(),
            1,
            challenge_count,
            self.round_scratch.eq_group_tables.as_mut_ptr(),
            self.round_scratch.eq_values.as_mut_ptr(),
            acc_size,
            context,
        )?;

        assert_eq!(
            device_claims_in.len(),
            claim_layout.len(),
            "device claims buffer must match claim layout length",
        );

        {
            let claims_e4: &era_cudart::slice::DeviceSlice<E4> =
                unsafe { device_claims_in[..claim_layout.len()].transmute::<E4>() };
            let batching_slice = unsafe { device_claim_point_in.slice(self.folding_steps, 1) };
            let batching_e4: &era_cudart::slice::DeviceSlice<E4> =
                unsafe { batching_slice.transmute::<E4>() };
            let claim_out_e4: &mut era_cudart::slice::DeviceSlice<E4> =
                unsafe { device_claim[..].transmute_mut::<E4>() };
            let eq_out_e4: &mut era_cudart::slice::DeviceSlice<E4> =
                unsafe { device_eq_prefactor[..].transmute_mut::<E4>() };
            crate::ops::blake2s::build_combined_claim(
                claims_e4,
                batching_e4,
                &desc_pairs,
                claim_out_e4,
                eq_out_e4,
                stream,
            )?;
        }

        let (batch_challenge_storage, batch_challenge_buffer) =
            self.schedule_batch_challenge_buffer_on_device(&device_claim_point_in, context)?;
        let flat_coeff_callbacks = self.schedule_flat_eval_recipes(
            &device_claim_point_in,
            device_lookup_and_constraint_ptr,
            device_external_challenges_ptr,
            context,
        )?;
        // Continuation kernel reads the same 3 challenges via per-element
        // pointers as the round-0 kernel above.
        let cont_batch_base_ptr =
            unsafe { device_claim_point_in.as_ptr().add(self.folding_steps) } as *const E4;
        let cont_lookup_mul_ptr = device_lookup_and_constraint_ptr as *const E4;
        let cont_lookup_add_ptr = unsafe { device_lookup_and_constraint_ptr.add(1) } as *const E4;
        self.schedule_flat_continuation_eval_recipes(
            cont_batch_base_ptr,
            cont_lookup_mul_ptr,
            cont_lookup_add_ptr,
            device_external_challenges_ptr as *const E4,
            context,
        )?;
        // Hoisted: `device_claim_point_out` holds the next layer's
        // `[claim_point || batching_challenge]` buffer. Slots `[0..folding_steps - 1]`
        // are written in-place by the per-round update kernels; slots
        // `[folding_steps - 1..folding_steps + 1]` are written by the
        // post-loop transcript squeeze.
        //
        // Round-N kernels read directly from `device_claim_point_out`:
        // - round 1 reads `[0..1]` (= c_0)
        // - round 2 reads `[0..2]` (= c_0, c_1) — the prior round's contiguous prefix
        // - round ≥ 3 reads `[step - 1..step]` (= c_{step - 1}, the just-produced challenge)
        // No packing buffer or per-round D2D needed.
        let next_claim_point_and_batching_len = self.folding_steps + 1;
        assert!(
            next_claim_point_and_batching_len
                <= super::backward_flat_compact::MAX_MAIN_LAYER_CLAIM_POINT_LEN,
            "main-layer claim point length {} exceeds __constant__ symbol capacity {}",
            next_claim_point_and_batching_len,
            super::backward_flat_compact::MAX_MAIN_LAYER_CLAIM_POINT_LEN
        );
        let mut device_claim_point_out = unsafe {
            DeviceClaimPointAndBatching::from_raw_symbol_parts(
                super::backward_flat_compact::get_main_layer_claim_point_device_ptr() as *mut E,
                next_claim_point_and_batching_len,
            )
        };
        let mut reduction_states = Vec::with_capacity(last_step);

        for step in 0..last_step {
            let acc_size = 1usize << (self.folding_steps - step - 1);
            if step == 0 {
                self.launch_round0_kernels(acc_size, context)?;
            } else {
                match step {
                    1 => self.launch_round1_kernels_from_symbol(acc_size, context)?,
                    2 => self.launch_round2_kernels_from_symbol(acc_size, context)?,
                    step => {
                        self.launch_round3_kernels_from_symbol(step, acc_size, false, context)?
                    }
                }
            }

            // Device-only reduction into round_scratch.reduction_output.
            self.run_round_coefficients_reduction_device(step, acc_size, context)?;
            self.fold_eq_values_for_next_round(acc_size, context)?;

            // Fused per-round update: reads (seed, claim, eq_prefactor) +
            // (e, c) reduction output + prev_coord; writes updated state,
            // pushes the round's 4 coefficients into device_coeffs at
            // [step*4..step*4+4], and emits the next folding challenge
            // directly into `claim_point_out[step]`.
            let prev_coord_slice = unsafe { device_claim_point_in.slice(step, 1) };
            // SAFETY: see the dim-reducing twin — the coeffs buffer is either
            // a slab subslice (held alive by `_proof_slab` keepalive) or
            // `fallback_device_coeffs` (dropped after every kernel that writes
            // through this pointer is scheduled). The 4-element window is
            // in-bounds (`coeffs_total_len = last_step * 4`).
            let coeffs_round_slice =
                unsafe { DeviceSlice::from_raw_parts_mut(coeffs_buffer_ptr.add(step * 4), 4) };
            let challenge_slot = unsafe { device_claim_point_out.slice_mut(step, 1) };
            E::launch_backward_sumcheck_round_update(
                &self.round_scratch.reduction_output,
                prev_coord_slice,
                &mut device_seed,
                &mut device_claim,
                &mut device_eq_prefactor,
                coeffs_round_slice,
                challenge_slot,
                stream,
            )?;

            reduction_states.push(ScheduledDimensionReducingReductionState {
                callbacks: Callbacks::new(),
                _phantom: std::marker::PhantomData,
            });
        }
        self.launch_round3_kernels_from_symbol(last_step, 1, true, context)?;

        // B1: coeffs already landed in the slab via the per-round kernels
        // (or in `fallback_device_coeffs` for test paths). No post-loop slab
        // D2D needed.

        // Device-side inter-layer transcript (main-layer variant): pack the
        // flattened last-round evaluations (2 E per address, vs 4 in dim-
        // reducing) — written **directly into the slab** via B2. Absorbed
        // into device_seed via transcript_commit, then squeezed into 2 E4
        // challenges `[last_r, next_batching_challenge]`. The same packed
        // buffer feeds `backward_new_claims_linear`.
        let transcript_input_sources = self.final_evaluation_sources_for_last_step(last_step);
        let num_addresses = transcript_input_sources.len();
        let transcript_inputs_len = num_addresses * 2;
        let transcript_input_addresses: Vec<GKRAddress> =
            transcript_input_sources.keys().copied().collect();
        // B2: per-address gather writes straight into the slab's
        // `final_step_evaluations` range. Flat layout (2 E per address, in
        // BTreeMap key order from `final_evaluation_sources_for_last_step`)
        // matches what `build_proof_layout_inputs` stored in
        // `ProofLayout.backward[slot].final_step_eval_addresses`.
        let mut fallback_d_layer_transcript_inputs: Option<DeviceAllocation<E>> = None;
        let transcript_inputs_buffer_ptr: *mut E = if let Some(slab) = proof_slab {
            if transcript_inputs_len > 0 {
                let (dst_ptr, dst_len) = unsafe {
                    proof_layout
                        .backward_final_step_evals_device_mut(slab.as_ptr() as *mut u8, layer_slot)
                };
                debug_assert_eq!(
                    dst_len, transcript_inputs_len,
                    "slab final_step_evaluations range must match main-layer transcript_inputs_len",
                );
                dst_ptr as *mut E
            } else {
                null_mut()
            }
        } else {
            let alloc: DeviceAllocation<E> =
                context.alloc(transcript_inputs_len.max(1), AllocationPlacement::Top)?;
            let ptr = alloc.as_ptr() as *mut E;
            fallback_d_layer_transcript_inputs = Some(alloc);
            ptr
        };
        // B7: per-address gather kernel for the main-layer variant (2 E per
        // address). Pointer table rides inline in the kernel-arg struct; see
        // the dim-reducing twin for context.
        if num_addresses > 0 {
            let src_ptrs: Vec<u64> = transcript_input_sources
                .values()
                .map(|p| *p as u64)
                .collect();
            let dst = unsafe {
                DeviceSlice::from_raw_parts_mut(
                    transcript_inputs_buffer_ptr as *mut E4,
                    transcript_inputs_len,
                )
            };
            crate::ops::blake2s::gather_e_addresses(&src_ptrs, dst, 2, stream)?;
        }

        // SAFETY: E = E4 in every instantiation of this scheduler. The
        // slab/fallback memory is alive through the kernel launch, and
        // `transcript_commit` only reads.
        let transcript_inputs_e_slice = unsafe {
            DeviceSlice::from_raw_parts(
                transcript_inputs_buffer_ptr as *const E,
                transcript_inputs_len,
            )
        };
        let d_transcript_inputs_u32 = unsafe { transcript_inputs_e_slice.transmute::<u32>() };
        crate::ops::blake2s::transcript_commit(&mut device_seed, d_transcript_inputs_u32, stream)?;

        // Squeeze the 2 layer challenges directly into the tail of
        // `device_claim_point_out` — slots
        // `[last_step..last_step + 2] = [last_r, next_batching_challenge]`.
        // SAFETY: `last_step + 2 = folding_steps + 1 = next_claim_point_and_batching_len`,
        // so the range is in-bounds, and only this scheduling site writes it.
        {
            let layer_challenges_dst = unsafe { device_claim_point_out.slice_mut(last_step, 2) };
            // SAFETY: E = E4 in every instantiation; matches host `draw_random_field_els::<BF, E4>`.
            let layer_challenges_dst_e4 = unsafe { layer_challenges_dst.transmute_mut::<E4>() };
            crate::ops::blake2s::transcript_squeeze_e4(
                &mut device_seed,
                layer_challenges_dst_e4,
                stream,
            )?;
        }

        // Look up orphan addresses for this layer's slot. These are
        // `outputs[layer_idx - 1] − inputs[layer_idx]` (i.e., layer-(L-1)
        // kernel outputs that L's kernels do NOT consume) and must be
        // explicitly evaluated at the just-produced folding point so
        // L-1's `desc_pairs` build can resolve them in its IN claim
        // layout. See [backward.rs] `compute_main_layer_orphan_output_addresses_per_layer`
        // for the producer side. Empty for `layer_idx == 0` and for
        // any layer that consumes every immediate-child output.
        let orphan_addresses: Vec<GKRAddress> = proof_layout.backward[layer_slot]
            .extra_evaluations_addresses
            .clone();
        let orphan_count = orphan_addresses.len();
        if orphan_count > 0 {
            assert!(
                storage.is_some(),
                "main-layer extras eval requires a storage handle; production callers must pass Some(&storage)"
            );
        }
        let total_new_claims_len = num_addresses + orphan_count;

        // Device-side per-address `new_claims` evaluator (main-layer variant:
        // interpolate `v0, v1` at `last_r`). Replaces the host loop inside the
        // final readback callback. Allocation extends by `orphan_count` so
        // the on-device extras kernel can write extras into the tail.
        let mut device_new_claims: DeviceAllocation<E> =
            context.alloc(total_new_claims_len.max(1), AllocationPlacement::Top)?;
        if num_addresses > 0 {
            // SAFETY: E = E4 in every instantiation; transmutes match the
            // kernel's `e4` view of the packed evals and challenges. The
            // slab/fallback memory is alive through the kernel launch.
            let transcript_inputs_e_view = unsafe {
                DeviceSlice::from_raw_parts(
                    transcript_inputs_buffer_ptr as *const E,
                    transcript_inputs_len,
                )
            };
            let transcript_inputs_e4: &era_cudart::slice::DeviceSlice<E4> =
                unsafe { transcript_inputs_e_view.transmute::<E4>() };
            // SAFETY: layer-challenge tail lives at
            // `claim_point_out[last_step..last_step + 2]`; reading the first
            // element (`last_r`) for the kernel.
            let challenges_view = unsafe {
                DeviceSlice::from_raw_parts(device_claim_point_out.as_ptr().add(last_step), 1)
            };
            let challenges_e4: &era_cudart::slice::DeviceSlice<E4> =
                unsafe { challenges_view.transmute::<E4>() };
            let new_claims_e4: &mut era_cudart::slice::DeviceSlice<E4> =
                unsafe { device_new_claims[..num_addresses].transmute_mut::<E4>() };
            crate::ops::blake2s::backward_new_claims_linear(
                transcript_inputs_e4,
                challenges_e4,
                new_claims_e4,
                stream,
            )?;
        }

        // Schedule on-device evaluation of orphan output polys at the
        // full folding point `[r_0..r_{last_step-1}, last_r]`
        // (= `device_claim_point_out[0..self.folding_steps]`). Each
        // orphan's claim is written into:
        //   - `device_new_claims[num_addresses..num_addresses + orphan_count]`
        //     (tail) so the next layer's IN claim buffer carries it; and
        //   - `proof_layout.backward[layer_slot].extra_evaluations` slab
        //     range so the verifier can read the explicit at-point evals.
        // Returns a keepalive that holds eq_values, block_partials,
        // reduction_temp, and the orphan poly views (Arc-clones of the
        // consolidated backings) until exec_stream has finished every
        // kernel reading them. Drop happens at end of scheduler — same
        // pattern as `fallback_d_layer_transcript_inputs`.
        let extras_keepalive: Option<MainLayerExtrasKeepalive<BF, E>> = if orphan_count > 0 {
            // SAFETY: device_claim_point_out is `MAX_MAIN_LAYER_CLAIM_POINT_LEN`
            // long; `[0..folding_steps]` is in-bounds. The orphan eval
            // tail starts at `device_new_claims[num_addresses]`.
            let folding_point_ptr = device_claim_point_out.as_ptr();
            let trace_len = 1usize << self.folding_steps;
            let extras_dst_ptr = unsafe { device_new_claims.as_mut_ptr().add(num_addresses) };
            Some(schedule_main_layer_extras_eval::<E>(
                self.layer_idx,
                &orphan_addresses,
                storage.expect("extras eval requires storage handle"),
                folding_point_ptr,
                self.folding_steps,
                trace_len,
                extras_dst_ptr,
                proof_slab,
                proof_layout,
                layer_slot,
                context,
            )?)
        } else {
            None
        };

        // `device_claim_point_out` is already populated in place — slots
        // `[0..last_step]` by the per-round update kernels (folding challenges)
        // and slots `[last_step..last_step + 2]` by the transcript squeeze
        // (`last_r`, `next_batching_challenge`). No post-loop pack copies.

        // Combined claim layout = transcript inputs (in BTreeMap key order)
        // followed by orphans (in BTreeSet order). Orphans are disjoint from
        // transcript inputs by construction (orphan = layer-(L-1) output not
        // consumed by L), so the combined Vec has no duplicates.
        let mut combined_addresses = transcript_input_addresses.clone();
        combined_addresses.extend(orphan_addresses.iter().copied());
        let next_claim_layout = ClaimBufferLayout::from_addresses(combined_addresses);
        let callback_addresses = next_claim_layout.addresses.clone();
        let mut final_readback_callbacks = Callbacks::new();
        if mirror_layer_to_host {
            // Fork exec -> d2h: every D2H source below has been written on exec by this point
            // (d_layer_challenges via `transcript_squeeze_e4`, device_new_claims via
            // `backward_new_claims_linear`, device_seed/device_folding_challenges from earlier
            // work in this layer; coeffs and packed last-evals are now slab-direct via B1/B2
            // and not D2H'd here). A single fork event covers all of them; the matching join
            // is recorded after the last D2H below.
            let layer_src_ready = era_cudart::event::CudaEvent::create_with_flags(
                era_cudart::event::CudaEventCreateFlags::DISABLE_TIMING,
            )?;
            layer_src_ready.record(stream)?;
            let d2h_stream = context.get_d2h_stream();
            d2h_stream.wait_event(
                &layer_src_ready,
                era_cudart::stream::CudaStreamWaitEventFlags::DEFAULT,
            )?;

            let mut layer_challenges_host: HostAllocation<[E]> =
                unsafe { context.alloc_host_uninit_slice(2) };
            let layer_challenges_accessor = layer_challenges_host.get_accessor();
            // SAFETY: `[last_step..last_step + 2]` were just written by the
            // transcript squeeze on `stream`; d2h_stream waits on
            // `layer_src_ready` before this read.
            let layer_challenges_src = unsafe {
                DeviceSlice::from_raw_parts(device_claim_point_out.as_ptr().add(last_step), 2)
            };
            memory_copy_async(&mut layer_challenges_host, layer_challenges_src, d2h_stream)?;

            // Single D2H of device-computed new_claims, including any
            // orphan extras the on-device extras kernel appended at
            // `[num_addresses..num_addresses + orphan_count]`.
            let mut new_claims_host: HostAllocation<[E]> =
                unsafe { context.alloc_host_uninit_slice(total_new_claims_len.max(1)) };
            let new_claims_accessor = new_claims_host.get_accessor();
            if total_new_claims_len > 0 {
                memory_copy_async(
                    &mut new_claims_host,
                    &device_new_claims[..total_new_claims_len],
                    d2h_stream,
                )?;
            }

            // D2H the on-device per-layer state that the final readback needs to
            // advance the workflow (seed + folding challenges for WHIR host setup;
            // coeffs and packed last-evaluations stay on device and flow through
            // the proof slab via B1/B2). All copies continue on `d2h_stream`
            // within the same fork/join window as the D2Hs above.
            let mut final_seed_host = unsafe { context.alloc_host_uninit_slice(STATE_SIZE) };
            let final_seed_accessor = final_seed_host.get_accessor();
            memory_copy_async(&mut final_seed_host, &device_seed, d2h_stream)?;
            let mut final_folding_challenges_host: HostAllocation<[E]> =
                unsafe { context.alloc_host_uninit_slice(last_step) };
            let final_folding_challenges_accessor = final_folding_challenges_host.get_accessor();
            // SAFETY: `[0..last_step]` were written in-place by the per-round
            // update kernels.
            let folding_src =
                unsafe { DeviceSlice::from_raw_parts(device_claim_point_out.as_ptr(), last_step) };
            memory_copy_async(&mut final_folding_challenges_host, folding_src, d2h_stream)?;

            // Join d2h -> exec: the per-layer D2Hs above are fully scheduled. Exec waits on this
            // event before the final readback callback (which reads the host slabs) is scheduled,
            // and before any downstream drop of the source allocations at the end of this function.
            let layer_d2h_done = era_cudart::event::CudaEvent::create_with_flags(
                era_cudart::event::CudaEventCreateFlags::DISABLE_TIMING,
            )?;
            layer_d2h_done.record(d2h_stream)?;
            stream.wait_event(
                &layer_d2h_done,
                era_cudart::stream::CudaStreamWaitEventFlags::DEFAULT,
            )?;

            let shared_state_for_callback = shared_state_handle;
            let workflow_state_for_callback = workflow_state;
            let layer_idx = self.layer_idx;
            final_readback_callbacks.schedule(
                move || unsafe {
                    // Populate the rolling state from the D2H'd device state. The
                    // seed captured here is already post-commit+squeeze; the 2
                    // challenges live in `layer_challenges_host`.
                    let state = shared_state_for_callback.get_mut();
                    state.seed = Seed(
                        <&[u32; STATE_SIZE]>::try_from(final_seed_accessor.get())
                            .expect("seed readback has STATE_SIZE words")
                            .to_owned(),
                    );
                    state.folding_challenges.clear();
                    state
                        .folding_challenges
                        .extend_from_slice(final_folding_challenges_accessor.get());

                    let [last_r, next_batching_challenge]: [E; 2] = layer_challenges_accessor
                        .get()
                        .try_into()
                        .expect("layer challenges D2H has length 2");
                    let mut new_claim_point = state.folding_challenges.clone();
                    new_claim_point.push(last_r);
                    // Rebuild `new_claims` from the D2H'd device-computed buffer
                    // (host `interpolate_linear` loop is now a kernel).
                    let new_claims_slice = new_claims_accessor.get();
                    let new_claims: BTreeMap<GKRAddress, E> = callback_addresses
                        .iter()
                        .enumerate()
                        .map(|(i, addr)| (*addr, new_claims_slice[i]))
                        .collect();

                    {
                        let workflow_state = workflow_state_for_callback.get_mut();
                        workflow_state.current_claims = new_claims.clone();
                        workflow_state.current_claim_point = new_claim_point.clone();
                        workflow_state.current_batching_challenge = next_batching_challenge;
                        workflow_state.seed = state.seed;
                        workflow_state
                            .claims_for_layers
                            .insert(layer_idx, new_claims.clone());
                        workflow_state
                            .points_for_claims_at_layer
                            .insert(layer_idx, new_claim_point.clone());
                    }

                    state.result = Some(GpuGKRMainLayerExecution {
                        new_claims,
                        new_claim_point,
                        next_batching_challenge,
                        updated_seed: state.seed,
                    });
                },
                stream,
            )?;
        }
        layer_range.end(stream)?;
        tracing_ranges.push(layer_range);

        drop(fallback_d_layer_transcript_inputs);
        drop(device_claim);
        drop(device_eq_prefactor);
        drop(fallback_device_coeffs);
        drop(device_claim_point_in);
        drop(device_claims_in);
        // Stream-ordered drop: every scheduled extras-eval kernel +
        // memcpy has been issued by this point, so the temporary
        // device buffers (eq_values, block_partials, reduction_temp)
        // and the orphan view Arc-clones can release here. The pool
        // defers the underlying free until exec_stream has progressed
        // past the writes.
        drop(extras_keepalive);
        Ok(GpuGKRMainLayerScheduledLayerExecution {
            tracing_ranges,
            start_callbacks: Callbacks::new(),
            batch_challenge_storage,
            batch_challenge_buffer,
            reduction_states,
            final_readback: ScheduledDimensionReducingFinalReadback {
                callbacks: final_readback_callbacks,
                _phantom: std::marker::PhantomData,
            },
            flat_coeff_callbacks,
            recipe_upload_callbacks: std::mem::replace(
                &mut self.recipe_upload_callbacks,
                Callbacks::new(),
            ),
            shared_state,
            device_seed: Some(device_seed),
            device_claim_point_for_next_layer: Some(device_claim_point_out),
            device_claims_for_next_layer: Some(device_new_claims),
            claim_layout_for_next_layer: Some(next_claim_layout),
        })
    }
}

impl<E: FieldExtension<BF> + Field> GpuGKRMainLayerScheduledLayerExecution<E> {
    pub(crate) fn into_host_keepalive(self) -> GpuGKRMainLayerHostKeepalive<E> {
        let Self {
            tracing_ranges,
            start_callbacks,
            batch_challenge_storage,
            batch_challenge_buffer: _,
            reduction_states,
            final_readback,
            flat_coeff_callbacks,
            recipe_upload_callbacks,
            shared_state,
            device_seed: _,
            device_claim_point_for_next_layer: _,
            device_claims_for_next_layer: _,
            claim_layout_for_next_layer: _,
        } = self;
        GpuGKRMainLayerHostKeepalive {
            tracing_ranges,
            start_callbacks,
            batch_challenge_storage: challenge_storage_into_host_keepalive(batch_challenge_storage),
            reduction_states,
            final_readback,
            flat_coeff_callbacks,
            recipe_upload_callbacks,
            shared_state,
        }
    }

    pub(crate) fn into_execution(self) -> GpuGKRMainLayerExecution<E> {
        let Self {
            mut shared_state, ..
        } = self;
        shared_state
            .result
            .take()
            .expect("main-layer execution is not ready yet")
    }
}

impl<B, E> GpuGKRBackwardScheduledExecution<B, E>
where
    E: FieldExtension<BF> + Field,
{
    pub(crate) fn into_host_keepalive(self) -> GpuGKRBackwardHostKeepalive<B, E> {
        let Self {
            tracing_ranges,
            dimension_reducing_layers,
            main_layers,
            shared_state,
            initial_callbacks,
            external_challenges_device_keepalive,
            final_device_seed,
            final_device_claim_point_and_batching,
            final_claim_layout,
            final_seed_host,
            final_claim_point_and_batching_host,
        } = self;
        GpuGKRBackwardHostKeepalive {
            tracing_ranges,
            dimension_reducing_layers: dimension_reducing_layers
                .into_iter()
                .map(GpuGKRDimensionReducingScheduledLayerExecution::into_host_keepalive)
                .collect(),
            main_layers: main_layers
                .into_iter()
                .map(GpuGKRMainLayerScheduledLayerExecution::into_host_keepalive)
                .collect(),
            shared_state,
            initial_callbacks,
            external_challenges_device_keepalive,
            final_device_seed,
            final_device_claim_point_and_batching,
            final_claim_layout,
            final_seed_host,
            final_claim_point_and_batching_host,
        }
    }

    pub(crate) fn shared_state_handle(&mut self) -> ScheduledBackwardWorkflowStateHandle<E> {
        crate::primitives::context::UnsafeMutAccessor::new(self.shared_state.as_mut())
    }

    /// Device-resident layer-0 claim point. The final-device buffer packs
    /// `[claim_point || batching_challenge]`, so we slice off the trailing batching
    /// element. Stream-ordered against `exec_stream`; consumers must respect that
    /// `self` (the keepalive) remains live until any kernel reading the slice has
    /// been scheduled.
    pub(crate) fn final_device_claim_point(&self) -> &era_cudart::slice::DeviceSlice<E> {
        let buffer = self
            .final_device_claim_point_and_batching
            .as_ref()
            .expect("backward claim_point handoff buffer must be allocated before consumption");
        let len = buffer.len();
        assert!(
            len >= 1,
            "final claim point handoff must include batching challenge"
        );
        unsafe { buffer.slice(0, len - 1) }
    }

    pub(crate) fn final_device_seed_and_claim_point_mut(
        &mut self,
    ) -> (
        &mut DeviceAllocation<u32>,
        &era_cudart::slice::DeviceSlice<E>,
    ) {
        let device_seed = self
            .final_device_seed
            .as_mut()
            .expect("backward seed handoff buffer must be allocated before consumption");
        let buffer = self
            .final_device_claim_point_and_batching
            .as_ref()
            .expect("backward claim_point handoff buffer must be allocated before consumption");
        let len = buffer.len();
        assert!(
            len >= 1,
            "final claim point handoff must include batching challenge"
        );
        (device_seed, unsafe { buffer.slice(0, len - 1) })
    }

    /// Schedule-time-known set of layer-1 incoming claim addresses (i.e. the
    /// addresses whose claim values land in the final main-layer's device
    /// claim buffer). Exposed so that base-layer claim scheduling can build
    /// its extras plan from a schedule-time slice without ever waiting for a
    /// runtime D2H + host BTreeMap materialization.
    pub(crate) fn final_claim_addresses(&self) -> &[GKRAddress] {
        &self
            .final_claim_layout
            .as_ref()
            .expect("backward layer-0 claim layout must be set before consumption")
            .addresses
    }

    pub(crate) fn schedule_post_backward_handoff(
        &mut self,
        context: &ProverContext,
    ) -> CudaResult<Callbacks<'static>>
    where
        E: 'static,
    {
        let stream = context.get_exec_stream();
        let device_seed = self
            .final_device_seed
            .as_ref()
            .expect("post-backward handoff requires final device seed");
        let device_claim_point_and_batching = self
            .final_device_claim_point_and_batching
            .as_ref()
            .expect("post-backward handoff requires final device claim point");
        assert!(
            device_claim_point_and_batching.len() >= 1,
            "final claim point handoff must include batching challenge"
        );

        let mut final_seed_host = unsafe { context.alloc_host_uninit_slice::<u32>(STATE_SIZE) };
        let final_seed_accessor = final_seed_host.get_accessor();
        let mut final_claim_point_and_batching_host =
            unsafe { context.alloc_host_uninit_slice::<E>(device_claim_point_and_batching.len()) };
        let final_claim_point_and_batching_accessor =
            final_claim_point_and_batching_host.get_accessor();

        memory_copy_async(&mut final_seed_host, device_seed, stream)?;
        memory_copy_async(
            &mut final_claim_point_and_batching_host,
            device_claim_point_and_batching.as_slice(),
            stream,
        )?;

        let shared_state = self.shared_state_handle();
        let mut callbacks = Callbacks::new();
        callbacks.schedule(
            move || unsafe {
                let seed = Seed(
                    <&[u32; STATE_SIZE]>::try_from(final_seed_accessor.get())
                        .expect("seed handoff has STATE_SIZE words")
                        .to_owned(),
                );
                let claim_point_and_batching = final_claim_point_and_batching_accessor.get();
                let (claim_point, batching_challenge) =
                    claim_point_and_batching.split_at(claim_point_and_batching.len() - 1);
                let current_claim_point = claim_point.to_vec();
                let current_batching_challenge = batching_challenge[0];

                let state = shared_state.get_mut();
                state.current_batching_challenge = current_batching_challenge;
                state.seed = seed;
                state
                    .points_for_claims_at_layer
                    .insert(0, current_claim_point);
            },
            stream,
        )?;

        // Park the pinned host buffers on `self` so they outlive the scheduled
        // callback. The callback's accessors are raw pointers into these
        // chunks; `backward_scheduled` stays alive (via the proof keepalive)
        // until the proof finishes, which is well after the callback fires.
        // Storing on `self` instead of dropping at function return prevents
        // pool reuse from a sibling prove writing into the same chunks before
        // this prove's callback executes.
        self.final_seed_host = Some(final_seed_host);
        self.final_claim_point_and_batching_host = Some(final_claim_point_and_batching_host);
        Ok(callbacks)
    }

    pub(crate) fn wait(self, context: &ProverContext) -> CudaResult<GpuGKRBackwardExecution<E>> {
        context.get_exec_stream().synchronize()?;
        let Self {
            mut shared_state, ..
        } = self;
        let state = shared_state.as_mut();
        Ok(GpuGKRBackwardExecution {
            claims_for_layers: std::mem::take(&mut state.claims_for_layers),
            points_for_claims_at_layer: std::mem::take(&mut state.points_for_claims_at_layer),
            next_batching_challenge: state.current_batching_challenge,
            updated_seed: state.seed,
        })
    }
}

impl<E> GpuGKRDimensionReducingBackwardState<BF, E>
where
    E: Field
        + FieldExtension<BF>
        + Reduce
        + GpuDimensionReducingKernelSet
        + GpuBackwardSumcheckRoundUpdateKernel
        + super::backward_flat_compact::GpuFlatRound0CompactKernelSet
        + super::backward_flat_compact::GpuFlatRound0ConstantCompactKernelSet
        + super::backward_flat_compact::GpuFlatRound1UnifiedCompactKernelSet
        + super::backward_flat_compact::GpuFlatRound2UnifiedCompactKernelSet
        + super::backward_flat_compact::GpuFlatRound3UnifiedCompactKernelSet
        + 'static,
    Mul: BinaryOp<E, E, E>,
    [(); E::DEGREE]: Sized,
{
    pub(crate) fn schedule_execute_backward_workflow_from_shared_state(
        mut self,
        compiled_circuit: GKRCircuitArtifact<BF>,
        external_challenges: GKRExternalChallenges<BF, E>,
        device_external_challenges_ptr: *const E,
        mut shared_state: Box<ScheduledBackwardWorkflowState<E>>,
        initial_d_seed: DeviceAllocation<u32>,
        initial_d_claim_point_and_batching: DeviceAllocation<E>,
        initial_d_claims: DeviceAllocation<E>,
        initial_claim_layout: ClaimBufferLayout,
        device_lookup_and_constraint: DeviceAllocation<E>,
        mirror_layers_to_host: bool,
        // Phase 2b: the proof slab and its layout thread through from prove().
        // Per-layer schedulers D2D-copy slab-bound fields
        // (`internal_round_coefficients`, `final_step_evaluations`) into slab
        // offsets via `ProofLayout` accessors. `extra_evaluations_from_caching_relations`
        // is represented as sparse references into the slab-resident WHIR base
        // eval ranges and merged at Phase 4 parse time.
        // `None` skips all slab routing (test paths).
        proof_slab: Option<&DeviceAllocation<E4>>,
        proof_layout: &ProofLayout,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRBackwardScheduledExecution<BF, E>> {
        let shared_state_handle =
            crate::primitives::context::UnsafeMutAccessor::new(shared_state.as_mut());
        let stream = context.get_exec_stream();
        let mut workflow_initial_callbacks = Callbacks::new();
        // `[lookup_mul, lookup_add]` is threaded as a device-resident buffer into every
        // main-layer `schedule_flat_eval_recipes` call so those layers can D2D
        // the per-proof constants into their eval_recipes challenges buffer
        // instead of reading `workflow_state` inside a per-layer host callback.
        let device_lookup_and_constraint_ptr = device_lookup_and_constraint.as_ptr();
        let mut tracing_ranges = Vec::new();
        let workflow_range = Range::new("gkr.backward.schedule")?;
        workflow_range.start(stream)?;
        let mut dimension_reducing_layers = Vec::new();
        let dimension_reducing_layers_range = Range::new("gkr.backward.dimension_reducing_layers")?;
        dimension_reducing_layers_range.start(stream)?;
        // `shared_device_seed` lives across every backward layer. It enters the
        // pass from `initial_d_seed` (post-forward device squeeze in proof.rs),
        // is mutated in place by each layer's fused per-round kernel and
        // end-of-layer device transcript work, and flows to the next layer via
        // the layer's returned `Execution::device_seed`. No H2D, no per-layer
        // allocation — the whole backward seed pipeline is GPU-resident.
        let mut shared_device_seed = initial_d_seed;
        // `shared_device_claim_point` holds the next layer's input claim_point
        // followed by its batching_challenge, in the same `[claim_point ||
        // batching]` layout each layer consumes directly. The first layer
        // receives the post-forward device squeeze
        // buffer (`evaluation_point || batching_challenge`) unchanged; every
        // subsequent layer receives a symbol-backed view sized to its own
        // `[claim_point || batching]` layout and populated on device by the
        // previous layer's round-update and transcript kernels.
        let mut shared_device_claim_point =
            DeviceClaimPointAndBatching::from_allocation(initial_d_claim_point_and_batching);
        let mut shared_device_claims = initial_d_claims;
        let mut shared_claim_layout = initial_claim_layout;
        // `backward_layer_slot` tracks the scheduler-order index into
        // `_proof_layout.backward[...]`. The outer BTreeMap in
        // `dimension_reducing_inputs` pops highest-first (see
        // `GpuGKRDimensionReducingBackwardState::new`), which matches
        // `build_proof_layout_inputs`'s dim-reducing slot numbering: slot 0 is
        // the highest layer_idx (`initial_layer_for_sumcheck`) and slots
        // ascend as we descend through the dim-reducing chain. Main layers
        // continue from slot `num_dim_reducing_layers` and count downward
        // through `compiled_circuit.layers[num_main - 1..=0]`.
        let mut backward_layer_slot: usize = 0;
        while let Some(mut prepared_layer) = self.prepare_next_layer_static(context)? {
            let layer_idx = prepared_layer.layer_idx;
            let mut execution = prepared_layer
                .schedule_execute_dimension_reducing_layer_from_workflow_state(
                    shared_state_handle,
                    shared_device_seed,
                    shared_device_claim_point,
                    shared_device_claims,
                    &shared_claim_layout,
                    proof_slab,
                    proof_layout,
                    backward_layer_slot,
                    mirror_layers_to_host,
                    context,
                )?;
            shared_device_seed = execution
                .device_seed
                .take()
                .expect("dim-reducing scheduler must return the device seed");
            shared_device_claim_point = execution
                .device_claim_point_for_next_layer
                .take()
                .expect("dim-reducing scheduler must return the device claim_point");
            shared_device_claims = execution
                .device_claims_for_next_layer
                .take()
                .expect("dim-reducing scheduler must return the device claims");
            shared_claim_layout = execution
                .claim_layout_for_next_layer
                .take()
                .expect("dim-reducing scheduler must return the claim layout");
            dimension_reducing_layers.push(execution);
            backward_layer_slot += 1;
            // Stream-ordered storage can be dropped once the layer's uploads and kernels have
            // been fully enqueued on exec_stream.
            self.purge_up_to_layer(layer_idx);
        }
        dimension_reducing_layers_range.end(stream)?;
        tracing_ranges.push(dimension_reducing_layers_range);

        let mut main_backward_state = self.into_main_layer_backward_state_static(
            compiled_circuit,
            external_challenges,
            false,
        );
        let mut main_layers = Vec::new();
        let main_layers_range = Range::new("gkr.backward.main_layers")?;
        main_layers_range.start(stream)?;
        while let Some(mut prepared_layer) =
            main_backward_state.prepare_next_layer_static(context)?
        {
            let layer_idx = prepared_layer.layer_idx;
            // SAFETY: `prepare_next_layer_static` released its `&mut`
            // borrow on `main_backward_state` when it returned. The
            // re-borrow here is read-only and lives only across the
            // scheduler call (which doesn't touch storage mutably).
            let storage_for_extras = main_backward_state.storage();
            let mut execution = prepared_layer.schedule_execute_main_layer_from_workflow_state(
                shared_state_handle,
                shared_device_seed,
                shared_device_claim_point,
                shared_device_claims,
                &shared_claim_layout,
                device_lookup_and_constraint_ptr,
                device_external_challenges_ptr,
                proof_slab,
                proof_layout,
                backward_layer_slot,
                mirror_layers_to_host,
                Some(storage_for_extras),
                context,
            )?;
            shared_device_seed = execution
                .device_seed
                .take()
                .expect("main-layer scheduler must return the device seed");
            shared_device_claim_point = execution
                .device_claim_point_for_next_layer
                .take()
                .expect("main-layer scheduler must return the device claim_point");
            shared_device_claims = execution
                .device_claims_for_next_layer
                .take()
                .expect("main-layer scheduler must return the device claims");
            shared_claim_layout = execution
                .claim_layout_for_next_layer
                .take()
                .expect("main-layer scheduler must return the claim layout");
            main_layers.push(execution);
            backward_layer_slot += 1;
            main_backward_state.purge_up_to_layer(layer_idx);
        }
        main_layers_range.end(stream)?;
        tracing_ranges.push(main_layers_range);

        let GpuGKRMainLayerBackwardState { storage: _, .. } = main_backward_state;
        // Remaining main-layer storage drops here after all exec-stream work has been scheduled.
        // The shared device buffers now hold the final backward handoff. The hot proof path
        // materializes them once, outside `gkr.backward.*`, before base-layer/WHIR host setup.
        // Stream-ordered drop: the device buffer stays alive on GPU until
        // all scheduled reads complete (last layer's per-element pointer
        // reads in eval_recipes_e4 / eval_continuation_recipes_e4).
        drop(device_lookup_and_constraint);
        // Backward-end join: per-layer joins already cover each layer's D2Hs individually, but
        // this defensive join gives a single "both streams drained through backward" point
        // before WHIR-setup callbacks on exec_stream read `workflow_state.points_for_claims_at_layer[0]`
        // and `workflow_state.seed`, and before `backward_scheduled.wait()`'s
        // `exec_stream.synchronize()` blocks the host thread.
        let backward_d2h_done = era_cudart::event::CudaEvent::create_with_flags(
            era_cudart::event::CudaEventCreateFlags::DISABLE_TIMING,
        )?;
        backward_d2h_done.record(context.get_d2h_stream())?;
        stream.wait_event(
            &backward_d2h_done,
            era_cudart::stream::CudaStreamWaitEventFlags::DEFAULT,
        )?;
        workflow_range.end(stream)?;
        tracing_ranges.push(workflow_range);

        // Stream-ordered drop: the final main-layer kernel wrote into
        // `shared_device_claims` on `exec_stream`; nothing else reads it now
        // that base-layer claim scheduling sources layer-1 incoming addresses
        // from `final_claim_layout` and layer-0 values from the slab. The
        // pool defers the underlying free until exec_stream has progressed
        // past the writing kernel, so dropping here is safe.
        drop(shared_device_claims);

        Ok(GpuGKRBackwardScheduledExecution {
            tracing_ranges,
            dimension_reducing_layers,
            main_layers,
            shared_state,
            initial_callbacks: workflow_initial_callbacks,
            external_challenges_device_keepalive: None,
            final_device_seed: Some(shared_device_seed),
            final_device_claim_point_and_batching: Some(shared_device_claim_point),
            final_claim_layout: Some(shared_claim_layout),
            final_seed_host: None,
            final_claim_point_and_batching_host: None,
        })
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn schedule_execute_backward_workflow(
        self,
        compiled_circuit: GKRCircuitArtifact<BF>,
        external_challenges: GKRExternalChallenges<BF, E>,
        initial_output_layer_idx: usize,
        top_layer_claims: BTreeMap<GKRAddress, E>,
        evaluation_point: Vec<E>,
        seed: Seed,
        batching_challenge: E,
        lookup_multiplicative_challenge: E,
        lookup_additive_challenge: E,
        proof_slab: Option<&DeviceAllocation<E4>>,
        proof_layout: &ProofLayout,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRBackwardScheduledExecution<BF, E>> {
        let mut shared_state = Box::new(ScheduledBackwardWorkflowState {
            claims_for_layers: BTreeMap::from([(
                initial_output_layer_idx,
                top_layer_claims.clone(),
            )]),
            points_for_claims_at_layer: BTreeMap::from([(
                initial_output_layer_idx,
                evaluation_point.clone(),
            )]),
            current_claims: top_layer_claims,
            current_claim_point: evaluation_point,
            current_batching_challenge: batching_challenge,
            lookup_multiplicative_challenge,
            lookup_additive_challenge,
            seed,
        });
        // Host seed / claim_point / batching_challenge are only available via this
        // test-path entry point; stage them into device buffers so the orchestrator's
        // device-resident seed + claim_point pipelines kick off with the right values.
        // All host staging must happen inside stream-scheduled callbacks per the GPU
        // scheduling contract (`HostAllocation` contents are only touched as stream ops);
        // the produced `Callbacks` ride along in the returned execution's keepalive.
        let mut initial_callbacks = Callbacks::new();
        let initial_d_seed =
            h2d_seed_from_host(context, &mut initial_callbacks, &shared_state.seed)?;
        let initial_d_claim_point_and_batching = h2d_claim_point_and_batching_from_host(
            context,
            &mut initial_callbacks,
            &shared_state.current_claim_point,
            shared_state.current_batching_challenge,
        )?;
        let (initial_d_claims, initial_claim_layout) = h2d_claims_from_host(
            context,
            &mut initial_callbacks,
            &shared_state.current_claims,
        )?;
        let device_lookup_and_constraint = h2d_lookup_and_constraint_from_shared_state::<E>(
            context,
            &mut initial_callbacks,
            crate::primitives::context::UnsafeMutAccessor::new(shared_state.as_mut()),
        )?;
        let mut external_challenges_flat = external_challenges
            .permutation_argument_linearization_challenges
            .to_vec();
        external_challenges_flat.push(external_challenges.permutation_argument_additive_part);
        let mut external_challenges_host =
            unsafe { context.alloc_host_uninit_slice(external_challenges_flat.len()) };
        unsafe {
            external_challenges_host
                .get_mut_accessor()
                .get_mut()
                .copy_from_slice(&external_challenges_flat);
        }
        let mut device_external_challenges = context
            .alloc(external_challenges_host.len(), AllocationPlacement::BestFit)
            .unwrap();
        memory_copy_async(
            &mut device_external_challenges,
            &external_challenges_host,
            context.get_exec_stream(),
        )?;
        drop(external_challenges_host);

        let mut execution = self.schedule_execute_backward_workflow_from_shared_state(
            compiled_circuit,
            external_challenges,
            device_external_challenges.as_ptr(),
            shared_state,
            initial_d_seed,
            initial_d_claim_point_and_batching,
            initial_d_claims,
            initial_claim_layout,
            device_lookup_and_constraint,
            true,
            proof_slab,
            proof_layout,
            context,
        )?;
        execution.initial_callbacks.extend(initial_callbacks);
        execution.external_challenges_device_keepalive = Some(device_external_challenges);
        Ok(execution)
    }
}

#[cfg(test)]
mod tests {
    use super::{
        build_dimension_reducing_kernel_blueprints,
        build_inits_and_teardowns_initial_pair_inputs_and_metadata,
        build_lookup_from_vector_input_with_setup_inputs_and_metadata,
        build_lookup_with_dens_and_setup_expressions_inputs_and_metadata,
        build_main_layer_kernel_blueprints, build_main_layer_kernel_blueprints_static,
        build_max_quadratic_relation_inputs_and_metadata,
        build_single_max_quadratic_constraint_inputs_and_metadata,
        canonical_inits_and_teardowns_top_bits, eq_group_tables_len,
        launch_build_eq_values_from_point, launch_build_round0_eq_values_from_pairs,
        launch_fold_eq_values_in_place, launch_lookup_continuation, launch_lookup_round0,
        launch_pairwise_continuation, launch_pairwise_round0,
        make_deferred_backward_workflow_state, populate_backward_workflow_state,
        DeviceClaimPointAndBatching, GKRCircuitArtifact, GpuGKRDimensionReducingBackwardState,
        GpuGKRMainLayerConstraintLinearTerm, GpuGKRMainLayerConstraintQuadraticTerm,
        GpuGKRMainLayerKernelKind,
    };
    use crate::allocator::tracker::AllocationPlacement;
    use crate::ops::cub::device_reduce::{get_reduce_temp_storage_bytes, ReduceOperation};
    use crate::primitives::callbacks::Callbacks;
    use crate::primitives::context::{DeviceAllocation, ProverContext};
    use crate::primitives::field::{BF, E4};
    use crate::prover::gkr::{
        GpuBaseFieldPolySource, GpuExtensionFieldPolyContinuingLaunchDescriptor,
        GpuExtensionFieldPolyInitialSource, GpuSumcheckRound0DeviceLaunchDescriptors,
        GpuSumcheckRound0HostLaunchDescriptors, GpuSumcheckRound0ScheduledLaunchDescriptors,
    };
    use crate::prover::test_utils::make_test_context;
    use cs::definitions::{GKRAddress, VirtualSetupPoly};
    use cs::gkr_compiler::{
        GKRLayerDescription, GateArtifacts, InitsOrTeardownsTimestampAndValue, NoFieldGKRRelation,
        NoFieldMaxQuadraticConstraintsGKRRelation, NoFieldMaxQuadraticGKRRelation, OutputType,
    };
    use era_cudart::memory::memory_copy_async;
    use era_cudart::slice::{CudaSlice, CudaSliceMut, DeviceSlice};
    use field::{Field, FieldExtension, PrimeField};
    use prover::gkr::high_bits_offset_for_inits_and_teardowns;
    use prover::gkr::prover::dimension_reduction::forward::DimensionReducingInputOutput;
    use prover::gkr::prover::GKRExternalChallenges;
    use prover::gkr::sumcheck::evaluation_kernels::BatchedGKRKernel;
    use prover::transcript::Seed;
    use serial_test::serial;
    use std::collections::BTreeMap;

    use crate::ops::blake2s::STATE_SIZE;

    fn sample_ext(seed: u32) -> E4 {
        E4::from_array_of_base([
            BF::new(seed),
            BF::new(seed + 1),
            BF::new(seed + 2),
            BF::new(seed + 3),
        ])
    }

    fn sample_external_challenges(seed: u32) -> GKRExternalChallenges<BF, E4> {
        GKRExternalChallenges {
            permutation_argument_linearization_challenges: std::array::from_fn(|idx| {
                sample_ext(seed + 10 + idx as u32)
            }),
            permutation_argument_additive_part: sample_ext(seed),
            _marker: std::marker::PhantomData,
        }
    }

    fn successive_powers<E: Field>(base: E, count: usize) -> Vec<E> {
        let mut current = E::ONE;
        (0..count)
            .map(|_| {
                let result = current;
                current.mul_assign(&base);
                result
            })
            .collect()
    }

    fn interleaved_pairs_to_strided<T: Copy>(values: &[T]) -> Vec<T> {
        assert_eq!(values.len() % 2, 0);
        let pair_count = values.len() / 2;
        let mut result = Vec::with_capacity(values.len());
        for idx in 0..pair_count {
            result.push(values[idx * 2]);
        }
        for idx in 0..pair_count {
            result.push(values[idx * 2 + 1]);
        }
        result
    }

    fn alloc_and_copy<T: Copy>(context: &ProverContext, values: &[T]) -> DeviceAllocation<T> {
        let mut allocation = context
            .alloc(values.len(), AllocationPlacement::BestFit)
            .unwrap();
        memory_copy_async(&mut allocation, values, context.get_exec_stream()).unwrap();
        allocation
    }

    fn copy_device_values<T: Copy>(context: &ProverContext, values: &DeviceSlice<T>) -> Vec<T> {
        let mut allocation = unsafe { context.alloc_host_uninit_slice(values.len()) };
        memory_copy_async(&mut allocation, values, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        unsafe { allocation.get_accessor().get().to_vec() }
    }

    fn assert_base_poly_source_slice_eq(
        actual: &[GpuBaseFieldPolySource<BF>],
        expected: &[GpuBaseFieldPolySource<BF>],
        message: &str,
    ) {
        assert_eq!(actual.len(), expected.len(), "{message}: len mismatch");
        for (idx, (actual, expected)) in actual.iter().zip(expected.iter()).enumerate() {
            assert_eq!(
                actual.start, expected.start,
                "{message}: start mismatch at index {idx}"
            );
            assert_eq!(
                actual.next_layer_size, expected.next_layer_size,
                "{message}: next_layer_size mismatch at index {idx}"
            );
            assert_eq!(
                actual.source_kind, expected.source_kind,
                "{message}: source_kind mismatch at index {idx}"
            );
        }
    }

    fn assert_extension_poly_source_slice_eq(
        actual: &[GpuExtensionFieldPolyInitialSource<E4>],
        expected: &[GpuExtensionFieldPolyInitialSource<E4>],
        message: &str,
    ) {
        assert_eq!(actual.len(), expected.len(), "{message}: len mismatch");
        for (idx, (actual, expected)) in actual.iter().zip(expected.iter()).enumerate() {
            assert_eq!(
                actual.start, expected.start,
                "{message}: start mismatch at index {idx}"
            );
            assert_eq!(
                actual.next_layer_size, expected.next_layer_size,
                "{message}: next_layer_size mismatch at index {idx}"
            );
        }
    }

    fn assert_extension_poly_continuing_slice_eq(
        actual: &[GpuExtensionFieldPolyContinuingLaunchDescriptor<E4>],
        expected: &[GpuExtensionFieldPolyContinuingLaunchDescriptor<E4>],
        message: &str,
    ) {
        assert_eq!(actual.len(), expected.len(), "{message}: len mismatch");
        for (idx, (actual, expected)) in actual.iter().zip(expected.iter()).enumerate() {
            assert_eq!(
                actual.previous_layer_start, expected.previous_layer_start,
                "{message}: previous_layer_start mismatch at index {idx}"
            );
            assert_eq!(
                actual.this_layer_start, expected.this_layer_start,
                "{message}: this_layer_start mismatch at index {idx}"
            );
            assert_eq!(
                actual.this_layer_size, expected.this_layer_size,
                "{message}: this_layer_size mismatch at index {idx}"
            );
            assert_eq!(
                actual.next_layer_size, expected.next_layer_size,
                "{message}: next_layer_size mismatch at index {idx}"
            );
            assert_eq!(
                actual.first_access, expected.first_access,
                "{message}: first_access mismatch at index {idx}"
            );
        }
    }

    #[test]
    fn lookup_with_dens_and_setup_expression_metadata_uses_tail_relative_indices() {
        let input = (
            GKRAddress::BaseLayerWitness(10),
            cs::definitions::gkr::NoFieldVectorLookupRelation {
                columns: vec![
                    cs::definitions::gkr::NoFieldLinearRelation::from_single_input(
                        GKRAddress::BaseLayerWitness(20),
                    ),
                    cs::definitions::gkr::NoFieldLinearRelation::from_single_input(
                        GKRAddress::BaseLayerWitness(21),
                    ),
                ]
                .into_boxed_slice(),
                lookup_set_index: 0,
            },
        );
        let setup = (
            GKRAddress::BaseLayerWitness(11),
            vec![
                GKRAddress::BaseLayerWitness(30),
                GKRAddress::BaseLayerWitness(31),
            ]
            .into_boxed_slice(),
        );

        let (inputs, metadata) =
            build_lookup_with_dens_and_setup_expressions_inputs_and_metadata::<E4>(
                &input,
                &setup,
                [GKRAddress::InnerLayer {
                    layer: 1,
                    offset: 0,
                }; 2],
                E4::from_base(BF::from_u32_unchecked(5)),
                E4::ZERO,
            );

        assert_eq!(
            inputs.inputs_in_base,
            vec![
                GKRAddress::BaseLayerWitness(10),
                GKRAddress::BaseLayerWitness(11),
                GKRAddress::BaseLayerWitness(20),
                GKRAddress::BaseLayerWitness(21),
                GKRAddress::BaseLayerWitness(30),
                GKRAddress::BaseLayerWitness(31),
            ],
        );
        assert_eq!(
            metadata
                .quadratic_terms
                .iter()
                .map(|term| term.lhs)
                .collect::<Vec<_>>(),
            vec![0, 1],
        );
        assert_eq!(
            metadata
                .linear_terms
                .iter()
                .map(|term| term.input)
                .collect::<Vec<_>>(),
            vec![2, 3],
        );
    }

    #[test]
    fn lookup_from_vector_input_with_setup_metadata_uses_tail_relative_indices() {
        let input = cs::definitions::gkr::NoFieldVectorLookupRelation {
            columns: vec![
                cs::definitions::gkr::NoFieldLinearRelation::from_single_input(
                    GKRAddress::BaseLayerWitness(20),
                ),
                cs::definitions::gkr::NoFieldLinearRelation::from_single_input(
                    GKRAddress::BaseLayerWitness(21),
                ),
            ]
            .into_boxed_slice(),
            lookup_set_index: 0,
        };
        let setup = (
            GKRAddress::BaseLayerWitness(11),
            vec![
                GKRAddress::BaseLayerWitness(30),
                GKRAddress::BaseLayerWitness(31),
            ]
            .into_boxed_slice(),
        );

        let (inputs, metadata) = build_lookup_from_vector_input_with_setup_inputs_and_metadata::<E4>(
            &input,
            &setup,
            [GKRAddress::InnerLayer {
                layer: 1,
                offset: 0,
            }; 2],
            E4::from_base(BF::from_u32_unchecked(5)),
            E4::ZERO,
        );

        assert_eq!(
            inputs.inputs_in_base,
            vec![
                GKRAddress::BaseLayerWitness(11),
                GKRAddress::BaseLayerWitness(20),
                GKRAddress::BaseLayerWitness(21),
                GKRAddress::BaseLayerWitness(30),
                GKRAddress::BaseLayerWitness(31),
            ],
        );
        assert_eq!(
            metadata
                .quadratic_terms
                .iter()
                .map(|term| term.lhs)
                .collect::<Vec<_>>(),
            vec![0, 1],
        );
        assert_eq!(
            metadata
                .linear_terms
                .iter()
                .map(|term| term.input)
                .collect::<Vec<_>>(),
            vec![2, 3],
        );
    }

    fn eq_weights_for_binary_tail(challenge: E4) -> [E4; 2] {
        let mut one_minus = E4::ONE;
        one_minus.sub_assign(&challenge);
        [one_minus, challenge]
    }

    fn eq_values_for_suffix(challenges: &[E4]) -> Vec<E4> {
        let acc_size = 1usize << challenges.len();
        let mut result = Vec::with_capacity(acc_size);
        for gid in 0..acc_size {
            let mut acc = E4::ONE;
            for (idx, challenge) in challenges.iter().copied().enumerate() {
                let bit = ((gid >> (challenges.len() - 1 - idx)) & 1) != 0;
                let term = if bit {
                    challenge
                } else {
                    let mut one_minus = E4::ONE;
                    one_minus.sub_assign(&challenge);
                    one_minus
                };
                acc.mul_assign(&term);
            }
            result.push(acc);
        }
        result
    }

    fn fold_eq_values_cpu(values: &mut Vec<E4>) {
        assert!(values.len().is_power_of_two());
        let half_len = values.len() / 2;
        for idx in 0..half_len {
            let upper = values[idx + half_len];
            values[idx].add_assign(&upper);
        }
        values.truncate(half_len);
    }

    fn fold_continuing_value(values: &[E4], challenge: E4, idx: usize) -> E4 {
        let half = values.len() / 2;
        let mut delta = values[half + idx];
        delta.sub_assign(&values[idx]);
        let mut result = challenge;
        result.mul_assign(&delta);
        result.add_assign(&values[idx]);
        result
    }

    #[test]
    #[serial]
    fn shared_state_dimension_reduction_purges_storage_after_each_layer() {
        let fixture = crate::prover::tests::prepare_basic_unrolled_async_backward_fixture(8);
        let context = &fixture.context;
        let expected_dimension_reducing_layers =
            fixture.initial_output_layer_idx - fixture.compiled_circuit.layers.len();
        assert!(
            expected_dimension_reducing_layers >= 2,
            "fixture must include multiple dimension-reducing layers"
        );

        let mut backward_state = fixture.gpu_backward_state;
        let mut shared_state = make_deferred_backward_workflow_state();
        let shared_state_handle =
            crate::primitives::context::UnsafeMutAccessor::new(shared_state.as_mut());
        let fixture_evaluation_point_for_device = fixture.evaluation_point.clone();
        let fixture_top_layer_claims_for_device = fixture.top_layer_claims.clone();
        populate_backward_workflow_state(
            shared_state_handle,
            fixture.initial_output_layer_idx,
            fixture.top_layer_claims,
            fixture.evaluation_point,
            fixture.seed,
            fixture.batching_challenge,
            fixture.lookup_multiplicative_part,
            fixture.lookup_additive_part,
        );

        let mut initial_callbacks = crate::primitives::callbacks::Callbacks::new();
        let mut shared_device_seed = crate::prover::gkr::backward::h2d_seed_from_host(
            context,
            &mut initial_callbacks,
            &fixture.seed,
        )
        .unwrap();

        let shared_device_claim_point_initial =
            crate::prover::gkr::backward::h2d_claim_point_and_batching_from_host::<E4>(
                context,
                &mut initial_callbacks,
                &fixture_evaluation_point_for_device,
                fixture.batching_challenge,
            )
            .unwrap();
        let mut shared_device_claim_point =
            DeviceClaimPointAndBatching::from_allocation(shared_device_claim_point_initial);
        let (mut shared_device_claims, mut shared_claim_layout) =
            crate::prover::gkr::backward::h2d_claims_from_host::<E4>(
                context,
                &mut initial_callbacks,
                &fixture_top_layer_claims_for_device,
            )
            .unwrap();

        let proof_layout = crate::prover::proof_layout::ProofLayout::new(
            &crate::prover::proof_layout::placeholder_inputs_for_prove(),
        );
        let mut dimension_reducing_layers = Vec::new();
        let mut purged_layers = 0usize;
        let mut layer_slot = 0usize;
        while let Some(mut prepared_layer) =
            backward_state.prepare_next_layer_static(context).unwrap()
        {
            let layer_idx = prepared_layer.layer_idx;
            let mut scheduled = prepared_layer
                .schedule_execute_dimension_reducing_layer_from_workflow_state(
                    shared_state_handle,
                    shared_device_seed,
                    shared_device_claim_point,
                    shared_device_claims,
                    &shared_claim_layout,
                    None,
                    &proof_layout,
                    layer_slot,
                    true,
                    context,
                )
                .unwrap();
            layer_slot += 1;
            shared_device_seed = scheduled.device_seed.take().unwrap();
            shared_device_claim_point = scheduled.device_claim_point_for_next_layer.take().unwrap();
            shared_device_claims = scheduled.device_claims_for_next_layer.take().unwrap();
            shared_claim_layout = scheduled.claim_layout_for_next_layer.take().unwrap();
            dimension_reducing_layers.push(scheduled);
            backward_state.purge_up_to_layer(layer_idx);
            purged_layers += 1;

            assert_eq!(
                backward_state.storage().layers.len(),
                layer_idx + 1,
                "storage should be truncated through scheduled dimension-reducing layer {layer_idx}"
            );
            assert!(
                backward_state.storage().layers.get(layer_idx + 1).is_none(),
                "layers above {layer_idx} should be purged after scheduling"
            );
        }

        assert_eq!(purged_layers, expected_dimension_reducing_layers);

        let fixture_external_challenges_for_device = fixture.external_challenges.clone();
        let mut main_state = backward_state.into_main_layer_backward_state(
            fixture.compiled_circuit,
            fixture.external_challenges,
            fixture.lookup_multiplicative_part,
            E4::ZERO,
            false,
        );
        let mut first_main_layer = main_state
            .prepare_next_layer_static(context)
            .unwrap()
            .expect("expected first main-layer plan after dimension reduction");
        let first_main_layer_idx = first_main_layer.layer_idx;
        let device_lookup_and_constraint =
            crate::prover::gkr::backward::h2d_lookup_and_constraint_from_shared_state::<E4>(
                context,
                &mut initial_callbacks,
                shared_state_handle,
            )
            .unwrap();
        let mut external_challenges_flat = fixture_external_challenges_for_device
            .permutation_argument_linearization_challenges
            .to_vec();
        external_challenges_flat
            .push(fixture_external_challenges_for_device.permutation_argument_additive_part);
        let mut external_challenges_host =
            unsafe { context.alloc_host_uninit_slice(external_challenges_flat.len()) };
        unsafe {
            external_challenges_host
                .get_mut_accessor()
                .get_mut()
                .copy_from_slice(&external_challenges_flat);
        }
        let mut device_external_challenges = context
            .alloc(external_challenges_host.len(), AllocationPlacement::BestFit)
            .unwrap();
        memory_copy_async(
            &mut device_external_challenges,
            &external_challenges_host,
            context.get_exec_stream(),
        )
        .unwrap();
        drop(external_challenges_host);
        let main_proof_layout = crate::prover::proof_layout::ProofLayout::new(
            &crate::prover::proof_layout::placeholder_inputs_for_prove(),
        );
        let _first_main_layer_execution = first_main_layer
            .schedule_execute_main_layer_from_workflow_state(
                shared_state_handle,
                shared_device_seed,
                shared_device_claim_point,
                shared_device_claims,
                &shared_claim_layout,
                device_lookup_and_constraint.as_ptr(),
                device_external_challenges.as_ptr(),
                None,
                &main_proof_layout,
                0,
                true,
                // Test path: placeholder proof layout has empty
                // `extra_evaluations_addresses` for every slot, so no
                // extras work runs and storage isn't dereferenced.
                None,
                context,
            )
            .unwrap();

        context.get_exec_stream().synchronize().unwrap();
        drop(initial_callbacks);

        let execution = super::take_backward_execution_from_shared_state(shared_state_handle);
        assert!(
            execution
                .claims_for_layers
                .contains_key(&first_main_layer_idx),
            "shared-state workflow should still schedule the first main layer after purging"
        );
    }

    #[test]
    fn main_layer_kind_batch_challenge_count_matches_all_supported_kinds() {
        let one_challenge_kinds = [
            GpuGKRMainLayerKernelKind::BaseCopy,
            GpuGKRMainLayerKernelKind::ExtCopy,
            GpuGKRMainLayerKernelKind::Product,
            GpuGKRMainLayerKernelKind::MaskIdentity,
            GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic,
            GpuGKRMainLayerKernelKind::MaxQuadraticBaseOutput,
            GpuGKRMainLayerKernelKind::LinearBaseOutput,
            GpuGKRMainLayerKernelKind::InitsAndTeardownsInitialPair,
            GpuGKRMainLayerKernelKind::InitialGrandProductWithoutCaches,
            GpuGKRMainLayerKernelKind::MaterializeGrandProductTermExpression,
        ];
        let two_challenge_kinds = [
            GpuGKRMainLayerKernelKind::LookupPair,
            GpuGKRMainLayerKernelKind::LookupBasePair,
            GpuGKRMainLayerKernelKind::LookupBaseMinusMultiplicityByBase,
            GpuGKRMainLayerKernelKind::LookupExtMinusMultiplicityByExt,
            GpuGKRMainLayerKernelKind::LookupUnbalanced,
            GpuGKRMainLayerKernelKind::LookupWithCachedDensAndSetup,
            GpuGKRMainLayerKernelKind::LookupPairFromBaseInputs,
            GpuGKRMainLayerKernelKind::LookupWithDensAndSetupExpressions,
            GpuGKRMainLayerKernelKind::LookupPairFromVectorInputs,
            GpuGKRMainLayerKernelKind::LookupFromVectorInputWithSetup,
            GpuGKRMainLayerKernelKind::LookupUnbalancedPairWithVectorInputs,
            GpuGKRMainLayerKernelKind::LookupExtPair,
            GpuGKRMainLayerKernelKind::LookupUnbalancedExtension,
        ];

        for kind in one_challenge_kinds {
            assert_eq!(super::main_layer_kind_batch_challenge_count(kind), 1);
        }
        for kind in two_challenge_kinds {
            assert_eq!(super::main_layer_kind_batch_challenge_count(kind), 2);
        }
    }

    #[test]
    fn dimension_reducing_kernel_blueprints_match_cpu_order_and_challenges() {
        let layer = BTreeMap::from([
            (
                OutputType::PermutationProduct,
                DimensionReducingInputOutput {
                    inputs: vec![
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 10,
                            offset: 0,
                        },
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 10,
                            offset: 1,
                        },
                    ],
                    output: vec![
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 11,
                            offset: 0,
                        },
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 11,
                            offset: 1,
                        },
                    ],
                },
            ),
            (
                OutputType::Lookup16Bits,
                DimensionReducingInputOutput {
                    inputs: vec![
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 10,
                            offset: 2,
                        },
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 10,
                            offset: 3,
                        },
                    ],
                    output: vec![
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 11,
                            offset: 2,
                        },
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 11,
                            offset: 3,
                        },
                    ],
                },
            ),
            (
                OutputType::LookupTimestamps,
                DimensionReducingInputOutput {
                    inputs: vec![
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 10,
                            offset: 4,
                        },
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 10,
                            offset: 5,
                        },
                    ],
                    output: vec![
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 11,
                            offset: 4,
                        },
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 11,
                            offset: 5,
                        },
                    ],
                },
            ),
            (
                OutputType::GenericLookup,
                DimensionReducingInputOutput {
                    inputs: vec![
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 10,
                            offset: 6,
                        },
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 10,
                            offset: 7,
                        },
                    ],
                    output: vec![
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 11,
                            offset: 6,
                        },
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 11,
                            offset: 7,
                        },
                    ],
                },
            ),
        ]);

        let batch_challenge_base = sample_ext(10);
        let blueprints = build_dimension_reducing_kernel_blueprints(&layer, batch_challenge_base);
        let powers = successive_powers(batch_challenge_base, 8);

        assert_eq!(blueprints.len(), 5);
        assert_eq!(
            blueprints[0].inputs.inputs_in_extension,
            vec![layer[&OutputType::PermutationProduct].inputs[0]]
        );
        assert_eq!(
            blueprints[0].inputs.outputs_in_extension,
            vec![layer[&OutputType::PermutationProduct].output[0]]
        );
        assert_eq!(blueprints[0].batch_challenges, vec![powers[0]]);

        assert_eq!(
            blueprints[1].inputs.inputs_in_extension,
            vec![layer[&OutputType::PermutationProduct].inputs[1]]
        );
        assert_eq!(
            blueprints[1].inputs.outputs_in_extension,
            vec![layer[&OutputType::PermutationProduct].output[1]]
        );
        assert_eq!(blueprints[1].batch_challenges, vec![powers[1]]);

        assert_eq!(
            blueprints[2].inputs.inputs_in_extension,
            layer[&OutputType::Lookup16Bits].inputs
        );
        assert_eq!(
            blueprints[2].inputs.outputs_in_extension,
            layer[&OutputType::Lookup16Bits].output
        );
        assert_eq!(blueprints[2].batch_challenges, vec![powers[2], powers[3]]);

        assert_eq!(
            blueprints[3].inputs.inputs_in_extension,
            layer[&OutputType::LookupTimestamps].inputs
        );
        assert_eq!(
            blueprints[3].inputs.outputs_in_extension,
            layer[&OutputType::LookupTimestamps].output
        );
        assert_eq!(blueprints[3].batch_challenges, vec![powers[4], powers[5]]);

        assert_eq!(
            blueprints[4].inputs.inputs_in_extension,
            layer[&OutputType::GenericLookup].inputs
        );
        assert_eq!(
            blueprints[4].inputs.outputs_in_extension,
            layer[&OutputType::GenericLookup].output
        );
        assert_eq!(blueprints[4].batch_challenges, vec![powers[6], powers[7]]);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn pairwise_round0_kernel_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_values = (0..8).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let output_values = (0..4).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
        let batch_challenge = sample_ext(200);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch_challenge]);
        let input = alloc_and_copy(&context, &input_values);
        let output = alloc_and_copy(&context, &output_values);
        let mut contributions = alloc_and_copy(&context, &[E4::ZERO; 4]);

        let mut round0 = GpuSumcheckRound0ScheduledLaunchDescriptors {
            callbacks: Callbacks::new(),
            host: GpuSumcheckRound0HostLaunchDescriptors {
                base_field_inputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(0)
                },
                extension_field_inputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(1)
                },
                base_field_outputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(0)
                },
                extension_field_outputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(1)
                },
            },
            device: GpuSumcheckRound0DeviceLaunchDescriptors {
                base_field_inputs: context
                    .alloc::<GpuBaseFieldPolySource<BF>>(0, AllocationPlacement::Top)
                    .unwrap(),
                extension_field_inputs: context
                    .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(1, AllocationPlacement::Top)
                    .unwrap(),
                base_field_outputs: context
                    .alloc::<GpuBaseFieldPolySource<BF>>(0, AllocationPlacement::Top)
                    .unwrap(),
                extension_field_outputs: context
                    .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(1, AllocationPlacement::Top)
                    .unwrap(),
            },
        };
        unsafe {
            round0
                .host
                .extension_field_inputs
                .get_mut_accessor()
                .get_mut()[0] = GpuExtensionFieldPolyInitialSource {
                start: input.as_ptr(),
                next_layer_size: 4,
            };
            round0
                .host
                .extension_field_outputs
                .get_mut_accessor()
                .get_mut()[0] = GpuExtensionFieldPolyInitialSource {
                start: output.as_ptr(),
                next_layer_size: 2,
            };
        }
        memory_copy_async(
            &mut round0.device.extension_field_inputs,
            &round0.host.extension_field_inputs,
            context.get_exec_stream(),
        )
        .unwrap();
        memory_copy_async(
            &mut round0.device.extension_field_outputs,
            &round0.host.extension_field_outputs,
            context.get_exec_stream(),
        )
        .unwrap();

        launch_pairwise_round0::<E4>(
            &round0,
            batch_challenges_dev.as_ptr(),
            contributions.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();
        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let mut expected = Vec::new();
        for output_index in 0..2 {
            let index = output_index * 2;
            let mut c0 = batch_challenge;
            c0.mul_assign(&output_values[output_index]);
            let mut a = input_values[4 + index];
            a.sub_assign(&input_values[index]);
            let mut b = input_values[4 + index + 1];
            b.sub_assign(&input_values[index + 1]);
            let mut c1 = a;
            c1.mul_assign(&b);
            c1.mul_assign(&batch_challenge);
            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn lookup_round0_kernel_matches_cpu() {
        let context = make_test_context(64, 8);
        let input0_values = (0..8).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let input1_values = (0..8).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
        let output_num_values = (0..4).map(|i| sample_ext(200 + i)).collect::<Vec<_>>();
        let output_den_values = (0..4).map(|i| sample_ext(300 + i)).collect::<Vec<_>>();
        let input0 = alloc_and_copy(&context, &input0_values);
        let input1 = alloc_and_copy(&context, &input1_values);
        let output_num = alloc_and_copy(&context, &output_num_values);
        let output_den = alloc_and_copy(&context, &output_den_values);
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();
        let batch0 = sample_ext(400);
        let batch1 = sample_ext(500);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch0, batch1]);

        let mut round0 = GpuSumcheckRound0ScheduledLaunchDescriptors {
            callbacks: Callbacks::new(),
            host: GpuSumcheckRound0HostLaunchDescriptors {
                base_field_inputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(0)
                },
                extension_field_inputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(2)
                },
                base_field_outputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(0)
                },
                extension_field_outputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(2)
                },
            },
            device: GpuSumcheckRound0DeviceLaunchDescriptors {
                base_field_inputs: context
                    .alloc::<GpuBaseFieldPolySource<BF>>(0, AllocationPlacement::Top)
                    .unwrap(),
                extension_field_inputs: context
                    .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(2, AllocationPlacement::Top)
                    .unwrap(),
                base_field_outputs: context
                    .alloc::<GpuBaseFieldPolySource<BF>>(0, AllocationPlacement::Top)
                    .unwrap(),
                extension_field_outputs: context
                    .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(2, AllocationPlacement::Top)
                    .unwrap(),
            },
        };
        unsafe {
            round0
                .host
                .extension_field_inputs
                .get_mut_accessor()
                .get_mut()[0] = GpuExtensionFieldPolyInitialSource {
                start: input0.as_ptr(),
                next_layer_size: 4,
            };
            round0
                .host
                .extension_field_inputs
                .get_mut_accessor()
                .get_mut()[1] = GpuExtensionFieldPolyInitialSource {
                start: input1.as_ptr(),
                next_layer_size: 4,
            };
            round0
                .host
                .extension_field_outputs
                .get_mut_accessor()
                .get_mut()[0] = GpuExtensionFieldPolyInitialSource {
                start: output_num.as_ptr(),
                next_layer_size: 2,
            };
            round0
                .host
                .extension_field_outputs
                .get_mut_accessor()
                .get_mut()[1] = GpuExtensionFieldPolyInitialSource {
                start: output_den.as_ptr(),
                next_layer_size: 2,
            };
        }
        memory_copy_async(
            &mut round0.device.extension_field_inputs,
            &round0.host.extension_field_inputs,
            context.get_exec_stream(),
        )
        .unwrap();
        memory_copy_async(
            &mut round0.device.extension_field_outputs,
            &round0.host.extension_field_outputs,
            context.get_exec_stream(),
        )
        .unwrap();

        launch_lookup_round0::<E4>(
            &round0,
            batch_challenges_dev.as_ptr(),
            contributions.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();
        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let mut expected = Vec::new();
        for output_index in 0..2 {
            let index = output_index * 2;
            let pair_index = index + 1;

            let mut a = input0_values[4 + index];
            a.sub_assign(&input0_values[index]);
            let mut b = input1_values[4 + index];
            b.sub_assign(&input1_values[index]);
            let mut c = input0_values[4 + pair_index];
            c.sub_assign(&input0_values[pair_index]);
            let mut d = input1_values[4 + pair_index];
            d.sub_assign(&input1_values[pair_index]);

            let mut num = a;
            num.mul_assign(&d);
            let mut t = c;
            t.mul_assign(&b);
            num.add_assign(&t);

            let mut den = b;
            den.mul_assign(&d);

            let mut c0 = batch0;
            c0.mul_assign(&output_num_values[output_index]);
            let mut output_den_term = batch1;
            output_den_term.mul_assign(&output_den_values[output_index]);
            c0.add_assign(&output_den_term);

            let mut c1 = batch0;
            c1.mul_assign(&num);
            let mut den_term = batch1;
            den_term.mul_assign(&den);
            c1.add_assign(&den_term);

            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn lookup_continuation_kernel_matches_cpu() {
        let context = make_test_context(64, 8);
        let prev0 = (0..16).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let prev1 = (0..16).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
        let challenge = sample_ext(300);
        let batch0 = sample_ext(400);
        let batch1 = sample_ext(500);
        let prev0_dev = alloc_and_copy(&context, &prev0);
        let prev1_dev = alloc_and_copy(&context, &prev1);
        let cache0: DeviceAllocation<E4> = context.alloc(8, AllocationPlacement::Top).unwrap();
        let cache1: DeviceAllocation<E4> = context.alloc(8, AllocationPlacement::Top).unwrap();
        let folding_challenge_dev = alloc_and_copy(&context, &[challenge]);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch0, batch1]);
        let descriptors = [
            GpuExtensionFieldPolyContinuingLaunchDescriptor {
                previous_layer_start: prev0_dev.as_ptr(),
                this_layer_start: cache0.as_ptr().cast_mut(),
                this_layer_size: 8,
                next_layer_size: 4,
                first_access: true,
            },
            GpuExtensionFieldPolyContinuingLaunchDescriptor {
                previous_layer_start: prev1_dev.as_ptr(),
                this_layer_start: cache1.as_ptr().cast_mut(),
                this_layer_size: 8,
                next_layer_size: 4,
                first_access: true,
            },
        ];
        let descriptors_dev = alloc_and_copy(&context, &descriptors);
        let contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();

        launch_lookup_continuation::<E4>(
            descriptors_dev.as_ptr(),
            folding_challenge_dev.as_ptr(),
            batch_challenges_dev.as_ptr(),
            false,
            contributions.as_ptr().cast_mut(),
            2,
            &context,
        )
        .unwrap();
        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let fold = |values: &[E4], idx: usize| {
            let mut delta = values[8 + idx];
            delta.sub_assign(&values[idx]);
            let mut result = challenge;
            result.mul_assign(&delta);
            result.add_assign(&values[idx]);
            result
        };
        let mut expected = Vec::new();
        for output_index in 0..2 {
            let idx = output_index * 2;
            let a0 = fold(&prev0, idx);
            let a1_full = fold(&prev0, idx + 4);
            let mut da = a1_full;
            da.sub_assign(&a0);
            let b0 = fold(&prev1, idx);
            let b1_full = fold(&prev1, idx + 4);
            let mut db = b1_full;
            db.sub_assign(&b0);

            let c0 = fold(&prev0, idx + 1);
            let c1_full = fold(&prev0, idx + 5);
            let mut dc = c1_full;
            dc.sub_assign(&c0);
            let d0 = fold(&prev1, idx + 1);
            let d1_full = fold(&prev1, idx + 5);
            let mut dd = d1_full;
            dd.sub_assign(&d0);

            let mut num0 = a0;
            num0.mul_assign(&d0);
            let mut t0 = c0;
            t0.mul_assign(&b0);
            num0.add_assign(&t0);
            let mut den0 = b0;
            den0.mul_assign(&d0);

            let mut num1 = da;
            num1.mul_assign(&dd);
            let mut t1 = dc;
            t1.mul_assign(&db);
            num1.add_assign(&t1);
            let mut den1 = db;
            den1.mul_assign(&dd);

            let mut e0 = batch0;
            e0.mul_assign(&num0);
            let mut e0_den = batch1;
            e0_den.mul_assign(&den0);
            e0.add_assign(&e0_den);

            let mut e1 = batch0;
            e1.mul_assign(&num1);
            let mut e1_den = batch1;
            e1_den.mul_assign(&den1);
            e1.add_assign(&e1_den);

            expected.push(e0);
            expected.push(e1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn pairwise_continuation_kernel_matches_cpu() {
        let context = make_test_context(64, 8);
        let prev = (0..16).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let challenge = sample_ext(300);
        let batch = sample_ext(400);
        let prev_dev = alloc_and_copy(&context, &prev);
        let cache: DeviceAllocation<E4> = context.alloc(8, AllocationPlacement::Top).unwrap();
        let folding_challenge_dev = alloc_and_copy(&context, &[challenge]);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch]);
        let descriptors = [GpuExtensionFieldPolyContinuingLaunchDescriptor {
            previous_layer_start: prev_dev.as_ptr(),
            this_layer_start: cache.as_ptr().cast_mut(),
            this_layer_size: 8,
            next_layer_size: 4,
            first_access: true,
        }];
        let descriptors_dev = alloc_and_copy(&context, &descriptors);
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();

        launch_pairwise_continuation::<E4>(
            descriptors_dev.as_ptr(),
            folding_challenge_dev.as_ptr(),
            batch_challenges_dev.as_ptr(),
            false,
            contributions.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();
        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let fold = |values: &[E4], idx: usize| {
            let mut delta = values[8 + idx];
            delta.sub_assign(&values[idx]);
            let mut result = challenge;
            result.mul_assign(&delta);
            result.add_assign(&values[idx]);
            result
        };

        let mut expected = Vec::new();
        for output_index in 0..2 {
            let idx = output_index * 2;
            let even0 = fold(&prev, idx);
            let even1 = fold(&prev, idx + 4);
            let mut even_delta = even1;
            even_delta.sub_assign(&even0);

            let odd0 = fold(&prev, idx + 1);
            let odd1 = fold(&prev, idx + 5);
            let mut odd_delta = odd1;
            odd_delta.sub_assign(&odd0);

            let mut c0 = even0;
            c0.mul_assign(&odd0);
            c0.mul_assign(&batch);

            let mut c1 = even_delta;
            c1.mul_assign(&odd_delta);
            c1.mul_assign(&batch);

            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn accumulator_eq_multiply_and_reduce_match_cpu() {
        let context = make_test_context(64, 8);
        let accumulator = vec![
            sample_ext(10),
            sample_ext(20),
            sample_ext(11),
            sample_ext(21),
        ];
        let eq = vec![sample_ext(30), sample_ext(31)];
        let eq_dev = alloc_and_copy(&context, &eq);
        let mut accumulator_dev = alloc_and_copy(&context, &accumulator);
        let temp_bytes = get_reduce_temp_storage_bytes::<E4>(ReduceOperation::Sum, 2).unwrap();
        let mut temp = context.alloc(temp_bytes, AllocationPlacement::Top).unwrap();
        let mut reduced = context.alloc(2, AllocationPlacement::Top).unwrap();

        super::apply_eq_and_reduce_accumulator(
            &eq_dev,
            &mut accumulator_dev,
            &mut reduced,
            &mut temp,
            2,
            &context,
        )
        .unwrap();

        let mut host = unsafe { context.alloc_host_uninit_slice(2) };
        memory_copy_async(&mut host, &reduced, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let mut expected = [E4::ZERO; 2];
        for row in 0..2 {
            let mut row0 = accumulator[row];
            row0.mul_assign(&eq[row]);
            expected[0].add_assign(&row0);

            let mut row1 = accumulator[2 + row];
            row1.mul_assign(&eq[row]);
            expected[1].add_assign(&row1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn pairwise_round0_kernel_accumulates_into_existing_buffer() {
        let context = make_test_context(64, 8);
        let input_values = (0..8).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let output_values = (0..4).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
        let batch_challenge = sample_ext(200);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch_challenge]);
        let input = alloc_and_copy(&context, &input_values);
        let output = alloc_and_copy(&context, &output_values);
        let initial = vec![
            sample_ext(300),
            sample_ext(301),
            sample_ext(302),
            sample_ext(303),
        ];
        let mut contributions = alloc_and_copy(&context, &initial);

        let mut round0 = GpuSumcheckRound0ScheduledLaunchDescriptors {
            callbacks: Callbacks::new(),
            host: GpuSumcheckRound0HostLaunchDescriptors {
                base_field_inputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(0)
                },
                extension_field_inputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(1)
                },
                base_field_outputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(0)
                },
                extension_field_outputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(1)
                },
            },
            device: GpuSumcheckRound0DeviceLaunchDescriptors {
                base_field_inputs: context
                    .alloc::<GpuBaseFieldPolySource<BF>>(0, AllocationPlacement::Top)
                    .unwrap(),
                extension_field_inputs: context
                    .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(1, AllocationPlacement::Top)
                    .unwrap(),
                base_field_outputs: context
                    .alloc::<GpuBaseFieldPolySource<BF>>(0, AllocationPlacement::Top)
                    .unwrap(),
                extension_field_outputs: context
                    .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(1, AllocationPlacement::Top)
                    .unwrap(),
            },
        };
        unsafe {
            round0
                .host
                .extension_field_inputs
                .get_mut_accessor()
                .get_mut()[0] = GpuExtensionFieldPolyInitialSource {
                start: input.as_ptr(),
                next_layer_size: 4,
            };
            round0
                .host
                .extension_field_outputs
                .get_mut_accessor()
                .get_mut()[0] = GpuExtensionFieldPolyInitialSource {
                start: output.as_ptr(),
                next_layer_size: 2,
            };
        }
        memory_copy_async(
            &mut round0.device.extension_field_inputs,
            &round0.host.extension_field_inputs,
            context.get_exec_stream(),
        )
        .unwrap();
        memory_copy_async(
            &mut round0.device.extension_field_outputs,
            &round0.host.extension_field_outputs,
            context.get_exec_stream(),
        )
        .unwrap();

        launch_pairwise_round0::<E4>(
            &round0,
            batch_challenges_dev.as_ptr(),
            contributions.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();
        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let mut expected = initial;
        for output_index in 0..2 {
            let index = output_index * 2;
            let mut c0 = batch_challenge;
            c0.mul_assign(&output_values[output_index]);
            expected[output_index].add_assign(&c0);

            let mut a = input_values[4 + index];
            a.sub_assign(&input_values[index]);
            let mut b = input_values[4 + index + 1];
            b.sub_assign(&input_values[index + 1]);
            let mut c1 = a;
            c1.mul_assign(&b);
            c1.mul_assign(&batch_challenge);
            expected[2 + output_index].add_assign(&c1);
        }

        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn build_eq_values_from_point_matches_cpu() {
        let context = make_test_context(1024, 512);

        for (challenge_count, challenge_offset) in
            [(0usize, 0usize), (1, 1), (7, 2), (8, 0), (9, 3), (23, 1)]
        {
            let claim_point_len = challenge_offset + challenge_count + 1;
            let claim_point = (0..claim_point_len)
                .map(|idx| sample_ext(40 + idx as u32))
                .collect::<Vec<_>>();
            let claim_point_dev = alloc_and_copy(&context, &claim_point);
            let acc_size = 1usize << challenge_count;
            let mut eq_group_tables = context
                .alloc(
                    eq_group_tables_len(challenge_count).max(1),
                    AllocationPlacement::Top,
                )
                .unwrap();
            let mut eq_values = context
                .alloc(acc_size.max(1), AllocationPlacement::Top)
                .unwrap();

            launch_build_eq_values_from_point::<E4>(
                claim_point_dev.as_ptr(),
                challenge_offset,
                challenge_count,
                eq_group_tables.as_mut_ptr(),
                eq_values.as_mut_ptr(),
                acc_size,
                &context,
            )
            .unwrap();

            let actual = copy_device_values(&context, &eq_values);
            let expected = eq_values_for_suffix(
                &claim_point[challenge_offset..challenge_offset + challenge_count],
            );
            assert_eq!(
                actual, expected,
                "challenge_count={challenge_count}, challenge_offset={challenge_offset}"
            );
        }
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn build_round0_eq_values_from_pairs_matches_cpu() {
        let context = make_test_context(1024, 512);

        for challenge_count in [0usize, 1, 7, 8, 9, 23] {
            let claim_point = (0..=challenge_count)
                .map(|idx| sample_ext(400 + idx as u32))
                .collect::<Vec<_>>();
            let eq_pair_values = super::make_round0_eq_pair_values(&claim_point);
            let acc_size = 1usize << challenge_count;
            let mut eq_pair_values_dev = context
                .alloc(eq_pair_values.len().max(1), AllocationPlacement::Top)
                .unwrap();
            if !eq_pair_values.is_empty() {
                memory_copy_async(
                    &mut eq_pair_values_dev,
                    &eq_pair_values,
                    context.get_exec_stream(),
                )
                .unwrap();
            }
            let eq_group_tables_len = super::round0_eq_group_tables_len(claim_point.len()).max(1);
            let mut eq_group_tables = context
                .alloc(eq_group_tables_len, AllocationPlacement::Top)
                .unwrap();
            let mut eq_values = context
                .alloc(acc_size.max(1), AllocationPlacement::Top)
                .unwrap();

            launch_build_round0_eq_values_from_pairs::<E4>(
                eq_pair_values_dev.as_ptr(),
                challenge_count,
                eq_group_tables.as_mut_ptr(),
                eq_values.as_mut_ptr(),
                acc_size,
                &context,
            )
            .unwrap();

            let actual = copy_device_values(&context, &eq_values);
            let expected = eq_values_for_suffix(&claim_point[1..]);
            assert_eq!(actual, expected, "challenge_count={challenge_count}");
        }
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn fold_eq_values_in_place_matches_cpu() {
        let context = make_test_context(1024, 512);
        let challenge_count = 23usize;
        let claim_point = (0..=challenge_count)
            .map(|idx| sample_ext(500 + idx as u32))
            .collect::<Vec<_>>();
        let mut expected = eq_values_for_suffix(&claim_point[1..]);
        let mut eq_values = alloc_and_copy(&context, &expected);
        let mut current_len = expected.len();

        while current_len > 1 {
            let half_len = current_len / 2;
            launch_fold_eq_values_in_place::<E4>(eq_values.as_mut_ptr(), half_len, &context)
                .unwrap();
            fold_eq_values_cpu(&mut expected);
            let actual = copy_device_values(&context, &eq_values[..half_len]);
            assert_eq!(actual, expected, "current_len={current_len}");
            current_len = half_len;
        }
    }

    #[test]
    fn single_max_quadratic_constraint_uses_direct_metadata_and_no_outputs() {
        let storage = crate::prover::gkr::GpuGKRStorage::<BF, E4> {
            layers: vec![Default::default()],
            layout: None,
        };
        let constraint_input = NoFieldMaxQuadraticGKRRelation {
            quadratic_terms: vec![
                (
                    GKRAddress::BaseLayerMemory(0),
                    vec![
                        (2u32, GKRAddress::BaseLayerWitness(1)),
                        (3u32, GKRAddress::BaseLayerMemory(0)),
                    ]
                    .into_boxed_slice(),
                ),
                (
                    GKRAddress::BaseLayerWitness(2),
                    vec![(5u32, GKRAddress::BaseLayerWitness(1))].into_boxed_slice(),
                ),
            ]
            .into_boxed_slice(),
            linear_terms: vec![
                (7u32, GKRAddress::BaseLayerMemory(3)),
                (11u32, GKRAddress::BaseLayerWitness(2)),
            ]
            .into_boxed_slice(),
            constant: 13,
        };
        let layer = GKRLayerDescription {
            layer: 0,
            gates_with_external_connections: Vec::new(),
            cached_relations: BTreeMap::new(),
            intermediate_layer_width: None,
            gates: vec![GateArtifacts {
                output_layer: 1,
                enforced_relation: NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint {
                    input: constraint_input.clone(),
                },
            }],
        };

        let external_challenges = sample_external_challenges(40);
        let blueprints = build_main_layer_kernel_blueprints(
            &layer,
            0,
            &storage,
            &external_challenges,
            &[],
            0,
            sample_ext(10),
            sample_ext(20),
            sample_ext(20),
            2,
            2,
        );
        assert_eq!(blueprints.len(), 1);
        let blueprint = &blueprints[0];
        let (expected_inputs, expected_metadata) =
            build_single_max_quadratic_constraint_inputs_and_metadata::<E4>(&constraint_input);

        assert_eq!(
            blueprint.kind,
            GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic
        );
        assert_eq!(blueprint.batch_challenges, vec![E4::ONE]);
        assert_eq!(blueprint.inputs, expected_inputs);
        assert!(blueprint.inputs.outputs_in_base.is_empty());
        assert!(blueprint.inputs.outputs_in_extension.is_empty());

        let metadata = blueprint
            .constraint_metadata_source
            .as_ref()
            .expect("constraint metadata must be present");
        let metadata = match metadata {
            super::GpuGKRMainLayerConstraintMetadataSource::Immediate(metadata) => metadata,
            super::GpuGKRMainLayerConstraintMetadataSource::Deferred(..) => {
                panic!("single max quadratic constraint must use immediate metadata")
            }
        };
        assert_eq!(metadata, &expected_metadata);
    }

    #[test]
    fn max_quadratic_relation_dispatches_with_base_output() {
        let storage = crate::prover::gkr::GpuGKRStorage::<BF, E4> {
            layers: vec![Default::default()],
            layout: None,
        };
        let constraint_input = NoFieldMaxQuadraticGKRRelation {
            quadratic_terms: vec![
                (
                    GKRAddress::BaseLayerMemory(0),
                    vec![
                        (2u32, GKRAddress::BaseLayerWitness(1)),
                        (3u32, GKRAddress::BaseLayerMemory(0)),
                    ]
                    .into_boxed_slice(),
                ),
                (
                    GKRAddress::BaseLayerWitness(2),
                    vec![(5u32, GKRAddress::BaseLayerWitness(1))].into_boxed_slice(),
                ),
            ]
            .into_boxed_slice(),
            linear_terms: vec![
                (7u32, GKRAddress::BaseLayerMemory(3)),
                (11u32, GKRAddress::BaseLayerWitness(2)),
            ]
            .into_boxed_slice(),
            constant: 13,
        };
        let output_address = GKRAddress::ScratchSpace(0);
        let layer = GKRLayerDescription {
            layer: 0,
            gates_with_external_connections: Vec::new(),
            cached_relations: BTreeMap::new(),
            intermediate_layer_width: None,
            gates: vec![GateArtifacts {
                output_layer: 1,
                enforced_relation: NoFieldGKRRelation::MaxQuadratic {
                    input: constraint_input.clone(),
                    output: output_address,
                },
            }],
        };

        let external_challenges = sample_external_challenges(40);
        let blueprints = build_main_layer_kernel_blueprints(
            &layer,
            0,
            &storage,
            &external_challenges,
            &[],
            0,
            sample_ext(10),
            sample_ext(20),
            sample_ext(20),
            2,
            2,
        );
        assert_eq!(blueprints.len(), 1);
        let blueprint = &blueprints[0];
        let (expected_inputs, expected_metadata) = build_max_quadratic_relation_inputs_and_metadata::<
            E4,
        >(&constraint_input, output_address);

        assert_eq!(
            blueprint.kind,
            GpuGKRMainLayerKernelKind::MaxQuadraticBaseOutput
        );
        assert_eq!(blueprint.batch_challenges, vec![E4::ONE]);
        assert_eq!(blueprint.inputs, expected_inputs);
        assert_eq!(blueprint.inputs.outputs_in_base, vec![output_address]);
        assert!(blueprint.inputs.outputs_in_extension.is_empty());

        let metadata = blueprint
            .constraint_metadata_source
            .as_ref()
            .expect("constraint metadata must be present");
        let metadata = match metadata {
            super::GpuGKRMainLayerConstraintMetadataSource::Immediate(metadata) => metadata,
            super::GpuGKRMainLayerConstraintMetadataSource::Deferred(..) => {
                panic!("max quadratic relation must use immediate metadata")
            }
        };
        assert_eq!(metadata, &expected_metadata);
        // The MaxQuadraticBaseOutput kernel reuses the constraint helper
        // unchanged, only attaching the output to outputs_in_base — the
        // metadata's linear and quadratic terms match the constraint-only
        // build exactly.
        let (_, base_metadata) =
            build_single_max_quadratic_constraint_inputs_and_metadata::<E4>(&constraint_input);
        assert_eq!(metadata.linear_terms, base_metadata.linear_terms);
        assert_eq!(metadata.quadratic_terms, base_metadata.quadratic_terms);
    }

    #[test]
    fn main_layer_blueprints_for_inits_and_teardowns_initial_pair_use_canonical_top_bits() {
        let storage = crate::prover::gkr::GpuGKRStorage::<BF, E4> {
            layers: vec![Default::default()],
            layout: None,
        };
        let init_output = GKRAddress::InnerLayer {
            layer: 1,
            offset: 0,
        };
        let teardown_output = GKRAddress::InnerLayer {
            layer: 1,
            offset: 1,
        };
        let layer = GKRLayerDescription {
            layer: 0,
            gates_with_external_connections: Vec::new(),
            cached_relations: BTreeMap::new(),
            intermediate_layer_width: None,
            gates: vec![
                GateArtifacts {
                    output_layer: 1,
                    enforced_relation: NoFieldGKRRelation::InitsOrTeardownsInitialPair {
                        timestamp_and_value: InitsOrTeardownsTimestampAndValue::Init,
                        setup: [
                            GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsLow),
                            GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsHigh),
                        ],
                        output: init_output,
                        set_idxes: [1, 4],
                    },
                },
                GateArtifacts {
                    output_layer: 1,
                    enforced_relation: NoFieldGKRRelation::InitsOrTeardownsInitialPair {
                        timestamp_and_value: InitsOrTeardownsTimestampAndValue::Teardown {
                            lhs_timestamp: [0, 1],
                            lhs_value: [2, 3],
                            rhs_timestamp: [1, 0],
                            rhs_value: [3, 2],
                        },
                        setup: [
                            GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsLow),
                            GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsHigh),
                        ],
                        output: teardown_output,
                        set_idxes: [0, 5],
                    },
                },
            ],
        };
        let external_challenges = sample_external_challenges(60);
        let canonical_top_bits = canonical_inits_and_teardowns_top_bits(6);
        let high_bits_shift = high_bits_offset_for_inits_and_teardowns::<2>(1 << 16);

        let dynamic_blueprints = build_main_layer_kernel_blueprints(
            &layer,
            0,
            &storage,
            &external_challenges,
            &canonical_top_bits,
            high_bits_shift,
            sample_ext(10),
            sample_ext(15),
            sample_ext(20),
            4,
            0,
        );
        let static_blueprints = build_main_layer_kernel_blueprints_static(
            &layer,
            0,
            &|addr| storage.layers[0].base_field_inputs.contains_key(addr),
            &external_challenges,
            &canonical_top_bits,
            high_bits_shift,
            4,
            0,
        );

        assert_eq!(dynamic_blueprints.len(), 2);
        assert_eq!(static_blueprints.len(), 2);

        let expected_specs = [
            (
                InitsOrTeardownsTimestampAndValue::Init,
                init_output,
                [canonical_top_bits[1], canonical_top_bits[4]],
            ),
            (
                InitsOrTeardownsTimestampAndValue::Teardown {
                    lhs_timestamp: [0, 1],
                    lhs_value: [2, 3],
                    rhs_timestamp: [1, 0],
                    rhs_value: [3, 2],
                },
                teardown_output,
                [canonical_top_bits[0], canonical_top_bits[5]],
            ),
        ];

        for ((dynamic_blueprint, static_blueprint), (timestamp_and_value, output, top_bits)) in
            dynamic_blueprints
                .iter()
                .zip(static_blueprints.iter())
                .zip(expected_specs.iter())
        {
            let (expected_inputs, expected_metadata) =
                build_inits_and_teardowns_initial_pair_inputs_and_metadata(
                    timestamp_and_value,
                    [
                        GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsLow),
                        GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsHigh),
                    ],
                    *output,
                    *top_bits,
                    high_bits_shift,
                    &external_challenges,
                );

            for blueprint in [dynamic_blueprint, static_blueprint] {
                assert_eq!(
                    blueprint.kind,
                    GpuGKRMainLayerKernelKind::InitsAndTeardownsInitialPair
                );
                assert_eq!(blueprint.inputs, expected_inputs);
                let metadata = blueprint
                    .constraint_metadata_source
                    .as_ref()
                    .expect("init/teardown metadata must be present");
                let metadata = match metadata {
                    super::GpuGKRMainLayerConstraintMetadataSource::Immediate(metadata) => metadata,
                    super::GpuGKRMainLayerConstraintMetadataSource::Deferred(..) => {
                        panic!("init/teardown metadata must be materialized immediately")
                    }
                };
                assert_eq!(metadata, &expected_metadata);
            }
        }

        assert_eq!(dynamic_blueprints[0].batch_challenges, vec![E4::ONE]);
        assert_eq!(dynamic_blueprints[1].batch_challenges, vec![sample_ext(10)]);
        assert!(static_blueprints[0].batch_challenges.is_empty());
        assert!(static_blueprints[1].batch_challenges.is_empty());
    }

    #[test]
    fn compute_main_layer_orphan_output_addresses_picks_unconsumed_outputs() {
        // Three layers; layer 0 produces an InnerLayer{1,0} output that
        // layer-1's kernels do not read — exactly the MaxQuadratic-with-
        // higher-layer-consumer case the GPU port now handles. Bottom
        // layer (layer_idx == 0) is always empty (no layer below). Top
        // layer's slot lists orphans of the layer below it (here:
        // layer-1 outputs that layer 2 doesn't consume).
        let layer0_inputs = vec![GKRAddress::BaseLayerWitness(0)];
        let layer1_inputs = vec![GKRAddress::BaseLayerWitness(1)];
        let layer2_inputs = vec![
            GKRAddress::ScratchSpace(7),
            GKRAddress::InnerLayer {
                layer: 2,
                offset: 0,
            },
        ];
        let inputs_per_layer = vec![layer0_inputs, layer1_inputs, layer2_inputs];

        let layer0_outputs = vec![GKRAddress::InnerLayer {
            layer: 1,
            offset: 0,
        }];
        let layer1_outputs = vec![
            GKRAddress::ScratchSpace(7),
            GKRAddress::InnerLayer {
                layer: 2,
                offset: 0,
            },
        ];
        let layer2_outputs = vec![GKRAddress::InnerLayer {
            layer: 3,
            offset: 0,
        }];
        let outputs_per_layer = vec![layer0_outputs, layer1_outputs, layer2_outputs];

        let orphans = super::compute_main_layer_orphan_output_addresses_per_layer::<E4>(
            &inputs_per_layer,
            &outputs_per_layer,
        );

        // Bottom layer (layer 0): nothing below it — always empty.
        assert!(orphans[0].is_empty());
        // Layer 1's orphan list = layer-0 outputs not consumed by layer 1.
        // layer 0's output InnerLayer{1,0} is NOT in layer 1's inputs
        // (which is BaseLayerWitness(1)) — so it IS an orphan emitted at
        // scheduler 1.
        assert_eq!(
            orphans[1],
            vec![GKRAddress::InnerLayer {
                layer: 1,
                offset: 0,
            }],
        );
        // Layer 2's orphan list = layer-1 outputs not consumed by layer 2.
        // both ScratchSpace(7) and InnerLayer{2,0} ARE in layer 2's
        // inputs, so neither is an orphan.
        assert!(orphans[2].is_empty());
    }

    #[test]
    fn compute_main_layer_orphan_output_addresses_handles_empty() {
        let orphans = super::compute_main_layer_orphan_output_addresses_per_layer::<E4>(&[], &[]);
        assert!(orphans.is_empty());
    }
}
