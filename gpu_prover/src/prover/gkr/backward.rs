use std::cell::UnsafeCell;
use std::collections::{BTreeMap, VecDeque};
use std::mem::align_of;
use std::ptr::{null, null_mut};
use std::slice;

use cs::definitions::{
    gkr::AddressSpaceType, GKRAddress, MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
    MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
    MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
    MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX, MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
    MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
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
use prover::gkr::prover::transcript_utils::{commit_field_els, draw_random_field_els};
use prover::gkr::prover::{GKRExternalChallenges, SumcheckIntermediateProofValues};
use prover::gkr::sumcheck::evaluation_kernels::{
    BaseFieldCopyGKRRelation, BatchConstraintEvalGKRRelation, BatchedGKRKernel,
    ExtensionCopyGKRRelation, GKRInputs, LookupBaseExtMinusBaseExtGKRRelation,
    LookupBaseMinusMultiplicityByBaseGKRRelation, LookupBasePairGKRRelation,
    LookupExtensionMinusMultiplicityByExtensionGKRRelation, LookupExtensionPairGKRRelation,
    LookupPairGKRRelation, LookupRationalPairWithUnbalancedBaseGKRRelation,
    LookupRationalPairWithUnbalancedExtensionGKRRelation, MaskIntoIdentityProductGKRRelation,
    SameSizeProductGKRRelation,
};
use prover::gkr::sumcheck::{
    evaluate_eq_poly, evaluate_small_univariate_poly, output_univariate_monomial_form_max_quadratic,
};
use prover::transcript::Seed;

pub(crate) use super::backward_kernels::*;
use super::transform::normalize_compiled_circuit_for_gpu;
use super::{
    alloc_host_and_schedule_copy, GpuBaseFieldPolySource,
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
use crate::ops::cub::device_reduce::{
    get_reduce_temp_storage_bytes, reduce, Reduce, ReduceOperation,
};
use crate::ops::cub::CUB_TEMP_STORAGE_EXTRA_ALIGNMENT_LOG2;
use crate::ops::simple::{mul_into_y, BinaryOp, Mul};
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{
    DeviceAllocation, HostAllocation, ProverContext, UnsafeAccessor, UnsafeMutAccessor,
};
use crate::primitives::device_structures::{DeviceVectorChunk, DeviceVectorChunkMut};
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E4};
use crate::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};

fn remap_constraint_input(
    mapping: &mut BTreeMap<GKRAddress, usize>,
    inputs: &mut Vec<GKRAddress>,
    address: GKRAddress,
) -> usize {
    if let GKRAddress::ScratchSpace(..) = address {
        panic!("Scratch space addresses are not allowed in constraints");
    }
    if let Some(idx) = mapping.get(&address).copied() {
        idx
    } else {
        let idx = mapping.len();
        mapping.insert(address, idx);
        inputs.push(address);
        idx
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

fn memory_query_as_flattened_relation<E: Field + FieldExtension<BF>>(
    rel: &cs::gkr_compiler::NoFieldSpecialMemoryContributionRelation,
    external_challenges: &GKRExternalChallenges<BF, E>,
) -> (BTreeMap<GKRAddress, E>, E) {
    let mut result = BTreeMap::new();
    let mut constant_term = external_challenges.permutation_argument_additive_part;

    match rel.address_space {
        cs::gkr_compiler::CompiledAddressSpaceRelationStrict::Constant(c) => {
            assert!(c < (1u32 << 16));
            constant_term.add_assign_base(&BF::from_u32_unchecked(c));
        }
        cs::gkr_compiler::CompiledAddressSpaceRelationStrict::IsRam(offset) => {
            assert_eq!(AddressSpaceType::RAM as u8, 1);
            assert!(result
                .insert(GKRAddress::BaseLayerMemory(offset), E::ONE)
                .is_none());
        }
        cs::gkr_compiler::CompiledAddressSpaceRelationStrict::IsRegister(offset) => {
            assert_eq!(AddressSpaceType::Register as u8, 0);
            assert!(result
                .insert(GKRAddress::BaseLayerMemory(offset), E::MINUS_ONE)
                .is_none());
            constant_term.add_assign_base(&BF::ONE);
        }
    }

    match &rel.address {
        cs::gkr_compiler::CompiledAddressStrict::ConstantU16(c) => {
            let mut challenge = external_challenges.permutation_argument_linearization_challenges
                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
            challenge.mul_assign_by_base(&BF::from_u32_unchecked(*c as u32));
            constant_term.add_assign(&challenge);
        }
        cs::gkr_compiler::CompiledAddressStrict::Constant(c) => {
            assert!(*c < (1u32 << 16));
            let mut challenge = external_challenges.permutation_argument_linearization_challenges
                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
            challenge.mul_assign_by_base(&BF::from_u32_unchecked(*c));
            constant_term.add_assign(&challenge);
        }
        cs::gkr_compiler::CompiledAddressStrict::U16Space(offset) => {
            let challenge = external_challenges.permutation_argument_linearization_challenges
                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
            assert!(result
                .insert(GKRAddress::BaseLayerMemory(*offset), challenge)
                .is_none());
        }
        cs::gkr_compiler::CompiledAddressStrict::U32Space([low, high]) => {
            for (idx, offset) in [
                (MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX, *low),
                (MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX, *high),
            ] {
                let challenge =
                    external_challenges.permutation_argument_linearization_challenges[idx];
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
                let mut challenge = external_challenges
                    .permutation_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                challenge.mul_assign_by_base(&BF::from_u32_unchecked(c as u32));
                assert!(result
                    .insert(GKRAddress::BaseLayerMemory(offset), challenge)
                    .is_none());
            }
            {
                let mut challenge = external_challenges
                    .permutation_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                assert!(result
                    .insert(GKRAddress::BaseLayerMemory(*low_base), challenge)
                    .is_none());
                challenge.mul_assign_by_base(&BF::from_u32_unchecked(*low_offset as u32));
                constant_term.add_assign(&challenge);
            }
            {
                let challenge = external_challenges.permutation_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
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
                let mut challenge = external_challenges
                    .permutation_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                assert!(result
                    .insert(GKRAddress::BaseLayerMemory(ts[0]), challenge)
                    .is_none());
                challenge.mul_assign_by_base(&BF::from_u32_unchecked(rel.timestamp_offset as u32));
                constant_term.add_assign(&challenge);
            }
            {
                let challenge = external_challenges.permutation_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
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
                (MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX, read_value[0]),
                (MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX, read_value[1]),
            ] {
                let challenge =
                    external_challenges.permutation_argument_linearization_challenges[idx];
                assert!(result
                    .insert(GKRAddress::BaseLayerMemory(offset), challenge)
                    .is_none());
            }
        }
        cs::definitions::gkr::RamWordRepresentation::U8Limbs(read_value_bytes) => {
            let byte_shift = BF::from_u32_unchecked(1u32 << 8);
            for (idx, offset_low, offset_high) in [
                (
                    MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
                    read_value_bytes[0],
                    read_value_bytes[1],
                ),
                (
                    MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
                    read_value_bytes[2],
                    read_value_bytes[3],
                ),
            ] {
                let mut challenge =
                    external_challenges.permutation_argument_linearization_challenges[idx];
                assert!(result
                    .insert(GKRAddress::BaseLayerMemory(offset_low), challenge)
                    .is_none());
                challenge.mul_assign_by_base(&byte_shift);
                assert!(result
                    .insert(GKRAddress::BaseLayerMemory(offset_high), challenge)
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
) -> (BTreeMap<GKRAddress, E>, E) {
    let mut result = BTreeMap::new();
    let mut constant_term = external_challenges.permutation_argument_additive_part;
    constant_term.add_assign_base(&BF::from_u32_unchecked(AddressSpaceType::RAM as u32));

    {
        let challenge = external_challenges.permutation_argument_linearization_challenges
            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        assert!(result.insert(setup[0], challenge).is_none());
    }
    {
        let mut challenge = external_challenges.permutation_argument_linearization_challenges
            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
        assert!(result.insert(setup[1], challenge).is_none());
        challenge.mul_assign_by_base(&BF::from_u32_unchecked(
            address_high_bits << address_high_bits_shift,
        ));
        constant_term.add_assign(&challenge);
    }

    if let Some((timestamps, values)) = timestamps_and_values {
        for (idx, address) in [
            (
                MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
                timestamps[0],
            ),
            (
                MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
                timestamps[1],
            ),
            (MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX, values[0]),
            (MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX, values[1]),
        ] {
            let challenge = external_challenges.permutation_argument_linearization_challenges[idx];
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
    for (&lhs_address, &lhs_challenge) in lhs_terms.iter() {
        let lhs_idx = remap_constraint_input(&mut mapping, &mut inputs, lhs_address);
        for (&rhs_address, &rhs_challenge) in rhs_terms.iter() {
            let rhs_idx = remap_constraint_input(&mut mapping, &mut inputs, rhs_address);
            let mut challenge = lhs_challenge;
            challenge.mul_assign(&rhs_challenge);
            quadratic_terms.push(GpuGKRMainLayerConstraintQuadraticTerm {
                lhs: lhs_idx as u32,
                rhs: rhs_idx as u32,
                challenge,
            });
        }
    }

    let mut linear_acc = BTreeMap::new();
    for (&address, &challenge) in lhs_terms.iter() {
        let idx = remap_constraint_input(&mut mapping, &mut inputs, address);
        let mut linear = challenge;
        linear.mul_assign(&rhs_constant);
        linear_acc
            .entry(idx)
            .and_modify(|acc: &mut E| {
                acc.add_assign(&linear);
            })
            .or_insert(linear);
    }
    for (&address, &challenge) in rhs_terms.iter() {
        let idx = remap_constraint_input(&mut mapping, &mut inputs, address);
        let mut linear = challenge;
        linear.mul_assign(&lhs_constant);
        linear_acc
            .entry(idx)
            .and_modify(|acc: &mut E| {
                acc.add_assign(&linear);
            })
            .or_insert(linear);
    }

    let linear_terms = linear_acc
        .into_iter()
        .map(|(input, challenge)| GpuGKRMainLayerConstraintLinearTerm {
            input: input as u32,
            challenge,
        })
        .collect();
    let mut constant_offset = lhs_constant;
    constant_offset.mul_assign(&rhs_constant);

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
            constant_offset,
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
            let rhs_idx = if *lhs == *rhs {
                lhs_idx
            } else {
                remap_constraint_input(&mut mapping, &mut inputs, *rhs)
            };
            quadratic_terms.push(GpuGKRMainLayerConstraintQuadraticTerm {
                lhs: lhs_idx as u32,
                rhs: rhs_idx as u32,
                challenge: E::from_base(BF::from_u32_with_reduction(*coeff)),
            });
        }
    }

    for (coeff, input) in relation.linear_terms.iter() {
        let input_idx = remap_constraint_input(&mut mapping, &mut inputs, *input);
        linear_terms.push(GpuGKRMainLayerConstraintLinearTerm {
            input: input_idx as u32,
            challenge: E::from_base(BF::from_u32_with_reduction(*coeff)),
        });
    }

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
            constant_offset: E::from_base(BF::from_u32_with_reduction(relation.constant)),
        },
    )
}

pub(crate) fn build_constraints_max_quadratic_inputs_and_template(
    relation: &NoFieldMaxQuadraticConstraintsGKRRelation,
) -> (GKRInputs, GpuGKRMainLayerConstraintTemplate) {
    let mut mapping = BTreeMap::new();
    let mut inputs = Vec::new();
    let mut quadratic_terms = Vec::new();
    let mut linear_terms = Vec::new();

    for ((lhs, rhs), challenge_terms) in relation.quadratic_terms.iter() {
        let lhs_idx = remap_constraint_input(&mut mapping, &mut inputs, *lhs);
        let rhs_idx = if *lhs == *rhs {
            lhs_idx
        } else {
            remap_constraint_input(&mut mapping, &mut inputs, *rhs)
        };
        quadratic_terms.push(GpuGKRMainLayerConstraintQuadraticTemplate {
            lhs: lhs_idx as u32,
            rhs: rhs_idx as u32,
            challenge_terms: challenge_terms
                .iter()
                .map(|(coeff, power)| GpuGKRMainLayerConstraintChallengeTerm {
                    coeff: BF::from_u32_with_reduction(*coeff),
                    source: GpuGKRMainLayerDeferredChallengeSource::ConstraintBatch,
                    power: *power as u32,
                })
                .collect(),
        });
    }

    for (input, challenge_terms) in relation.linear_terms.iter() {
        let input_idx = remap_constraint_input(&mut mapping, &mut inputs, *input);
        linear_terms.push(GpuGKRMainLayerConstraintLinearTemplate {
            input: input_idx as u32,
            challenge_terms: challenge_terms
                .iter()
                .map(|(coeff, power)| GpuGKRMainLayerConstraintChallengeTerm {
                    coeff: BF::from_u32_with_reduction(*coeff),
                    source: GpuGKRMainLayerDeferredChallengeSource::ConstraintBatch,
                    power: *power as u32,
                })
                .collect(),
        });
    }

    (
        GKRInputs {
            inputs_in_base: inputs,
            inputs_in_extension: Vec::new(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: Vec::new(),
        },
        GpuGKRMainLayerConstraintTemplate {
            quadratic_terms,
            linear_terms,
            constant_terms: relation
                .constants
                .iter()
                .map(|(coeff, power)| GpuGKRMainLayerConstraintChallengeTerm {
                    coeff: BF::from_u32_with_reduction(*coeff),
                    source: GpuGKRMainLayerDeferredChallengeSource::ConstraintBatch,
                    power: *power as u32,
                })
                .collect(),
        },
    )
}

fn build_linear_base_kernel_inputs_and_metadata<E: Field + FieldExtension<BF>>(
    relation: &cs::definitions::gkr::NoFieldLinearRelation,
    output: GKRAddress,
) -> (GKRInputs, GpuGKRMainLayerConstraintHostMetadata<E>) {
    let mut mapping = BTreeMap::new();
    let mut inputs = Vec::new();
    let mut linear_terms = Vec::new();

    for (coeff, input) in relation.linear_terms.iter() {
        let input_idx = remap_constraint_input(&mut mapping, &mut inputs, *input);
        linear_terms.push(GpuGKRMainLayerConstraintLinearTerm {
            input: input_idx as u32,
            challenge: E::from_base(BF::from_u32_with_reduction(*coeff)),
        });
    }

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
            constant_offset: E::from_base(BF::from_u32_with_reduction(relation.constant)),
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

fn remap_no_cache_linear_form_inputs<E: Field>(
    mapping: &mut BTreeMap<GKRAddress, usize>,
    inputs: &mut Vec<GKRAddress>,
    terms: &BTreeMap<GKRAddress, E>,
) {
    for address in terms.keys().copied() {
        remap_no_cache_base_input(mapping, inputs, address);
    }
}

fn collect_no_cache_linear_form_inputs<E: Field>(
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
            },
        )
        .collect::<Vec<_>>();
    if !constant.is_zero() {
        encoded.push(GpuGKRMainLayerConstraintQuadraticTerm {
            lhs: NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL,
            rhs: 0,
            challenge: constant,
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
        })
        .collect::<Vec<_>>();
    if !constant.is_zero() {
        encoded.push(GpuGKRMainLayerConstraintLinearTerm {
            input: NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL,
            challenge: constant,
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
        quadratic_terms: encode_linear_form_as_quadratic_terms(&mapping, &lhs_terms, lhs_constant),
        linear_terms: encode_linear_form_as_linear_terms(&mapping, &rhs_terms, rhs_constant),
        constant_offset: E::ZERO,
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
        linear_terms: encode_linear_form_as_linear_terms(&mapping, &terms, constant),
        constant_offset: E::ZERO,
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

struct PreparedDimensionReducingKernelStaticData<B, E: Copy> {
    kind: GpuGKRDimensionReducingKernelKind,
    batch_challenge_offset: usize,
    batch_challenge_count: usize,
    round0_descriptors: GpuSumcheckRound0LaunchDescriptors<B, E>,
    round1_descriptors: GpuSumcheckRound1HostLaunchDescriptors<B, E>,
    round2_descriptors: Option<GpuSumcheckRound2HostLaunchDescriptors<B, E>>,
    round3_descriptors: Vec<GpuGKRDimensionReducingRound3HostDescriptors<E>>,
}

fn build_dimension_reducing_round0_batch_template<B, E: Field>(
    folding_steps: usize,
    static_data: &[PreparedDimensionReducingKernelStaticData<B, E>],
    spill_builder: &mut SpillPayloadBuilder,
) -> GpuGKRDimensionReducingRound0Batch<E> {
    let mut batch = GpuGKRDimensionReducingRound0Batch::default();
    batch.record_count = static_data.len() as u32;
    let mut inline_builder = InlinePayloadBuilder::new();

    for (idx, kernel) in static_data.iter().enumerate() {
        debug_assert!(kernel.round0_descriptors.base_field_inputs.is_empty());
        debug_assert!(kernel.round0_descriptors.base_field_outputs.is_empty());
        let mark = inline_builder.mark();
        let inline_ext_inputs =
            inline_builder.try_push_copy(&kernel.round0_descriptors.extension_field_inputs);
        let inline_ext_outputs =
            inline_builder.try_push_copy(&kernel.round0_descriptors.extension_field_outputs);
        let (record_mode, extension_inputs, extension_outputs) =
            if let (Some(extension_inputs), Some(extension_outputs)) =
                (inline_ext_inputs, inline_ext_outputs)
            {
                (
                    GpuGKRDimensionReducingBatchRecordMode::InlineDescriptors,
                    extension_inputs,
                    extension_outputs,
                )
            } else {
                inline_builder.restore(mark);
                (
                    GpuGKRDimensionReducingBatchRecordMode::PointerDescriptors,
                    spill_builder.push_copy(&kernel.round0_descriptors.extension_field_inputs),
                    spill_builder.push_copy(&kernel.round0_descriptors.extension_field_outputs),
                )
            };

        batch.records[idx] = GpuGKRDimensionReducingRound0BatchRecord {
            kind: kernel.kind.as_u32(),
            record_mode: record_mode.as_u32(),
            _reserved0: 0,
            _reserved1: 0,
            extension_inputs,
            extension_outputs,
            batch_challenge_offset: kernel.batch_challenge_offset as u32,
            batch_challenge_count: kernel.batch_challenge_count as u32,
        };
    }

    batch.inline_payload = inline_builder.into_bytes();
    batch
}

fn build_dimension_reducing_round1_batch_template<B, E: Field>(
    folding_steps: usize,
    static_data: &[PreparedDimensionReducingKernelStaticData<B, E>],
    spill_builder: &mut SpillPayloadBuilder,
) -> GpuGKRDimensionReducingRound1Batch<E> {
    let mut batch = GpuGKRDimensionReducingRound1Batch::default();
    batch.record_count = static_data.len() as u32;
    let mut inline_builder = InlinePayloadBuilder::new();

    for (idx, kernel) in static_data.iter().enumerate() {
        debug_assert!(kernel.round1_descriptors.base_field_inputs.is_empty());
        let mark = inline_builder.mark();
        let inline_ext_inputs =
            inline_builder.try_push_copy(&kernel.round1_descriptors.extension_field_inputs);
        let (record_mode, extension_inputs) = if let Some(extension_inputs) = inline_ext_inputs {
            (
                GpuGKRDimensionReducingBatchRecordMode::InlineDescriptors,
                extension_inputs,
            )
        } else {
            inline_builder.restore(mark);
            (
                GpuGKRDimensionReducingBatchRecordMode::PointerDescriptors,
                spill_builder.push_copy(&kernel.round1_descriptors.extension_field_inputs),
            )
        };

        batch.records[idx] = GpuGKRDimensionReducingContinuationBatchRecord {
            kind: kernel.kind.as_u32(),
            record_mode: record_mode.as_u32(),
            _reserved0: 0,
            _reserved1: 0,
            extension_inputs,
            batch_challenge_offset: kernel.batch_challenge_offset as u32,
            batch_challenge_count: kernel.batch_challenge_count as u32,
        };
    }

    batch.inline_payload = inline_builder.into_bytes();
    batch
}

fn build_dimension_reducing_round2_batch_template<B, E: Field>(
    folding_steps: usize,
    static_data: &[PreparedDimensionReducingKernelStaticData<B, E>],
    spill_builder: &mut SpillPayloadBuilder,
) -> GpuGKRDimensionReducingRound2Batch<E> {
    let mut batch = GpuGKRDimensionReducingRound2Batch::default();
    batch.record_count = static_data.len() as u32;
    let mut inline_builder = InlinePayloadBuilder::new();

    for (idx, kernel) in static_data.iter().enumerate() {
        let descriptors = kernel
            .round2_descriptors
            .as_ref()
            .expect("round 2 descriptors must be present when round 2 template is built");
        debug_assert!(descriptors.base_field_inputs.is_empty());
        let mark = inline_builder.mark();
        let inline_ext_inputs = inline_builder.try_push_copy(&descriptors.extension_field_inputs);
        let (record_mode, extension_inputs) = if let Some(extension_inputs) = inline_ext_inputs {
            (
                GpuGKRDimensionReducingBatchRecordMode::InlineDescriptors,
                extension_inputs,
            )
        } else {
            inline_builder.restore(mark);
            (
                GpuGKRDimensionReducingBatchRecordMode::PointerDescriptors,
                spill_builder.push_copy(&descriptors.extension_field_inputs),
            )
        };

        batch.records[idx] = GpuGKRDimensionReducingContinuationBatchRecord {
            kind: kernel.kind.as_u32(),
            record_mode: record_mode.as_u32(),
            _reserved0: 0,
            _reserved1: 0,
            extension_inputs,
            batch_challenge_offset: kernel.batch_challenge_offset as u32,
            batch_challenge_count: kernel.batch_challenge_count as u32,
        };
    }

    batch.inline_payload = inline_builder.into_bytes();
    batch
}

fn build_dimension_reducing_round3_batch_templates<B, E: Field>(
    folding_steps: usize,
    static_data: &[PreparedDimensionReducingKernelStaticData<B, E>],
    spill_builder: &mut SpillPayloadBuilder,
) -> Vec<GpuGKRDimensionReducingRound3BatchTemplate<E>> {
    let mut result = Vec::with_capacity(folding_steps.saturating_sub(3));
    for step in 3..folding_steps {
        let mut batch = GpuGKRDimensionReducingRound3Batch::default();
        batch.record_count = static_data.len() as u32;
        let mut inline_builder = InlinePayloadBuilder::new();

        for (idx, kernel) in static_data.iter().enumerate() {
            let descriptors = kernel
                .round3_descriptors
                .iter()
                .find(|descriptors| descriptors.step == step)
                .unwrap_or_else(|| {
                    panic!("missing dimension-reducing round 3 descriptors for step {step}")
                });
            debug_assert!(descriptors.descriptors.base_field_inputs.is_empty());
            let mark = inline_builder.mark();
            let inline_ext_inputs =
                inline_builder.try_push_copy(&descriptors.descriptors.extension_field_inputs);
            let (record_mode, extension_inputs) = if let Some(extension_inputs) = inline_ext_inputs
            {
                (
                    GpuGKRDimensionReducingBatchRecordMode::InlineDescriptors,
                    extension_inputs,
                )
            } else {
                inline_builder.restore(mark);
                (
                    GpuGKRDimensionReducingBatchRecordMode::PointerDescriptors,
                    spill_builder.push_copy(&descriptors.descriptors.extension_field_inputs),
                )
            };

            batch.records[idx] = GpuGKRDimensionReducingContinuationBatchRecord {
                kind: kernel.kind.as_u32(),
                record_mode: record_mode.as_u32(),
                _reserved0: 0,
                _reserved1: 0,
                extension_inputs,
                batch_challenge_offset: kernel.batch_challenge_offset as u32,
                batch_challenge_count: kernel.batch_challenge_count as u32,
            };
        }

        batch.inline_payload = inline_builder.into_bytes();
        result.push(GpuGKRDimensionReducingRound3BatchTemplate { step, batch });
    }
    result
}

fn build_dimension_reducing_batch_templates<B, E: Field>(
    folding_steps: usize,
    static_data: &[PreparedDimensionReducingKernelStaticData<B, E>],
) -> (
    GpuGKRDimensionReducingRound0Batch<E>,
    GpuGKRDimensionReducingRound1Batch<E>,
    Option<GpuGKRDimensionReducingRound2Batch<E>>,
    Vec<GpuGKRDimensionReducingRound3BatchTemplate<E>>,
    Vec<u8>,
) {
    let mut spill_builder = SpillPayloadBuilder::default();
    let round0 = build_dimension_reducing_round0_batch_template(
        folding_steps,
        static_data,
        &mut spill_builder,
    );
    let round1 = build_dimension_reducing_round1_batch_template(
        folding_steps,
        static_data,
        &mut spill_builder,
    );
    let round2 = (folding_steps >= 3).then(|| {
        build_dimension_reducing_round2_batch_template(
            folding_steps,
            static_data,
            &mut spill_builder,
        )
    });
    let round3 = build_dimension_reducing_round3_batch_templates(
        folding_steps,
        static_data,
        &mut spill_builder,
    );
    (round0, round1, round2, round3, spill_builder.bytes)
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
    constraint_batch_challenge: E,
) -> E {
    let mut total = E::ZERO;
    for term in challenge_terms.iter() {
        let challenge = match term.source {
            GpuGKRMainLayerDeferredChallengeSource::LookupMultiplicative => {
                lookup_multiplicative_challenge
            }
            GpuGKRMainLayerDeferredChallengeSource::LookupAdditive => lookup_additive_challenge,
            GpuGKRMainLayerDeferredChallengeSource::ConstraintBatch => constraint_batch_challenge,
        };
        let mut contribution = challenge.pow(term.power);
        contribution.mul_assign_by_base(&term.coeff);
        total.add_assign(&contribution);
    }
    total
}

fn resolve_main_layer_constraint_metadata<E: Field + FieldExtension<BF>>(
    source: Option<GpuGKRMainLayerConstraintMetadataSource<E>>,
    constraint_batch_challenge: E,
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

fn pack_metadata_block<E: Field>(
    metadata: Option<&GpuGKRMainLayerConstraintHostMetadata<E>>,
    inline_builder: &mut InlinePayloadBuilder,
    spill_builder: &mut SpillPayloadBuilder,
) -> (
    bool,
    GpuGKRMainLayerPayloadRange,
    GpuGKRMainLayerPayloadRange,
    E,
) {
    let Some(metadata) = metadata else {
        return (
            true,
            GpuGKRMainLayerPayloadRange::default(),
            GpuGKRMainLayerPayloadRange::default(),
            E::ZERO,
        );
    };

    let mark = inline_builder.mark();
    let inline_quadratic = inline_builder.try_push_copy(&metadata.quadratic_terms);
    let inline_linear = inline_builder.try_push_copy(&metadata.linear_terms);
    if let (Some(quadratic_terms), Some(linear_terms)) = (inline_quadratic, inline_linear) {
        return (
            true,
            quadratic_terms,
            linear_terms,
            metadata.constant_offset,
        );
    }
    inline_builder.restore(mark);
    (
        false,
        spill_builder.push_copy(&metadata.quadratic_terms),
        spill_builder.push_copy(&metadata.linear_terms),
        metadata.constant_offset,
    )
}

fn build_main_layer_round0_batch_template<E: Field>(
    folding_steps: usize,
    static_data: &[PreparedMainLayerKernelStaticData<E>],
    spill_builder: &mut SpillPayloadBuilder,
) -> GpuGKRMainRound0BatchStatic<E> {
    let mut batch = GpuGKRMainRound0BatchStatic::default();
    batch.record_count = static_data.len() as u32;
    let mut inline_builder = InlinePayloadBuilder::new();

    for (idx, kernel) in static_data.iter().enumerate() {
        let mark = inline_builder.mark();
        let inline_base_inputs =
            inline_builder.try_push_copy(&kernel.round0_descriptors.base_field_inputs);
        let inline_ext_inputs =
            inline_builder.try_push_copy(&kernel.round0_descriptors.extension_field_inputs);
        let inline_base_outputs =
            inline_builder.try_push_copy(&kernel.round0_descriptors.base_field_outputs);
        let inline_ext_outputs =
            inline_builder.try_push_copy(&kernel.round0_descriptors.extension_field_outputs);

        let (record_mode, base_inputs, extension_inputs, base_outputs, extension_outputs) =
            if let (
                Some(base_inputs),
                Some(extension_inputs),
                Some(base_outputs),
                Some(extension_outputs),
            ) = (
                inline_base_inputs,
                inline_ext_inputs,
                inline_base_outputs,
                inline_ext_outputs,
            ) {
                (
                    GpuGKRMainLayerBatchRecordMode::InlineAll,
                    base_inputs,
                    extension_inputs,
                    base_outputs,
                    extension_outputs,
                )
            } else {
                inline_builder.restore(mark);
                (
                    GpuGKRMainLayerBatchRecordMode::PointerDescriptors,
                    spill_builder.push_copy(&kernel.round0_descriptors.base_field_inputs),
                    spill_builder.push_copy(&kernel.round0_descriptors.extension_field_inputs),
                    spill_builder.push_copy(&kernel.round0_descriptors.base_field_outputs),
                    spill_builder.push_copy(&kernel.round0_descriptors.extension_field_outputs),
                )
            };

        let (metadata_inline, quadratic_terms, linear_terms, constant_offset) = pack_metadata_block(
            kernel.constraint_metadata.as_ref(),
            &mut inline_builder,
            spill_builder,
        );

        batch.records[idx] = GpuGKRMainRound0BatchRecord {
            kind: kernel.kind.as_u32(),
            record_mode: match (record_mode, metadata_inline) {
                (GpuGKRMainLayerBatchRecordMode::InlineAll, true) => {
                    GpuGKRMainLayerBatchRecordMode::InlineAll
                }
                (GpuGKRMainLayerBatchRecordMode::InlineAll, false) => {
                    GpuGKRMainLayerBatchRecordMode::InlineNoMetadata
                }
                _ => GpuGKRMainLayerBatchRecordMode::PointerDescriptors,
            }
            .as_u32(),
            metadata_inline: metadata_inline as u32,
            _reserved: 0,
            base_inputs,
            extension_inputs,
            base_outputs,
            extension_outputs,
            quadratic_terms,
            linear_terms,
            auxiliary_challenge: kernel.auxiliary_challenge,
            constant_offset,
        };
    }

    batch.inline_payload = inline_builder.into_bytes();
    batch
}

fn build_main_layer_round1_batch_template<E: Field>(
    folding_steps: usize,
    static_data: &[PreparedMainLayerKernelStaticData<E>],
    spill_builder: &mut SpillPayloadBuilder,
) -> GpuGKRMainRound1BatchStatic<E> {
    let mut batch = GpuGKRMainRound1BatchStatic::default();
    batch.record_count = static_data.len() as u32;
    let mut inline_builder = InlinePayloadBuilder::new();

    for (idx, kernel) in static_data.iter().enumerate() {
        let mark = inline_builder.mark();
        let inline_base_inputs =
            inline_builder.try_push_copy(&kernel.round1_descriptors.base_field_inputs);
        let inline_ext_inputs =
            inline_builder.try_push_copy(&kernel.round1_descriptors.extension_field_inputs);

        let (record_mode, base_inputs, extension_inputs) =
            if let (Some(base_inputs), Some(extension_inputs)) =
                (inline_base_inputs, inline_ext_inputs)
            {
                (
                    GpuGKRMainLayerBatchRecordMode::InlineAll,
                    base_inputs,
                    extension_inputs,
                )
            } else {
                inline_builder.restore(mark);
                (
                    GpuGKRMainLayerBatchRecordMode::PointerDescriptors,
                    spill_builder.push_copy(&kernel.round1_descriptors.base_field_inputs),
                    spill_builder.push_copy(&kernel.round1_descriptors.extension_field_inputs),
                )
            };

        let (metadata_inline, quadratic_terms, linear_terms, constant_offset) = pack_metadata_block(
            kernel.constraint_metadata.as_ref(),
            &mut inline_builder,
            spill_builder,
        );

        batch.records[idx] = GpuGKRMainRound1BatchRecord {
            kind: kernel.kind.as_u32(),
            record_mode: match (record_mode, metadata_inline) {
                (GpuGKRMainLayerBatchRecordMode::InlineAll, true) => {
                    GpuGKRMainLayerBatchRecordMode::InlineAll
                }
                (GpuGKRMainLayerBatchRecordMode::InlineAll, false) => {
                    GpuGKRMainLayerBatchRecordMode::InlineNoMetadata
                }
                _ => GpuGKRMainLayerBatchRecordMode::PointerDescriptors,
            }
            .as_u32(),
            metadata_inline: metadata_inline as u32,
            _reserved: 0,
            base_inputs,
            extension_inputs,
            quadratic_terms,
            linear_terms,
            auxiliary_challenge: kernel.auxiliary_challenge,
            constant_offset,
        };
    }

    batch.inline_payload = inline_builder.into_bytes();
    batch
}

fn build_main_layer_round2_batch_template<E: Field>(
    folding_steps: usize,
    static_data: &[PreparedMainLayerKernelStaticData<E>],
    spill_builder: &mut SpillPayloadBuilder,
) -> GpuGKRMainRound2BatchStatic<E> {
    let mut batch = GpuGKRMainRound2BatchStatic::default();
    batch.record_count = static_data.len() as u32;
    let mut inline_builder = InlinePayloadBuilder::new();

    for (idx, kernel) in static_data.iter().enumerate() {
        let mark = inline_builder.mark();
        let inline_base_inputs =
            inline_builder.try_push_copy(&kernel.round2_descriptors.base_field_inputs);
        let inline_ext_inputs =
            inline_builder.try_push_copy(&kernel.round2_descriptors.extension_field_inputs);

        let (record_mode, base_inputs, extension_inputs) =
            if let (Some(base_inputs), Some(extension_inputs)) =
                (inline_base_inputs, inline_ext_inputs)
            {
                (
                    GpuGKRMainLayerBatchRecordMode::InlineAll,
                    base_inputs,
                    extension_inputs,
                )
            } else {
                inline_builder.restore(mark);
                (
                    GpuGKRMainLayerBatchRecordMode::PointerDescriptors,
                    spill_builder.push_copy(&kernel.round2_descriptors.base_field_inputs),
                    spill_builder.push_copy(&kernel.round2_descriptors.extension_field_inputs),
                )
            };

        let (metadata_inline, quadratic_terms, linear_terms, constant_offset) = pack_metadata_block(
            kernel.constraint_metadata.as_ref(),
            &mut inline_builder,
            spill_builder,
        );

        batch.records[idx] = GpuGKRMainRound2BatchRecord {
            kind: kernel.kind.as_u32(),
            record_mode: match (record_mode, metadata_inline) {
                (GpuGKRMainLayerBatchRecordMode::InlineAll, true) => {
                    GpuGKRMainLayerBatchRecordMode::InlineAll
                }
                (GpuGKRMainLayerBatchRecordMode::InlineAll, false) => {
                    GpuGKRMainLayerBatchRecordMode::InlineNoMetadata
                }
                _ => GpuGKRMainLayerBatchRecordMode::PointerDescriptors,
            }
            .as_u32(),
            metadata_inline: metadata_inline as u32,
            _reserved: 0,
            base_inputs,
            extension_inputs,
            quadratic_terms,
            linear_terms,
            auxiliary_challenge: kernel.auxiliary_challenge,
            constant_offset,
        };
    }

    batch.inline_payload = inline_builder.into_bytes();
    batch
}

fn build_main_layer_round3_batch_templates<E: Field>(
    folding_steps: usize,
    static_data: &[PreparedMainLayerKernelStaticData<E>],
    spill_builder: &mut SpillPayloadBuilder,
) -> Vec<GpuGKRMainLayerRound3BatchTemplate<E>> {
    let mut result = Vec::with_capacity(folding_steps.saturating_sub(3));
    for step in 3..folding_steps {
        let mut batch = GpuGKRMainRound3BatchStatic::default();
        batch.record_count = static_data.len() as u32;
        let mut inline_builder = InlinePayloadBuilder::new();

        for (idx, kernel) in static_data.iter().enumerate() {
            let descriptors = kernel
                .round3_descriptors
                .iter()
                .find(|descriptors| descriptors.step == step)
                .unwrap_or_else(|| panic!("missing round 3 descriptors for step {step}"));

            let mark = inline_builder.mark();
            let inline_base_inputs =
                inline_builder.try_push_copy(&descriptors.descriptors.base_field_inputs);
            let inline_ext_inputs =
                inline_builder.try_push_copy(&descriptors.descriptors.extension_field_inputs);

            let (record_mode, base_inputs, extension_inputs) =
                if let (Some(base_inputs), Some(extension_inputs)) =
                    (inline_base_inputs, inline_ext_inputs)
                {
                    (
                        GpuGKRMainLayerBatchRecordMode::InlineAll,
                        base_inputs,
                        extension_inputs,
                    )
                } else {
                    inline_builder.restore(mark);
                    (
                        GpuGKRMainLayerBatchRecordMode::PointerDescriptors,
                        spill_builder.push_copy(&descriptors.descriptors.base_field_inputs),
                        spill_builder.push_copy(&descriptors.descriptors.extension_field_inputs),
                    )
                };

            let (metadata_inline, quadratic_terms, linear_terms, constant_offset) =
                pack_metadata_block(
                    kernel.constraint_metadata.as_ref(),
                    &mut inline_builder,
                    spill_builder,
                );

            batch.records[idx] = GpuGKRMainRound3BatchRecord {
                kind: kernel.kind.as_u32(),
                record_mode: match (record_mode, metadata_inline) {
                    (GpuGKRMainLayerBatchRecordMode::InlineAll, true) => {
                        GpuGKRMainLayerBatchRecordMode::InlineAll
                    }
                    (GpuGKRMainLayerBatchRecordMode::InlineAll, false) => {
                        GpuGKRMainLayerBatchRecordMode::InlineNoMetadata
                    }
                    _ => GpuGKRMainLayerBatchRecordMode::PointerDescriptors,
                }
                .as_u32(),
                metadata_inline: metadata_inline as u32,
                _reserved: 0,
                base_inputs,
                extension_inputs,
                quadratic_terms,
                linear_terms,
                auxiliary_challenge: kernel.auxiliary_challenge,
                constant_offset,
            };
        }

        batch.inline_payload = inline_builder.into_bytes();
        result.push(GpuGKRMainLayerRound3BatchTemplate { step, batch });
    }
    result
}

fn build_main_layer_batch_templates<E: Field>(
    folding_steps: usize,
    static_data: &[PreparedMainLayerKernelStaticData<E>],
) -> (
    GpuGKRMainRound0BatchStatic<E>,
    GpuGKRMainRound1BatchStatic<E>,
    GpuGKRMainRound2BatchStatic<E>,
    Vec<GpuGKRMainLayerRound3BatchTemplate<E>>,
    Vec<u8>,
) {
    let mut spill_builder = SpillPayloadBuilder::default();
    let round0 =
        build_main_layer_round0_batch_template(folding_steps, static_data, &mut spill_builder);
    let round1 =
        build_main_layer_round1_batch_template(folding_steps, static_data, &mut spill_builder);
    let round2 =
        build_main_layer_round2_batch_template(folding_steps, static_data, &mut spill_builder);
    let round3 =
        build_main_layer_round3_batch_templates(folding_steps, static_data, &mut spill_builder);
    (round0, round1, round2, round3, spill_builder.bytes)
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
    constraint_batch_challenge: E,
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
            NoFieldGKRRelation::Copy { input, output } => {
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
            NoFieldGKRRelation::EnforceConstraintsMaxQuadratic { input } => {
                let relation =
                    BatchConstraintEvalGKRRelation::<BF, E>::new(input, constraint_batch_challenge);
                let constraint_metadata = GpuGKRMainLayerConstraintHostMetadata {
                    quadratic_terms: relation
                        .kernel
                        .quadratic_parts
                        .iter()
                        .map(
                            |((lhs, rhs), challenge)| GpuGKRMainLayerConstraintQuadraticTerm {
                                lhs: *lhs as u32,
                                rhs: *rhs as u32,
                                challenge: *challenge,
                            },
                        )
                        .collect(),
                    linear_terms: relation
                        .kernel
                        .linear_parts
                        .iter()
                        .map(|(input, challenge)| GpuGKRMainLayerConstraintLinearTerm {
                            input: *input as u32,
                            challenge: *challenge,
                        })
                        .collect(),
                    constant_offset: relation.kernel.constant_offset,
                };
                blueprints.push(
                    GpuGKRMainLayerKernelBlueprint {
                        kind: GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic,
                        inputs: <BatchConstraintEvalGKRRelation<BF, E> as BatchedGKRKernel<
                            BF,
                            E,
                        >>::get_inputs(&relation),
                        batch_challenge_offset: next_batch_challenge_offset,
                        batch_challenge_count: 1,
                        batch_challenges: {
                            next_batch_challenge_offset += 1;
                            vec![get_challenge()]
                        },
                        auxiliary_challenge_source:
                            GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(E::ZERO),
                        constraint_metadata_source: Some(
                            GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                        ),
                    },
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
            NoFieldGKRRelation::MaxQuadratic { .. }
            | NoFieldGKRRelation::UnbalancedGrandProductWithCache { .. } => {
                unimplemented!(
                    "unsupported GPU main-layer relation: {:?}",
                    gate.enforced_relation
                )
            }
        }
    }

    blueprints
}

fn build_main_layer_kernel_blueprints_static<E: Field + FieldExtension<BF>>(
    layer: &GKRLayerDescription,
    layer_idx: usize,
    storage: &GpuGKRStorage<BF, E>,
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
            NoFieldGKRRelation::Copy { input, output } => {
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(1, &mut next_batch_challenge_offset);
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
            NoFieldGKRRelation::EnforceConstraintsMaxQuadratic { input } => {
                let (inputs, constraint_metadata) =
                    build_constraints_max_quadratic_inputs_and_template(input);
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
                        GpuGKRMainLayerConstraintMetadataSource::Deferred(constraint_metadata),
                    ),
                });
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
            NoFieldGKRRelation::MaxQuadratic { .. }
            | NoFieldGKRRelation::UnbalancedGrandProductWithCache { .. } => {
                unimplemented!(
                    "unsupported GPU main-layer relation: {:?}",
                    gate.enforced_relation
                )
            }
        }
    }

    blueprints
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
        constraint_batch_challenge: E,
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
            constraint_batch_challenge,
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
            blueprints.len() <= GKR_BACKWARD_MAX_KERNELS_PER_LAYER,
            "fused dimension-reducing backward supports at most {} kernels per layer, got {}",
            GKR_BACKWARD_MAX_KERNELS_PER_LAYER,
            blueprints.len()
        );

        let mut round0_descriptors = Vec::with_capacity(blueprints.len());
        for blueprint in blueprints.iter() {
            round0_descriptors.push(self.storage.get_for_sumcheck_round_0(&blueprint.inputs));
        }

        let mut round1_prepared_all = Vec::with_capacity(blueprints.len());
        for blueprint in blueprints.iter() {
            round1_prepared_all.push(
                self.storage
                    .prepare_for_sumcheck_round_1(&blueprint.inputs, context)?,
            );
        }

        let mut round2_prepared_all = Vec::with_capacity(blueprints.len());
        for blueprint in blueprints.iter() {
            round2_prepared_all.push(if folding_steps >= 3 {
                Some(
                    self.storage
                        .prepare_for_sumcheck_round_2(&blueprint.inputs, context)?,
                )
            } else {
                None
            });
        }

        let mut round3_prepared_all = Vec::with_capacity(blueprints.len());
        round3_prepared_all.resize_with(blueprints.len(), Vec::new);
        for step in 3..folding_steps {
            for (prepared_for_kernel, blueprint) in
                round3_prepared_all.iter_mut().zip(blueprints.iter())
            {
                let prepared = self.storage.prepare_for_sumcheck_round_3_and_beyond(
                    &blueprint.inputs,
                    step,
                    context,
                )?;
                prepared_for_kernel.push(GpuGKRDimensionReducingRound3Prepared { step, prepared });
            }
        }

        let mut static_data = Vec::with_capacity(blueprints.len());
        let mut kernel_plans = Vec::with_capacity(blueprints.len());
        for (
            (((blueprint, round0_descriptors_for_kernel), round1_prepared), round2_prepared),
            round3_and_beyond_prepared,
        ) in blueprints
            .into_iter()
            .zip(round0_descriptors.iter())
            .zip(round1_prepared_all.into_iter())
            .zip(round2_prepared_all.into_iter())
            .zip(round3_prepared_all.into_iter())
        {
            let round1_descriptors = round1_prepared.build_launch_descriptors();
            let round2_descriptors = round2_prepared
                .as_ref()
                .map(GpuSumcheckRound2PreparedStorage::build_launch_descriptors);
            let round3_descriptors = round3_and_beyond_prepared
                .iter()
                .map(|round3| GpuGKRDimensionReducingRound3HostDescriptors {
                    step: round3.step,
                    descriptors: round3.prepared.build_launch_descriptors(),
                })
                .collect();

            static_data.push(PreparedDimensionReducingKernelStaticData {
                kind: blueprint.kind,
                batch_challenge_offset: blueprint.batch_challenge_offset,
                batch_challenge_count: blueprint.batch_challenge_count,
                round0_descriptors: GpuSumcheckRound0LaunchDescriptors {
                    base_field_inputs: Vec::new(),
                    extension_field_inputs: round0_descriptors_for_kernel
                        .extension_field_inputs
                        .clone(),
                    base_field_outputs: Vec::new(),
                    extension_field_outputs: round0_descriptors_for_kernel
                        .extension_field_outputs
                        .clone(),
                },
                round1_descriptors,
                round2_descriptors,
                round3_descriptors,
            });
            kernel_plans.push(GpuGKRDimensionReducingKernelPlan {
                kind: blueprint.kind,
                inputs: blueprint.inputs,
                batch_challenge_offset: blueprint.batch_challenge_offset,
                batch_challenge_count: blueprint.batch_challenge_count,
                batch_challenges: blueprint.batch_challenges,
                round1_prepared,
                round2_prepared,
                round3_and_beyond_prepared,
            });
        }

        let (
            round0_batch_template,
            round1_batch_template,
            round2_batch_template,
            round3_batch_templates,
            static_spill_bytes,
        ) = build_dimension_reducing_batch_templates(folding_steps, &static_data);

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
            round0_descriptors,
            round0_batch_template,
            round1_batch_template,
            round2_batch_template,
            round3_batch_templates,
            static_spill_bytes,
            round_scratch,
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

        let mut round1_prepared_all = Vec::with_capacity(blueprints.len());
        for blueprint in blueprints.iter() {
            round1_prepared_all.push(
                self.storage
                    .prepare_for_sumcheck_round_1(&blueprint.inputs, context)?,
            );
        }

        let mut round2_prepared_all = Vec::with_capacity(blueprints.len());
        for blueprint in blueprints.iter() {
            round2_prepared_all.push(
                self.storage
                    .prepare_for_sumcheck_round_2(&blueprint.inputs, context)?,
            );
        }

        let mut round3_prepared_all = Vec::with_capacity(blueprints.len());
        round3_prepared_all.resize_with(blueprints.len(), Vec::new);
        for step in 3..folding_steps {
            for (prepared_for_kernel, blueprint) in
                round3_prepared_all.iter_mut().zip(blueprints.iter())
            {
                let prepared = self.storage.prepare_for_sumcheck_round_3_and_beyond(
                    &blueprint.inputs,
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
                resolve_main_layer_constraint_metadata(
                    blueprint.constraint_metadata_source.clone(),
                    self.constraint_batch_challenge,
                )
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

        let (
            round0_batch_template,
            round1_batch_template,
            round2_batch_template,
            round3_batch_templates,
            static_spill_bytes,
        ) = build_main_layer_batch_templates(folding_steps, &static_data);

        // Build the flat round 0 plan from gate structure + constraint sources.
        // Works for both deferred (production) and immediate (test) paths.
        let flat_round0_template = {
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
            Some(super::backward_flat::build_flat_round0_plan(&gates))
        };

        // Compile recipes for device and allocate buffers for eval_recipes.
        // Recipe data is staged through pinned host memory via callbacks to avoid
        // pageable memory copies (which CUDA silently makes synchronous).
        let mut recipe_callbacks = Callbacks::new();
        let (
            flat_recipe_headers,
            flat_recipe_terms,
            flat_coeff_device_buf,
            flat_challenges_buf,
            flat_use_constant,
        ) = if let Some(ref plan) = flat_round0_template {
            let total = plan.total_coefficients();
            if total > 0 {
                let compiled = super::backward_flat::compile_recipes_for_device(&plan.recipes);
                let headers_host =
                    alloc_host_and_schedule_copy(context, &mut recipe_callbacks, compiled.headers);
                let mut headers_dev: DeviceAllocation<crate::ops::eval_recipes::GpuRecipeHeader> =
                    context.alloc(headers_host.len(), AllocationPlacement::BestFit)?;
                memory_copy_async(&mut headers_dev, &headers_host, context.get_exec_stream())?;
                drop(headers_host);
                let terms_dev = if compiled.terms.is_empty() {
                    context.alloc(1, AllocationPlacement::BestFit)?
                } else {
                    let terms_host = alloc_host_and_schedule_copy(
                        context,
                        &mut recipe_callbacks,
                        compiled.terms,
                    );
                    let mut d: DeviceAllocation<crate::ops::eval_recipes::GpuPrefactorTerm> =
                        context.alloc(terms_host.len(), AllocationPlacement::BestFit)?;
                    memory_copy_async(&mut d, &terms_host, context.get_exec_stream())?;
                    drop(terms_host);
                    d
                };
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
                let challenges_buf: DeviceAllocation<E> =
                    context.alloc(4, AllocationPlacement::BestFit)?;
                (
                    Some(headers_dev),
                    Some(terms_dev),
                    coeff_buf,
                    Some(challenges_buf),
                    use_constant,
                )
            } else {
                (None, None, None, None, true)
            }
        } else {
            (None, None, None, None, true)
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
            flat_continuation_descs,
            flat_cont_recipe_headers,
            flat_cont_recipe_terms,
            flat_cont_coeff_device_buf,
            flat_cont_use_constant,
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
        // Build combined unified tiled desc from the round1 desc.
        let flat_round1_unified_desc = if let (Some(ref r1_desc), Some(plan)) =
            (&flat_round1_desc, flat_continuation_plan.as_ref())
        {
            Some(super::backward_flat::build_unified_tiled_desc(
                r1_desc, plan,
            ))
        } else {
            None
        };
        let flat_round2_desc =
            Self::build_flat_round2_desc(flat_continuation_plan.as_ref(), &kernel_plans);
        // Build combined unified tiled desc for round 2.
        let flat_round2_unified_desc = if let (Some(ref r2_desc), Some(plan)) =
            (&flat_round2_desc, flat_continuation_plan.as_ref())
        {
            Some(super::backward_flat::build_round2_tiled_desc(r2_desc, plan))
        } else {
            None
        };
        // Build per-step unified tiled descs for round 3+ from the existing per-step
        // static descs. The term structure is shared via the continuation plan.
        let flat_continuation_unified_descs = if let Some(ref plan) = flat_continuation_plan {
            flat_continuation_descs
                .iter()
                .map(|(step, desc)| {
                    let unified = super::backward_flat::build_continuation_tiled_desc(desc, plan);
                    (*step, unified)
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
            constraint_batch_challenge: self.constraint_batch_challenge,
            kernel_plans,
            round0_descriptors,
            round0_batch_template,
            flat_round0_template,
            flat_recipe_headers,
            flat_recipe_terms,
            flat_coeff_device_buf,
            flat_challenges_buf,
            flat_use_constant,
            flat_continuation_plan,
            flat_continuation_descs,
            flat_cont_recipe_headers,
            flat_cont_recipe_terms,
            flat_cont_coeff_device_buf,
            flat_cont_use_constant,
            flat_round1_desc,
            flat_round1_unified_desc,
            flat_round2_desc,
            flat_round2_unified_desc,
            flat_continuation_unified_descs,
            round1_batch_template,
            round2_batch_template,
            round3_batch_templates,
            static_spill_bytes,
            round_scratch,
            recipe_upload_callbacks: recipe_callbacks,
        })
    }

    /// Build the flat round 1 static desc from the continuation plan and round 1 prepared storage.
    fn build_flat_round1_desc(
        plan: Option<&super::backward_flat::FlatContinuationBuildPlan<E>>,
        kernel_plans: &[GpuGKRMainLayerKernelPlan<E>],
    ) -> Option<Box<super::backward_flat::GpuFlatRound1StaticDesc>> {
        use super::backward_flat::{
            GpuFlatBaseAfterOneSourceEntry, GpuFlatContinuingSourceEntry, GpuFlatRound1StaticDesc,
            FLAT_CONT_EXT_SOURCE_BIT, FLAT_CONT_MAX_BASE_SOURCES, FLAT_CONT_MAX_EXT_SOURCES,
        };

        let plan = plan?;
        let mut desc = Box::new(GpuFlatRound1StaticDesc::default());

        // Copy term arrays from the continuation plan.
        desc.c0_only_linear[..plan.term_desc.num_c0_only_linear as usize].copy_from_slice(
            &plan.term_desc.c0_only_linear[..plan.term_desc.num_c0_only_linear as usize],
        );
        desc.num_c0_only_linear = plan.term_desc.num_c0_only_linear;
        desc.unified_quadratic[..plan.term_desc.num_unified_quadratic as usize].copy_from_slice(
            &plan.term_desc.unified_quadratic[..plan.term_desc.num_unified_quadratic as usize],
        );
        desc.num_unified_quadratic = plan.term_desc.num_unified_quadratic;
        desc.unified_linear[..plan.term_desc.num_unified_linear as usize].copy_from_slice(
            &plan.term_desc.unified_linear[..plan.term_desc.num_unified_linear as usize],
        );
        desc.num_unified_linear = plan.term_desc.num_unified_linear;
        desc.num_constants = plan.term_desc.num_constants;

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

        // Remap source indices in term arrays.
        for i in 0..desc.num_c0_only_linear as usize {
            let remap = idx_remap[desc.c0_only_linear[i].source_idx as usize];
            debug_assert!(remap != UNASSIGNED, "flat round1: missing source remap");
            desc.c0_only_linear[i].source_idx = remap;
        }
        for i in 0..desc.num_unified_quadratic as usize {
            let remap_a = idx_remap[desc.unified_quadratic[i].source_a as usize];
            let remap_b = idx_remap[desc.unified_quadratic[i].source_b as usize];
            debug_assert!(
                remap_a != UNASSIGNED && remap_b != UNASSIGNED,
                "flat round1: missing source remap",
            );
            desc.unified_quadratic[i].source_a = remap_a;
            desc.unified_quadratic[i].source_b = remap_b;
        }
        for i in 0..desc.num_unified_linear as usize {
            let remap = idx_remap[desc.unified_linear[i].source_idx as usize];
            debug_assert!(remap != UNASSIGNED, "flat round1: missing source remap");
            desc.unified_linear[i].source_idx = remap;
        }

        Some(desc)
    }

    /// Build the flat round 2 static desc from the continuation plan and round 2 prepared storage.
    fn build_flat_round2_desc(
        plan: Option<&super::backward_flat::FlatContinuationBuildPlan<E>>,
        kernel_plans: &[GpuGKRMainLayerKernelPlan<E>],
    ) -> Option<Box<super::backward_flat::GpuFlatRound2StaticDesc>> {
        use super::backward_flat::{
            GpuFlatBaseAfterTwoSourceEntry, GpuFlatContinuingSourceEntry, GpuFlatRound2StaticDesc,
            FLAT_CONT_EXT_SOURCE_BIT, FLAT_CONT_MAX_BASE_SOURCES, FLAT_CONT_MAX_EXT_SOURCES,
        };

        let plan = plan?;
        let mut desc = Box::new(GpuFlatRound2StaticDesc::default());

        // Copy term arrays.
        desc.c0_only_linear[..plan.term_desc.num_c0_only_linear as usize].copy_from_slice(
            &plan.term_desc.c0_only_linear[..plan.term_desc.num_c0_only_linear as usize],
        );
        desc.num_c0_only_linear = plan.term_desc.num_c0_only_linear;
        desc.unified_quadratic[..plan.term_desc.num_unified_quadratic as usize].copy_from_slice(
            &plan.term_desc.unified_quadratic[..plan.term_desc.num_unified_quadratic as usize],
        );
        desc.num_unified_quadratic = plan.term_desc.num_unified_quadratic;
        desc.unified_linear[..plan.term_desc.num_unified_linear as usize].copy_from_slice(
            &plan.term_desc.unified_linear[..plan.term_desc.num_unified_linear as usize],
        );
        desc.num_unified_linear = plan.term_desc.num_unified_linear;
        desc.num_constants = plan.term_desc.num_constants;

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

        // Remap source indices.
        for i in 0..desc.num_c0_only_linear as usize {
            let remap = idx_remap[desc.c0_only_linear[i].source_idx as usize];
            debug_assert!(remap != UNASSIGNED, "flat round2: missing source remap");
            desc.c0_only_linear[i].source_idx = remap;
        }
        for i in 0..desc.num_unified_quadratic as usize {
            let remap_a = idx_remap[desc.unified_quadratic[i].source_a as usize];
            let remap_b = idx_remap[desc.unified_quadratic[i].source_b as usize];
            debug_assert!(
                remap_a != UNASSIGNED && remap_b != UNASSIGNED,
                "flat round2: missing source remap",
            );
            desc.unified_quadratic[i].source_a = remap_a;
            desc.unified_quadratic[i].source_b = remap_b;
        }
        for i in 0..desc.num_unified_linear as usize {
            let remap = idx_remap[desc.unified_linear[i].source_idx as usize];
            debug_assert!(remap != UNASSIGNED, "flat round2: missing source remap");
            desc.unified_linear[i].source_idx = remap;
        }

        Some(desc)
    }

    /// Build flat continuation artifacts for round 3+ kernel dispatch.
    #[allow(clippy::type_complexity)]
    fn build_flat_continuation_artifacts(
        &self,
        static_data: &[PreparedMainLayerKernelStaticData<E>],
        kernel_plans: &[GpuGKRMainLayerKernelPlan<E>],
        folding_steps: usize,
        layer_idx: usize,
        context: &ProverContext,
    ) -> CudaResult<(
        Option<super::backward_flat::FlatContinuationBuildPlan<E>>,
        Vec<(
            usize,
            Box<super::backward_flat::GpuFlatContinuationStaticDesc>,
        )>,
        Option<DeviceAllocation<crate::ops::eval_recipes::GpuRecipeHeader>>,
        Option<DeviceAllocation<crate::ops::eval_recipes::GpuPrefactorTerm>>,
        Option<DeviceAllocation<E>>,
        bool,
        Callbacks<'static>,
    )> {
        use super::backward_flat::{
            build_flat_continuation_plan, compile_recipes_for_device,
            GpuFlatContinuationStaticDesc, GpuFlatContinuingSourceEntry,
            PreparedGateForFlatContinuationPlan, FLAT_CONT_CONST_MAX,
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
            return Ok((Some(plan), vec![], None, None, None, true, Callbacks::new()));
        }

        // Compile recipes for device (same as round 0 flow).
        // Stage through pinned host memory via callbacks to avoid pageable copies.
        let compiled = compile_recipes_for_device(&plan.recipes);
        let stream = context.get_exec_stream();
        let mut cont_recipe_callbacks = Callbacks::new();
        let headers_host =
            alloc_host_and_schedule_copy(context, &mut cont_recipe_callbacks, compiled.headers);
        let mut headers_dev: DeviceAllocation<crate::ops::eval_recipes::GpuRecipeHeader> =
            context.alloc(headers_host.len(), AllocationPlacement::BestFit)?;
        memory_copy_async(&mut headers_dev, &headers_host, stream)?;
        drop(headers_host);
        let terms_dev = if compiled.terms.is_empty() {
            context.alloc(1, AllocationPlacement::BestFit)?
        } else {
            let terms_host =
                alloc_host_and_schedule_copy(context, &mut cont_recipe_callbacks, compiled.terms);
            let mut d: DeviceAllocation<crate::ops::eval_recipes::GpuPrefactorTerm> =
                context.alloc(terms_host.len(), AllocationPlacement::BestFit)?;
            memory_copy_async(&mut d, &terms_host, stream)?;
            drop(terms_host);
            d
        };
        let mut use_constant = !self.is_delegation || layer_idx != 0;
        if use_constant && total > FLAT_CONT_CONST_MAX {
            use_constant = false;
        }
        let coeff_buf = if use_constant {
            None
        } else {
            Some(context.alloc(total, AllocationPlacement::BestFit)?)
        };

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
        let mut per_step_descs = Vec::new();
        for step in first_step..folding_steps {
            let mut desc = *plan.term_desc.clone();
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
                desc.sources[assignment.source_table_idx as usize] = GpuFlatContinuingSourceEntry {
                    previous_layer_start: if combined_first_access {
                        src_plan.previous_layer_start as *const u8
                    } else {
                        std::ptr::null()
                    },
                    this_layer_cache_start: src_plan.this_layer_start as *mut u8,
                };
            }
            per_step_descs.push((step, Box::new(desc)));
        }

        Ok((
            Some(plan),
            per_step_descs,
            Some(headers_dev),
            Some(terms_dev),
            coeff_buf,
            use_constant,
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
            self.constraint_batch_challenge,
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
            &self.storage,
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

    pub(crate) fn round0_descriptors(&self) -> &[GpuSumcheckRound0LaunchDescriptors<B, E>] {
        &self.round0_descriptors
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

#[derive(Clone)]
struct PackedMainLayerBatchChallengeSpec<E> {
    kind: GpuGKRMainLayerKernelKind,
    batch_challenge_offset: usize,
    batch_challenges: Vec<E>,
}

fn packed_main_layer_batch_challenge_specs<E: Clone>(
    kernel_plans: &[GpuGKRMainLayerKernelPlan<E>],
) -> Vec<PackedMainLayerBatchChallengeSpec<E>> {
    kernel_plans
        .iter()
        .map(|kernel| PackedMainLayerBatchChallengeSpec {
            kind: kernel.kind,
            batch_challenge_offset: kernel.batch_challenge_offset,
            batch_challenges: kernel.batch_challenges.clone(),
        })
        .collect()
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

fn fill_packed_main_layer_batch_challenges_from_specs<E: Field>(
    specs: &[PackedMainLayerBatchChallengeSpec<E>],
    batch_challenge_base: E,
    dst: &mut [E],
) {
    let expected_len = specs
        .iter()
        .map(|spec| main_layer_kind_batch_challenge_count(spec.kind))
        .sum::<usize>();
    assert_eq!(dst.len(), expected_len);
    let mut packed_offset = 0usize;
    for spec in specs.iter() {
        let count = main_layer_kind_batch_challenge_count(spec.kind);
        assert_eq!(
            spec.batch_challenge_offset, packed_offset,
            "main-layer batch challenges must stay densely packed in record order"
        );
        let dst_slice = &mut dst[packed_offset..packed_offset + count];
        if spec.batch_challenges.is_empty() {
            let mut challenge = field_pow(batch_challenge_base, spec.batch_challenge_offset);
            for dst in dst_slice.iter_mut() {
                *dst = challenge;
                challenge.mul_assign(&batch_challenge_base);
            }
        } else {
            assert_eq!(
                spec.batch_challenges.len(),
                count,
                "kernel {:?} materialized unexpected batch-challenge count",
                spec.kind
            );
            dst_slice.copy_from_slice(&spec.batch_challenges);
        }
        packed_offset += count;
    }
}

fn pack_main_layer_batch_challenges<E: Field>(
    kernel_plans: &[GpuGKRMainLayerKernelPlan<E>],
    batch_challenge_base: E,
) -> Vec<E> {
    let mut packed = vec![E::ZERO; packed_main_layer_batch_challenge_len(kernel_plans)];
    fill_packed_main_layer_batch_challenges(kernel_plans, batch_challenge_base, &mut packed);
    packed
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
    E: Field + FieldExtension<BF> + Reduce + GpuDimensionReducingKernelSet,
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
        unsafe {
            self.round_scratch
                .claim_point
                .as_ptr()
                .add(self.folding_steps)
        }
    }

    fn compute_combined_claim_with_batch_base(
        &self,
        output_claims: &BTreeMap<GKRAddress, E>,
        batch_challenge_base: E,
    ) -> E {
        let mut result = E::ZERO;
        for kernel in self.kernel_plans.iter() {
            let mut challenge = field_pow(batch_challenge_base, kernel.batch_challenge_offset);
            for output in kernel.inputs.outputs_in_extension.iter() {
                let mut term = output_claims
                    .get(output)
                    .copied()
                    .unwrap_or_else(|| panic!("missing output claim for {output:?}"));
                term.mul_assign(&challenge);
                result.add_assign(&term);
                challenge.mul_assign(&batch_challenge_base);
            }
        }

        result
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
        static_spill_upload: Option<&ScheduledUpload<u8>>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let mut batch = self.round0_batch_template;
        batch.eq_values = self.round_scratch.eq_values.as_ptr();
        batch.batch_challenge_base = self.batch_challenge_base_ptr();
        batch.contributions = self.round_scratch.accumulator.as_mut_ptr();
        batch.spill_payload = static_spill_upload
            .map(|upload| upload.device.as_ptr())
            .unwrap_or(null());
        launch_dim_reducing_round0_batched(&batch, acc_size, context)
    }

    fn launch_round1_kernels(
        &mut self,
        folding_challenge: &ScheduledChallengeBuffer<E>,
        acc_size: usize,
        explicit_form: bool,
        static_spill_upload: Option<&ScheduledUpload<u8>>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let mut batch = self.round1_batch_template;
        batch.eq_values = self.round_scratch.eq_values.as_ptr();
        batch.batch_challenge_base = self.batch_challenge_base_ptr();
        batch.folding_challenge = folding_challenge.as_ptr();
        batch.contributions = self.round_scratch.accumulator.as_mut_ptr();
        batch.spill_payload = static_spill_upload
            .map(|upload| upload.device.as_ptr())
            .unwrap_or(null());
        batch.explicit_form = explicit_form;
        launch_dim_reducing_round1_batched(&batch, acc_size, context)
    }

    fn launch_round2_kernels(
        &mut self,
        folding_challenge: &ScheduledChallengeBuffer<E>,
        acc_size: usize,
        explicit_form: bool,
        static_spill_upload: Option<&ScheduledUpload<u8>>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let mut batch = self
            .round2_batch_template
            .expect("round 2 batch template must be present");
        batch.eq_values = self.round_scratch.eq_values.as_ptr();
        batch.batch_challenge_base = self.batch_challenge_base_ptr();
        batch.folding_challenge = folding_challenge.as_ptr();
        batch.contributions = self.round_scratch.accumulator.as_mut_ptr();
        batch.spill_payload = static_spill_upload
            .map(|upload| upload.device.as_ptr())
            .unwrap_or(null());
        batch.explicit_form = explicit_form;
        launch_dim_reducing_round2_batched(&batch, acc_size, context)
    }

    fn launch_round3_kernels(
        &mut self,
        step: usize,
        folding_challenge: &ScheduledChallengeBuffer<E>,
        acc_size: usize,
        explicit_form: bool,
        static_spill_upload: Option<&ScheduledUpload<u8>>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let mut batch = self
            .round3_batch_templates
            .iter()
            .find(|template| template.step == step)
            .unwrap_or_else(|| {
                panic!("missing dimension-reducing round 3 template for step {step}")
            })
            .batch;
        batch.eq_values = self.round_scratch.eq_values.as_ptr();
        batch.batch_challenge_base = self.batch_challenge_base_ptr();
        batch.folding_challenge = folding_challenge.as_ptr();
        batch.contributions = self.round_scratch.accumulator.as_mut_ptr();
        batch.spill_payload = static_spill_upload
            .map(|upload| upload.device.as_ptr())
            .unwrap_or(null());
        batch.explicit_form = explicit_form;
        launch_dim_reducing_round3_batched(&batch, acc_size, context)
    }

    fn schedule_round_coefficients_reduction(
        &mut self,
        step: usize,
        acc_size: usize,
        context: &ProverContext,
    ) -> CudaResult<HostAllocation<[E]>> {
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

        let mut reduction_host = unsafe { context.alloc_host_uninit_slice(2) };
        memory_copy_async(
            &mut reduction_host,
            &self.round_scratch.reduction_output,
            context.get_exec_stream(),
        )?;
        Ok(reduction_host)
    }

    fn schedule_device_values_readback_from_raw_ptr(
        &self,
        ptr: *const E,
        len: usize,
        context: &ProverContext,
    ) -> CudaResult<HostAllocation<[E]>> {
        let device = unsafe { DeviceSlice::from_raw_parts(ptr, len) };
        let mut host = unsafe { context.alloc_host_uninit_slice(len) };
        memory_copy_async(&mut host, device, context.get_exec_stream())?;
        Ok(host)
    }

    fn evaluate_with_two_variable_eq_ext(values: &[E; 4], r_before_last: E, r_last: E) -> E {
        let mut result = E::ZERO;

        let mut w00 = E::ONE;
        w00.sub_assign(&r_before_last);
        let mut tmp = E::ONE;
        tmp.sub_assign(&r_last);
        w00.mul_assign(&tmp);
        let mut term = values[0];
        term.mul_assign(&w00);
        result.add_assign(&term);

        let mut w01 = E::ONE;
        w01.sub_assign(&r_before_last);
        w01.mul_assign(&r_last);
        let mut term = values[1];
        term.mul_assign(&w01);
        result.add_assign(&term);

        let mut w10 = r_before_last;
        let mut tmp = E::ONE;
        tmp.sub_assign(&r_last);
        w10.mul_assign(&tmp);
        let mut term = values[2];
        term.mul_assign(&w10);
        result.add_assign(&term);

        let mut w11 = r_before_last;
        w11.mul_assign(&r_last);
        let mut term = values[3];
        term.mul_assign(&w11);
        result.add_assign(&term);

        result
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

    fn schedule_last_evaluations_readback(
        &self,
        last_step: usize,
        context: &ProverContext,
    ) -> CudaResult<BTreeMap<GKRAddress, HostAllocation<[E]>>> {
        let mut result = BTreeMap::new();
        for (address, ptr) in self.final_evaluation_sources_for_last_step(last_step) {
            result.insert(
                address,
                self.schedule_device_values_readback_from_raw_ptr(ptr, 4, context)?,
            );
        }
        Ok(result)
    }

    pub(crate) fn schedule_execute_dimension_reducing_layer(
        &mut self,
        output_layer_claims: &BTreeMap<GKRAddress, E>,
        previous_claim_point: &[E],
        seed: Seed,
        batch_challenge_base: E,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRDimensionReducingScheduledLayerExecution<B, E>> {
        assert_eq!(
            previous_claim_point.len(),
            self.folding_steps,
            "dimension-reducing claim point must match folding steps"
        );
        if let Some(prepared_base) = self.batch_challenge_base {
            assert_eq!(
                prepared_base, batch_challenge_base,
                "dimension-reducing execution batching challenge must match prepared layer state"
            );
        }

        let last_step = self.folding_steps - 1;
        let static_spill_upload = schedule_static_spill_upload(context, &self.static_spill_bytes)?;
        let mut round_challenge_buffers = Vec::with_capacity(last_step);
        let mut round_challenge_storage = if last_step == 0 {
            None
        } else {
            Some(ScheduledChallengeStorage::new(
                context.alloc(last_step, AllocationPlacement::Top)?,
            ))
        };
        let mut start_callbacks = Callbacks::new();
        let mut claim_point_values = previous_claim_point.to_vec();
        claim_point_values.push(batch_challenge_base);
        let claim_point_host =
            alloc_host_and_schedule_copy(context, &mut start_callbacks, claim_point_values);
        let eq_pair_values_host = alloc_host_and_schedule_copy(
            context,
            &mut start_callbacks,
            make_round0_eq_pair_values(previous_claim_point),
        );
        memory_copy_async(
            &mut self.round_scratch.claim_point,
            &claim_point_host,
            context.get_exec_stream(),
        )?;
        self.build_round0_eq_values(&eq_pair_values_host, context)?;
        drop(claim_point_host);
        drop(eq_pair_values_host);

        let mut shared_state = Box::new(ScheduledDimensionReducingLayerExecutionState {
            seed,
            claim: self.compute_combined_claim(output_layer_claims),
            eq_prefactor: E::ONE,
            folding_challenges: Vec::with_capacity(self.folding_steps + 1),
            internal_round_coefficients: Vec::with_capacity(self.folding_steps - 1),
            result: None,
        });
        let shared_state_handle =
            crate::primitives::context::UnsafeMutAccessor::new(shared_state.as_mut());
        let mut reduction_states = Vec::with_capacity(last_step);

        for step in 0..last_step {
            let acc_size = 1usize << (self.folding_steps - step - 1);
            if step == 0 {
                self.launch_round0_kernels(acc_size, static_spill_upload.as_ref(), context)?;
            } else {
                match step {
                    1 => self.launch_round1_kernels(
                        &round_challenge_buffers[step - 1],
                        acc_size,
                        false,
                        static_spill_upload.as_ref(),
                        context,
                    )?,
                    2 => self.launch_round2_kernels(
                        &round_challenge_buffers[step - 1],
                        acc_size,
                        false,
                        static_spill_upload.as_ref(),
                        context,
                    )?,
                    _ => self.launch_round3_kernels(
                        step,
                        &round_challenge_buffers[step - 1],
                        acc_size,
                        false,
                        static_spill_upload.as_ref(),
                        context,
                    )?,
                }
            }
            let reduction_output =
                self.schedule_round_coefficients_reduction(step, acc_size, context)?;
            self.fold_eq_values_for_next_round(acc_size, context)?;
            let reduction_accessor = reduction_output.get_accessor();
            let next_round_challenges_offset = if step < last_step { Some(step) } else { None };
            let shared_state_for_callback = shared_state_handle;
            let previous_claim_coord = previous_claim_point[step];
            let callback = move |dst: &mut [E]| {
                debug_assert_eq!(dst.len(), 1);
                unsafe {
                    let reduction = reduction_accessor.get();
                    let c0 = reduction[0];
                    let c2 = reduction[1];
                    let state = shared_state_for_callback.get_mut();
                    let mut normalized_claim = state.claim;
                    normalized_claim.mul_assign(
                        &state
                            .eq_prefactor
                            .inverse()
                            .expect("eq prefactor must be non-zero"),
                    );
                    let coeffs = output_univariate_monomial_form_max_quadratic::<BF, E>(
                        previous_claim_coord,
                        normalized_claim,
                        c0,
                        c2,
                    );
                    commit_field_els(&mut state.seed, &coeffs);
                    state.internal_round_coefficients.push(coeffs);

                    let folding_challenge = draw_random_field_els::<BF, E>(&mut state.seed, 1)[0];
                    state.claim =
                        evaluate_small_univariate_poly::<BF, E, _>(&coeffs, &folding_challenge);
                    state.eq_prefactor =
                        evaluate_eq_poly::<BF, E>(&folding_challenge, &previous_claim_coord);
                    state.folding_challenges.push(folding_challenge);
                    dst[0] = folding_challenge;
                }
            };
            let callbacks = if let (Some(storage), Some(offset)) = (
                round_challenge_storage.as_mut(),
                next_round_challenges_offset,
            ) {
                round_challenge_buffers.push(schedule_packed_round_challenge_upload(
                    context,
                    storage.device_accessor(),
                    &mut storage.callbacks,
                    offset,
                    1,
                    callback,
                )?);
                Callbacks::new()
            } else {
                let mut callbacks = Callbacks::new();
                callbacks.schedule(
                    move || {
                        let mut tmp = [E::ZERO; 1];
                        callback(&mut tmp);
                    },
                    context.get_exec_stream(),
                )?;
                callbacks
            };
            drop(reduction_output);
            reduction_states.push(ScheduledDimensionReducingReductionState {
                callbacks,
                _phantom: std::marker::PhantomData,
            });
        }

        match last_step {
            1 => self.launch_round1_kernels(
                &round_challenge_buffers[last_step - 1],
                1,
                true,
                static_spill_upload.as_ref(),
                context,
            )?,
            2 => self.launch_round2_kernels(
                &round_challenge_buffers[last_step - 1],
                1,
                true,
                static_spill_upload.as_ref(),
                context,
            )?,
            step => self.launch_round3_kernels(
                step,
                &round_challenge_buffers[last_step - 1],
                1,
                true,
                static_spill_upload.as_ref(),
                context,
            )?,
        }
        let final_evaluations = self.schedule_last_evaluations_readback(last_step, context)?;
        let final_evaluation_accessors: Vec<_> = final_evaluations
            .iter()
            .map(|(addr, values)| (*addr, values.get_accessor()))
            .collect();
        let shared_state_for_callback = shared_state_handle;
        let folding_steps = self.folding_steps;
        let mut final_readback_callbacks = Callbacks::new();
        final_readback_callbacks.schedule(
            move || unsafe {
                let mut last_evaluations = BTreeMap::new();
                for (address, accessor) in final_evaluation_accessors.iter() {
                    let values: [E; 4] = accessor.get().try_into().unwrap();
                    last_evaluations.insert(*address, values);
                }

                let transcript_inputs: Vec<E> = last_evaluations
                    .values()
                    .flat_map(|values| values.iter().copied())
                    .collect();
                let state = shared_state_for_callback.get_mut();
                commit_field_els(&mut state.seed, &transcript_inputs);

                let challenges = draw_random_field_els::<BF, E>(&mut state.seed, 3);
                let [r_before_last, r_last, next_batching_challenge]: [E; 3] =
                    challenges.try_into().unwrap();
                let mut new_claim_point = state.folding_challenges.clone();
                new_claim_point.push(r_before_last);
                new_claim_point.push(r_last);

                let new_claims = last_evaluations
                    .iter()
                    .map(|(addr, values)| {
                        (
                            *addr,
                            Self::evaluate_with_two_variable_eq_ext(values, r_before_last, r_last),
                        )
                    })
                    .collect();

                let proof = SumcheckIntermediateProofValues::<BF, E> {
                    sumcheck_num_rounds: folding_steps,
                    internal_round_coefficients: state.internal_round_coefficients.clone(),
                    final_step_evaluations: last_evaluations
                        .iter()
                        .map(|(addr, values)| (*addr, values.to_vec()))
                        .collect(),
                    extra_evaluations_from_caching_relations: BTreeMap::new(),
                    _marker: core::marker::PhantomData,
                };

                state.result = Some(GpuGKRDimensionReducingLayerExecution {
                    proof,
                    new_claims,
                    new_claim_point,
                    next_batching_challenge,
                    updated_seed: state.seed,
                });
            },
            context.get_exec_stream(),
        )?;

        Ok(GpuGKRDimensionReducingScheduledLayerExecution {
            tracing_ranges: Vec::new(),
            start_callbacks,
            static_spill_upload,
            round_challenge_storage,
            round_challenge_buffers,
            reduction_states,
            final_readback: {
                drop(final_evaluations);
                ScheduledDimensionReducingFinalReadback {
                    callbacks: final_readback_callbacks,
                    _phantom: std::marker::PhantomData,
                }
            },
            shared_state,
            _phantom: std::marker::PhantomData,
        })
    }

    pub(crate) fn schedule_execute_dimension_reducing_layer_from_workflow_state(
        &mut self,
        workflow_state: ScheduledBackwardWorkflowStateHandle<E>,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRDimensionReducingScheduledLayerExecution<B, E>> {
        let stream = context.get_exec_stream();
        let mut tracing_ranges = Vec::new();
        let layer_name = format!("gkr.backward.dimension_reducing.layer.{}", self.layer_idx);
        let layer_range = Range::new(layer_name.clone())?;
        layer_range.start(stream)?;
        let last_step = self.folding_steps - 1;
        let mut start_callbacks = Callbacks::new();
        let static_spill_upload = schedule_static_spill_upload(context, &self.static_spill_bytes)?;
        let mut shared_state = Box::new(ScheduledDimensionReducingLayerExecutionState {
            seed: Seed::default(),
            claim: E::ZERO,
            eq_prefactor: E::ONE,
            folding_challenges: Vec::with_capacity(self.folding_steps + 1),
            internal_round_coefficients: Vec::with_capacity(self.folding_steps - 1),
            result: None,
        });
        let shared_state_handle =
            crate::primitives::context::UnsafeMutAccessor::new(shared_state.as_mut());

        let mut claim_point_host =
            unsafe { context.alloc_host_uninit_slice(self.folding_steps + 1) };
        let claim_point_accessor = claim_point_host.get_mut_accessor();
        let mut eq_pair_values_host = unsafe {
            context.alloc_host_uninit_slice(round0_eq_pair_values_len(self.folding_steps))
        };
        let eq_pair_values_accessor = eq_pair_values_host.get_mut_accessor();
        let workflow_state_for_start = workflow_state;
        let shared_state_for_start = shared_state_handle;
        let layer_claim_callback = self
            .kernel_plans
            .iter()
            .map(|kernel| {
                (
                    kernel.batch_challenge_offset,
                    kernel.inputs.outputs_in_extension.clone(),
                )
            })
            .collect::<Vec<_>>();
        start_callbacks.schedule(
            move || unsafe {
                let workflow_state = workflow_state_for_start.get();
                let dst = claim_point_accessor.get_mut();
                let claim_len = dst.len() - 1;
                dst[..claim_len].copy_from_slice(&workflow_state.current_claim_point);
                dst[claim_len] = workflow_state.current_batching_challenge;
                fill_round0_eq_pair_values(
                    eq_pair_values_accessor.get_mut(),
                    &workflow_state.current_claim_point,
                );
                let layer_state = shared_state_for_start.get_mut();
                layer_state.seed = workflow_state.seed;
                layer_state.claim = {
                    let mut result = E::ZERO;
                    for (offset, outputs) in layer_claim_callback.iter() {
                        let mut challenge =
                            field_pow(workflow_state.current_batching_challenge, *offset);
                        for output in outputs.iter() {
                            let mut term = workflow_state
                                .current_claims
                                .get(output)
                                .copied()
                                .unwrap_or_else(|| panic!("missing output claim for {output:?}"));
                            term.mul_assign(&challenge);
                            result.add_assign(&term);
                            challenge.mul_assign(&workflow_state.current_batching_challenge);
                        }
                    }
                    result
                };
                layer_state.eq_prefactor = E::ONE;
                layer_state.folding_challenges.clear();
                layer_state.internal_round_coefficients.clear();
            },
            stream,
        )?;
        memory_copy_async(
            &mut self.round_scratch.claim_point,
            &claim_point_host,
            stream,
        )?;
        self.build_round0_eq_values(&eq_pair_values_host, context)?;
        let mut round_challenge_buffers = Vec::with_capacity(last_step);
        let mut round_challenge_storage = if last_step == 0 {
            None
        } else {
            Some(ScheduledChallengeStorage::new(
                context.alloc(last_step, AllocationPlacement::Top)?,
            ))
        };
        let mut reduction_states = Vec::with_capacity(last_step);

        for step in 0..last_step {
            let acc_size = 1usize << (self.folding_steps - step - 1);
            if step == 0 {
                self.launch_round0_kernels(acc_size, static_spill_upload.as_ref(), context)?;
            } else {
                match step {
                    1 => self.launch_round1_kernels(
                        &round_challenge_buffers[step - 1],
                        acc_size,
                        false,
                        static_spill_upload.as_ref(),
                        context,
                    )?,
                    2 => self.launch_round2_kernels(
                        &round_challenge_buffers[step - 1],
                        acc_size,
                        false,
                        static_spill_upload.as_ref(),
                        context,
                    )?,
                    _ => self.launch_round3_kernels(
                        step,
                        &round_challenge_buffers[step - 1],
                        acc_size,
                        false,
                        static_spill_upload.as_ref(),
                        context,
                    )?,
                }
            }

            let reduction_output =
                self.schedule_round_coefficients_reduction(step, acc_size, context)?;
            self.fold_eq_values_for_next_round(acc_size, context)?;
            let reduction_accessor = reduction_output.get_accessor();
            let next_round_challenges_offset = if step < last_step { Some(step) } else { None };
            let shared_state_for_callback = shared_state_handle;
            let previous_claim_coord_idx = step;
            let claim_point_for_callback = workflow_state;
            let callback = move |dst: &mut [E]| unsafe {
                debug_assert_eq!(dst.len(), 1);
                let reduction = reduction_accessor.get();
                let c0 = reduction[0];
                let c2 = reduction[1];
                let previous_claim_coord =
                    claim_point_for_callback.get().current_claim_point[previous_claim_coord_idx];
                let state = shared_state_for_callback.get_mut();
                let mut normalized_claim = state.claim;
                normalized_claim.mul_assign(
                    &state
                        .eq_prefactor
                        .inverse()
                        .expect("eq prefactor must be non-zero"),
                );
                let coeffs = output_univariate_monomial_form_max_quadratic::<BF, E>(
                    previous_claim_coord,
                    normalized_claim,
                    c0,
                    c2,
                );
                commit_field_els(&mut state.seed, &coeffs);
                state.internal_round_coefficients.push(coeffs);

                let folding_challenge = draw_random_field_els::<BF, E>(&mut state.seed, 1)[0];
                state.claim =
                    evaluate_small_univariate_poly::<BF, E, _>(&coeffs, &folding_challenge);
                state.eq_prefactor =
                    evaluate_eq_poly::<BF, E>(&folding_challenge, &previous_claim_coord);
                state.folding_challenges.push(folding_challenge);
                dst[0] = folding_challenge;
            };
            let callbacks = if let (Some(storage), Some(offset)) = (
                round_challenge_storage.as_mut(),
                next_round_challenges_offset,
            ) {
                round_challenge_buffers.push(schedule_packed_round_challenge_upload(
                    context,
                    storage.device_accessor(),
                    &mut storage.callbacks,
                    offset,
                    1,
                    callback,
                )?);
                Callbacks::new()
            } else {
                let mut callbacks = Callbacks::new();
                callbacks.schedule(
                    move || {
                        let mut tmp = [E::ZERO; 1];
                        callback(&mut tmp);
                    },
                    stream,
                )?;
                callbacks
            };
            drop(reduction_output);
            reduction_states.push(ScheduledDimensionReducingReductionState {
                callbacks,
                _phantom: std::marker::PhantomData,
            });
        }

        match last_step {
            1 => self.launch_round1_kernels(
                &round_challenge_buffers[last_step - 1],
                1,
                true,
                static_spill_upload.as_ref(),
                context,
            )?,
            2 => self.launch_round2_kernels(
                &round_challenge_buffers[last_step - 1],
                1,
                true,
                static_spill_upload.as_ref(),
                context,
            )?,
            step => self.launch_round3_kernels(
                step,
                &round_challenge_buffers[last_step - 1],
                1,
                true,
                static_spill_upload.as_ref(),
                context,
            )?,
        }
        let final_evaluations = self.schedule_last_evaluations_readback(last_step, context)?;
        let final_evaluation_accessors: Vec<_> = final_evaluations
            .iter()
            .map(|(addr, values)| (*addr, values.get_accessor()))
            .collect();
        let shared_state_for_callback = shared_state_handle;
        let workflow_state_for_callback = workflow_state;
        let folding_steps = self.folding_steps;
        let layer_idx = self.layer_idx;
        let mut final_readback_callbacks = Callbacks::new();
        final_readback_callbacks.schedule(
            move || unsafe {
                let mut last_evaluations = BTreeMap::new();
                for (address, accessor) in final_evaluation_accessors.iter() {
                    let values: [E; 4] = accessor.get().try_into().unwrap();
                    last_evaluations.insert(*address, values);
                }

                let transcript_inputs: Vec<E> = last_evaluations
                    .values()
                    .flat_map(|values| values.iter().copied())
                    .collect();
                let state = shared_state_for_callback.get_mut();
                commit_field_els(&mut state.seed, &transcript_inputs);

                let challenges = draw_random_field_els::<BF, E>(&mut state.seed, 3);
                let [r_before_last, r_last, next_batching_challenge]: [E; 3] =
                    challenges.try_into().unwrap();
                let mut new_claim_point = state.folding_challenges.clone();
                new_claim_point.push(r_before_last);
                new_claim_point.push(r_last);

                let new_claims = last_evaluations
                    .iter()
                    .map(|(addr, values)| {
                        (
                            *addr,
                            Self::evaluate_with_two_variable_eq_ext(values, r_before_last, r_last),
                        )
                    })
                    .collect::<BTreeMap<_, _>>();

                let proof = SumcheckIntermediateProofValues::<BF, E> {
                    sumcheck_num_rounds: folding_steps,
                    internal_round_coefficients: state.internal_round_coefficients.clone(),
                    final_step_evaluations: last_evaluations
                        .iter()
                        .map(|(addr, values)| (*addr, values.to_vec()))
                        .collect(),
                    extra_evaluations_from_caching_relations: BTreeMap::new(),
                    _marker: core::marker::PhantomData,
                };

                {
                    let workflow_state = workflow_state_for_callback.get_mut();
                    workflow_state.current_claims = new_claims.clone();
                    workflow_state.current_claim_point = new_claim_point.clone();
                    workflow_state.current_batching_challenge = next_batching_challenge;
                    workflow_state.seed = state.seed;
                    workflow_state.proofs.insert(layer_idx, proof.clone());
                    workflow_state
                        .claims_for_layers
                        .insert(layer_idx, new_claims.clone());
                    workflow_state
                        .points_for_claims_at_layer
                        .insert(layer_idx, new_claim_point.clone());
                }

                state.result = Some(GpuGKRDimensionReducingLayerExecution {
                    proof,
                    new_claims,
                    new_claim_point,
                    next_batching_challenge,
                    updated_seed: state.seed,
                });
            },
            stream,
        )?;
        layer_range.end(stream)?;
        tracing_ranges.push(layer_range);

        drop(claim_point_host);
        drop(eq_pair_values_host);
        Ok(GpuGKRDimensionReducingScheduledLayerExecution {
            tracing_ranges,
            start_callbacks,
            static_spill_upload,
            round_challenge_storage,
            round_challenge_buffers,
            reduction_states,
            final_readback: {
                drop(final_evaluations);
                ScheduledDimensionReducingFinalReadback {
                    callbacks: final_readback_callbacks,
                    _phantom: std::marker::PhantomData,
                }
            },
            shared_state,
            _phantom: std::marker::PhantomData,
        })
    }
}

impl<B, E: FieldExtension<BF> + Field> GpuGKRDimensionReducingScheduledLayerExecution<B, E> {
    pub(crate) fn into_host_keepalive(self) -> GpuGKRDimensionReducingHostKeepalive<B, E> {
        let Self {
            tracing_ranges,
            start_callbacks,
            static_spill_upload,
            round_challenge_storage,
            round_challenge_buffers: _,
            reduction_states,
            final_readback,
            shared_state,
            _phantom: _,
        } = self;
        GpuGKRDimensionReducingHostKeepalive {
            tracing_ranges,
            start_callbacks,
            static_spill_upload: static_spill_upload.map(upload_into_host_keepalive),
            round_challenge_storage: round_challenge_storage
                .map(challenge_storage_into_host_keepalive),
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
        + GpuMainLayerKernelSet
        + super::backward_flat::GpuFlatRound0KernelSet
        + super::backward_flat::GpuFlatRound0ConstantKernelSet,
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

    fn compute_combined_claim_with_batch_base(
        &self,
        output_claims: &BTreeMap<GKRAddress, E>,
        batch_challenge_base: E,
    ) -> E {
        let mut result = E::ZERO;
        for kernel in self.kernel_plans.iter() {
            if kernel.kind == GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic {
                continue;
            }
            let mut challenge = field_pow(batch_challenge_base, kernel.batch_challenge_offset);
            for output in kernel
                .inputs
                .outputs_in_base
                .iter()
                .chain(kernel.inputs.outputs_in_extension.iter())
            {
                let mut term = output_claims
                    .get(output)
                    .copied()
                    .unwrap_or_else(|| panic!("missing output claim for {output:?}"));
                term.mul_assign(&challenge);
                result.add_assign(&term);
                challenge.mul_assign(&batch_challenge_base);
            }
        }

        result
    }

    fn schedule_batch_challenge_buffer(
        &self,
        batch_challenge_base: E,
        context: &ProverContext,
    ) -> CudaResult<(ScheduledChallengeStorage<E>, ScheduledChallengeBuffer<E>)> {
        let packed = pack_main_layer_batch_challenges(&self.kernel_plans, batch_challenge_base);
        assert!(
            !packed.is_empty(),
            "main-layer batched execution requires at least one packed batch challenge"
        );
        let len = packed.len();
        let mut storage =
            ScheduledChallengeStorage::new(context.alloc(len, AllocationPlacement::Top)?);
        let buffer = schedule_packed_round_challenge_upload(
            context,
            storage.device_accessor(),
            &mut storage.callbacks,
            0,
            len,
            move |dst| {
                dst.copy_from_slice(&packed);
            },
        )?;
        Ok((storage, buffer))
    }

    fn schedule_batch_challenge_buffer_from_workflow_state(
        &self,
        workflow_state: ScheduledBackwardWorkflowStateHandle<E>,
        context: &ProverContext,
    ) -> CudaResult<(ScheduledChallengeStorage<E>, ScheduledChallengeBuffer<E>)> {
        let specs = packed_main_layer_batch_challenge_specs(&self.kernel_plans);
        let len = specs
            .iter()
            .map(|spec| main_layer_kind_batch_challenge_count(spec.kind))
            .sum::<usize>();
        assert!(
            len > 0,
            "main-layer batched execution requires at least one packed batch challenge"
        );
        let mut storage =
            ScheduledChallengeStorage::new(context.alloc(len, AllocationPlacement::Top)?);
        let buffer = schedule_packed_round_challenge_upload(
            context,
            storage.device_accessor(),
            &mut storage.callbacks,
            0,
            len,
            move |dst| {
                let batch_challenge_base =
                    unsafe { workflow_state.get() }.current_batching_challenge;
                fill_packed_main_layer_batch_challenges_from_specs(
                    &specs,
                    batch_challenge_base,
                    dst,
                );
            },
        )?;
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
        batch_challenges: &ScheduledChallengeBuffer<E>,
        runtime_uploads: Option<&ScheduledMainLayerRuntimeUploads<E>>,
        acc_size: usize,
        static_spill_upload: Option<&ScheduledUpload<u8>>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        // Use the flat kernel if eval_recipes has been scheduled (recipe headers exist).
        if let Some(ref plan) = self.flat_round0_template {
            if self.flat_recipe_headers.is_some() {
                if self.flat_use_constant {
                    return super::backward_flat::launch_main_round0_flat_constant(
                        &plan.static_desc,
                        self.round_scratch.eq_values.as_ptr(),
                        self.round_scratch.accumulator.as_mut_ptr(),
                        acc_size as u32,
                        context,
                    );
                } else {
                    return super::backward_flat::launch_main_round0_flat(
                        &plan.static_desc,
                        self.flat_coeff_device_buf.as_ref().unwrap().as_ptr(),
                        self.round_scratch.eq_values.as_ptr(),
                        self.round_scratch.accumulator.as_mut_ptr(),
                        acc_size as u32,
                        context,
                    );
                }
            }
        }
        let batch_runtime = GpuGKRMainRound0BatchRuntime {
            eq_values: self.round_scratch.eq_values.as_ptr(),
            batch_challenges: batch_challenges.as_ptr(),
            contributions: self.round_scratch.accumulator.as_mut_ptr(),
            spill_payload: static_spill_upload
                .map(|upload| upload.device.as_ptr())
                .unwrap_or(null()),
            auxiliary_challenges: runtime_uploads
                .map(|uploads| uploads.auxiliary_challenges.device.as_ptr())
                .unwrap_or(null()),
            constraint_metadata: runtime_uploads
                .map(|uploads| uploads.constraint_metadata_pointers.device.as_ptr())
                .unwrap_or(null()),
        };
        launch_main_round0_batched(
            &self.round0_batch_template,
            &batch_runtime,
            acc_size,
            context,
        )
    }

    fn launch_round1_kernels(
        &mut self,
        batch_challenges: &ScheduledChallengeBuffer<E>,
        folding_challenge: &ScheduledChallengeBuffer<E>,
        runtime_uploads: Option<&ScheduledMainLayerRuntimeUploads<E>>,
        acc_size: usize,
        explicit_form: bool,
        static_spill_upload: Option<&ScheduledUpload<u8>>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        // Try flat path first.
        if let Some(ref desc) = self.flat_round1_desc {
            if self.flat_cont_recipe_headers.is_some() {
                let size_check = self.flat_round1_size_check();
                if let Some(sizes) = size_check.resolve(acc_size) {
                    let folding_ptr = folding_challenge.as_ptr().cast();
                    let eq_ptr = self.round_scratch.eq_values.as_ptr().cast();
                    let contrib_ptr = self.round_scratch.accumulator.as_mut_ptr().cast();

                    if self.flat_cont_use_constant {
                        if !explicit_form {
                            if let Some(ref unified_desc) = self.flat_round1_unified_desc {
                                super::backward_flat::launch_main_round1_flat_constant_unified(
                                    unified_desc,
                                    folding_ptr,
                                    sizes.fold_stride,
                                    sizes.next_layer_size,
                                    eq_ptr,
                                    contrib_ptr,
                                    acc_size as u32,
                                    context,
                                )?;
                            } else {
                                super::backward_flat::launch_main_round1_flat_constant_warp_split(
                                    desc,
                                    folding_ptr,
                                    sizes.fold_stride,
                                    sizes.next_layer_size,
                                    eq_ptr,
                                    contrib_ptr,
                                    acc_size as u32,
                                    context,
                                )?;
                            }
                        } else {
                            super::backward_flat::launch_main_round1_flat_constant(
                                desc,
                                folding_ptr,
                                sizes.fold_stride,
                                sizes.next_layer_size,
                                eq_ptr,
                                contrib_ptr,
                                acc_size as u32,
                                explicit_form,
                                context,
                            )?;
                        }
                    } else {
                        let coeff_ptr = self
                            .flat_cont_coeff_device_buf
                            .as_ref()
                            .unwrap()
                            .as_ptr()
                            .cast();
                        super::backward_flat::launch_main_round1_flat(
                            desc,
                            coeff_ptr,
                            folding_ptr,
                            sizes.fold_stride,
                            sizes.next_layer_size,
                            eq_ptr,
                            contrib_ptr,
                            acc_size as u32,
                            explicit_form,
                            context,
                        )?;
                    }

                    return Ok(());
                }
            }
        }
        // Fall back to batched path.
        let batch_runtime = GpuGKRMainRound1BatchRuntime {
            eq_values: self.round_scratch.eq_values.as_ptr(),
            batch_challenges: batch_challenges.as_ptr(),
            folding_challenge: folding_challenge.as_ptr(),
            contributions: self.round_scratch.accumulator.as_mut_ptr(),
            spill_payload: static_spill_upload
                .map(|upload| upload.device.as_ptr())
                .unwrap_or(null()),
            auxiliary_challenges: runtime_uploads
                .map(|uploads| uploads.auxiliary_challenges.device.as_ptr())
                .unwrap_or(null()),
            constraint_metadata: runtime_uploads
                .map(|uploads| uploads.constraint_metadata_pointers.device.as_ptr())
                .unwrap_or(null()),
        };
        launch_main_round1_batched(
            &self.round1_batch_template,
            &batch_runtime,
            acc_size,
            explicit_form,
            context,
        )
    }

    fn launch_round2_kernels(
        &mut self,
        batch_challenges: &ScheduledChallengeBuffer<E>,
        folding_challenges: &ScheduledChallengeBuffer<E>,
        runtime_uploads: Option<&ScheduledMainLayerRuntimeUploads<E>>,
        acc_size: usize,
        explicit_form: bool,
        static_spill_upload: Option<&ScheduledUpload<u8>>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        // Try flat path first.
        if let Some(ref desc) = self.flat_round2_desc {
            if self.flat_cont_recipe_headers.is_some() {
                let size_check = self.flat_round2_size_check();
                if let Some(sizes) = size_check.resolve(acc_size) {
                    let folding_ptr = folding_challenges.as_ptr().cast();
                    let eq_ptr = self.round_scratch.eq_values.as_ptr().cast();
                    let contrib_ptr = self.round_scratch.accumulator.as_mut_ptr().cast();

                    if self.flat_cont_use_constant {
                        // Prefer unified tiled kernel for compact form.
                        if !explicit_form {
                            if let Some(ref unified_desc) = self.flat_round2_unified_desc {
                                super::backward_flat::launch_main_round2_flat_constant_unified(
                                    unified_desc,
                                    folding_ptr,
                                    sizes.fold_stride,
                                    sizes.next_layer_size,
                                    eq_ptr,
                                    contrib_ptr,
                                    acc_size as u32,
                                    context,
                                )?;
                                return Ok(());
                            }
                        }
                        super::backward_flat::launch_main_round2_flat_constant(
                            desc,
                            folding_ptr,
                            sizes.fold_stride,
                            sizes.next_layer_size,
                            eq_ptr,
                            contrib_ptr,
                            acc_size as u32,
                            explicit_form,
                            context,
                        )?;
                    } else {
                        let coeff_ptr = self
                            .flat_cont_coeff_device_buf
                            .as_ref()
                            .unwrap()
                            .as_ptr()
                            .cast();
                        super::backward_flat::launch_main_round2_flat(
                            desc,
                            coeff_ptr,
                            folding_ptr,
                            sizes.fold_stride,
                            sizes.next_layer_size,
                            eq_ptr,
                            contrib_ptr,
                            acc_size as u32,
                            explicit_form,
                            context,
                        )?;
                    }

                    return Ok(());
                }
            }
        }
        // Fall back to batched path.
        let batch_runtime = GpuGKRMainRound2BatchRuntime {
            eq_values: self.round_scratch.eq_values.as_ptr(),
            batch_challenges: batch_challenges.as_ptr(),
            folding_challenges: folding_challenges.as_ptr(),
            contributions: self.round_scratch.accumulator.as_mut_ptr(),
            spill_payload: static_spill_upload
                .map(|upload| upload.device.as_ptr())
                .unwrap_or(null()),
            auxiliary_challenges: runtime_uploads
                .map(|uploads| uploads.auxiliary_challenges.device.as_ptr())
                .unwrap_or(null()),
            constraint_metadata: runtime_uploads
                .map(|uploads| uploads.constraint_metadata_pointers.device.as_ptr())
                .unwrap_or(null()),
        };
        launch_main_round2_batched(
            &self.round2_batch_template,
            &batch_runtime,
            acc_size,
            explicit_form,
            context,
        )
    }

    fn launch_round3_kernels(
        &mut self,
        step: usize,
        batch_challenges: &ScheduledChallengeBuffer<E>,
        folding_challenge: &ScheduledChallengeBuffer<E>,
        runtime_uploads: Option<&ScheduledMainLayerRuntimeUploads<E>>,
        acc_size: usize,
        explicit_form: bool,
        static_spill_upload: Option<&ScheduledUpload<u8>>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        // Try flat continuation path first.
        if let Some((_, desc)) = self
            .flat_continuation_descs
            .iter()
            .find(|(s, _)| *s == step)
        {
            if self.flat_cont_recipe_headers.is_some() {
                let size_check = self.flat_round3_size_check(step);
                if let Some(sizes) = size_check.resolve(acc_size) {
                    // SAFETY: E is always E4 in practice (the only kernel instantiation).
                    let folding_ptr = folding_challenge.as_ptr().cast();
                    let eq_ptr = self.round_scratch.eq_values.as_ptr().cast();
                    let contrib_ptr = self.round_scratch.accumulator.as_mut_ptr().cast();

                    if self.flat_cont_use_constant {
                        // Prefer unified tiled kernel if available.
                        if let Some((_, unified_desc)) = self
                            .flat_continuation_unified_descs
                            .iter()
                            .find(|(s, _)| *s == step)
                        {
                            return super::backward_flat::launch_main_round3_flat_constant_unified(
                                unified_desc,
                                folding_ptr,
                                sizes.fold_stride,
                                sizes.next_layer_size,
                                eq_ptr,
                                contrib_ptr,
                                acc_size as u32,
                                explicit_form,
                                context,
                            );
                        }
                        return super::backward_flat::launch_main_round3_flat_constant(
                            desc,
                            folding_ptr,
                            sizes.fold_stride,
                            sizes.next_layer_size,
                            eq_ptr,
                            contrib_ptr,
                            acc_size as u32,
                            explicit_form,
                            context,
                        );
                    } else {
                        let coeff_ptr = self
                            .flat_cont_coeff_device_buf
                            .as_ref()
                            .unwrap()
                            .as_ptr()
                            .cast();
                        return super::backward_flat::launch_main_round3_flat(
                            desc,
                            coeff_ptr,
                            folding_ptr,
                            sizes.fold_stride,
                            sizes.next_layer_size,
                            eq_ptr,
                            contrib_ptr,
                            acc_size as u32,
                            explicit_form,
                            context,
                        );
                    }
                }
            }
        }

        // Fall back to batched path.
        let batch_static = self
            .round3_batch_templates
            .iter()
            .find(|template| template.step == step)
            .unwrap_or_else(|| panic!("missing round 3 template for step {step}"))
            .batch;
        let batch_runtime = GpuGKRMainRound3BatchRuntime {
            eq_values: self.round_scratch.eq_values.as_ptr(),
            batch_challenges: batch_challenges.as_ptr(),
            folding_challenge: folding_challenge.as_ptr(),
            contributions: self.round_scratch.accumulator.as_mut_ptr(),
            spill_payload: static_spill_upload
                .map(|upload| upload.device.as_ptr())
                .unwrap_or(null()),
            auxiliary_challenges: runtime_uploads
                .map(|uploads| uploads.auxiliary_challenges.device.as_ptr())
                .unwrap_or(null()),
            constraint_metadata: runtime_uploads
                .map(|uploads| uploads.constraint_metadata_pointers.device.as_ptr())
                .unwrap_or(null()),
        };
        launch_main_round3_batched(
            &batch_static,
            &batch_runtime,
            acc_size,
            explicit_form,
            context,
        )
    }

    fn schedule_round_coefficients_reduction(
        &mut self,
        step: usize,
        acc_size: usize,
        context: &ProverContext,
    ) -> CudaResult<HostAllocation<[E]>> {
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

        let mut reduction_host = unsafe { context.alloc_host_uninit_slice(2) };
        memory_copy_async(
            &mut reduction_host,
            &self.round_scratch.reduction_output,
            context.get_exec_stream(),
        )?;
        Ok(reduction_host)
    }

    fn schedule_device_values_readback_from_raw_ptr(
        &self,
        ptr: *const E,
        len: usize,
        context: &ProverContext,
    ) -> CudaResult<HostAllocation<[E]>> {
        let device = unsafe { DeviceSlice::from_raw_parts(ptr, len) };
        let mut host = unsafe { context.alloc_host_uninit_slice(len) };
        memory_copy_async(&mut host, device, context.get_exec_stream())?;
        Ok(host)
    }

    fn schedule_runtime_uploads_from_workflow_state(
        &self,
        workflow_state: ScheduledBackwardWorkflowStateHandle<E>,
        context: &ProverContext,
    ) -> CudaResult<ScheduledMainLayerRuntimeUploads<E>> {
        let mut callbacks = Callbacks::new();
        let auxiliary_challenges = schedule_callback_populated_upload(
            context,
            self.kernel_plans.len(),
            &mut callbacks,
            {
                let sources = self
                    .kernel_plans
                    .iter()
                    .map(|kernel| kernel.auxiliary_challenge_source)
                    .collect::<Vec<_>>();
                move |dst: &mut [E]| unsafe {
                    let workflow_state = workflow_state.get();
                    for (dst, source) in dst.iter_mut().zip(sources.iter().copied()) {
                        *dst = match source {
                            GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(value) => value,
                            GpuGKRMainLayerAuxiliaryChallengeSource::LookupAdditive => {
                                workflow_state.lookup_additive_challenge
                            }
                        };
                    }
                }
            },
        )?;
        let deferred_constraint_metadata = self
            .kernel_plans
            .iter()
            .map(|kernel| match kernel.constraint_metadata_source.as_ref() {
                Some(GpuGKRMainLayerConstraintMetadataSource::Deferred(template)) => Ok(Some(
                    schedule_deferred_main_layer_constraint_metadata_upload(
                        template,
                        workflow_state,
                        context,
                    )?,
                )),
                _ => Ok(None),
            })
            .collect::<CudaResult<Vec<_>>>()?;
        let metadata_pointers = deferred_constraint_metadata
            .iter()
            .map(|metadata| constraint_metadata_device_pointers(metadata.as_ref()))
            .collect::<Vec<_>>();
        let constraint_metadata_pointers = schedule_callback_populated_upload(
            context,
            metadata_pointers.len(),
            &mut callbacks,
            move |dst: &mut [GpuGKRMainLayerConstraintMetadataDevicePointers<E>]| {
                dst.copy_from_slice(&metadata_pointers);
            },
        )?;
        Ok(ScheduledMainLayerRuntimeUploads {
            callbacks,
            auxiliary_challenges,
            deferred_constraint_metadata,
            constraint_metadata_pointers,
        })
    }

    /// Schedule eval_recipes on the GPU: callback uploads 4 challenge scalars,
    /// then eval_recipes kernel computes coefficients in device memory.
    /// Returns callbacks that must be kept alive until after execution.
    fn schedule_flat_eval_recipes(
        &mut self,
        workflow_state: ScheduledBackwardWorkflowStateHandle<E>,
        context: &ProverContext,
    ) -> CudaResult<Callbacks<'static>> {
        let challenges_buf = match self.flat_challenges_buf {
            Some(ref mut buf) => buf,
            None => return Ok(Callbacks::new()),
        };
        let headers = self.flat_recipe_headers.as_ref().unwrap();
        let terms = self.flat_recipe_terms.as_ref().unwrap();

        // Callback writes 4 challenge scalars to pinned host allocation.
        let mut callbacks = Callbacks::new();
        let challenges_upload: ScheduledUpload<E> = schedule_callback_populated_upload(
            context,
            4,
            &mut callbacks,
            move |dst: &mut [E]| unsafe {
                let ws = workflow_state.get();
                dst[0] = ws.current_batching_challenge;
                dst[1] = ws.lookup_multiplicative_challenge;
                dst[2] = ws.lookup_additive_challenge;
                dst[3] = ws.constraint_batch_challenge;
            },
        )?;
        // Async copy 4 scalars to device.
        memory_copy_async(
            challenges_buf,
            &challenges_upload.device,
            context.get_exec_stream(),
        )?;

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

        // Launch eval_recipes kernel.
        crate::ops::eval_recipes::eval_recipes_e4(
            challenges_buf.as_ptr().cast(),
            headers,
            terms,
            coeff_out_ptr,
            context.get_exec_stream(),
        )?;

        // Keep callback + upload alive until execution completes.
        let mut result = challenges_upload.callbacks;
        result.extend(callbacks);
        Ok(result)
    }

    /// Schedule eval_recipes for continuation coefficients (rounds 3+).
    /// Reuses the round 0 challenges buffer (same 4 challenge values).
    /// Must be called AFTER schedule_flat_eval_recipes so the challenges
    /// buffer is already populated on the stream.
    fn schedule_flat_continuation_eval_recipes(
        &mut self,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let headers = match self.flat_cont_recipe_headers {
            Some(ref h) => h,
            None => return Ok(()),
        };
        debug_assert!(
            self.flat_challenges_buf.is_some(),
            "flat continuation: challenges buffer missing",
        );
        // Reuse round 0's challenges buffer — same 4 challenge values.
        let challenges_buf = match self.flat_challenges_buf {
            Some(ref buf) => buf,
            None => return Ok(()),
        };
        let terms = self.flat_cont_recipe_terms.as_ref().unwrap();

        let coeff_out_ptr: *mut E4 = if self.flat_cont_use_constant {
            super::backward_flat::get_constant_continuation_coefficients_device_ptr()
        } else {
            self.flat_cont_coeff_device_buf
                .as_mut()
                .unwrap()
                .as_mut_ptr()
                .cast()
        };

        super::backward_flat::eval_continuation_recipes_e4(
            challenges_buf.as_ptr().cast(),
            headers,
            terms,
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

    fn schedule_last_evaluations_readback(
        &self,
        last_step: usize,
        context: &ProverContext,
    ) -> CudaResult<BTreeMap<GKRAddress, HostAllocation<[E]>>> {
        let mut result = BTreeMap::new();
        for (address, ptr) in self.final_evaluation_sources_for_last_step(last_step) {
            result.insert(
                address,
                self.schedule_device_values_readback_from_raw_ptr(ptr, 2, context)?,
            );
        }
        Ok(result)
    }

    fn interpolate_linear(f0: E, f1: E, r: &E) -> E {
        let mut result = f1;
        result.sub_assign(&f0);
        result.mul_assign(r);
        result.add_assign(&f0);
        result
    }

    pub(crate) fn schedule_execute_main_layer(
        &mut self,
        output_layer_claims: &BTreeMap<GKRAddress, E>,
        previous_claim_point: &[E],
        seed: Seed,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRMainLayerScheduledLayerExecution<E>> {
        assert_eq!(
            previous_claim_point.len(),
            self.folding_steps,
            "main-layer claim point must match folding steps"
        );

        let last_step = self.folding_steps - 1;
        assert!(last_step >= 3);
        let static_spill_upload = schedule_static_spill_upload(context, &self.static_spill_bytes)?;
        let mut round_challenge_buffers = Vec::with_capacity(last_step);
        let round_challenge_len = (1..=last_step)
            .map(main_layer_round_challenge_len)
            .sum::<usize>();
        let mut round_challenge_storage = ScheduledChallengeStorage::new(
            context.alloc(round_challenge_len, AllocationPlacement::Top)?,
        );
        let mut next_round_challenge_offset = 0usize;
        let mut start_callbacks = Callbacks::new();
        let mut start_state_values = previous_claim_point.to_vec();
        start_state_values.push(
            self.batch_challenge_base
                .expect("direct main-layer execution requires a prepared batching challenge base"),
        );
        let claim_point_host =
            alloc_host_and_schedule_copy(context, &mut start_callbacks, start_state_values);
        let eq_pair_values_host = alloc_host_and_schedule_copy(
            context,
            &mut start_callbacks,
            make_round0_eq_pair_values(previous_claim_point),
        );
        memory_copy_async(
            &mut self.round_scratch.claim_point,
            &claim_point_host,
            context.get_exec_stream(),
        )?;
        self.build_round0_eq_values(&eq_pair_values_host, context)?;
        drop(claim_point_host);
        drop(eq_pair_values_host);
        let (batch_challenge_storage, batch_challenge_buffer) = self
            .schedule_batch_challenge_buffer(
                self.batch_challenge_base.expect(
                    "direct main-layer execution requires a prepared batching challenge base",
                ),
                context,
            )?;

        let mut shared_state = Box::new(ScheduledMainLayerExecutionState {
            seed,
            claim: self.compute_combined_claim(output_layer_claims),
            eq_prefactor: E::ONE,
            folding_challenges: Vec::with_capacity(self.folding_steps),
            internal_round_coefficients: Vec::with_capacity(self.folding_steps - 1),
            result: None,
        });
        let shared_state_handle =
            crate::primitives::context::UnsafeMutAccessor::new(shared_state.as_mut());
        let mut reduction_states = Vec::with_capacity(last_step);

        // Schedule eval_recipes for the static path.
        // Stage challenge scalars through pinned host memory via callback to avoid
        // pageable memory copies (stack arrays are not pinned).
        let flat_coeff_callbacks = if let Some(ref mut challenges_buf) = self.flat_challenges_buf {
            let batch_base = self
                .batch_challenge_base
                .expect("static path requires batch_challenge_base");
            let lm = self.lookup_multiplicative_challenge;
            let la = self.lookup_additive_challenge;
            let cb = self.constraint_batch_challenge;
            let mut challenges_callbacks = Callbacks::new();
            let challenges_host = alloc_host_and_schedule_copy(
                context,
                &mut challenges_callbacks,
                vec![batch_base, lm, la, cb],
            );
            memory_copy_async(challenges_buf, &challenges_host, context.get_exec_stream())?;
            drop(challenges_host);
            let headers = self.flat_recipe_headers.as_ref().unwrap();
            let terms = self.flat_recipe_terms.as_ref().unwrap();
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
                challenges_buf.as_ptr().cast(),
                headers,
                terms,
                coeff_out_ptr,
                context.get_exec_stream(),
            )?;
            challenges_callbacks
        } else {
            Callbacks::new()
        };
        self.schedule_flat_continuation_eval_recipes(context)?;
        for step in 0..last_step {
            let acc_size = 1usize << (self.folding_steps - step - 1);
            if step == 0 {
                self.launch_round0_kernels(
                    &batch_challenge_buffer,
                    None,
                    acc_size,
                    static_spill_upload.as_ref(),
                    context,
                )?;
            } else {
                match step {
                    1 => self.launch_round1_kernels(
                        &batch_challenge_buffer,
                        &round_challenge_buffers[step - 1],
                        None,
                        acc_size,
                        false,
                        static_spill_upload.as_ref(),
                        context,
                    )?,
                    2 => self.launch_round2_kernels(
                        &batch_challenge_buffer,
                        &round_challenge_buffers[step - 1],
                        None,
                        acc_size,
                        false,
                        static_spill_upload.as_ref(),
                        context,
                    )?,
                    _ => self.launch_round3_kernels(
                        step,
                        &batch_challenge_buffer,
                        &round_challenge_buffers[step - 1],
                        None,
                        acc_size,
                        false,
                        static_spill_upload.as_ref(),
                        context,
                    )?,
                }
            }

            let reduction_output =
                self.schedule_round_coefficients_reduction(step, acc_size, context)?;
            self.fold_eq_values_for_next_round(acc_size, context)?;
            let reduction_accessor = reduction_output.get_accessor();
            let next_round_len =
                (step < last_step).then(|| main_layer_round_challenge_len(step + 1));
            let shared_state_for_callback = shared_state_handle;
            let previous_claim_coord = previous_claim_point[step];
            let callback = move |dst: &mut [E]| unsafe {
                let reduction = reduction_accessor.get();
                let c0 = reduction[0];
                let c2 = reduction[1];
                let state = shared_state_for_callback.get_mut();
                let mut normalized_claim = state.claim;
                normalized_claim.mul_assign(
                    &state
                        .eq_prefactor
                        .inverse()
                        .expect("eq prefactor must be non-zero"),
                );
                let coeffs = output_univariate_monomial_form_max_quadratic::<BF, E>(
                    previous_claim_coord,
                    normalized_claim,
                    c0,
                    c2,
                );
                commit_field_els(&mut state.seed, &coeffs);
                state.internal_round_coefficients.push(coeffs);

                let folding_challenge = draw_random_field_els::<BF, E>(&mut state.seed, 1)[0];
                state.claim =
                    evaluate_small_univariate_poly::<BF, E, _>(&coeffs, &folding_challenge);
                state.eq_prefactor =
                    evaluate_eq_poly::<BF, E>(&folding_challenge, &previous_claim_coord);
                state.folding_challenges.push(folding_challenge);
                match step + 1 {
                    1 => dst[0] = state.folding_challenges[0],
                    2 => {
                        dst[0] = state.folding_challenges[0];
                        dst[1] = state.folding_challenges[1];
                    }
                    _ => dst[0] = *state.folding_challenges.last().unwrap(),
                }
            };
            let callbacks = if let Some(len) = next_round_len {
                let offset = next_round_challenge_offset;
                next_round_challenge_offset += len;
                round_challenge_buffers.push(schedule_packed_round_challenge_upload(
                    context,
                    round_challenge_storage.device_accessor(),
                    &mut round_challenge_storage.callbacks,
                    offset,
                    len,
                    callback,
                )?);
                Callbacks::new()
            } else {
                let mut callbacks = Callbacks::new();
                callbacks.schedule(
                    move || {
                        let mut tmp = [E::ZERO; 2];
                        callback(&mut tmp[..main_layer_round_challenge_len(step + 1)]);
                    },
                    context.get_exec_stream(),
                )?;
                callbacks
            };
            drop(reduction_output);
            reduction_states.push(ScheduledDimensionReducingReductionState {
                callbacks,
                _phantom: std::marker::PhantomData,
            });
        }

        self.launch_round3_kernels(
            last_step,
            &batch_challenge_buffer,
            &round_challenge_buffers[last_step - 1],
            None,
            1,
            true,
            static_spill_upload.as_ref(),
            context,
        )?;
        let final_evaluations = self.schedule_last_evaluations_readback(last_step, context)?;
        let final_evaluation_accessors: Vec<_> = final_evaluations
            .iter()
            .map(|(addr, values)| (*addr, values.get_accessor()))
            .collect();
        let shared_state_for_callback = shared_state_handle;
        let folding_steps = self.folding_steps;
        let mut final_readback_callbacks = Callbacks::new();
        final_readback_callbacks.schedule(
            move || unsafe {
                let mut last_evaluations = BTreeMap::new();
                for (address, accessor) in final_evaluation_accessors.iter() {
                    let values: [E; 2] = accessor.get().try_into().unwrap();
                    last_evaluations.insert(*address, values);
                }

                let transcript_inputs: Vec<E> = last_evaluations
                    .values()
                    .flat_map(|values| values.iter().copied())
                    .collect();
                let state = shared_state_for_callback.get_mut();
                commit_field_els(&mut state.seed, &transcript_inputs);

                let challenges = draw_random_field_els::<BF, E>(&mut state.seed, 2);
                let [last_r, next_batching_challenge]: [E; 2] = challenges.try_into().unwrap();
                let mut new_claim_point = state.folding_challenges.clone();
                new_claim_point.push(last_r);
                let new_claims = last_evaluations
                    .iter()
                    .map(|(addr, [f0, f1])| (*addr, Self::interpolate_linear(*f0, *f1, &last_r)))
                    .collect();
                let proof = SumcheckIntermediateProofValues::<BF, E> {
                    sumcheck_num_rounds: folding_steps,
                    internal_round_coefficients: state.internal_round_coefficients.clone(),
                    final_step_evaluations: last_evaluations
                        .iter()
                        .map(|(addr, values)| (*addr, values.to_vec()))
                        .collect(),
                    extra_evaluations_from_caching_relations: BTreeMap::new(),
                    _marker: core::marker::PhantomData,
                };

                state.result = Some(GpuGKRMainLayerExecution {
                    proof,
                    new_claims,
                    new_claim_point,
                    next_batching_challenge,
                    updated_seed: state.seed,
                });
            },
            context.get_exec_stream(),
        )?;

        Ok(GpuGKRMainLayerScheduledLayerExecution {
            tracing_ranges: Vec::new(),
            start_callbacks,
            static_spill_upload,
            batch_challenge_storage,
            batch_challenge_buffer,
            round_challenge_storage,
            round_challenge_buffers,
            reduction_states,
            final_readback: {
                drop(final_evaluations);
                ScheduledDimensionReducingFinalReadback {
                    callbacks: final_readback_callbacks,
                    _phantom: std::marker::PhantomData,
                }
            },
            runtime_uploads: None,
            flat_coeff_callbacks,
            recipe_upload_callbacks: std::mem::replace(
                &mut self.recipe_upload_callbacks,
                Callbacks::new(),
            ),
            shared_state,
        })
    }

    pub(crate) fn schedule_execute_main_layer_from_workflow_state(
        &mut self,
        workflow_state: ScheduledBackwardWorkflowStateHandle<E>,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRMainLayerScheduledLayerExecution<E>> {
        let stream = context.get_exec_stream();
        let mut tracing_ranges = Vec::new();
        let layer_name = format!("gkr.backward.main.layer.{}", self.layer_idx);
        let layer_range = Range::new(layer_name.clone())?;
        layer_range.start(stream)?;
        let last_step = self.folding_steps - 1;
        assert!(last_step >= 3);
        let mut start_callbacks = Callbacks::new();
        let static_spill_upload = schedule_static_spill_upload(context, &self.static_spill_bytes)?;
        let mut shared_state = Box::new(ScheduledMainLayerExecutionState {
            seed: Seed::default(),
            claim: E::ZERO,
            eq_prefactor: E::ONE,
            folding_challenges: Vec::with_capacity(self.folding_steps),
            internal_round_coefficients: Vec::with_capacity(self.folding_steps - 1),
            result: None,
        });
        let shared_state_handle =
            crate::primitives::context::UnsafeMutAccessor::new(shared_state.as_mut());

        let mut claim_point_host =
            unsafe { context.alloc_host_uninit_slice(self.folding_steps + 1) };
        let claim_point_accessor = claim_point_host.get_mut_accessor();
        let mut eq_pair_values_host = unsafe {
            context.alloc_host_uninit_slice(round0_eq_pair_values_len(self.folding_steps))
        };
        let eq_pair_values_accessor = eq_pair_values_host.get_mut_accessor();
        let workflow_state_for_start = workflow_state;
        let shared_state_for_start = shared_state_handle;
        let layer_claim_callback = self
            .kernel_plans
            .iter()
            .filter(|kernel| {
                kernel.kind != GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic
            })
            .map(|kernel| {
                (
                    kernel.batch_challenge_offset,
                    kernel
                        .inputs
                        .outputs_in_base
                        .iter()
                        .chain(kernel.inputs.outputs_in_extension.iter())
                        .copied()
                        .collect::<Vec<_>>(),
                )
            })
            .collect::<Vec<_>>();
        start_callbacks.schedule(
            move || unsafe {
                let workflow_state = workflow_state_for_start.get();
                let dst = claim_point_accessor.get_mut();
                let claim_len = dst.len() - 1;
                dst[..claim_len].copy_from_slice(&workflow_state.current_claim_point);
                dst[claim_len] = workflow_state.current_batching_challenge;
                fill_round0_eq_pair_values(
                    eq_pair_values_accessor.get_mut(),
                    &workflow_state.current_claim_point,
                );
                let layer_state = shared_state_for_start.get_mut();
                layer_state.seed = workflow_state.seed;
                layer_state.claim = {
                    let mut result = E::ZERO;
                    for (offset, outputs) in layer_claim_callback.iter() {
                        let mut challenge =
                            field_pow(workflow_state.current_batching_challenge, *offset);
                        for output in outputs.iter() {
                            let mut term = workflow_state
                                .current_claims
                                .get(output)
                                .copied()
                                .unwrap_or_else(|| panic!("missing output claim for {output:?}"));
                            term.mul_assign(&challenge);
                            result.add_assign(&term);
                            challenge.mul_assign(&workflow_state.current_batching_challenge);
                        }
                    }
                    result
                };
                layer_state.eq_prefactor = E::ONE;
                layer_state.folding_challenges.clear();
                layer_state.internal_round_coefficients.clear();
            },
            stream,
        )?;
        memory_copy_async(
            &mut self.round_scratch.claim_point,
            &claim_point_host,
            stream,
        )?;
        self.build_round0_eq_values(&eq_pair_values_host, context)?;
        let (batch_challenge_storage, batch_challenge_buffer) =
            self.schedule_batch_challenge_buffer_from_workflow_state(workflow_state, context)?;
        let runtime_uploads =
            self.schedule_runtime_uploads_from_workflow_state(workflow_state, context)?;
        let flat_coeff_callbacks = self.schedule_flat_eval_recipes(workflow_state, context)?;
        self.schedule_flat_continuation_eval_recipes(context)?;
        let mut round_challenge_buffers = Vec::with_capacity(last_step);
        let round_challenge_len = (1..=last_step)
            .map(main_layer_round_challenge_len)
            .sum::<usize>();
        let mut round_challenge_storage = ScheduledChallengeStorage::new(
            context.alloc(round_challenge_len, AllocationPlacement::Top)?,
        );
        let mut next_round_challenge_offset = 0usize;
        let mut reduction_states = Vec::with_capacity(last_step);

        for step in 0..last_step {
            let acc_size = 1usize << (self.folding_steps - step - 1);
            if step == 0 {
                self.launch_round0_kernels(
                    &batch_challenge_buffer,
                    Some(&runtime_uploads),
                    acc_size,
                    static_spill_upload.as_ref(),
                    context,
                )?;
            } else {
                match step {
                    1 => self.launch_round1_kernels(
                        &batch_challenge_buffer,
                        &round_challenge_buffers[step - 1],
                        Some(&runtime_uploads),
                        acc_size,
                        false,
                        static_spill_upload.as_ref(),
                        context,
                    )?,
                    2 => self.launch_round2_kernels(
                        &batch_challenge_buffer,
                        &round_challenge_buffers[step - 1],
                        Some(&runtime_uploads),
                        acc_size,
                        false,
                        static_spill_upload.as_ref(),
                        context,
                    )?,
                    _ => self.launch_round3_kernels(
                        step,
                        &batch_challenge_buffer,
                        &round_challenge_buffers[step - 1],
                        Some(&runtime_uploads),
                        acc_size,
                        false,
                        static_spill_upload.as_ref(),
                        context,
                    )?,
                }
            }
            let reduction_output =
                self.schedule_round_coefficients_reduction(step, acc_size, context)?;
            self.fold_eq_values_for_next_round(acc_size, context)?;
            let reduction_accessor = reduction_output.get_accessor();
            let next_round_len =
                (step < last_step).then(|| main_layer_round_challenge_len(step + 1));
            let shared_state_for_callback = shared_state_handle;
            let previous_claim_coord_idx = step;
            let claim_point_for_callback = workflow_state;
            let callback = move |dst: &mut [E]| unsafe {
                let reduction = reduction_accessor.get();
                let c0 = reduction[0];
                let c2 = reduction[1];
                let previous_claim_coord =
                    claim_point_for_callback.get().current_claim_point[previous_claim_coord_idx];
                let state = shared_state_for_callback.get_mut();
                let mut normalized_claim = state.claim;
                normalized_claim.mul_assign(
                    &state
                        .eq_prefactor
                        .inverse()
                        .expect("eq prefactor must be non-zero"),
                );
                let coeffs = output_univariate_monomial_form_max_quadratic::<BF, E>(
                    previous_claim_coord,
                    normalized_claim,
                    c0,
                    c2,
                );
                commit_field_els(&mut state.seed, &coeffs);
                state.internal_round_coefficients.push(coeffs);

                let folding_challenge = draw_random_field_els::<BF, E>(&mut state.seed, 1)[0];
                state.claim =
                    evaluate_small_univariate_poly::<BF, E, _>(&coeffs, &folding_challenge);
                state.eq_prefactor =
                    evaluate_eq_poly::<BF, E>(&folding_challenge, &previous_claim_coord);
                state.folding_challenges.push(folding_challenge);
                match step + 1 {
                    1 => dst[0] = state.folding_challenges[0],
                    2 => {
                        dst[0] = state.folding_challenges[0];
                        dst[1] = state.folding_challenges[1];
                    }
                    _ => dst[0] = *state.folding_challenges.last().unwrap(),
                }
            };
            let callbacks = if let Some(len) = next_round_len {
                let offset = next_round_challenge_offset;
                next_round_challenge_offset += len;
                round_challenge_buffers.push(schedule_packed_round_challenge_upload(
                    context,
                    round_challenge_storage.device_accessor(),
                    &mut round_challenge_storage.callbacks,
                    offset,
                    len,
                    callback,
                )?);
                Callbacks::new()
            } else {
                let mut callbacks = Callbacks::new();
                callbacks.schedule(
                    move || {
                        let mut tmp = [E::ZERO; 2];
                        callback(&mut tmp[..main_layer_round_challenge_len(step + 1)]);
                    },
                    stream,
                )?;
                callbacks
            };
            drop(reduction_output);
            reduction_states.push(ScheduledDimensionReducingReductionState {
                callbacks,
                _phantom: std::marker::PhantomData,
            });
        }
        self.launch_round3_kernels(
            last_step,
            &batch_challenge_buffer,
            &round_challenge_buffers[last_step - 1],
            Some(&runtime_uploads),
            1,
            true,
            static_spill_upload.as_ref(),
            context,
        )?;
        let final_evaluations = self.schedule_last_evaluations_readback(last_step, context)?;
        let final_evaluation_accessors: Vec<_> = final_evaluations
            .iter()
            .map(|(addr, values)| (*addr, values.get_accessor()))
            .collect();
        let shared_state_for_callback = shared_state_handle;
        let workflow_state_for_callback = workflow_state;
        let folding_steps = self.folding_steps;
        let layer_idx = self.layer_idx;
        let mut final_readback_callbacks = Callbacks::new();
        final_readback_callbacks.schedule(
            move || unsafe {
                let mut last_evaluations = BTreeMap::new();
                for (address, accessor) in final_evaluation_accessors.iter() {
                    let values: [E; 2] = accessor.get().try_into().unwrap();
                    last_evaluations.insert(*address, values);
                }

                let transcript_inputs: Vec<E> = last_evaluations
                    .values()
                    .flat_map(|values| values.iter().copied())
                    .collect();
                let state = shared_state_for_callback.get_mut();
                commit_field_els(&mut state.seed, &transcript_inputs);

                let challenges = draw_random_field_els::<BF, E>(&mut state.seed, 2);
                let [last_r, next_batching_challenge]: [E; 2] = challenges.try_into().unwrap();
                let mut new_claim_point = state.folding_challenges.clone();
                new_claim_point.push(last_r);
                let new_claims = last_evaluations
                    .iter()
                    .map(|(addr, [f0, f1])| (*addr, Self::interpolate_linear(*f0, *f1, &last_r)))
                    .collect::<BTreeMap<_, _>>();
                let proof = SumcheckIntermediateProofValues::<BF, E> {
                    sumcheck_num_rounds: folding_steps,
                    internal_round_coefficients: state.internal_round_coefficients.clone(),
                    final_step_evaluations: last_evaluations
                        .iter()
                        .map(|(addr, values)| (*addr, values.to_vec()))
                        .collect(),
                    extra_evaluations_from_caching_relations: BTreeMap::new(),
                    _marker: core::marker::PhantomData,
                };

                {
                    let workflow_state = workflow_state_for_callback.get_mut();
                    workflow_state.current_claims = new_claims.clone();
                    workflow_state.current_claim_point = new_claim_point.clone();
                    workflow_state.current_batching_challenge = next_batching_challenge;
                    workflow_state.seed = state.seed;
                    workflow_state.proofs.insert(layer_idx, proof.clone());
                    workflow_state
                        .claims_for_layers
                        .insert(layer_idx, new_claims.clone());
                    workflow_state
                        .points_for_claims_at_layer
                        .insert(layer_idx, new_claim_point.clone());
                }

                state.result = Some(GpuGKRMainLayerExecution {
                    proof,
                    new_claims,
                    new_claim_point,
                    next_batching_challenge,
                    updated_seed: state.seed,
                });
            },
            stream,
        )?;
        layer_range.end(stream)?;
        tracing_ranges.push(layer_range);

        drop(claim_point_host);
        drop(eq_pair_values_host);
        Ok(GpuGKRMainLayerScheduledLayerExecution {
            tracing_ranges,
            start_callbacks,
            static_spill_upload,
            batch_challenge_storage,
            batch_challenge_buffer,
            round_challenge_storage,
            round_challenge_buffers,
            reduction_states,
            final_readback: {
                drop(final_evaluations);
                ScheduledDimensionReducingFinalReadback {
                    callbacks: final_readback_callbacks,
                    _phantom: std::marker::PhantomData,
                }
            },
            runtime_uploads: Some(runtime_uploads),
            flat_coeff_callbacks,
            recipe_upload_callbacks: std::mem::replace(
                &mut self.recipe_upload_callbacks,
                Callbacks::new(),
            ),
            shared_state,
        })
    }
}

impl<E: FieldExtension<BF> + Field> GpuGKRMainLayerScheduledLayerExecution<E> {
    pub(crate) fn into_host_keepalive(self) -> GpuGKRMainLayerHostKeepalive<E> {
        let Self {
            tracing_ranges,
            start_callbacks,
            static_spill_upload,
            batch_challenge_storage,
            round_challenge_storage,
            batch_challenge_buffer: _,
            round_challenge_buffers: _,
            reduction_states,
            final_readback,
            runtime_uploads,
            flat_coeff_callbacks,
            recipe_upload_callbacks,
            shared_state,
        } = self;
        GpuGKRMainLayerHostKeepalive {
            tracing_ranges,
            start_callbacks,
            static_spill_upload: static_spill_upload.map(upload_into_host_keepalive),
            batch_challenge_storage: challenge_storage_into_host_keepalive(batch_challenge_storage),
            round_challenge_storage: challenge_storage_into_host_keepalive(round_challenge_storage),
            reduction_states,
            final_readback,
            runtime_uploads: runtime_uploads.map(runtime_uploads_into_host_keepalive),
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
        }
    }

    pub(crate) fn shared_state_handle(&mut self) -> ScheduledBackwardWorkflowStateHandle<E> {
        crate::primitives::context::UnsafeMutAccessor::new(self.shared_state.as_mut())
    }

    pub(crate) fn wait(self, context: &ProverContext) -> CudaResult<GpuGKRBackwardExecution<E>> {
        context.get_exec_stream().synchronize()?;
        let Self {
            mut shared_state, ..
        } = self;
        let state = shared_state.as_mut();
        Ok(GpuGKRBackwardExecution {
            proofs: std::mem::take(&mut state.proofs),
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
        + GpuMainLayerKernelSet
        + super::backward_flat::GpuFlatRound0KernelSet
        + super::backward_flat::GpuFlatRound0ConstantKernelSet
        + 'static,
    Mul: BinaryOp<E, E, E>,
    [(); E::DEGREE]: Sized,
{
    pub(crate) fn schedule_execute_backward_workflow_from_shared_state(
        mut self,
        compiled_circuit: GKRCircuitArtifact<BF>,
        external_challenges: GKRExternalChallenges<BF, E>,
        mut shared_state: Box<ScheduledBackwardWorkflowState<E>>,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRBackwardScheduledExecution<BF, E>> {
        let shared_state_handle =
            crate::primitives::context::UnsafeMutAccessor::new(shared_state.as_mut());
        let stream = context.get_exec_stream();
        let mut tracing_ranges = Vec::new();
        let workflow_range = Range::new("gkr.backward.schedule")?;
        workflow_range.start(stream)?;
        let mut dimension_reducing_layers = Vec::new();
        let dimension_reducing_layers_range = Range::new("gkr.backward.dimension_reducing_layers")?;
        dimension_reducing_layers_range.start(stream)?;
        while let Some(mut prepared_layer) = self.prepare_next_layer_static(context)? {
            let layer_idx = prepared_layer.layer_idx;
            dimension_reducing_layers.push(
                prepared_layer.schedule_execute_dimension_reducing_layer_from_workflow_state(
                    shared_state_handle,
                    context,
                )?,
            );
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
            main_layers.push(
                prepared_layer.schedule_execute_main_layer_from_workflow_state(
                    shared_state_handle,
                    context,
                )?,
            );
            main_backward_state.purge_up_to_layer(layer_idx);
        }
        main_layers_range.end(stream)?;
        tracing_ranges.push(main_layers_range);

        let GpuGKRMainLayerBackwardState { storage: _, .. } = main_backward_state;
        // Remaining main-layer storage drops here after all exec-stream work has been scheduled.
        workflow_range.end(stream)?;
        tracing_ranges.push(workflow_range);

        Ok(GpuGKRBackwardScheduledExecution {
            tracing_ranges,
            dimension_reducing_layers,
            main_layers,
            shared_state,
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
        constraint_batch_challenge: E,
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
            constraint_batch_challenge,
            seed,
            proofs: BTreeMap::new(),
        });
        self.schedule_execute_backward_workflow_from_shared_state(
            compiled_circuit,
            external_challenges,
            shared_state,
            context,
        )
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
        build_single_max_quadratic_constraint_inputs_and_metadata,
        canonical_inits_and_teardowns_top_bits, eq_group_tables_len,
        launch_build_eq_values_from_point, launch_build_round0_eq_values_from_pairs,
        launch_fold_eq_values_in_place, launch_lookup_continuation, launch_lookup_round0,
        launch_main_round0, launch_pairwise_continuation, launch_pairwise_round0,
        make_deferred_backward_workflow_state, populate_backward_workflow_state,
        GKRCircuitArtifact, GpuGKRDimensionReducingBackwardState,
        GpuGKRMainLayerConstraintLinearTerm, GpuGKRMainLayerConstraintQuadraticTerm,
        GpuGKRMainLayerKernelKind,
    };
    use crate::allocator::tracker::AllocationPlacement;
    use crate::ops::cub::device_reduce::{get_reduce_temp_storage_bytes, ReduceOperation};
    use crate::primitives::callbacks::Callbacks;
    use crate::primitives::context::{DeviceAllocation, ProverContext};
    use crate::primitives::field::{BF, E4};
    use crate::prover::gkr::{
        GpuBaseFieldPolySource, GpuBaseFieldSourceKind,
        GpuExtensionFieldPolyContinuingLaunchDescriptor, GpuExtensionFieldPolyInitialSource,
        GpuSumcheckRound0DeviceLaunchDescriptors, GpuSumcheckRound0HostLaunchDescriptors,
        GpuSumcheckRound0ScheduledLaunchDescriptors,
    };
    use crate::prover::test_utils::make_test_context;
    use cs::definitions::{GKRAddress, VirtualSetupPoly, NUM_MEM_ARGUMENT_KEY_PARTS};
    use cs::gkr_compiler::{
        GKRLayerDescription, GateArtifacts, InitsOrTeardownsTimestampAndValue, NoFieldGKRRelation,
        NoFieldMaxQuadraticConstraintsGKRRelation, NoFieldMaxQuadraticGKRRelation, OutputType,
    };
    use era_cudart::memory::memory_copy_async;
    use era_cudart::slice::{CudaSlice, CudaSliceMut, DeviceSlice};
    use field::{Field, FieldExtension, PrimeField};
    use prover::gkr::high_bits_offset_for_inits_and_teardowns;
    use prover::gkr::prover::dimension_reduction::forward::DimensionReducingInputOutput;
    use prover::gkr::prover::transcript_utils::{commit_field_els, draw_random_field_els};
    use prover::gkr::prover::GKRExternalChallenges;
    use prover::gkr::sumcheck::evaluation_kernels::{
        BatchConstraintEvalGKRRelation, BatchedGKRKernel,
    };
    use prover::gkr::sumcheck::output_univariate_monomial_form_max_quadratic;
    use prover::transcript::Seed;
    use serial_test::serial;
    use std::collections::BTreeMap;
    use std::ptr::null;

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

    fn payload_slice<'a, T: Copy>(
        inline_payload: &'a [u8],
        spill_payload: &'a [u8],
        range: super::GpuGKRMainLayerPayloadRange,
        from_inline: bool,
    ) -> &'a [T] {
        if range.count == 0 {
            return &[];
        }
        let bytes = if from_inline {
            inline_payload
        } else {
            spill_payload
        };
        let start = range.offset as usize;
        let len = range.count as usize;
        // SAFETY: the payload builders align and serialize typed slices into these byte buffers,
        // and tests decode them with the exact same element type and count.
        unsafe { std::slice::from_raw_parts(bytes.as_ptr().add(start).cast::<T>(), len) }
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
        populate_backward_workflow_state(
            shared_state_handle,
            fixture.initial_output_layer_idx,
            fixture.top_layer_claims,
            fixture.evaluation_point,
            fixture.seed,
            fixture.batching_challenge,
            fixture.lookup_multiplicative_part,
            fixture.lookup_additive_part,
            fixture.constraints_batch_challenge,
        );

        let mut dimension_reducing_layers = Vec::new();
        let mut purged_layers = 0usize;
        while let Some(mut prepared_layer) =
            backward_state.prepare_next_layer_static(context).unwrap()
        {
            let layer_idx = prepared_layer.layer_idx;
            let scheduled = prepared_layer
                .schedule_execute_dimension_reducing_layer_from_workflow_state(
                    shared_state_handle,
                    context,
                )
                .unwrap();
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

        let mut main_state = backward_state.into_main_layer_backward_state(
            fixture.compiled_circuit,
            fixture.external_challenges,
            fixture.lookup_multiplicative_part,
            E4::ZERO,
            E4::ZERO,
            false,
        );
        let mut first_main_layer = main_state
            .prepare_next_layer_static(context)
            .unwrap()
            .expect("expected first main-layer plan after dimension reduction");
        let first_main_layer_idx = first_main_layer.layer_idx;
        let _first_main_layer_execution = first_main_layer
            .schedule_execute_main_layer_from_workflow_state(shared_state_handle, context)
            .unwrap();

        context.get_exec_stream().synchronize().unwrap();

        let execution = super::take_backward_execution_from_shared_state(shared_state_handle);
        assert!(
            execution.proofs.contains_key(&first_main_layer_idx),
            "shared-state workflow should still schedule the first main layer after purging"
        );
    }

    #[test]
    #[serial]
    fn first_dimension_reducing_static_batch_templates_match_expected_values() {
        let fixture = crate::prover::tests::prepare_basic_unrolled_async_backward_fixture(8);
        let context = &fixture.context;
        let mut backward_state = fixture.gpu_backward_state;

        let static_plan = backward_state
            .prepare_next_layer_static(context)
            .unwrap()
            .expect("expected first dimension-reducing layer");

        assert!(
            static_plan.batch_challenge_base.is_none(),
            "static dimension-reducing preparation should defer the batching challenge base",
        );

        let static_spill_upload =
            super::schedule_static_spill_upload(context, &static_plan.static_spill_bytes).unwrap();
        if let Some(upload) = static_spill_upload.as_ref() {
            assert_eq!(
                copy_device_values(context, &upload.device),
                static_plan.static_spill_bytes,
                "static spill upload must match the single packed spill blob",
            );
        } else {
            assert!(
                static_plan.static_spill_bytes.is_empty(),
                "empty spill bytes should not schedule a spill upload",
            );
        }

        let round0_batch = &static_plan.round0_batch_template;
        assert_eq!(
            round0_batch.record_count as usize,
            static_plan.kernel_plans.len()
        );

        for (idx, kernel_plan) in static_plan.kernel_plans.iter().enumerate() {
            let record = &round0_batch.records[idx];
            let descriptors_inline = record.record_mode
                == super::GpuGKRDimensionReducingBatchRecordMode::InlineDescriptors.as_u32();
            assert_eq!(record.kind, kernel_plan.kind.as_u32());
            assert_eq!(
                record.batch_challenge_offset as usize,
                kernel_plan.batch_challenge_offset
            );
            assert_eq!(
                record.batch_challenge_count as usize,
                kernel_plan.batch_challenge_count
            );
            let round0 = &static_plan.round0_descriptors[idx];
            assert_extension_poly_source_slice_eq(
                payload_slice::<GpuExtensionFieldPolyInitialSource<E4>>(
                    &round0_batch.inline_payload,
                    &static_plan.static_spill_bytes,
                    record.extension_inputs,
                    descriptors_inline,
                ),
                round0.extension_field_inputs.as_slice(),
                &format!("kernel {idx} round0 extension input descriptors mismatch"),
            );
            assert_extension_poly_source_slice_eq(
                payload_slice::<GpuExtensionFieldPolyInitialSource<E4>>(
                    &round0_batch.inline_payload,
                    &static_plan.static_spill_bytes,
                    record.extension_outputs,
                    descriptors_inline,
                ),
                round0.extension_field_outputs.as_slice(),
                &format!("kernel {idx} round0 extension output descriptors mismatch"),
            );
        }

        let round1_batch = &static_plan.round1_batch_template;
        assert_eq!(
            round1_batch.record_count as usize,
            static_plan.kernel_plans.len()
        );
        for (idx, kernel_plan) in static_plan.kernel_plans.iter().enumerate() {
            let record = &round1_batch.records[idx];
            let descriptors_inline = record.record_mode
                == super::GpuGKRDimensionReducingBatchRecordMode::InlineDescriptors.as_u32();
            assert_eq!(record.kind, kernel_plan.kind.as_u32());
            let round1 = kernel_plan.round1_prepared.build_launch_descriptors();
            assert_extension_poly_continuing_slice_eq(
                payload_slice::<GpuExtensionFieldPolyContinuingLaunchDescriptor<E4>>(
                    &round1_batch.inline_payload,
                    &static_plan.static_spill_bytes,
                    record.extension_inputs,
                    descriptors_inline,
                ),
                round1.extension_field_inputs.as_slice(),
                &format!("kernel {idx} round1 extension input descriptors mismatch"),
            );
        }

        if let Some(round2_batch) = static_plan.round2_batch_template.as_ref() {
            assert_eq!(
                round2_batch.record_count as usize,
                static_plan.kernel_plans.len()
            );
            for (idx, kernel_plan) in static_plan.kernel_plans.iter().enumerate() {
                let record = &round2_batch.records[idx];
                let descriptors_inline = record.record_mode
                    == super::GpuGKRDimensionReducingBatchRecordMode::InlineDescriptors.as_u32();
                assert_eq!(record.kind, kernel_plan.kind.as_u32());
                let round2 = kernel_plan
                    .round2_prepared
                    .as_ref()
                    .expect("round2 descriptors should be present")
                    .build_launch_descriptors();
                assert_extension_poly_continuing_slice_eq(
                    payload_slice::<GpuExtensionFieldPolyContinuingLaunchDescriptor<E4>>(
                        &round2_batch.inline_payload,
                        &static_plan.static_spill_bytes,
                        record.extension_inputs,
                        descriptors_inline,
                    ),
                    round2.extension_field_inputs.as_slice(),
                    &format!("kernel {idx} round2 extension input descriptors mismatch"),
                );
            }
        }

        for round3_template in static_plan.round3_batch_templates.iter() {
            let step = round3_template.step;
            let batch = &round3_template.batch;
            assert_eq!(batch.record_count as usize, static_plan.kernel_plans.len());
            for (idx, kernel_plan) in static_plan.kernel_plans.iter().enumerate() {
                let record = &batch.records[idx];
                let descriptors_inline = record.record_mode
                    == super::GpuGKRDimensionReducingBatchRecordMode::InlineDescriptors.as_u32();
                assert_eq!(record.kind, kernel_plan.kind.as_u32());
                let round3 = kernel_plan
                    .round3_and_beyond_prepared
                    .iter()
                    .find(|prepared| prepared.step == step)
                    .unwrap_or_else(|| panic!("missing round3 descriptors for step {step}"))
                    .prepared
                    .build_launch_descriptors();
                assert_extension_poly_continuing_slice_eq(
                    payload_slice::<GpuExtensionFieldPolyContinuingLaunchDescriptor<E4>>(
                        &batch.inline_payload,
                        &static_plan.static_spill_bytes,
                        record.extension_inputs,
                        descriptors_inline,
                    ),
                    round3.extension_field_inputs.as_slice(),
                    &format!(
                        "kernel {idx} round3 step {step} extension input descriptors mismatch"
                    ),
                );
            }
        }
    }

    #[test]
    #[serial]
    fn first_main_layer_static_batch_templates_match_expected_values() {
        fn advance_dimension_reduction(
            mut state: GpuGKRDimensionReducingBackwardState<BF, E4>,
            compiled_circuit: &GKRCircuitArtifact<BF>,
            external_challenges: &GKRExternalChallenges<BF, E4>,
            mut current_claims: BTreeMap<GKRAddress, E4>,
            mut current_point: Vec<E4>,
            mut seed: Seed,
            mut batching_challenge: E4,
            lookup_multiplicative_part: E4,
            lookup_additive_part: E4,
            constraints_batch_challenge: E4,
            context: &ProverContext,
        ) -> (
            crate::prover::gkr::backward::GpuGKRMainLayerBackwardState<E4>,
            BTreeMap<GKRAddress, E4>,
            Vec<E4>,
            Seed,
            E4,
        ) {
            while let Some(mut plan) = state
                .prepare_next_layer(batching_challenge, context)
                .unwrap()
            {
                let scheduled = plan
                    .schedule_execute_dimension_reducing_layer(
                        &current_claims,
                        &current_point,
                        seed,
                        batching_challenge,
                        context,
                    )
                    .unwrap();
                context.get_exec_stream().synchronize().unwrap();
                let execution = scheduled.into_execution();
                current_claims = execution.new_claims;
                current_point = execution.new_claim_point;
                seed = execution.updated_seed;
                batching_challenge = execution.next_batching_challenge;
            }

            (
                state.into_main_layer_backward_state(
                    compiled_circuit.clone(),
                    external_challenges.clone(),
                    lookup_multiplicative_part,
                    lookup_additive_part,
                    constraints_batch_challenge,
                    false,
                ),
                current_claims,
                current_point,
                seed,
                batching_challenge,
            )
        }

        let fixture = crate::prover::tests::prepare_basic_unrolled_async_backward_fixture(8);
        let context = &fixture.context;
        let (mut main_state, current_claims, current_point, seed, batching_challenge) =
            advance_dimension_reduction(
                fixture.gpu_backward_state,
                &fixture.compiled_circuit,
                &fixture.external_challenges,
                fixture.top_layer_claims,
                fixture.evaluation_point,
                fixture.seed,
                fixture.batching_challenge,
                fixture.lookup_multiplicative_part,
                fixture.lookup_additive_part,
                fixture.constraints_batch_challenge,
                context,
            );

        let static_plan = main_state
            .prepare_next_layer_static(context)
            .unwrap()
            .expect("expected first main-layer plan");
        let expected = crate::prover::tests::expected_main_layer_kernel_specs_for_test(
            &fixture.compiled_circuit.layers[static_plan.layer_idx],
            static_plan.layer_idx,
            main_state.storage(),
            &fixture.external_challenges,
            batching_challenge,
            fixture.lookup_multiplicative_part,
            fixture.lookup_additive_part,
            fixture.constraints_batch_challenge,
            fixture.compiled_circuit.memory_layout.total_width,
            fixture.compiled_circuit.witness_layout.total_width,
        );
        assert_eq!(static_plan.kernel_plans.len(), expected.len());

        let mut shared_state = make_deferred_backward_workflow_state();
        let shared_state_handle =
            crate::primitives::context::UnsafeMutAccessor::new(shared_state.as_mut());
        populate_backward_workflow_state(
            shared_state_handle,
            static_plan.layer_idx + 1,
            current_claims,
            current_point,
            seed,
            batching_challenge,
            fixture.lookup_multiplicative_part,
            fixture.lookup_additive_part,
            fixture.constraints_batch_challenge,
        );

        assert!(
            static_plan.batch_challenge_base.is_none(),
            "workflow/static preparation should defer the batching-challenge base to layer start"
        );

        let static_spill_upload =
            super::schedule_static_spill_upload(context, &static_plan.static_spill_bytes).unwrap();
        if let Some(upload) = static_spill_upload.as_ref() {
            assert_eq!(
                copy_device_values(context, &upload.device),
                static_plan.static_spill_bytes,
                "static spill upload must match the single packed spill blob",
            );
        } else {
            assert!(
                static_plan.static_spill_bytes.is_empty(),
                "empty spill bytes should not schedule a spill upload",
            );
        }

        let round0_batch = &static_plan.round0_batch_template;
        assert_eq!(round0_batch.record_count as usize, expected.len());
        let packed_batch_challenges =
            super::pack_main_layer_batch_challenges(&static_plan.kernel_plans, batching_challenge);
        let expected_packed_batch_challenges = expected
            .iter()
            .flat_map(|kernel| kernel.batch_challenges.iter().copied())
            .collect::<Vec<_>>();
        assert_eq!(
            super::packed_main_layer_batch_challenge_len(&static_plan.kernel_plans),
            expected_packed_batch_challenges.len(),
            "packed main-layer batch challenge length mismatch",
        );
        assert_eq!(
            packed_batch_challenges, expected_packed_batch_challenges,
            "packed main-layer batch challenges must match dynamic preparation order",
        );

        for (idx, expected_kernel) in expected.iter().enumerate() {
            let kernel_plan = &static_plan.kernel_plans[idx];
            let record = &round0_batch.records[idx];
            let descriptors_inline = record.record_mode
                != super::GpuGKRMainLayerBatchRecordMode::PointerDescriptors.as_u32();

            assert_eq!(record.kind, expected_kernel.kind.as_u32());
            assert_eq!(
                super::main_layer_kind_batch_challenge_count(kernel_plan.kind),
                kernel_plan.batch_challenge_count,
                "kernel {idx} batch challenge count mismatch",
            );
            assert_eq!(
                record.auxiliary_challenge,
                kernel_plan
                    .auxiliary_challenge_summary()
                    .unwrap_or(E4::ZERO),
                "kernel {idx} auxiliary challenge mismatch",
            );

            let round0 = &static_plan.round0_descriptors[idx];
            assert_base_poly_source_slice_eq(
                payload_slice::<GpuBaseFieldPolySource<BF>>(
                    &round0_batch.inline_payload,
                    &static_plan.static_spill_bytes,
                    record.base_inputs,
                    descriptors_inline,
                ),
                round0.base_field_inputs.as_slice(),
                &format!("kernel {idx} round0 base input descriptors mismatch"),
            );
            assert_extension_poly_source_slice_eq(
                payload_slice::<GpuExtensionFieldPolyInitialSource<E4>>(
                    &round0_batch.inline_payload,
                    &static_plan.static_spill_bytes,
                    record.extension_inputs,
                    descriptors_inline,
                ),
                round0.extension_field_inputs.as_slice(),
                &format!("kernel {idx} round0 extension input descriptors mismatch"),
            );
            assert_base_poly_source_slice_eq(
                payload_slice::<GpuBaseFieldPolySource<BF>>(
                    &round0_batch.inline_payload,
                    &static_plan.static_spill_bytes,
                    record.base_outputs,
                    descriptors_inline,
                ),
                round0.base_field_outputs.as_slice(),
                &format!("kernel {idx} round0 base output descriptors mismatch"),
            );
            assert_extension_poly_source_slice_eq(
                payload_slice::<GpuExtensionFieldPolyInitialSource<E4>>(
                    &round0_batch.inline_payload,
                    &static_plan.static_spill_bytes,
                    record.extension_outputs,
                    descriptors_inline,
                ),
                round0.extension_field_outputs.as_slice(),
                &format!("kernel {idx} round0 extension output descriptors mismatch"),
            );

            let metadata_inline = record.metadata_inline != 0;
            match kernel_plan.constraint_metadata_source.as_ref() {
                None => {
                    assert_eq!(record.quadratic_terms.count, 0);
                    assert_eq!(record.linear_terms.count, 0);
                    assert_eq!(record.constant_offset, E4::ZERO);
                }
                Some(super::GpuGKRMainLayerConstraintMetadataSource::Deferred(_)) => {
                    assert_eq!(record.quadratic_terms.count, 0);
                    assert_eq!(record.linear_terms.count, 0);
                    assert_eq!(record.constant_offset, E4::ZERO);
                }
                Some(super::GpuGKRMainLayerConstraintMetadataSource::Immediate(_)) => {
                    let expected_metadata = expected_kernel
                        .constraint_metadata
                        .as_ref()
                        .expect("immediate static metadata must match expected kernel metadata");
                    assert_eq!(
                        payload_slice::<GpuGKRMainLayerConstraintQuadraticTerm<E4>>(
                            &round0_batch.inline_payload,
                            &static_plan.static_spill_bytes,
                            record.quadratic_terms,
                            metadata_inline,
                        ),
                        expected_metadata.quadratic_terms.as_slice(),
                        "kernel {idx} quadratic metadata mismatch",
                    );
                    assert_eq!(
                        payload_slice::<GpuGKRMainLayerConstraintLinearTerm<E4>>(
                            &round0_batch.inline_payload,
                            &static_plan.static_spill_bytes,
                            record.linear_terms,
                            metadata_inline,
                        ),
                        expected_metadata.linear_terms.as_slice(),
                        "kernel {idx} linear metadata mismatch",
                    );
                    assert_eq!(
                        record.constant_offset, expected_metadata.constant_offset,
                        "kernel {idx} constant offset mismatch",
                    );
                }
            }
        }
    }

    #[test]
    fn main_layer_kind_batch_challenge_count_matches_all_supported_kinds() {
        let one_challenge_kinds = [
            GpuGKRMainLayerKernelKind::BaseCopy,
            GpuGKRMainLayerKernelKind::ExtCopy,
            GpuGKRMainLayerKernelKind::Product,
            GpuGKRMainLayerKernelKind::MaskIdentity,
            GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic,
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
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_layer_packed_batch_challenges_match_dynamic_and_static_preparation() {
        fn advance_dimension_reduction(
            mut state: GpuGKRDimensionReducingBackwardState<BF, E4>,
            compiled_circuit: &GKRCircuitArtifact<BF>,
            external_challenges: &GKRExternalChallenges<BF, E4>,
            mut current_claims: BTreeMap<GKRAddress, E4>,
            mut current_point: Vec<E4>,
            mut seed: Seed,
            mut batching_challenge: E4,
            lookup_multiplicative_part: E4,
            lookup_additive_part: E4,
            constraints_batch_challenge: E4,
            context: &ProverContext,
        ) -> (
            crate::prover::gkr::backward::GpuGKRMainLayerBackwardState<E4>,
            BTreeMap<GKRAddress, E4>,
            Vec<E4>,
            Seed,
            E4,
        ) {
            while let Some(mut plan) = state
                .prepare_next_layer(batching_challenge, context)
                .unwrap()
            {
                let scheduled = plan
                    .schedule_execute_dimension_reducing_layer(
                        &current_claims,
                        &current_point,
                        seed,
                        batching_challenge,
                        context,
                    )
                    .unwrap();
                context.get_exec_stream().synchronize().unwrap();
                let execution = scheduled.into_execution();
                current_claims = execution.new_claims;
                current_point = execution.new_claim_point;
                seed = execution.updated_seed;
                batching_challenge = execution.next_batching_challenge;
            }

            (
                state.into_main_layer_backward_state(
                    compiled_circuit.clone(),
                    external_challenges.clone(),
                    lookup_multiplicative_part,
                    lookup_additive_part,
                    constraints_batch_challenge,
                    false,
                ),
                current_claims,
                current_point,
                seed,
                batching_challenge,
            )
        }

        let dynamic_fixture =
            crate::prover::tests::prepare_basic_unrolled_async_backward_fixture(8);
        let dynamic_context = &dynamic_fixture.context;
        let (mut dynamic_state, _, _, _, dynamic_batching_challenge) = advance_dimension_reduction(
            dynamic_fixture.gpu_backward_state,
            &dynamic_fixture.compiled_circuit,
            &dynamic_fixture.external_challenges,
            dynamic_fixture.top_layer_claims,
            dynamic_fixture.evaluation_point,
            dynamic_fixture.seed,
            dynamic_fixture.batching_challenge,
            dynamic_fixture.lookup_multiplicative_part,
            dynamic_fixture.lookup_additive_part,
            dynamic_fixture.constraints_batch_challenge,
            dynamic_context,
        );
        let dynamic_plan = dynamic_state
            .prepare_next_layer(dynamic_batching_challenge, dynamic_context)
            .unwrap()
            .expect("expected first main-layer plan");
        let dynamic_packed = super::pack_main_layer_batch_challenges(
            &dynamic_plan.kernel_plans,
            dynamic_batching_challenge,
        );

        let static_fixture = crate::prover::tests::prepare_basic_unrolled_async_backward_fixture(8);
        let static_context = &static_fixture.context;
        let (mut static_state, _, _, _, static_batching_challenge) = advance_dimension_reduction(
            static_fixture.gpu_backward_state,
            &static_fixture.compiled_circuit,
            &static_fixture.external_challenges,
            static_fixture.top_layer_claims,
            static_fixture.evaluation_point,
            static_fixture.seed,
            static_fixture.batching_challenge,
            static_fixture.lookup_multiplicative_part,
            static_fixture.lookup_additive_part,
            static_fixture.constraints_batch_challenge,
            static_context,
        );
        let static_plan = static_state
            .prepare_next_layer_static(static_context)
            .unwrap()
            .expect("expected first main-layer plan");
        let static_packed = super::pack_main_layer_batch_challenges(
            &static_plan.kernel_plans,
            static_batching_challenge,
        );

        assert_eq!(dynamic_batching_challenge, static_batching_challenge);
        assert_eq!(
            dynamic_packed.len(),
            dynamic_plan
                .kernel_plans
                .iter()
                .map(|kernel| kernel.batch_challenge_count)
                .sum::<usize>(),
        );
        assert_eq!(
            static_packed.len(),
            static_plan
                .kernel_plans
                .iter()
                .map(|kernel| kernel.batch_challenge_count)
                .sum::<usize>(),
        );
        assert_eq!(dynamic_packed, static_packed);
    }

    #[test]
    #[serial]
    fn main_layer0_round_coefficients_match_cpu_reference() {
        let fixture = crate::prover::tests::prepare_basic_unrolled_async_backward_fixture(8);
        let cpu_fixture = crate::prover::tests::prepare_basic_unrolled_proof_fixture();
        let expected_layer0 = cpu_fixture
            .expected_cpu_proof
            .sumcheck_intermediate_values
            .get(&0)
            .expect("CPU proof must contain layer 0");
        let context = &fixture.context;

        let mut backward_state = fixture.gpu_backward_state;
        let mut current_claims = fixture.top_layer_claims;
        let mut current_point = fixture.evaluation_point;
        let mut seed = fixture.seed;
        let mut batching_challenge = fixture.batching_challenge;

        while let Some(mut plan) = backward_state
            .prepare_next_layer(batching_challenge, context)
            .unwrap()
        {
            let scheduled = plan
                .schedule_execute_dimension_reducing_layer(
                    &current_claims,
                    &current_point,
                    seed,
                    batching_challenge,
                    context,
                )
                .unwrap();
            context.get_exec_stream().synchronize().unwrap();
            let execution = scheduled.into_execution();
            current_claims = execution.new_claims;
            current_point = execution.new_claim_point;
            seed = execution.updated_seed;
            batching_challenge = execution.next_batching_challenge;
        }

        let mut main_state = backward_state.into_main_layer_backward_state(
            fixture.compiled_circuit,
            fixture.external_challenges,
            fixture.lookup_multiplicative_part,
            fixture.lookup_additive_part,
            fixture.constraints_batch_challenge,
            false,
        );

        let mut layer0_plan = loop {
            let Some(mut plan) = main_state
                .prepare_next_layer(batching_challenge, context)
                .unwrap()
            else {
                panic!("expected to reach main layer 0");
            };
            let layer_idx = plan.layer_idx;
            if layer_idx == 0 {
                break plan;
            }
            let scheduled = plan
                .schedule_execute_main_layer(&current_claims, &current_point, seed, context)
                .unwrap();
            context.get_exec_stream().synchronize().unwrap();
            let execution = scheduled.into_execution();
            current_claims = execution.new_claims;
            current_point = execution.new_claim_point;
            seed = execution.updated_seed;
            batching_challenge = execution.next_batching_challenge;
            main_state.purge_up_to_layer(layer_idx);
        };

        let static_spill_upload =
            super::schedule_static_spill_upload(context, &layer0_plan.static_spill_bytes).unwrap();
        let mut start_state_host =
            unsafe { context.alloc_host_uninit_slice(current_point.len() + 1) };
        let batch_challenge_base = layer0_plan
            .batch_challenge_base
            .expect("direct main-layer plan must store the batching challenge base");
        unsafe {
            start_state_host
                .get_mut_accessor()
                .get_mut()
                .copy_from_slice(
                    &current_point
                        .iter()
                        .copied()
                        .chain(std::iter::once(batch_challenge_base))
                        .collect::<Vec<_>>(),
                );
        }
        memory_copy_async(
            &mut layer0_plan.round_scratch.claim_point,
            &start_state_host,
            context.get_exec_stream(),
        )
        .unwrap();
        let (_batch_challenge_storage, batch_challenge_buffer) = layer0_plan
            .schedule_batch_challenge_buffer(batch_challenge_base, context)
            .unwrap();

        let mut probe_seed = seed;
        let mut probe_claim = layer0_plan.compute_combined_claim(&current_claims);
        let mut eq_prefactor = E4::ONE;
        let mut folding_challenges = Vec::with_capacity(layer0_plan.folding_steps);

        for step in 0..(layer0_plan.folding_steps - 1) {
            let acc_size = 1usize << (layer0_plan.folding_steps - step - 1);
            match step {
                0 => {
                    layer0_plan
                        .launch_round0_kernels(
                            &batch_challenge_buffer,
                            None,
                            acc_size,
                            static_spill_upload.as_ref(),
                            context,
                        )
                        .unwrap();
                }
                1 => {
                    let (_folding_storage, folding_buffer) =
                        super::schedule_immediate_field_upload(
                            context,
                            1,
                            &[folding_challenges[0]],
                        )
                        .unwrap();
                    layer0_plan
                        .launch_round1_kernels(
                            &batch_challenge_buffer,
                            &folding_buffer,
                            None,
                            acc_size,
                            false,
                            static_spill_upload.as_ref(),
                            context,
                        )
                        .unwrap();
                }
                2 => {
                    let (_folding_storage, folding_buffer) =
                        super::schedule_immediate_field_upload(
                            context,
                            2,
                            &[folding_challenges[0], folding_challenges[1]],
                        )
                        .unwrap();
                    layer0_plan
                        .launch_round2_kernels(
                            &batch_challenge_buffer,
                            &folding_buffer,
                            None,
                            acc_size,
                            false,
                            static_spill_upload.as_ref(),
                            context,
                        )
                        .unwrap();
                }
                _ => {
                    let (_folding_storage, folding_buffer) =
                        super::schedule_immediate_field_upload(
                            context,
                            1,
                            &[*folding_challenges.last().unwrap()],
                        )
                        .unwrap();
                    layer0_plan
                        .launch_round3_kernels(
                            step,
                            &batch_challenge_buffer,
                            &folding_buffer,
                            None,
                            acc_size,
                            false,
                            static_spill_upload.as_ref(),
                            context,
                        )
                        .unwrap();
                }
            }

            let reduction_output = layer0_plan
                .schedule_round_coefficients_reduction(step, acc_size, context)
                .unwrap();
            context.get_exec_stream().synchronize().unwrap();
            let reduction_values: [E4; 2] =
                unsafe { reduction_output.get_accessor().get().try_into().unwrap() };

            let mut normalized_claim = probe_claim;
            normalized_claim.mul_assign(
                &eq_prefactor
                    .inverse()
                    .expect("eq prefactor must be non-zero"),
            );
            let coeffs = output_univariate_monomial_form_max_quadratic::<BF, E4>(
                current_point[step],
                normalized_claim,
                reduction_values[0],
                reduction_values[1],
            );
            assert_eq!(
                coeffs, expected_layer0.internal_round_coefficients[step],
                "layer 0 round {step} coeffs diverged: reduction={reduction_values:?}, normalized_claim={normalized_claim:?}, eq_prefactor={eq_prefactor:?}"
            );

            commit_field_els::<BF, E4>(&mut probe_seed, &coeffs);
            let folding_challenge = draw_random_field_els::<BF, E4>(&mut probe_seed, 1)[0];
            probe_claim = prover::gkr::sumcheck::evaluate_small_univariate_poly::<BF, E4, _>(
                &coeffs,
                &folding_challenge,
            );
            eq_prefactor = prover::gkr::sumcheck::evaluate_eq_poly::<BF, E4>(
                &folding_challenge,
                &current_point[step],
            );
            folding_challenges.push(folding_challenge);
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
    fn pairwise_round0_batched_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_values = (0..8).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let output_values = (0..4).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
        let claim_point = [sample_ext(50), sample_ext(60)];
        let input = alloc_and_copy(&context, &input_values);
        let output = alloc_and_copy(&context, &output_values);
        let eq = eq_weights_for_binary_tail(claim_point[1]);
        let eq_dev = alloc_and_copy(&context, &eq);
        let batch_challenge_base = sample_ext(200);
        let batch_challenge_base_dev = alloc_and_copy(&context, &[batch_challenge_base]);
        let mut contributions = alloc_and_copy(&context, &[E4::ZERO; 4]);

        let mut inline_builder = super::InlinePayloadBuilder::new();
        let extension_inputs = inline_builder
            .try_push_copy(&[GpuExtensionFieldPolyInitialSource {
                start: input.as_ptr(),
                next_layer_size: 4,
            }])
            .unwrap();
        let extension_outputs = inline_builder
            .try_push_copy(&[GpuExtensionFieldPolyInitialSource {
                start: output.as_ptr(),
                next_layer_size: 2,
            }])
            .unwrap();

        let mut batch = super::GpuGKRDimensionReducingRound0Batch::default();
        batch.record_count = 1;
        batch.eq_values = eq_dev.as_ptr();
        batch.batch_challenge_base = batch_challenge_base_dev.as_ptr();
        batch.contributions = contributions.as_mut_ptr();
        batch.inline_payload = inline_builder.into_bytes();
        batch.records[0] = super::GpuGKRDimensionReducingRound0BatchRecord {
            kind: super::GpuGKRDimensionReducingKernelKind::Pairwise.as_u32(),
            record_mode: super::GpuGKRDimensionReducingBatchRecordMode::InlineDescriptors.as_u32(),
            _reserved0: 0,
            _reserved1: 0,
            extension_inputs,
            extension_outputs,
            batch_challenge_offset: 1,
            batch_challenge_count: 1,
        };

        super::launch_dim_reducing_round0_batched(&batch, 2, &context).unwrap();
        let actual = copy_device_values(&context, &contributions);

        let mut expected = Vec::new();
        for gid in 0..2 {
            let index = gid * 2;
            let mut c0 = batch_challenge_base;
            c0.mul_assign(&output_values[gid]);
            c0.mul_assign(&eq[gid]);

            let mut lhs = input_values[4 + index];
            lhs.sub_assign(&input_values[index]);
            let mut rhs = input_values[4 + index + 1];
            rhs.sub_assign(&input_values[index + 1]);
            let mut c1 = lhs;
            c1.mul_assign(&rhs);
            c1.mul_assign(&batch_challenge_base);
            c1.mul_assign(&eq[gid]);

            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn lookup_round0_batched_matches_cpu() {
        let context = make_test_context(64, 8);
        let input0_values = (0..8).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let input1_values = (0..8).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
        let output_num_values = (0..4).map(|i| sample_ext(200 + i)).collect::<Vec<_>>();
        let output_den_values = (0..4).map(|i| sample_ext(300 + i)).collect::<Vec<_>>();
        let claim_point = [sample_ext(40), sample_ext(41)];
        let input0 = alloc_and_copy(&context, &input0_values);
        let input1 = alloc_and_copy(&context, &input1_values);
        let output_num = alloc_and_copy(&context, &output_num_values);
        let output_den = alloc_and_copy(&context, &output_den_values);
        let eq = eq_weights_for_binary_tail(claim_point[1]);
        let eq_dev = alloc_and_copy(&context, &eq);
        let batch_challenge_base = sample_ext(400);
        let batch_challenge_base_dev = alloc_and_copy(&context, &[batch_challenge_base]);
        let mut contributions = alloc_and_copy(&context, &[E4::ZERO; 4]);

        let mut inline_builder = super::InlinePayloadBuilder::new();
        let extension_inputs = inline_builder
            .try_push_copy(&[
                GpuExtensionFieldPolyInitialSource {
                    start: input0.as_ptr(),
                    next_layer_size: 4,
                },
                GpuExtensionFieldPolyInitialSource {
                    start: input1.as_ptr(),
                    next_layer_size: 4,
                },
            ])
            .unwrap();
        let extension_outputs = inline_builder
            .try_push_copy(&[
                GpuExtensionFieldPolyInitialSource {
                    start: output_num.as_ptr(),
                    next_layer_size: 2,
                },
                GpuExtensionFieldPolyInitialSource {
                    start: output_den.as_ptr(),
                    next_layer_size: 2,
                },
            ])
            .unwrap();

        let mut batch = super::GpuGKRDimensionReducingRound0Batch::default();
        batch.record_count = 1;
        batch.eq_values = eq_dev.as_ptr();
        batch.batch_challenge_base = batch_challenge_base_dev.as_ptr();
        batch.contributions = contributions.as_mut_ptr();
        batch.inline_payload = inline_builder.into_bytes();
        batch.records[0] = super::GpuGKRDimensionReducingRound0BatchRecord {
            kind: super::GpuGKRDimensionReducingKernelKind::Lookup.as_u32(),
            record_mode: super::GpuGKRDimensionReducingBatchRecordMode::InlineDescriptors.as_u32(),
            _reserved0: 0,
            _reserved1: 0,
            extension_inputs,
            extension_outputs,
            batch_challenge_offset: 1,
            batch_challenge_count: 2,
        };

        super::launch_dim_reducing_round0_batched(&batch, 2, &context).unwrap();
        let actual = copy_device_values(&context, &contributions);

        let batch0 = batch_challenge_base;
        let batch1 = super::field_pow(batch_challenge_base, 2);
        let mut expected = Vec::new();
        for gid in 0..2 {
            let index = gid * 2;
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
            c0.mul_assign(&output_num_values[gid]);
            let mut den_out = batch1;
            den_out.mul_assign(&output_den_values[gid]);
            c0.add_assign(&den_out);
            c0.mul_assign(&eq[gid]);

            let mut c1 = batch0;
            c1.mul_assign(&num);
            let mut den_term = batch1;
            den_term.mul_assign(&den);
            c1.add_assign(&den_term);
            c1.mul_assign(&eq[gid]);

            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn pairwise_round1_batched_matches_cpu() {
        let context = make_test_context(64, 8);
        let prev = (0..16).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let claim_point = [sample_ext(40), sample_ext(41), sample_ext(42)];
        let folding_challenge = sample_ext(300);
        let batch_challenge_base = sample_ext(400);
        let prev_dev = alloc_and_copy(&context, &prev);
        let eq = eq_weights_for_binary_tail(claim_point[2]);
        let eq_dev = alloc_and_copy(&context, &eq);
        let folding_challenge_dev = alloc_and_copy(&context, &[folding_challenge]);
        let batch_challenge_base_dev = alloc_and_copy(&context, &[batch_challenge_base]);
        let cache: DeviceAllocation<E4> = context.alloc(8, AllocationPlacement::Top).unwrap();
        let mut contributions = alloc_and_copy(&context, &[E4::ZERO; 4]);

        let mut inline_builder = super::InlinePayloadBuilder::new();
        let extension_inputs = inline_builder
            .try_push_copy(&[GpuExtensionFieldPolyContinuingLaunchDescriptor {
                previous_layer_start: prev_dev.as_ptr(),
                this_layer_start: cache.as_ptr().cast_mut(),
                this_layer_size: 8,
                next_layer_size: 4,
                first_access: true,
            }])
            .unwrap();

        let mut batch = super::GpuGKRDimensionReducingRound1Batch::default();
        batch.record_count = 1;
        batch.eq_values = eq_dev.as_ptr();
        batch.batch_challenge_base = batch_challenge_base_dev.as_ptr();
        batch.folding_challenge = folding_challenge_dev.as_ptr();
        batch.contributions = contributions.as_mut_ptr();
        batch.inline_payload = inline_builder.into_bytes();
        batch.records[0] = super::GpuGKRDimensionReducingContinuationBatchRecord {
            kind: super::GpuGKRDimensionReducingKernelKind::Pairwise.as_u32(),
            record_mode: super::GpuGKRDimensionReducingBatchRecordMode::InlineDescriptors.as_u32(),
            _reserved0: 0,
            _reserved1: 0,
            extension_inputs,
            batch_challenge_offset: 1,
            batch_challenge_count: 1,
        };

        super::launch_dim_reducing_round1_batched(&batch, 2, &context).unwrap();
        let actual = copy_device_values(&context, &contributions);

        let mut expected = Vec::new();
        for gid in 0..2 {
            let even_index = gid * 2;
            let odd_index = even_index + 1;
            let even0 = fold_continuing_value(&prev, folding_challenge, even_index);
            let even1 = fold_continuing_value(&prev, folding_challenge, even_index + 4);
            let mut even_delta = even1;
            even_delta.sub_assign(&even0);

            let odd0 = fold_continuing_value(&prev, folding_challenge, odd_index);
            let odd1 = fold_continuing_value(&prev, folding_challenge, odd_index + 4);
            let mut odd_delta = odd1;
            odd_delta.sub_assign(&odd0);

            let mut c0 = even0;
            c0.mul_assign(&odd0);
            c0.mul_assign(&batch_challenge_base);
            c0.mul_assign(&eq[gid]);

            let mut c1 = even_delta;
            c1.mul_assign(&odd_delta);
            c1.mul_assign(&batch_challenge_base);
            c1.mul_assign(&eq[gid]);

            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn lookup_round1_batched_matches_cpu() {
        let context = make_test_context(64, 8);
        let prev0 = (0..16).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let prev1 = (0..16).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
        let claim_point = [sample_ext(50), sample_ext(51), sample_ext(52)];
        let folding_challenge = sample_ext(300);
        let batch_challenge_base = sample_ext(400);
        let prev0_dev = alloc_and_copy(&context, &prev0);
        let prev1_dev = alloc_and_copy(&context, &prev1);
        let eq = eq_weights_for_binary_tail(claim_point[2]);
        let eq_dev = alloc_and_copy(&context, &eq);
        let folding_challenge_dev = alloc_and_copy(&context, &[folding_challenge]);
        let batch_challenge_base_dev = alloc_and_copy(&context, &[batch_challenge_base]);
        let cache0: DeviceAllocation<E4> = context.alloc(8, AllocationPlacement::Top).unwrap();
        let cache1: DeviceAllocation<E4> = context.alloc(8, AllocationPlacement::Top).unwrap();
        let mut contributions = alloc_and_copy(&context, &[E4::ZERO; 4]);

        let mut inline_builder = super::InlinePayloadBuilder::new();
        let extension_inputs = inline_builder
            .try_push_copy(&[
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
            ])
            .unwrap();

        let mut batch = super::GpuGKRDimensionReducingRound1Batch::default();
        batch.record_count = 1;
        batch.eq_values = eq_dev.as_ptr();
        batch.batch_challenge_base = batch_challenge_base_dev.as_ptr();
        batch.folding_challenge = folding_challenge_dev.as_ptr();
        batch.contributions = contributions.as_mut_ptr();
        batch.inline_payload = inline_builder.into_bytes();
        batch.records[0] = super::GpuGKRDimensionReducingContinuationBatchRecord {
            kind: super::GpuGKRDimensionReducingKernelKind::Lookup.as_u32(),
            record_mode: super::GpuGKRDimensionReducingBatchRecordMode::InlineDescriptors.as_u32(),
            _reserved0: 0,
            _reserved1: 0,
            extension_inputs,
            batch_challenge_offset: 1,
            batch_challenge_count: 2,
        };

        super::launch_dim_reducing_round1_batched(&batch, 2, &context).unwrap();
        let actual = copy_device_values(&context, &contributions);

        let batch0 = batch_challenge_base;
        let batch1 = super::field_pow(batch_challenge_base, 2);
        let mut expected = Vec::new();
        for gid in 0..2 {
            let even_index = gid * 2;
            let odd_index = even_index + 1;

            let a0 = fold_continuing_value(&prev0, folding_challenge, even_index);
            let a1_full = fold_continuing_value(&prev0, folding_challenge, even_index + 4);
            let mut da = a1_full;
            da.sub_assign(&a0);
            let b0 = fold_continuing_value(&prev1, folding_challenge, even_index);
            let b1_full = fold_continuing_value(&prev1, folding_challenge, even_index + 4);
            let mut db = b1_full;
            db.sub_assign(&b0);

            let c0 = fold_continuing_value(&prev0, folding_challenge, odd_index);
            let c1_full = fold_continuing_value(&prev0, folding_challenge, odd_index + 4);
            let mut dc = c1_full;
            dc.sub_assign(&c0);
            let d0 = fold_continuing_value(&prev1, folding_challenge, odd_index);
            let d1_full = fold_continuing_value(&prev1, folding_challenge, odd_index + 4);
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

            let mut out0 = batch0;
            out0.mul_assign(&num0);
            let mut out0_den = batch1;
            out0_den.mul_assign(&den0);
            out0.add_assign(&out0_den);
            out0.mul_assign(&eq[gid]);

            let mut out1 = batch0;
            out1.mul_assign(&num1);
            let mut out1_den = batch1;
            out1_den.mul_assign(&den1);
            out1.add_assign(&out1_den);
            out1.mul_assign(&eq[gid]);

            expected.push(out0);
            expected.push(out1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn pairwise_round2_batched_matches_cpu() {
        let context = make_test_context(64, 8);
        let prev = (0..16).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let claim_point = [
            sample_ext(40),
            sample_ext(41),
            sample_ext(42),
            sample_ext(43),
        ];
        let folding_challenge = sample_ext(300);
        let batch_challenge_base = sample_ext(400);
        let prev_dev = alloc_and_copy(&context, &prev);
        let eq = eq_weights_for_binary_tail(claim_point[3]);
        let eq_dev = alloc_and_copy(&context, &eq);
        let folding_challenge_dev = alloc_and_copy(&context, &[folding_challenge]);
        let batch_challenge_base_dev = alloc_and_copy(&context, &[batch_challenge_base]);
        let cache: DeviceAllocation<E4> = context.alloc(8, AllocationPlacement::Top).unwrap();
        let mut contributions = alloc_and_copy(&context, &[E4::ZERO; 4]);

        let mut inline_builder = super::InlinePayloadBuilder::new();
        let extension_inputs = inline_builder
            .try_push_copy(&[GpuExtensionFieldPolyContinuingLaunchDescriptor {
                previous_layer_start: prev_dev.as_ptr(),
                this_layer_start: cache.as_ptr().cast_mut(),
                this_layer_size: 8,
                next_layer_size: 4,
                first_access: true,
            }])
            .unwrap();

        let mut batch = super::GpuGKRDimensionReducingRound2Batch::default();
        batch.record_count = 1;
        batch.eq_values = eq_dev.as_ptr();
        batch.batch_challenge_base = batch_challenge_base_dev.as_ptr();
        batch.folding_challenge = folding_challenge_dev.as_ptr();
        batch.contributions = contributions.as_mut_ptr();
        batch.inline_payload = inline_builder.into_bytes();
        batch.records[0] = super::GpuGKRDimensionReducingContinuationBatchRecord {
            kind: super::GpuGKRDimensionReducingKernelKind::Pairwise.as_u32(),
            record_mode: super::GpuGKRDimensionReducingBatchRecordMode::InlineDescriptors.as_u32(),
            _reserved0: 0,
            _reserved1: 0,
            extension_inputs,
            batch_challenge_offset: 1,
            batch_challenge_count: 1,
        };

        super::launch_dim_reducing_round2_batched(&batch, 2, &context).unwrap();
        let actual = copy_device_values(&context, &contributions);

        let mut expected = Vec::new();
        for gid in 0..2 {
            let even_index = gid * 2;
            let odd_index = even_index + 1;
            let even0 = fold_continuing_value(&prev, folding_challenge, even_index);
            let even1 = fold_continuing_value(&prev, folding_challenge, even_index + 4);
            let mut even_delta = even1;
            even_delta.sub_assign(&even0);

            let odd0 = fold_continuing_value(&prev, folding_challenge, odd_index);
            let odd1 = fold_continuing_value(&prev, folding_challenge, odd_index + 4);
            let mut odd_delta = odd1;
            odd_delta.sub_assign(&odd0);

            let mut c0 = even0;
            c0.mul_assign(&odd0);
            c0.mul_assign(&batch_challenge_base);
            c0.mul_assign(&eq[gid]);

            let mut c1 = even_delta;
            c1.mul_assign(&odd_delta);
            c1.mul_assign(&batch_challenge_base);
            c1.mul_assign(&eq[gid]);

            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn lookup_round3_batched_matches_cpu() {
        let context = make_test_context(64, 8);
        let prev0 = (0..16).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let prev1 = (0..16).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
        let claim_point = [
            sample_ext(50),
            sample_ext(51),
            sample_ext(52),
            sample_ext(53),
            sample_ext(54),
        ];
        let folding_challenge = sample_ext(300);
        let batch_challenge_base = sample_ext(400);
        let prev0_dev = alloc_and_copy(&context, &prev0);
        let prev1_dev = alloc_and_copy(&context, &prev1);
        let eq = eq_weights_for_binary_tail(claim_point[4]);
        let eq_dev = alloc_and_copy(&context, &eq);
        let folding_challenge_dev = alloc_and_copy(&context, &[folding_challenge]);
        let batch_challenge_base_dev = alloc_and_copy(&context, &[batch_challenge_base]);
        let cache0: DeviceAllocation<E4> = context.alloc(8, AllocationPlacement::Top).unwrap();
        let cache1: DeviceAllocation<E4> = context.alloc(8, AllocationPlacement::Top).unwrap();
        let mut contributions = alloc_and_copy(&context, &[E4::ZERO; 4]);

        let mut inline_builder = super::InlinePayloadBuilder::new();
        let extension_inputs = inline_builder
            .try_push_copy(&[
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
            ])
            .unwrap();

        let mut batch = super::GpuGKRDimensionReducingRound3Batch::default();
        batch.record_count = 1;
        batch.eq_values = eq_dev.as_ptr();
        batch.batch_challenge_base = batch_challenge_base_dev.as_ptr();
        batch.folding_challenge = folding_challenge_dev.as_ptr();
        batch.contributions = contributions.as_mut_ptr();
        batch.inline_payload = inline_builder.into_bytes();
        batch.records[0] = super::GpuGKRDimensionReducingContinuationBatchRecord {
            kind: super::GpuGKRDimensionReducingKernelKind::Lookup.as_u32(),
            record_mode: super::GpuGKRDimensionReducingBatchRecordMode::InlineDescriptors.as_u32(),
            _reserved0: 0,
            _reserved1: 0,
            extension_inputs,
            batch_challenge_offset: 1,
            batch_challenge_count: 2,
        };

        super::launch_dim_reducing_round3_batched(&batch, 2, &context).unwrap();
        let actual = copy_device_values(&context, &contributions);

        let batch0 = batch_challenge_base;
        let batch1 = super::field_pow(batch_challenge_base, 2);
        let mut expected = Vec::new();
        for gid in 0..2 {
            let even_index = gid * 2;
            let odd_index = even_index + 1;

            let a0 = fold_continuing_value(&prev0, folding_challenge, even_index);
            let a1_full = fold_continuing_value(&prev0, folding_challenge, even_index + 4);
            let mut da = a1_full;
            da.sub_assign(&a0);
            let b0 = fold_continuing_value(&prev1, folding_challenge, even_index);
            let b1_full = fold_continuing_value(&prev1, folding_challenge, even_index + 4);
            let mut db = b1_full;
            db.sub_assign(&b0);

            let c0 = fold_continuing_value(&prev0, folding_challenge, odd_index);
            let c1_full = fold_continuing_value(&prev0, folding_challenge, odd_index + 4);
            let mut dc = c1_full;
            dc.sub_assign(&c0);
            let d0 = fold_continuing_value(&prev1, folding_challenge, odd_index);
            let d1_full = fold_continuing_value(&prev1, folding_challenge, odd_index + 4);
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

            let mut out0 = batch0;
            out0.mul_assign(&num0);
            let mut out0_den = batch1;
            out0_den.mul_assign(&den0);
            out0.add_assign(&out0_den);
            out0.mul_assign(&eq[gid]);

            let mut out1 = batch0;
            out1.mul_assign(&num1);
            let mut out1_den = batch1;
            out1_den.mul_assign(&den1);
            out1.add_assign(&out1_den);
            out1.mul_assign(&eq[gid]);

            expected.push(out0);
            expected.push(out1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
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
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round0_base_copy_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_values = (0..4).map(|i| BF::new(10 + i)).collect::<Vec<_>>();
        let output_values = (0..4).map(|i| BF::new(100 + i)).collect::<Vec<_>>();
        let input = alloc_and_copy(&context, &input_values);
        let output = alloc_and_copy(&context, &output_values);
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();
        let batch_challenge = sample_ext(200);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch_challenge, E4::ZERO]);
        let auxiliary_challenge_dev = alloc_and_copy(&context, &[E4::ZERO]);

        let mut round0 = GpuSumcheckRound0ScheduledLaunchDescriptors {
            callbacks: Callbacks::new(),
            host: GpuSumcheckRound0HostLaunchDescriptors {
                base_field_inputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(1)
                },
                extension_field_inputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(0)
                },
                base_field_outputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(1)
                },
                extension_field_outputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(0)
                },
            },
            device: GpuSumcheckRound0DeviceLaunchDescriptors {
                base_field_inputs: context
                    .alloc::<GpuBaseFieldPolySource<BF>>(1, AllocationPlacement::Top)
                    .unwrap(),
                extension_field_inputs: context
                    .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(0, AllocationPlacement::Top)
                    .unwrap(),
                base_field_outputs: context
                    .alloc::<GpuBaseFieldPolySource<BF>>(1, AllocationPlacement::Top)
                    .unwrap(),
                extension_field_outputs: context
                    .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(0, AllocationPlacement::Top)
                    .unwrap(),
            },
        };
        unsafe {
            round0.host.base_field_inputs.get_mut_accessor().get_mut()[0] =
                GpuBaseFieldPolySource {
                    start: input.as_ptr(),
                    next_layer_size: 2,
                    source_kind: GpuBaseFieldSourceKind::Real,
                };
            round0.host.base_field_outputs.get_mut_accessor().get_mut()[0] =
                GpuBaseFieldPolySource {
                    start: output.as_ptr(),
                    next_layer_size: 2,
                    source_kind: GpuBaseFieldSourceKind::Real,
                };
        }
        memory_copy_async(
            &mut round0.device.base_field_inputs,
            &round0.host.base_field_inputs,
            context.get_exec_stream(),
        )
        .unwrap();
        memory_copy_async(
            &mut round0.device.base_field_outputs,
            &round0.host.base_field_outputs,
            context.get_exec_stream(),
        )
        .unwrap();

        launch_main_round0(
            GpuGKRMainLayerKernelKind::BaseCopy,
            &round0,
            batch_challenges_dev.as_ptr(),
            auxiliary_challenge_dev.as_ptr(),
            None,
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
            let mut c0 = batch_challenge;
            c0.mul_assign_by_base(&output_values[output_index]);
            expected.push(c0);
            expected.push(E4::ZERO);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round0_batched_base_copy_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_values = (0..4).map(|i| BF::new(10 + i)).collect::<Vec<_>>();
        let output_values = (0..4).map(|i| BF::new(100 + i)).collect::<Vec<_>>();
        let claim_point = [sample_ext(50), sample_ext(60)];
        let input = alloc_and_copy(&context, &input_values);
        let output = alloc_and_copy(&context, &output_values);
        let eq = eq_weights_for_binary_tail(claim_point[1]);
        let eq_dev = alloc_and_copy(&context, &eq);
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();
        let batch_challenge = sample_ext(200);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch_challenge]);
        let mut inline_builder = super::InlinePayloadBuilder::new();
        let base_inputs = inline_builder
            .try_push_copy(&[GpuBaseFieldPolySource {
                start: input.as_ptr(),
                next_layer_size: 2,
                source_kind: GpuBaseFieldSourceKind::Real,
            }])
            .unwrap();
        let extension_inputs = super::GpuGKRMainLayerPayloadRange::default();
        let base_outputs = inline_builder
            .try_push_copy(&[GpuBaseFieldPolySource {
                start: output.as_ptr(),
                next_layer_size: 2,
                source_kind: GpuBaseFieldSourceKind::Real,
            }])
            .unwrap();
        let extension_outputs = super::GpuGKRMainLayerPayloadRange::default();

        let mut batch_static = super::GpuGKRMainRound0BatchStatic::default();
        batch_static.record_count = 1;
        batch_static.inline_payload = inline_builder.into_bytes();
        batch_static.records[0] = super::GpuGKRMainRound0BatchRecord {
            kind: GpuGKRMainLayerKernelKind::BaseCopy.as_u32(),
            record_mode: super::GpuGKRMainLayerBatchRecordMode::InlineAll.as_u32(),
            metadata_inline: 1,
            _reserved: 0,
            base_inputs,
            extension_inputs,
            base_outputs,
            extension_outputs,
            quadratic_terms: super::GpuGKRMainLayerPayloadRange::default(),
            linear_terms: super::GpuGKRMainLayerPayloadRange::default(),
            auxiliary_challenge: E4::ZERO,
            constant_offset: E4::ZERO,
        };
        let batch_runtime = super::GpuGKRMainRound0BatchRuntime {
            eq_values: eq_dev.as_ptr(),
            batch_challenges: batch_challenges_dev.as_ptr(),
            contributions: contributions.as_mut_ptr(),
            spill_payload: null(),
            auxiliary_challenges: null(),
            constraint_metadata: null(),
        };

        super::launch_main_round0_batched(&batch_static, &batch_runtime, 2, &context).unwrap();

        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let mut expected = Vec::new();
        for gid in 0..2 {
            let mut c0 = batch_challenge;
            c0.mul_assign_by_base(&output_values[gid]);
            c0.mul_assign(&eq[gid]);
            expected.push(c0);
            expected.push(E4::ZERO);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round0_batched_mixed_challenge_arities_match_cpu() {
        let context = make_test_context(64, 8);
        let copy_input_values = (0..4).map(|i| BF::new(10 + i)).collect::<Vec<_>>();
        let copy_output_values = (0..4).map(|i| BF::new(30 + i)).collect::<Vec<_>>();
        let lookup_b_values = (0..4).map(|i| BF::new(50 + i)).collect::<Vec<_>>();
        let lookup_d_values = (0..4).map(|i| BF::new(70 + i)).collect::<Vec<_>>();
        let lookup_num_values = (0..4).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
        let lookup_den_values = (0..4).map(|i| sample_ext(200 + i)).collect::<Vec<_>>();
        let claim_point = [sample_ext(300), sample_ext(301)];

        let copy_input = alloc_and_copy(&context, &copy_input_values);
        let copy_output = alloc_and_copy(&context, &copy_output_values);
        let lookup_b = alloc_and_copy(&context, &lookup_b_values);
        let lookup_d = alloc_and_copy(&context, &lookup_d_values);
        let lookup_num = alloc_and_copy(&context, &lookup_num_values);
        let lookup_den = alloc_and_copy(&context, &lookup_den_values);
        let eq = eq_weights_for_binary_tail(claim_point[1]);
        let eq_dev = alloc_and_copy(&context, &eq);
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();

        let copy_batch = sample_ext(400);
        let lookup_batch0 = sample_ext(500);
        let lookup_batch1 = sample_ext(600);
        let lookup_additive_challenge = sample_ext(700);
        let batch_challenges_dev =
            alloc_and_copy(&context, &[copy_batch, lookup_batch0, lookup_batch1]);

        let mut inline_builder = super::InlinePayloadBuilder::new();
        let copy_base_inputs = inline_builder
            .try_push_copy(&[GpuBaseFieldPolySource {
                start: copy_input.as_ptr(),
                next_layer_size: 2,
                source_kind: GpuBaseFieldSourceKind::Real,
            }])
            .unwrap();
        let copy_base_outputs = inline_builder
            .try_push_copy(&[GpuBaseFieldPolySource {
                start: copy_output.as_ptr(),
                next_layer_size: 2,
                source_kind: GpuBaseFieldSourceKind::Real,
            }])
            .unwrap();
        let lookup_base_inputs = inline_builder
            .try_push_copy(&[
                GpuBaseFieldPolySource {
                    start: lookup_b.as_ptr(),
                    next_layer_size: 2,
                    source_kind: GpuBaseFieldSourceKind::Real,
                },
                GpuBaseFieldPolySource {
                    start: lookup_d.as_ptr(),
                    next_layer_size: 2,
                    source_kind: GpuBaseFieldSourceKind::Real,
                },
            ])
            .unwrap();
        let lookup_extension_outputs = inline_builder
            .try_push_copy(&[
                GpuExtensionFieldPolyInitialSource {
                    start: lookup_num.as_ptr(),
                    next_layer_size: 2,
                },
                GpuExtensionFieldPolyInitialSource {
                    start: lookup_den.as_ptr(),
                    next_layer_size: 2,
                },
            ])
            .unwrap();

        let mut batch_static = super::GpuGKRMainRound0BatchStatic::default();
        batch_static.record_count = 2;
        batch_static.inline_payload = inline_builder.into_bytes();
        batch_static.records[0] = super::GpuGKRMainRound0BatchRecord {
            kind: GpuGKRMainLayerKernelKind::BaseCopy.as_u32(),
            record_mode: super::GpuGKRMainLayerBatchRecordMode::InlineAll.as_u32(),
            metadata_inline: 1,
            _reserved: 0,
            base_inputs: copy_base_inputs,
            extension_inputs: super::GpuGKRMainLayerPayloadRange::default(),
            base_outputs: copy_base_outputs,
            extension_outputs: super::GpuGKRMainLayerPayloadRange::default(),
            quadratic_terms: super::GpuGKRMainLayerPayloadRange::default(),
            linear_terms: super::GpuGKRMainLayerPayloadRange::default(),
            auxiliary_challenge: E4::ZERO,
            constant_offset: E4::ZERO,
        };
        batch_static.records[1] = super::GpuGKRMainRound0BatchRecord {
            kind: GpuGKRMainLayerKernelKind::LookupBasePair.as_u32(),
            record_mode: super::GpuGKRMainLayerBatchRecordMode::InlineAll.as_u32(),
            metadata_inline: 1,
            _reserved: 0,
            base_inputs: lookup_base_inputs,
            extension_inputs: super::GpuGKRMainLayerPayloadRange::default(),
            base_outputs: super::GpuGKRMainLayerPayloadRange::default(),
            extension_outputs: lookup_extension_outputs,
            quadratic_terms: super::GpuGKRMainLayerPayloadRange::default(),
            linear_terms: super::GpuGKRMainLayerPayloadRange::default(),
            auxiliary_challenge: lookup_additive_challenge,
            constant_offset: E4::ZERO,
        };
        let batch_runtime = super::GpuGKRMainRound0BatchRuntime {
            eq_values: eq_dev.as_ptr(),
            batch_challenges: batch_challenges_dev.as_ptr(),
            contributions: contributions.as_mut_ptr(),
            spill_payload: null(),
            auxiliary_challenges: null(),
            constraint_metadata: null(),
        };

        super::launch_main_round0_batched(&batch_static, &batch_runtime, 2, &context).unwrap();

        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let mut expected = Vec::new();
        for gid in 0..2 {
            let mut copy_c0 = copy_batch;
            copy_c0.mul_assign_by_base(&copy_output_values[gid]);

            let mut lookup_c0 = lookup_batch0;
            lookup_c0.mul_assign(&lookup_num_values[gid]);
            let mut lookup_den_term = lookup_batch1;
            lookup_den_term.mul_assign(&lookup_den_values[gid]);
            lookup_c0.add_assign(&lookup_den_term);

            let mut b1 = lookup_b_values[gid + 2];
            b1.sub_assign(&lookup_b_values[gid]);
            let mut d1 = lookup_d_values[gid + 2];
            d1.sub_assign(&lookup_d_values[gid]);
            let mut lookup_den = b1;
            lookup_den.mul_assign(&d1);
            let mut lookup_c1 = lookup_batch1;
            lookup_c1.mul_assign_by_base(&lookup_den);

            let mut total0 = copy_c0;
            total0.add_assign(&lookup_c0);
            total0.mul_assign(&eq[gid]);
            let mut total1 = lookup_c1;
            total1.mul_assign(&eq[gid]);
            expected.push(total0);
            expected.push(total1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round1_base_copy_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_values = (0..8).map(|i| BF::new(10 + i)).collect::<Vec<_>>();
        let input = alloc_and_copy(&context, &input_values);

        let folding_challenge = sample_ext(200);
        let batch_challenge = sample_ext(300);
        let folding_challenge_dev = alloc_and_copy(&context, &[folding_challenge]);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch_challenge, E4::ZERO]);
        let auxiliary_challenge_dev = alloc_and_copy(&context, &[E4::ZERO]);
        let base_cache: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();

        let base_descriptors = [
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input.as_ptr(),
                this_layer_cache_start: base_cache.as_ptr().cast_mut(),
                first_access: true,
                source_kind: GpuBaseFieldSourceKind::Real,
                _marker: core::marker::PhantomData,
            },
        ];
        let base_descriptors_dev = alloc_and_copy(&context, &base_descriptors);
        let ext_descriptors_dev = context
            .alloc::<GpuExtensionFieldPolyContinuingLaunchDescriptor<E4>>(
                0,
                AllocationPlacement::Top,
            )
            .unwrap();
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();

        let scheduled = crate::prover::gkr::GpuSumcheckRound1ScheduledLaunchDescriptors {
            device: crate::prover::gkr::GpuSumcheckRound1DeviceLaunchDescriptors {
                base_field_inputs: base_descriptors_dev,
                extension_field_inputs: ext_descriptors_dev,
            },
        };

        super::launch_main_round1(
            GpuGKRMainLayerKernelKind::BaseCopy,
            &scheduled,
            batch_challenges_dev.as_ptr(),
            folding_challenge_dev.as_ptr(),
            auxiliary_challenge_dev.as_ptr(),
            None,
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

        let fold_base = |values: &[BF], idx: usize| {
            let mut diff = values[4 + idx];
            diff.sub_assign(&values[idx]);
            let mut result = folding_challenge;
            result.mul_assign_by_base(&diff);
            result.add_assign_base(&values[idx]);
            result
        };

        let mut expected = Vec::new();
        for gid in 0..2 {
            let mut c0 = batch_challenge;
            c0.mul_assign(&fold_base(&input_values, gid));
            expected.push(c0);
            expected.push(E4::ZERO);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round1_ext_copy_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_values = (0..8).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let input = alloc_and_copy(&context, &input_values);

        let folding_challenge = sample_ext(200);
        let batch_challenge = sample_ext(300);
        let folding_challenge_dev = alloc_and_copy(&context, &[folding_challenge]);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch_challenge, E4::ZERO]);
        let auxiliary_challenge_dev = alloc_and_copy(&context, &[E4::ZERO]);
        let cache: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();

        let base_descriptors_dev = context
            .alloc::<crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor<BF, E4>>(0, AllocationPlacement::Top)
            .unwrap();
        let ext_descriptors = [GpuExtensionFieldPolyContinuingLaunchDescriptor {
            previous_layer_start: input.as_ptr(),
            this_layer_start: cache.as_ptr().cast_mut(),
            this_layer_size: 4,
            next_layer_size: 2,
            first_access: true,
        }];
        let ext_descriptors_dev = alloc_and_copy(&context, &ext_descriptors);
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();

        let scheduled = crate::prover::gkr::GpuSumcheckRound1ScheduledLaunchDescriptors {
            device: crate::prover::gkr::GpuSumcheckRound1DeviceLaunchDescriptors {
                base_field_inputs: base_descriptors_dev,
                extension_field_inputs: ext_descriptors_dev,
            },
        };

        super::launch_main_round1(
            GpuGKRMainLayerKernelKind::ExtCopy,
            &scheduled,
            batch_challenges_dev.as_ptr(),
            folding_challenge_dev.as_ptr(),
            auxiliary_challenge_dev.as_ptr(),
            None,
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

        let fold_ext = |values: &[E4], idx: usize| {
            let mut diff = values[4 + idx];
            diff.sub_assign(&values[idx]);
            let mut result = folding_challenge;
            result.mul_assign(&diff);
            result.add_assign(&values[idx]);
            result
        };

        let mut expected = Vec::new();
        for gid in 0..2 {
            let mut c0 = batch_challenge;
            c0.mul_assign(&fold_ext(&input_values, gid));
            expected.push(c0);
            expected.push(E4::ZERO);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round1_product_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_a_values = (0..8).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let input_b_values = (0..8).map(|i| sample_ext(30 + i)).collect::<Vec<_>>();
        let input_a = alloc_and_copy(&context, &input_a_values);
        let input_b = alloc_and_copy(&context, &input_b_values);

        let folding_challenge = sample_ext(200);
        let batch_challenge = sample_ext(300);
        let folding_challenge_dev = alloc_and_copy(&context, &[folding_challenge]);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch_challenge, E4::ZERO]);
        let auxiliary_challenge_dev = alloc_and_copy(&context, &[E4::ZERO]);
        let cache_a: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();
        let cache_b: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();

        let base_descriptors_dev = context
            .alloc::<crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor<BF, E4>>(0, AllocationPlacement::Top)
            .unwrap();
        let ext_descriptors = [
            GpuExtensionFieldPolyContinuingLaunchDescriptor {
                previous_layer_start: input_a.as_ptr(),
                this_layer_start: cache_a.as_ptr().cast_mut(),
                this_layer_size: 4,
                next_layer_size: 2,
                first_access: true,
            },
            GpuExtensionFieldPolyContinuingLaunchDescriptor {
                previous_layer_start: input_b.as_ptr(),
                this_layer_start: cache_b.as_ptr().cast_mut(),
                this_layer_size: 4,
                next_layer_size: 2,
                first_access: true,
            },
        ];
        let ext_descriptors_dev = alloc_and_copy(&context, &ext_descriptors);
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();

        let scheduled = crate::prover::gkr::GpuSumcheckRound1ScheduledLaunchDescriptors {
            device: crate::prover::gkr::GpuSumcheckRound1DeviceLaunchDescriptors {
                base_field_inputs: base_descriptors_dev,
                extension_field_inputs: ext_descriptors_dev,
            },
        };

        super::launch_main_round1(
            GpuGKRMainLayerKernelKind::Product,
            &scheduled,
            batch_challenges_dev.as_ptr(),
            folding_challenge_dev.as_ptr(),
            auxiliary_challenge_dev.as_ptr(),
            None,
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

        let fold_ext = |values: &[E4], idx: usize| {
            let mut diff = values[4 + idx];
            diff.sub_assign(&values[idx]);
            let mut result = folding_challenge;
            result.mul_assign(&diff);
            result.add_assign(&values[idx]);
            result
        };

        let mut expected = Vec::new();
        for gid in 0..2 {
            let a0 = fold_ext(&input_a_values, gid);
            let a1_full = fold_ext(&input_a_values, gid + 2);
            let mut da = a1_full;
            da.sub_assign(&a0);

            let b0 = fold_ext(&input_b_values, gid);
            let b1_full = fold_ext(&input_b_values, gid + 2);
            let mut db = b1_full;
            db.sub_assign(&b0);

            let mut c0 = batch_challenge;
            let mut eval0 = a0;
            eval0.mul_assign(&b0);
            c0.mul_assign(&eval0);

            let mut c1 = batch_challenge;
            let mut eval1 = da;
            eval1.mul_assign(&db);
            c1.mul_assign(&eval1);

            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round1_enforce_constraints_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_a_values = (0..8).map(|i| BF::new(10 + i)).collect::<Vec<_>>();
        let input_b_values = (0..8).map(|i| BF::new(30 + i)).collect::<Vec<_>>();
        let input_c_values = (0..8).map(|i| BF::new(50 + i)).collect::<Vec<_>>();
        let input_a = alloc_and_copy(&context, &input_a_values);
        let input_b = alloc_and_copy(&context, &input_b_values);
        let input_c = alloc_and_copy(&context, &input_c_values);

        let folding_challenge = sample_ext(200);
        let batch_challenge = sample_ext(300);
        let constant_offset = sample_ext(400);
        let quadratic_terms = vec![
            GpuGKRMainLayerConstraintQuadraticTerm {
                lhs: 0,
                rhs: 1,
                challenge: sample_ext(500),
            },
            GpuGKRMainLayerConstraintQuadraticTerm {
                lhs: 1,
                rhs: 2,
                challenge: sample_ext(600),
            },
        ];
        let linear_terms = vec![GpuGKRMainLayerConstraintLinearTerm {
            input: 2,
            challenge: sample_ext(700),
        }];
        let folding_challenge_dev = alloc_and_copy(&context, &[folding_challenge]);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch_challenge, E4::ZERO]);
        let auxiliary_challenge_dev = alloc_and_copy(&context, &[E4::ZERO]);
        let base_cache: DeviceAllocation<E4> = context.alloc(12, AllocationPlacement::Top).unwrap();

        let base_descriptors = [
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_a.as_ptr(),
                this_layer_cache_start: base_cache.as_ptr().cast_mut(),
                first_access: true,
                source_kind: GpuBaseFieldSourceKind::Real,
                _marker: core::marker::PhantomData::<E4>,
            },
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_b.as_ptr(),
                this_layer_cache_start: unsafe { base_cache.as_ptr().cast_mut().add(4) },
                first_access: true,
                source_kind: GpuBaseFieldSourceKind::Real,
                _marker: core::marker::PhantomData::<E4>,
            },
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_c.as_ptr(),
                this_layer_cache_start: unsafe { base_cache.as_ptr().cast_mut().add(8) },
                first_access: true,
                source_kind: GpuBaseFieldSourceKind::Real,
                _marker: core::marker::PhantomData::<E4>,
            },
        ];
        let base_descriptors_dev = alloc_and_copy(&context, &base_descriptors);
        let ext_descriptors_dev = context
            .alloc::<GpuExtensionFieldPolyContinuingLaunchDescriptor<E4>>(
                0,
                AllocationPlacement::Top,
            )
            .unwrap();
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();

        let constraint_upload = super::ScheduledMainLayerConstraintMetadataUpload {
            callbacks: Callbacks::new(),
            quadratic_terms: super::ScheduledUpload {
                callbacks: Callbacks::new(),
                device: alloc_and_copy(&context, &quadratic_terms),
            },
            linear_terms: super::ScheduledUpload {
                callbacks: Callbacks::new(),
                device: alloc_and_copy(&context, &linear_terms),
            },
            constant_offset: super::ScheduledUpload {
                callbacks: Callbacks::new(),
                device: alloc_and_copy(&context, &[constant_offset]),
            },
        };

        let scheduled = crate::prover::gkr::GpuSumcheckRound1ScheduledLaunchDescriptors {
            device: crate::prover::gkr::GpuSumcheckRound1DeviceLaunchDescriptors {
                base_field_inputs: base_descriptors_dev,
                extension_field_inputs: ext_descriptors_dev,
            },
        };

        super::launch_main_round1(
            GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic,
            &scheduled,
            batch_challenges_dev.as_ptr(),
            folding_challenge_dev.as_ptr(),
            auxiliary_challenge_dev.as_ptr(),
            Some(&constraint_upload),
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

        let fold_base = |values: &[BF], idx: usize| {
            let mut diff = values[4 + idx];
            diff.sub_assign(&values[idx]);
            let mut result = folding_challenge;
            result.mul_assign_by_base(&diff);
            result.add_assign_base(&values[idx]);
            result
        };

        let mut expected = Vec::new();
        for gid in 0..2 {
            let a0 = fold_base(&input_a_values, gid);
            let a1_full = fold_base(&input_a_values, gid + 2);
            let mut da = a1_full;
            da.sub_assign(&a0);

            let b0 = fold_base(&input_b_values, gid);
            let b1_full = fold_base(&input_b_values, gid + 2);
            let mut db = b1_full;
            db.sub_assign(&b0);

            let c0_in = fold_base(&input_c_values, gid);

            let mut eval0 = constant_offset;
            let mut term0 = a0;
            term0.mul_assign(&b0);
            term0.mul_assign(&quadratic_terms[0].challenge);
            eval0.add_assign(&term0);
            let mut term1 = b0;
            term1.mul_assign(&c0_in);
            term1.mul_assign(&quadratic_terms[1].challenge);
            eval0.add_assign(&term1);
            let mut linear = c0_in;
            linear.mul_assign(&linear_terms[0].challenge);
            eval0.add_assign(&linear);

            let mut eval1 = E4::ZERO;
            let mut delta0 = da;
            delta0.mul_assign(&db);
            delta0.mul_assign(&quadratic_terms[0].challenge);
            eval1.add_assign(&delta0);

            let c1_full = fold_base(&input_c_values, gid + 2);
            let mut dc = c1_full;
            dc.sub_assign(&c0_in);
            let mut delta1 = db;
            delta1.mul_assign(&dc);
            delta1.mul_assign(&quadratic_terms[1].challenge);
            eval1.add_assign(&delta1);

            let mut c0 = batch_challenge;
            c0.mul_assign(&eval0);
            let mut c1 = batch_challenge;
            c1.mul_assign(&eval1);
            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round1_batched_enforce_constraints_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_a_values = (0..8).map(|i| BF::new(10 + i)).collect::<Vec<_>>();
        let input_b_values = (0..8).map(|i| BF::new(30 + i)).collect::<Vec<_>>();
        let input_c_values = (0..8).map(|i| BF::new(50 + i)).collect::<Vec<_>>();
        let claim_point = [sample_ext(90), sample_ext(91), sample_ext(92)];
        let input_a = alloc_and_copy(&context, &input_a_values);
        let input_b = alloc_and_copy(&context, &input_b_values);
        let input_c = alloc_and_copy(&context, &input_c_values);
        let eq = eq_weights_for_binary_tail(claim_point[2]);
        let eq_dev = alloc_and_copy(&context, &eq);

        let folding_challenge = sample_ext(200);
        let batch_challenge = sample_ext(300);
        let constant_offset = sample_ext(400);
        let quadratic_terms = vec![
            GpuGKRMainLayerConstraintQuadraticTerm {
                lhs: 0,
                rhs: 1,
                challenge: sample_ext(500),
            },
            GpuGKRMainLayerConstraintQuadraticTerm {
                lhs: 1,
                rhs: 2,
                challenge: sample_ext(600),
            },
        ];
        let linear_terms = vec![GpuGKRMainLayerConstraintLinearTerm {
            input: 2,
            challenge: sample_ext(700),
        }];
        let folding_challenge_dev = alloc_and_copy(&context, &[folding_challenge]);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch_challenge]);
        let base_cache: DeviceAllocation<E4> = context.alloc(12, AllocationPlacement::Top).unwrap();

        let base_descriptors = [
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_a.as_ptr(),
                this_layer_cache_start: base_cache.as_ptr().cast_mut(),
                first_access: true,
                source_kind: GpuBaseFieldSourceKind::Real,
                _marker: core::marker::PhantomData::<E4>,
            },
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_b.as_ptr(),
                this_layer_cache_start: unsafe { base_cache.as_ptr().cast_mut().add(4) },
                first_access: true,
                source_kind: GpuBaseFieldSourceKind::Real,
                _marker: core::marker::PhantomData::<E4>,
            },
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_c.as_ptr(),
                this_layer_cache_start: unsafe { base_cache.as_ptr().cast_mut().add(8) },
                first_access: true,
                source_kind: GpuBaseFieldSourceKind::Real,
                _marker: core::marker::PhantomData::<E4>,
            },
        ];
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();
        let mut spill_builder = super::SpillPayloadBuilder::default();
        let base_inputs = spill_builder.push_copy(&base_descriptors);
        let extension_inputs = super::GpuGKRMainLayerPayloadRange::default();
        let quadratic_terms_range = spill_builder.push_copy(&quadratic_terms);
        let linear_terms_range = spill_builder.push_copy(&linear_terms);
        let spill_payload_dev = alloc_and_copy(&context, spill_builder.bytes.as_slice());

        let mut batch_static = super::GpuGKRMainRound1BatchStatic::default();
        batch_static.record_count = 1;
        batch_static.records[0] = super::GpuGKRMainRound1BatchRecord {
            kind: GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic.as_u32(),
            record_mode: super::GpuGKRMainLayerBatchRecordMode::PointerDescriptors.as_u32(),
            metadata_inline: 0,
            _reserved: 0,
            base_inputs,
            extension_inputs,
            quadratic_terms: quadratic_terms_range,
            linear_terms: linear_terms_range,
            auxiliary_challenge: E4::ZERO,
            constant_offset,
        };
        let batch_runtime = super::GpuGKRMainRound1BatchRuntime {
            eq_values: eq_dev.as_ptr(),
            batch_challenges: batch_challenges_dev.as_ptr(),
            folding_challenge: folding_challenge_dev.as_ptr(),
            contributions: contributions.as_mut_ptr(),
            spill_payload: spill_payload_dev.as_ptr(),
            auxiliary_challenges: null(),
            constraint_metadata: null(),
        };

        super::launch_main_round1_batched(&batch_static, &batch_runtime, 2, false, &context)
            .unwrap();

        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let fold_base = |values: &[BF], idx: usize| {
            let mut diff = values[4 + idx];
            diff.sub_assign(&values[idx]);
            let mut result = folding_challenge;
            result.mul_assign_by_base(&diff);
            result.add_assign_base(&values[idx]);
            result
        };

        let mut expected = Vec::new();
        for gid in 0..2 {
            let a0 = fold_base(&input_a_values, gid);
            let a1_full = fold_base(&input_a_values, gid + 2);
            let mut da = a1_full;
            da.sub_assign(&a0);

            let b0 = fold_base(&input_b_values, gid);
            let b1_full = fold_base(&input_b_values, gid + 2);
            let mut db = b1_full;
            db.sub_assign(&b0);

            let c0_in = fold_base(&input_c_values, gid);

            let mut eval0 = constant_offset;
            let mut term0 = a0;
            term0.mul_assign(&b0);
            term0.mul_assign(&quadratic_terms[0].challenge);
            eval0.add_assign(&term0);
            let mut term1 = b0;
            term1.mul_assign(&c0_in);
            term1.mul_assign(&quadratic_terms[1].challenge);
            eval0.add_assign(&term1);
            let mut linear = c0_in;
            linear.mul_assign(&linear_terms[0].challenge);
            eval0.add_assign(&linear);

            let mut eval1 = E4::ZERO;
            let mut delta0 = da;
            delta0.mul_assign(&db);
            delta0.mul_assign(&quadratic_terms[0].challenge);
            eval1.add_assign(&delta0);

            let c1_full = fold_base(&input_c_values, gid + 2);
            let mut dc = c1_full;
            dc.sub_assign(&c0_in);
            let mut delta1 = db;
            delta1.mul_assign(&dc);
            delta1.mul_assign(&quadratic_terms[1].challenge);
            eval1.add_assign(&delta1);

            let mut c0 = batch_challenge;
            c0.mul_assign(&eval0);
            c0.mul_assign(&eq[gid]);
            let mut c1 = batch_challenge;
            c1.mul_assign(&eval1);
            c1.mul_assign(&eq[gid]);
            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round1_batched_mixed_challenge_arities_match_cpu() {
        let context = make_test_context(64, 8);
        let copy_input_values = (0..8).map(|i| BF::new(10 + i)).collect::<Vec<_>>();
        let lookup_b_values = (0..8).map(|i| BF::new(30 + i)).collect::<Vec<_>>();
        let lookup_d_values = (0..8).map(|i| BF::new(50 + i)).collect::<Vec<_>>();
        let claim_point = [sample_ext(80), sample_ext(81), sample_ext(82)];

        let copy_input = alloc_and_copy(&context, &copy_input_values);
        let lookup_b = alloc_and_copy(&context, &lookup_b_values);
        let lookup_d = alloc_and_copy(&context, &lookup_d_values);
        let eq = eq_weights_for_binary_tail(claim_point[2]);
        let eq_dev = alloc_and_copy(&context, &eq);

        let folding_challenge = sample_ext(100);
        let copy_batch = sample_ext(200);
        let lookup_batch0 = sample_ext(300);
        let lookup_batch1 = sample_ext(400);
        let lookup_additive_challenge = sample_ext(500);
        let folding_challenge_dev = alloc_and_copy(&context, &[folding_challenge]);
        let batch_challenges_dev =
            alloc_and_copy(&context, &[copy_batch, lookup_batch0, lookup_batch1]);
        let base_cache: DeviceAllocation<E4> = context.alloc(12, AllocationPlacement::Top).unwrap();
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();

        let mut inline_builder = super::InlinePayloadBuilder::new();
        let copy_base_inputs = inline_builder
            .try_push_copy(&[
                crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                    base_layer_half_size: 4,
                    next_layer_size: 2,
                    base_input_start: copy_input.as_ptr(),
                    this_layer_cache_start: base_cache.as_ptr().cast_mut(),
                    first_access: true,
                    source_kind: GpuBaseFieldSourceKind::Real,
                    _marker: core::marker::PhantomData::<E4>,
                },
            ])
            .unwrap();
        let lookup_base_inputs = inline_builder
            .try_push_copy(&[
                crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                    base_layer_half_size: 4,
                    next_layer_size: 2,
                    base_input_start: lookup_b.as_ptr(),
                    this_layer_cache_start: unsafe { base_cache.as_ptr().cast_mut().add(4) },
                    first_access: true,
                    source_kind: GpuBaseFieldSourceKind::Real,
                    _marker: core::marker::PhantomData::<E4>,
                },
                crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                    base_layer_half_size: 4,
                    next_layer_size: 2,
                    base_input_start: lookup_d.as_ptr(),
                    this_layer_cache_start: unsafe { base_cache.as_ptr().cast_mut().add(8) },
                    first_access: true,
                    source_kind: GpuBaseFieldSourceKind::Real,
                    _marker: core::marker::PhantomData::<E4>,
                },
            ])
            .unwrap();

        let mut batch_static = super::GpuGKRMainRound1BatchStatic::default();
        batch_static.record_count = 2;
        batch_static.inline_payload = inline_builder.into_bytes();
        batch_static.records[0] = super::GpuGKRMainRound1BatchRecord {
            kind: GpuGKRMainLayerKernelKind::BaseCopy.as_u32(),
            record_mode: super::GpuGKRMainLayerBatchRecordMode::InlineAll.as_u32(),
            metadata_inline: 1,
            _reserved: 0,
            base_inputs: copy_base_inputs,
            extension_inputs: super::GpuGKRMainLayerPayloadRange::default(),
            quadratic_terms: super::GpuGKRMainLayerPayloadRange::default(),
            linear_terms: super::GpuGKRMainLayerPayloadRange::default(),
            auxiliary_challenge: E4::ZERO,
            constant_offset: E4::ZERO,
        };
        batch_static.records[1] = super::GpuGKRMainRound1BatchRecord {
            kind: GpuGKRMainLayerKernelKind::LookupBasePair.as_u32(),
            record_mode: super::GpuGKRMainLayerBatchRecordMode::InlineAll.as_u32(),
            metadata_inline: 1,
            _reserved: 0,
            base_inputs: lookup_base_inputs,
            extension_inputs: super::GpuGKRMainLayerPayloadRange::default(),
            quadratic_terms: super::GpuGKRMainLayerPayloadRange::default(),
            linear_terms: super::GpuGKRMainLayerPayloadRange::default(),
            auxiliary_challenge: lookup_additive_challenge,
            constant_offset: E4::ZERO,
        };
        let batch_runtime = super::GpuGKRMainRound1BatchRuntime {
            eq_values: eq_dev.as_ptr(),
            batch_challenges: batch_challenges_dev.as_ptr(),
            folding_challenge: folding_challenge_dev.as_ptr(),
            contributions: contributions.as_mut_ptr(),
            spill_payload: null(),
            auxiliary_challenges: null(),
            constraint_metadata: null(),
        };

        super::launch_main_round1_batched(&batch_static, &batch_runtime, 2, false, &context)
            .unwrap();

        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let fold_base = |values: &[BF], idx: usize| {
            let mut diff = values[4 + idx];
            diff.sub_assign(&values[idx]);
            let mut result = folding_challenge;
            result.mul_assign_by_base(&diff);
            result.add_assign_base(&values[idx]);
            result
        };

        let mut expected = Vec::new();
        for gid in 0..2 {
            let mut copy_c0 = copy_batch;
            copy_c0.mul_assign(&fold_base(&copy_input_values, gid));

            let b0 = fold_base(&lookup_b_values, gid);
            let b1_full = fold_base(&lookup_b_values, gid + 2);
            let mut db = b1_full;
            db.sub_assign(&b0);

            let d0 = fold_base(&lookup_d_values, gid);
            let d1_full = fold_base(&lookup_d_values, gid + 2);
            let mut dd = d1_full;
            dd.sub_assign(&d0);

            let mut shifted_b0 = b0;
            shifted_b0.add_assign(&lookup_additive_challenge);
            let mut shifted_d0 = d0;
            shifted_d0.add_assign(&lookup_additive_challenge);

            let mut num0 = shifted_b0;
            num0.add_assign(&shifted_d0);
            let mut den0 = shifted_b0;
            den0.mul_assign(&shifted_d0);

            let mut lookup_c0 = lookup_batch0;
            lookup_c0.mul_assign(&num0);
            let mut lookup_c0_den = lookup_batch1;
            lookup_c0_den.mul_assign(&den0);
            lookup_c0.add_assign(&lookup_c0_den);

            let mut lookup_c1 = lookup_batch1;
            let mut den1 = db;
            den1.mul_assign(&dd);
            lookup_c1.mul_assign(&den1);

            let mut total0 = copy_c0;
            total0.add_assign(&lookup_c0);
            total0.mul_assign(&eq[gid]);
            let mut total1 = lookup_c1;
            total1.mul_assign(&eq[gid]);
            expected.push(total0);
            expected.push(total1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round0_lookup_base_pair_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_b_values = (0..4).map(|i| BF::new(10 + i)).collect::<Vec<_>>();
        let input_d_values = (0..4).map(|i| BF::new(30 + i)).collect::<Vec<_>>();
        let output_num_values = (0..4).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
        let output_den_values = (0..4).map(|i| sample_ext(200 + i)).collect::<Vec<_>>();
        let input_b = alloc_and_copy(&context, &input_b_values);
        let input_d = alloc_and_copy(&context, &input_d_values);
        let output_num = alloc_and_copy(&context, &output_num_values);
        let output_den = alloc_and_copy(&context, &output_den_values);
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();
        let batch0 = sample_ext(300);
        let batch1 = sample_ext(400);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch0, batch1]);
        let lookup_additive_challenge = sample_ext(500);
        let auxiliary_challenge_dev = alloc_and_copy(&context, &[lookup_additive_challenge]);

        let mut round0 = GpuSumcheckRound0ScheduledLaunchDescriptors {
            callbacks: Callbacks::new(),
            host: GpuSumcheckRound0HostLaunchDescriptors {
                base_field_inputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(2)
                },
                extension_field_inputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(0)
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
                    .alloc::<GpuBaseFieldPolySource<BF>>(2, AllocationPlacement::Top)
                    .unwrap(),
                extension_field_inputs: context
                    .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(0, AllocationPlacement::Top)
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
            round0.host.base_field_inputs.get_mut_accessor().get_mut()[0] =
                GpuBaseFieldPolySource {
                    start: input_b.as_ptr(),
                    next_layer_size: 2,
                    source_kind: GpuBaseFieldSourceKind::Real,
                };
            round0.host.base_field_inputs.get_mut_accessor().get_mut()[1] =
                GpuBaseFieldPolySource {
                    start: input_d.as_ptr(),
                    next_layer_size: 2,
                    source_kind: GpuBaseFieldSourceKind::Real,
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
            &mut round0.device.base_field_inputs,
            &round0.host.base_field_inputs,
            context.get_exec_stream(),
        )
        .unwrap();
        memory_copy_async(
            &mut round0.device.extension_field_outputs,
            &round0.host.extension_field_outputs,
            context.get_exec_stream(),
        )
        .unwrap();

        launch_main_round0(
            GpuGKRMainLayerKernelKind::LookupBasePair,
            &round0,
            batch_challenges_dev.as_ptr(),
            auxiliary_challenge_dev.as_ptr(),
            None,
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
            let mut c0 = batch0;
            c0.mul_assign(&output_num_values[output_index]);
            let mut output_den_term = batch1;
            output_den_term.mul_assign(&output_den_values[output_index]);
            c0.add_assign(&output_den_term);

            let mut b1 = input_b_values[2 + output_index];
            b1.sub_assign(&input_b_values[output_index]);
            let mut d1 = input_d_values[2 + output_index];
            d1.sub_assign(&input_d_values[output_index]);
            let mut den = b1;
            den.mul_assign(&d1);

            let mut c1 = batch1;
            c1.mul_assign_by_base(&den);

            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round1_lookup_with_cached_dens_and_setup_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_a_values = (0..8).map(|i| BF::new(10 + i)).collect::<Vec<_>>();
        let input_c_values = (0..8).map(|i| BF::new(30 + i)).collect::<Vec<_>>();
        let input_b_values = (0..8).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
        let input_d_values = (0..8).map(|i| sample_ext(200 + i)).collect::<Vec<_>>();

        let input_a = alloc_and_copy(&context, &input_a_values);
        let input_c = alloc_and_copy(&context, &input_c_values);
        let input_b = alloc_and_copy(&context, &input_b_values);
        let input_d = alloc_and_copy(&context, &input_d_values);

        let folding_challenge = sample_ext(300);
        let batch0 = sample_ext(400);
        let batch1 = sample_ext(500);
        let lookup_additive_challenge = sample_ext(600);
        let folding_challenge_dev = alloc_and_copy(&context, &[folding_challenge]);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch0, batch1]);
        let auxiliary_challenge_dev = alloc_and_copy(&context, &[lookup_additive_challenge]);
        let cache_b: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();
        let cache_d: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();
        let base_cache: DeviceAllocation<E4> = context.alloc(8, AllocationPlacement::Top).unwrap();

        let base_descriptors = [
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_a.as_ptr(),
                this_layer_cache_start: base_cache.as_ptr().cast_mut(),
                first_access: true,
                source_kind: GpuBaseFieldSourceKind::Real,
                _marker: core::marker::PhantomData,
            },
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_c.as_ptr(),
                this_layer_cache_start: unsafe { base_cache.as_ptr().cast_mut().add(4) },
                first_access: true,
                source_kind: GpuBaseFieldSourceKind::Real,
                _marker: core::marker::PhantomData,
            },
        ];
        let ext_descriptors = [
            GpuExtensionFieldPolyContinuingLaunchDescriptor {
                previous_layer_start: input_b.as_ptr(),
                this_layer_start: cache_b.as_ptr().cast_mut(),
                this_layer_size: 4,
                next_layer_size: 2,
                first_access: true,
            },
            GpuExtensionFieldPolyContinuingLaunchDescriptor {
                previous_layer_start: input_d.as_ptr(),
                this_layer_start: cache_d.as_ptr().cast_mut(),
                this_layer_size: 4,
                next_layer_size: 2,
                first_access: true,
            },
        ];
        let base_descriptors_dev = alloc_and_copy(&context, &base_descriptors);
        let ext_descriptors_dev = alloc_and_copy(&context, &ext_descriptors);
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();

        let scheduled = crate::prover::gkr::GpuSumcheckRound1ScheduledLaunchDescriptors {
            device: crate::prover::gkr::GpuSumcheckRound1DeviceLaunchDescriptors {
                base_field_inputs: base_descriptors_dev,
                extension_field_inputs: ext_descriptors_dev,
            },
        };

        super::launch_main_round1(
            GpuGKRMainLayerKernelKind::LookupWithCachedDensAndSetup,
            &scheduled,
            batch_challenges_dev.as_ptr(),
            folding_challenge_dev.as_ptr(),
            auxiliary_challenge_dev.as_ptr(),
            None,
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

        let fold_base = |values: &[BF], idx: usize| {
            let mut diff = values[4 + idx];
            diff.sub_assign(&values[idx]);
            let mut result = folding_challenge;
            result.mul_assign_by_base(&diff);
            result.add_assign_base(&values[idx]);
            result
        };
        let fold_ext = |values: &[E4], idx: usize| {
            let mut diff = values[4 + idx];
            diff.sub_assign(&values[idx]);
            let mut result = folding_challenge;
            result.mul_assign(&diff);
            result.add_assign(&values[idx]);
            result
        };

        let mut expected = Vec::new();
        for gid in 0..2 {
            let a0 = fold_base(&input_a_values, gid);
            let a1_full = fold_base(&input_a_values, gid + 2);
            let mut da = a1_full;
            da.sub_assign(&a0);

            let c0_in = fold_base(&input_c_values, gid);
            let c1_full = fold_base(&input_c_values, gid + 2);
            let mut dc = c1_full;
            dc.sub_assign(&c0_in);

            let b0 = fold_ext(&input_b_values, gid);
            let b1_full = fold_ext(&input_b_values, gid + 2);
            let mut db = b1_full;
            db.sub_assign(&b0);

            let d0 = fold_ext(&input_d_values, gid);
            let d1_full = fold_ext(&input_d_values, gid + 2);
            let mut dd = d1_full;
            dd.sub_assign(&d0);

            let mut shifted_b0 = b0;
            shifted_b0.add_assign(&lookup_additive_challenge);
            let mut shifted_d0 = d0;
            shifted_d0.add_assign(&lookup_additive_challenge);
            let mut num0 = a0;
            num0.mul_assign(&shifted_d0);
            let mut t0 = c0_in;
            t0.mul_assign(&shifted_b0);
            num0.sub_assign(&t0);
            let mut den0 = shifted_b0;
            den0.mul_assign(&shifted_d0);

            let mut num1 = da;
            num1.mul_assign(&dd);
            let mut t1 = dc;
            t1.mul_assign(&db);
            num1.sub_assign(&t1);
            let mut den1 = db;
            den1.mul_assign(&dd);

            let mut c0 = batch0;
            c0.mul_assign(&num0);
            let mut c0_den = batch1;
            c0_den.mul_assign(&den0);
            c0.add_assign(&c0_den);

            let mut c1 = batch0;
            c1.mul_assign(&num1);
            let mut c1_den = batch1;
            c1_den.mul_assign(&den1);
            c1.add_assign(&c1_den);

            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round1_lookup_base_pair_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_b_values = (0..8).map(|i| BF::new(10 + i)).collect::<Vec<_>>();
        let input_d_values = (0..8).map(|i| BF::new(30 + i)).collect::<Vec<_>>();

        let input_b = alloc_and_copy(&context, &input_b_values);
        let input_d = alloc_and_copy(&context, &input_d_values);

        let folding_challenge = sample_ext(300);
        let batch0 = sample_ext(400);
        let batch1 = sample_ext(500);
        let lookup_additive_challenge = sample_ext(600);
        let folding_challenge_dev = alloc_and_copy(&context, &[folding_challenge]);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch0, batch1]);
        let auxiliary_challenge_dev = alloc_and_copy(&context, &[lookup_additive_challenge]);
        let base_cache: DeviceAllocation<E4> = context.alloc(8, AllocationPlacement::Top).unwrap();

        let base_descriptors = [
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_b.as_ptr(),
                this_layer_cache_start: base_cache.as_ptr().cast_mut(),
                first_access: true,
                source_kind: GpuBaseFieldSourceKind::Real,
                _marker: core::marker::PhantomData,
            },
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_d.as_ptr(),
                this_layer_cache_start: unsafe { base_cache.as_ptr().cast_mut().add(4) },
                first_access: true,
                source_kind: GpuBaseFieldSourceKind::Real,
                _marker: core::marker::PhantomData,
            },
        ];
        let base_descriptors_dev = alloc_and_copy(&context, &base_descriptors);
        let ext_descriptors_dev = context
            .alloc::<GpuExtensionFieldPolyContinuingLaunchDescriptor<E4>>(
                0,
                AllocationPlacement::Top,
            )
            .unwrap();
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();

        let scheduled = crate::prover::gkr::GpuSumcheckRound1ScheduledLaunchDescriptors {
            device: crate::prover::gkr::GpuSumcheckRound1DeviceLaunchDescriptors {
                base_field_inputs: base_descriptors_dev,
                extension_field_inputs: ext_descriptors_dev,
            },
        };

        super::launch_main_round1(
            GpuGKRMainLayerKernelKind::LookupBasePair,
            &scheduled,
            batch_challenges_dev.as_ptr(),
            folding_challenge_dev.as_ptr(),
            auxiliary_challenge_dev.as_ptr(),
            None,
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

        let fold_base = |values: &[BF], idx: usize| {
            let mut diff = values[4 + idx];
            diff.sub_assign(&values[idx]);
            let mut result = folding_challenge;
            result.mul_assign_by_base(&diff);
            result.add_assign_base(&values[idx]);
            result
        };

        let mut expected = Vec::new();
        for gid in 0..2 {
            let b0 = fold_base(&input_b_values, gid);
            let b1_full = fold_base(&input_b_values, gid + 2);
            let mut db = b1_full;
            db.sub_assign(&b0);

            let d0 = fold_base(&input_d_values, gid);
            let d1_full = fold_base(&input_d_values, gid + 2);
            let mut dd = d1_full;
            dd.sub_assign(&d0);

            let mut shifted_b0 = b0;
            shifted_b0.add_assign(&lookup_additive_challenge);
            let mut shifted_d0 = d0;
            shifted_d0.add_assign(&lookup_additive_challenge);

            let mut num0 = shifted_b0;
            num0.add_assign(&shifted_d0);
            let mut den0 = shifted_b0;
            den0.mul_assign(&shifted_d0);

            let num1 = E4::ZERO;
            let mut den1 = db;
            den1.mul_assign(&dd);

            let mut c0 = batch0;
            c0.mul_assign(&num0);
            let mut c0_den = batch1;
            c0_den.mul_assign(&den0);
            c0.add_assign(&c0_den);

            let mut c1 = batch0;
            c1.mul_assign(&num1);
            let mut c1_den = batch1;
            c1_den.mul_assign(&den1);
            c1.add_assign(&c1_den);

            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round1_lookup_base_minus_multiplicity_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_b_values = (0..8).map(|i| BF::new(10 + i)).collect::<Vec<_>>();
        let input_c_values = (0..8).map(|i| BF::new(30 + i)).collect::<Vec<_>>();
        let input_d_values = (0..8).map(|i| BF::new(50 + i)).collect::<Vec<_>>();

        let input_b = alloc_and_copy(&context, &input_b_values);
        let input_c = alloc_and_copy(&context, &input_c_values);
        let input_d = alloc_and_copy(&context, &input_d_values);

        let folding_challenge = sample_ext(300);
        let batch0 = sample_ext(400);
        let batch1 = sample_ext(500);
        let lookup_additive_challenge = sample_ext(600);
        let folding_challenge_dev = alloc_and_copy(&context, &[folding_challenge]);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch0, batch1]);
        let auxiliary_challenge_dev = alloc_and_copy(&context, &[lookup_additive_challenge]);
        let base_cache: DeviceAllocation<E4> = context.alloc(12, AllocationPlacement::Top).unwrap();

        let base_descriptors = [
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_b.as_ptr(),
                this_layer_cache_start: base_cache.as_ptr().cast_mut(),
                first_access: true,
                source_kind: GpuBaseFieldSourceKind::Real,
                _marker: core::marker::PhantomData,
            },
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_c.as_ptr(),
                this_layer_cache_start: unsafe { base_cache.as_ptr().cast_mut().add(4) },
                first_access: true,
                source_kind: GpuBaseFieldSourceKind::Real,
                _marker: core::marker::PhantomData,
            },
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_d.as_ptr(),
                this_layer_cache_start: unsafe { base_cache.as_ptr().cast_mut().add(8) },
                first_access: true,
                source_kind: GpuBaseFieldSourceKind::Real,
                _marker: core::marker::PhantomData,
            },
        ];
        let base_descriptors_dev = alloc_and_copy(&context, &base_descriptors);
        let ext_descriptors_dev = context
            .alloc::<GpuExtensionFieldPolyContinuingLaunchDescriptor<E4>>(
                0,
                AllocationPlacement::Top,
            )
            .unwrap();
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();

        let scheduled = crate::prover::gkr::GpuSumcheckRound1ScheduledLaunchDescriptors {
            device: crate::prover::gkr::GpuSumcheckRound1DeviceLaunchDescriptors {
                base_field_inputs: base_descriptors_dev,
                extension_field_inputs: ext_descriptors_dev,
            },
        };

        super::launch_main_round1(
            GpuGKRMainLayerKernelKind::LookupBaseMinusMultiplicityByBase,
            &scheduled,
            batch_challenges_dev.as_ptr(),
            folding_challenge_dev.as_ptr(),
            auxiliary_challenge_dev.as_ptr(),
            None,
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

        let fold_base = |values: &[BF], idx: usize| {
            let mut diff = values[4 + idx];
            diff.sub_assign(&values[idx]);
            let mut result = folding_challenge;
            result.mul_assign_by_base(&diff);
            result.add_assign_base(&values[idx]);
            result
        };

        let mut expected = Vec::new();
        for gid in 0..2 {
            let b0 = fold_base(&input_b_values, gid);
            let b1_full = fold_base(&input_b_values, gid + 2);
            let mut db = b1_full;
            db.sub_assign(&b0);

            let c0_in = fold_base(&input_c_values, gid);
            let c1_full = fold_base(&input_c_values, gid + 2);
            let mut dc = c1_full;
            dc.sub_assign(&c0_in);

            let d0 = fold_base(&input_d_values, gid);
            let d1_full = fold_base(&input_d_values, gid + 2);
            let mut dd = d1_full;
            dd.sub_assign(&d0);

            let mut shifted_b0 = b0;
            shifted_b0.add_assign(&lookup_additive_challenge);
            let mut shifted_d0 = d0;
            shifted_d0.add_assign(&lookup_additive_challenge);

            let mut num0 = shifted_d0;
            let mut t0 = c0_in;
            t0.mul_assign(&shifted_b0);
            num0.sub_assign(&t0);
            let mut den0 = shifted_b0;
            den0.mul_assign(&shifted_d0);

            let mut num1 = dc;
            num1.mul_assign(&db);
            num1.negate();
            let mut den1 = db;
            den1.mul_assign(&dd);

            let mut c0 = batch0;
            c0.mul_assign(&num0);
            let mut c0_den = batch1;
            c0_den.mul_assign(&den0);
            c0.add_assign(&c0_den);

            let mut c1 = batch0;
            c1.mul_assign(&num1);
            let mut c1_den = batch1;
            c1_den.mul_assign(&den1);
            c1.add_assign(&c1_den);

            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    fn main_layer_constraint_blueprint_metadata_matches_cpu() {
        let storage = crate::prover::gkr::GpuGKRStorage::<BF, E4> {
            layers: vec![Default::default()],
        };
        let constraint_input = NoFieldMaxQuadraticConstraintsGKRRelation {
            quadratic_terms: vec![
                (
                    (
                        GKRAddress::BaseLayerMemory(0),
                        GKRAddress::BaseLayerWitness(1),
                    ),
                    vec![(2u32, 0usize), (3u32, 2usize)].into_boxed_slice(),
                ),
                (
                    (
                        GKRAddress::BaseLayerWitness(1),
                        GKRAddress::BaseLayerWitness(1),
                    ),
                    vec![(5u32, 1usize)].into_boxed_slice(),
                ),
            ]
            .into_boxed_slice(),
            linear_terms: vec![(
                GKRAddress::BaseLayerMemory(1),
                vec![(7u32, 0usize)].into_boxed_slice(),
            )]
            .into_boxed_slice(),
            constants: vec![(11u32, 0usize), (13u32, 1usize)].into_boxed_slice(),
        };
        let layer = GKRLayerDescription {
            layer: 0,
            gates_with_external_connections: Vec::new(),
            cached_relations: BTreeMap::new(),
            gates: vec![GateArtifacts {
                output_layer: 1,
                enforced_relation: NoFieldGKRRelation::EnforceConstraintsMaxQuadratic {
                    input: constraint_input.clone(),
                },
            }],
        };
        let constraint_batch_challenge = sample_ext(20);
        let external_challenges = sample_external_challenges(30);
        let blueprints = build_main_layer_kernel_blueprints(
            &layer,
            0,
            &storage,
            &external_challenges,
            &[],
            0,
            sample_ext(10),
            sample_ext(25),
            sample_ext(30),
            constraint_batch_challenge,
            2,
            2,
        );

        assert_eq!(blueprints.len(), 1);
        let blueprint = &blueprints[0];
        let relation = BatchConstraintEvalGKRRelation::<BF, E4>::new(
            &constraint_input,
            constraint_batch_challenge,
        );

        assert_eq!(
            blueprint.kind,
            GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic
        );
        assert_eq!(blueprint.batch_challenges, vec![E4::ONE]);
        assert_eq!(
            blueprint.inputs,
            <BatchConstraintEvalGKRRelation<BF, E4> as BatchedGKRKernel<BF, E4>>::get_inputs(
                &relation,
            )
        );

        let metadata = blueprint
            .constraint_metadata_source
            .as_ref()
            .expect("constraint metadata must be present");
        let metadata = match metadata {
            super::GpuGKRMainLayerConstraintMetadataSource::Immediate(metadata) => metadata,
            super::GpuGKRMainLayerConstraintMetadataSource::Deferred(..) => {
                panic!("dynamic blueprint must materialize immediate constraint metadata")
            }
        };
        assert_eq!(metadata.constant_offset, relation.kernel.constant_offset);
        assert_eq!(
            metadata.quadratic_terms.len(),
            relation.kernel.quadratic_parts.len()
        );
        assert_eq!(
            metadata.linear_terms.len(),
            relation.kernel.linear_parts.len()
        );
        assert_eq!(
            metadata.quadratic_terms,
            relation
                .kernel
                .quadratic_parts
                .iter()
                .map(
                    |((lhs, rhs), challenge)| GpuGKRMainLayerConstraintQuadraticTerm {
                        lhs: *lhs as u32,
                        rhs: *rhs as u32,
                        challenge: *challenge,
                    }
                )
                .collect::<Vec<_>>()
        );
        assert_eq!(
            metadata.linear_terms,
            relation
                .kernel
                .linear_parts
                .iter()
                .map(|(input, challenge)| GpuGKRMainLayerConstraintLinearTerm {
                    input: *input as u32,
                    challenge: *challenge,
                })
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn single_max_quadratic_constraint_uses_direct_metadata_and_no_outputs() {
        let storage = crate::prover::gkr::GpuGKRStorage::<BF, E4> {
            layers: vec![Default::default()],
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
            sample_ext(30),
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
    fn main_layer_static_constraint_blueprint_metadata_matches_cpu() {
        let storage = crate::prover::gkr::GpuGKRStorage::<BF, E4> {
            layers: vec![Default::default()],
        };
        let constraint_input = NoFieldMaxQuadraticConstraintsGKRRelation {
            quadratic_terms: vec![
                (
                    (
                        GKRAddress::BaseLayerMemory(14),
                        GKRAddress::BaseLayerWitness(1),
                    ),
                    vec![(2u32, 0usize), (3u32, 2usize)].into_boxed_slice(),
                ),
                (
                    (
                        GKRAddress::BaseLayerMemory(0),
                        GKRAddress::BaseLayerMemory(14),
                    ),
                    vec![(5u32, 1usize)].into_boxed_slice(),
                ),
            ]
            .into_boxed_slice(),
            linear_terms: vec![(
                GKRAddress::BaseLayerWitness(0),
                vec![(7u32, 0usize)].into_boxed_slice(),
            )]
            .into_boxed_slice(),
            constants: vec![(11u32, 0usize), (13u32, 1usize)].into_boxed_slice(),
        };
        let layer = GKRLayerDescription {
            layer: 0,
            gates_with_external_connections: Vec::new(),
            cached_relations: BTreeMap::new(),
            gates: vec![GateArtifacts {
                output_layer: 1,
                enforced_relation: NoFieldGKRRelation::EnforceConstraintsMaxQuadratic {
                    input: constraint_input.clone(),
                },
            }],
        };
        let constraint_batch_challenge = sample_ext(20);
        let external_challenges = sample_external_challenges(50);
        let blueprints = build_main_layer_kernel_blueprints_static(
            &layer,
            0,
            &storage,
            &external_challenges,
            &[],
            0,
            16,
            4,
        );

        assert_eq!(blueprints.len(), 1);
        let blueprint = &blueprints[0];
        let (expected_inputs, expected_template) =
            super::build_constraints_max_quadratic_inputs_and_template(&constraint_input);

        assert_eq!(
            blueprint.kind,
            GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic
        );
        assert_eq!(blueprint.batch_challenges, Vec::<E4>::new());
        assert_eq!(blueprint.inputs, expected_inputs);

        let metadata = blueprint
            .constraint_metadata_source
            .as_ref()
            .expect("constraint metadata must be present");
        let metadata = match metadata {
            super::GpuGKRMainLayerConstraintMetadataSource::Deferred(metadata) => metadata,
            super::GpuGKRMainLayerConstraintMetadataSource::Immediate(..) => {
                panic!("static blueprint must defer constraint metadata")
            }
        };
        assert_eq!(metadata, &expected_template);
    }

    #[test]
    fn main_layer_blueprints_for_inits_and_teardowns_initial_pair_use_canonical_top_bits() {
        let storage = crate::prover::gkr::GpuGKRStorage::<BF, E4> {
            layers: vec![Default::default()],
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
            sample_ext(30),
            4,
            0,
        );
        let static_blueprints = build_main_layer_kernel_blueprints_static(
            &layer,
            0,
            &storage,
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
}
