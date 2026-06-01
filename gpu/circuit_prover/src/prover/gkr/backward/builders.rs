use std::collections::BTreeMap;

use super::kernels::*;
use crate::primitives::field::BF;
use crate::prover::gkr::immediate_factors::{
    ImmediateFactorRecipeStructural, IMMEDIATE_FACTOR_ADDITIVE_PART_IDX,
};
use crate::upstream::{
    AddressSpaceType, Field, FieldExtension, GKRAddress, GKRExternalChallenges, GKRInputs,
    InitsOrTeardownsTimestampAndValue, NoFieldMaxQuadraticGKRRelation, PrimeField,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
};

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

pub(super) fn lookup_constraint_term(
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

pub(super) fn single_column_lookup_as_flattened_relation_template<
    const WITH_ADDITIVE_PART: bool,
>(
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

pub(super) fn vector_lookup_as_flattened_relation_template<const WITH_ADDITIVE_PART: bool>(
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

pub(super) fn build_linear_base_kernel_inputs_and_metadata<E: Field + FieldExtension<BF>>(
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

pub(super) const NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL: u32 = u32::MAX;

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

pub(super) fn collect_no_cache_linear_form_inputs<E>(
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

pub(super) fn collect_no_cache_linear_form_template_inputs(
    forms: &[&BTreeMap<GKRAddress, Vec<GpuGKRMainLayerConstraintChallengeTerm>>],
) -> (BTreeMap<GKRAddress, usize>, Vec<GKRAddress>) {
    let mut mapping = BTreeMap::new();
    let mut inputs = Vec::new();
    for terms in forms.iter().copied() {
        remap_no_cache_linear_form_template_inputs(&mut mapping, &mut inputs, terms);
    }
    (mapping, inputs)
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

pub(super) fn encode_linear_form_as_quadratic_templates(
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

pub(super) fn encode_linear_form_as_linear_templates(
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

pub(super) fn validate_no_cache_linear_form_metadata<E: Field>(
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
