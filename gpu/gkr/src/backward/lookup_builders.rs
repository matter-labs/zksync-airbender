use crate::upstream::{
    GKRAddress, GKRInputs, NoFieldSingleColumnLookupRelation, NoFieldVectorLookupRelation,
};
use std::collections::BTreeMap;

use super::builders::{
    collect_no_cache_linear_form_template_inputs, encode_linear_form_as_linear_templates,
    encode_linear_form_as_quadratic_templates, lookup_constraint_term,
    single_column_lookup_as_flattened_relation_template,
    vector_lookup_as_flattened_relation_template,
};
use super::kernels::{
    GpuGKRMainLayerConstraintChallengeTerm, GpuGKRMainLayerConstraintTemplate,
    GpuGKRMainLayerDeferredChallengeSource,
};

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

pub(crate) fn build_lookup_pair_from_base_inputs_inputs_and_template(
    input: &[NoFieldSingleColumnLookupRelation; 2],
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

pub(crate) fn build_lookup_pair_from_vector_inputs_inputs_and_template(
    input: &[NoFieldVectorLookupRelation; 2],
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

pub(crate) fn build_materialized_vector_lookup_input_inputs_and_template(
    input: &NoFieldVectorLookupRelation,
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

pub(crate) fn build_lookup_with_dens_and_setup_expressions_inputs_and_template(
    input: &(GKRAddress, NoFieldVectorLookupRelation),
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

pub(crate) fn build_lookup_from_vector_input_with_setup_inputs_and_template(
    input: &NoFieldVectorLookupRelation,
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

pub(crate) fn build_lookup_unbalanced_pair_with_vector_inputs_inputs_and_template(
    input: [GKRAddress; 2],
    remainder: &NoFieldVectorLookupRelation,
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

// ---- Relocated from `backward/tests/lookup_builders.rs` (row 36): the
// `*_inputs_and_metadata` builders + their local helpers. Apex `expected_specs`
// consumes the builders as `gpu_gkr::backward::build_lookup_*`; `#[doc(hidden)]`.
use super::builders::{
    collect_no_cache_linear_form_inputs, validate_no_cache_linear_form_metadata,
    NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL,
};
use super::kernels::*;
use crate::immediate_factors::ImmediateFactorRecipeStructural;
use crate::upstream::{Field, FieldExtension, PrimeField};
use gpu_core::primitives::field::BF;

fn single_column_lookup_as_flattened_relation<
    E: Field + FieldExtension<BF>,
    const WITH_ADDITIVE_PART: bool,
>(
    rel: &NoFieldSingleColumnLookupRelation,
    lookup_challenges_additive_part: E,
) -> (BTreeMap<GKRAddress, E>, E) {
    let mut result = BTreeMap::new();
    let mut constant_term = if WITH_ADDITIVE_PART {
        lookup_challenges_additive_part
    } else {
        E::ZERO
    };

    for (coeff, address) in rel.input.linear_terms.iter() {
        assert!(result.insert(*address, E::from_base(*coeff)).is_none());
    }
    constant_term.add_assign_base(&rel.input.constant);

    (result, constant_term)
}

fn vector_lookup_as_flattened_relation<
    E: Field + FieldExtension<BF>,
    const WITH_ADDITIVE_PART: bool,
>(
    rel: &NoFieldVectorLookupRelation,
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
            t.mul_assign_by_base(coeff);
            assert!(result.insert(*address, t).is_none());
        }
        let mut t = challenge;
        t.mul_assign_by_base(&column.constant);
        constant_term.add_assign(&t);
        challenge.mul_assign(&lookup_challenges_multiplicative_part);
    }

    (result, constant_term)
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

#[doc(hidden)]
pub fn build_lookup_pair_from_base_inputs_inputs_and_metadata<E: Field + FieldExtension<BF>>(
    input: &[NoFieldSingleColumnLookupRelation; 2],
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

#[doc(hidden)]
pub fn build_lookup_pair_from_vector_inputs_inputs_and_metadata<E: Field + FieldExtension<BF>>(
    input: &[NoFieldVectorLookupRelation; 2],
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

pub(crate) fn build_materialized_vector_lookup_input_inputs_and_metadata<
    E: Field + FieldExtension<BF>,
>(
    input: &NoFieldVectorLookupRelation,
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

#[doc(hidden)]
pub fn build_lookup_with_dens_and_setup_expressions_inputs_and_metadata<
    E: Field + FieldExtension<BF>,
>(
    input: &(GKRAddress, NoFieldVectorLookupRelation),
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

#[doc(hidden)]
pub fn build_lookup_from_vector_input_with_setup_inputs_and_metadata<
    E: Field + FieldExtension<BF>,
>(
    input: &NoFieldVectorLookupRelation,
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

#[doc(hidden)]
pub fn build_lookup_unbalanced_pair_with_vector_inputs_inputs_and_metadata<
    E: Field + FieldExtension<BF>,
>(
    input: [GKRAddress; 2],
    remainder: &NoFieldVectorLookupRelation,
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
