use crate::upstream::{GKRAddress, GKRInputs};
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
