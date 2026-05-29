use super::*;

mod base_field_copy;
mod enforce_single_max_quadratic;
mod initial_grand_product_no_caches;
mod lookup_from_materialized_base_input_with_setup;
mod lookup_pair_from_base_inputs;
mod materialize_single_lookup_input;
mod vector_lookup_mask_by_expression_minus_multi_by_cached_setup;

pub(crate) fn compute_fn_ids(gate_idx: usize, layer_idx: usize) -> (Ident, Ident) {
    let compute_fn_initial_round_id = Ident::new(
        &format!(
            "compute_layer_{}_gate_{}_initial_round",
            layer_idx, gate_idx
        ),
        Span::call_site(),
    );
    let compute_fn_id = Ident::new(
        &format!("compute_layer_{}_gate_{}", layer_idx, gate_idx),
        Span::call_site(),
    );

    (compute_fn_initial_round_id, compute_fn_id)
}

pub(crate) fn generate_compute_fns_for_relation<F: PrimeField, E: FieldExtension<F> + Field>(
    relation: &NoFieldGKRRelation,
    gate_idx: usize,
    layer_idx: usize,
    num_challenges: usize,
    base_field_scratch_space_size: usize,
    ext_field_scratch_space_size: usize,
    all_base_outputs: &BTreeSet<GKRAddress>,
    all_ext_outputs: &BTreeSet<GKRAddress>,
    pos_state: &BTreeMap<GKRAddress, SumcheckAddressState>,
    challenges: Vec<usize>,
) -> (TokenStream, TokenStream) {
    match relation {
        NoFieldGKRRelation::CopyInBaseField { input, output } => {
            base_field_copy::generate_compute_fns::<F, E>(
                *input,
                *output,
                gate_idx,
                layer_idx,
                num_challenges,
                base_field_scratch_space_size,
                ext_field_scratch_space_size,
                all_base_outputs,
                all_ext_outputs,
                pos_state,
                challenges,
            )
        }
        NoFieldGKRRelation::InitialGrandProductWithoutCaches { input, output } => {
            initial_grand_product_no_caches::generate_compute_fns::<F, E>(
                input,
                *output,
                gate_idx,
                layer_idx,
                num_challenges,
                base_field_scratch_space_size,
                ext_field_scratch_space_size,
                all_base_outputs,
                all_ext_outputs,
                pos_state,
                challenges,
            )
        }
        NoFieldGKRRelation::LookupFromMaterializedBaseInputWithSetup {
            input,
            setup,
            output,
        } => lookup_from_materialized_base_input_with_setup::generate_compute_fns::<F, E>(
            *input,
            *setup,
            *output,
            gate_idx,
            layer_idx,
            num_challenges,
            base_field_scratch_space_size,
            ext_field_scratch_space_size,
            all_base_outputs,
            all_ext_outputs,
            pos_state,
            challenges,
        ),
        NoFieldGKRRelation::LookupPairFromBaseInputs {
            input,
            output,
            range_check_width,
        } => lookup_pair_from_base_inputs::generate_compute_fns::<F, E>(
            input,
            *output,
            gate_idx,
            layer_idx,
            num_challenges,
            base_field_scratch_space_size,
            ext_field_scratch_space_size,
            all_base_outputs,
            all_ext_outputs,
            pos_state,
            challenges,
        ),
        NoFieldGKRRelation::MaterializeSingleLookupInput {
            input,
            output,
            range_check_width,
        } => materialize_single_lookup_input::generate_compute_fns::<F, E>(
            input,
            *output,
            gate_idx,
            layer_idx,
            num_challenges,
            base_field_scratch_space_size,
            ext_field_scratch_space_size,
            all_base_outputs,
            all_ext_outputs,
            pos_state,
            challenges,
        ),
        NoFieldGKRRelation::LookupWithDensAndCachedSetup {
            input,
            setup,
            output,
        } => {
            vector_lookup_mask_by_expression_minus_multi_by_cached_setup::generate_compute_fns::<F, E>(
                input,
                *setup,
                *output,
                gate_idx,
                layer_idx,
                num_challenges,
                base_field_scratch_space_size,
                ext_field_scratch_space_size,
                all_base_outputs,
                all_ext_outputs,
                pos_state,
                challenges,
            )
        }
        NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint { input, expression } => {
            expression.assert_well_formed();
            enforce_single_max_quadratic::generate_compute_fns::<F, E>(
                expression,
                gate_idx,
                layer_idx,
                num_challenges,
                base_field_scratch_space_size,
                ext_field_scratch_space_size,
                all_base_outputs,
                all_ext_outputs,
                pos_state,
                challenges,
            )
        }
        a @ _ => {
            // return (quote! {}, quote! {});
            todo!("implement for {:?}", a);
        }
    }
}
