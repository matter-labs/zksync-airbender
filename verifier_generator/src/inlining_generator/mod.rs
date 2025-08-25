use super::*;

use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::Ident;

mod everywhere_except_last;
mod grand_product_accumulators;
mod utils;

use self::everywhere_except_last::*;
use self::grand_product_accumulators::*;
use self::utils::*;

mod everywhere_except_last_two;
use self::everywhere_except_last_two::*;

mod first_or_last_rows;
use self::first_or_last_rows::*;

#[derive(Clone)]
struct Idents {
    random_point_ident: Ident,
    witness_values_ident: Ident,
    memory_values_ident: Ident,
    setup_values_ident: Ident,
    stage_2_values_ident: Ident,
    witness_values_next_row_ident: Ident,
    memory_values_next_row_ident: Ident,
    stage_2_values_next_row_ident: Ident,
    quotient_alpha_ident: Ident,
    quotient_beta_ident: Ident,
    individual_term_ident: Ident,
    terms_accumulator_ident: Ident,
    divisors_ident: Ident,
    memory_argument_linearization_challenges_ident: Ident,
    memory_argument_gamma_ident: Ident,
    lookup_argument_linearization_challenges_ident: Ident,
    lookup_argument_gamma_ident: Ident,
    lookup_argument_two_gamma_ident: Ident,
    delegation_argument_linearization_challenges_ident: Ident,
    delegation_argument_gamma_ident: Ident,
    memory_timestamp_high_from_sequence_idx_ident: Ident,
    public_inputs_ident: Ident,
    #[allow(dead_code)]
    external_values_ident: Ident,
    aux_proof_values_ident: Ident,
    aux_boundary_values_ident: Ident,
    delegation_type_ident: Ident,
    delegation_argument_interpolant_linear_coeff_ident: Ident,
}

pub fn generate_inlined(compiled_circuit: CompiledCircuitArtifact<Mersenne31Field>) -> TokenStream {
    // we need to prepare a description for quotient evaluator, so we will assign the layout to the constant, and will also
    // will transform a description of the constraints to the literals

    let CompiledCircuitArtifact {
        witness_layout,
        memory_layout,
        setup_layout,
        stage_2_layout,
        degree_2_constraints,
        degree_1_constraints,
        state_linkage_constraints,
        public_inputs,
        lazy_init_address_aux_vars,
        ..
    } = compiled_circuit;

    let num_public_inputs = public_inputs.len();

    let random_point_ident = Ident::new("random_point", Span::call_site());
    let witness_values_ident = Ident::new("witness", Span::call_site());
    let memory_values_ident = Ident::new("memory", Span::call_site());
    let setup_values_ident = Ident::new("setup", Span::call_site());
    let stage_2_values_ident = Ident::new("stage_2", Span::call_site());
    let witness_values_next_row_ident = Ident::new("witness_next_row", Span::call_site());
    let memory_values_next_row_ident = Ident::new("memory_next_row", Span::call_site());
    let stage_2_values_next_row_ident = Ident::new("stage_2_next_row", Span::call_site());
    let quotient_alpha_ident = Ident::new("quotient_alpha", Span::call_site());
    let quotient_beta_ident = Ident::new("quotient_beta", Span::call_site());
    let terms_accumulator_ident = Ident::new("accumulated_contribution", Span::call_site());
    let individual_term_ident = Ident::new("individual_term", Span::call_site());
    let divisors_ident = Ident::new("divisors", Span::call_site());
    let memory_argument_linearization_challenges_ident = Ident::new(
        "memory_argument_linearization_challenges",
        Span::call_site(),
    );
    let memory_argument_gamma_ident = Ident::new("memory_argument_gamma", Span::call_site());
    let lookup_argument_linearization_challenges_ident = Ident::new(
        "lookup_argument_linearization_challenges",
        Span::call_site(),
    );
    let lookup_argument_gamma_ident = Ident::new("lookup_argument_gamma", Span::call_site());
    let lookup_argument_two_gamma_ident =
        Ident::new("lookup_argument_two_gamma", Span::call_site());
    let delegation_argument_linearization_challenges_ident = Ident::new(
        "delegation_argument_linearization_challenges",
        Span::call_site(),
    );
    let delegation_argument_gamma_ident =
        Ident::new("delegation_argument_gamma", Span::call_site());
    let memory_timestamp_high_from_sequence_idx_ident =
        Ident::new("memory_timestamp_high_from_sequence_idx", Span::call_site());
    let public_inputs_ident = Ident::new("public_inputs", Span::call_site());
    let external_values_ident = Ident::new("external_values", Span::call_site());
    let aux_proof_values_ident = Ident::new("aux_proof_values", Span::call_site());
    let aux_boundary_values_ident = Ident::new("aux_boundary_values", Span::call_site());
    let delegation_type_ident = Ident::new("delegation_type", Span::call_site());
    let delegation_argument_interpolant_linear_coeff_ident = Ident::new(
        "delegation_argument_interpolant_linear_coeff",
        Span::call_site(),
    );

    let idents = Idents {
        random_point_ident,
        witness_values_ident,
        memory_values_ident,
        setup_values_ident,
        stage_2_values_ident,
        witness_values_next_row_ident,
        memory_values_next_row_ident,
        stage_2_values_next_row_ident,
        terms_accumulator_ident,
        quotient_alpha_ident,
        quotient_beta_ident,
        divisors_ident,
        individual_term_ident,
        memory_argument_linearization_challenges_ident,
        memory_argument_gamma_ident,
        lookup_argument_linearization_challenges_ident,
        lookup_argument_gamma_ident,
        lookup_argument_two_gamma_ident,
        delegation_argument_linearization_challenges_ident,
        delegation_argument_gamma_ident,
        memory_timestamp_high_from_sequence_idx_ident,
        public_inputs_ident,
        external_values_ident,
        aux_proof_values_ident,
        aux_boundary_values_ident,
        delegation_type_ident,
        delegation_argument_interpolant_linear_coeff_ident,
    };

    let num_boolean_constraints = witness_layout.boolean_vars_columns_range.num_elements();

    // we also use Horner rule, so we reduce multiplication complexity

    // first all the constraints for the case of every row except last
    let mut every_row_except_last_stream = TokenStream::new();

    let mut common_constraints = vec![];
    // specialized boolean constraints, that can be degraded to single multiplication effectively
    for i in 0..num_boolean_constraints {
        let column_index = witness_layout.boolean_vars_columns_range.get_range(i).start;
        let expr = produce_boolean_constraint(column_index, &idents);
        common_constraints.push(expr);
    }
    // constraints themselves, skipping boolean
    for el in degree_2_constraints
        .into_iter()
        .skip(num_boolean_constraints)
    {
        let expr = transform_degree_2_constraint(el, &idents);
        common_constraints.push(expr);
    }

    for el in degree_1_constraints.into_iter() {
        let expr = transform_degree_1_constraint(el, &idents);
        common_constraints.push(expr);
    }
    accumulate_contributions(
        &mut every_row_except_last_stream,
        None,
        common_constraints,
        &idents,
    );

    // special compiler-defined constraints. Note that all timestamp comparisons are effectively
    // merged with width-16 range checks

    // if we process delegations - we should process checks in case if processing doesn't happen
    if memory_layout.delegation_processor_layout.is_some() {
        let (common, exprs) = transform_delegation_ram_conventions(&memory_layout, &idents);
        accumulate_contributions(
            &mut every_row_except_last_stream,
            Some(common),
            exprs,
            &idents,
        );
    }

    // now lookup width 1
    {
        // range check 16
        {
            let bound = stage_2_layout
                .intermediate_polys_for_range_check_16
                .num_pairs;
            assert_eq!(
                bound,
                witness_layout.range_check_16_lookup_expressions.len() / 2
            );
            let num_shuffle_ram_accesses = memory_layout.shuffle_ram_access_sets.len();
            let shuffle_ram_special_case_bound = bound - num_shuffle_ram_accesses;
            assert!(witness_layout.range_check_16_lookup_expressions.len() % 2 == 0);
            for (i, pair) in witness_layout
                .range_check_16_lookup_expressions
                .array_chunks::<2>()
                .enumerate()
            {
                let (common, exprs) = transform_width_1_range_checks_pair(
                    pair,
                    i,
                    stage_2_layout.intermediate_polys_for_range_check_16,
                    &idents,
                    &stage_2_layout,
                    false,
                );
                accumulate_contributions(
                    &mut every_row_except_last_stream,
                    Some(common),
                    exprs,
                    &idents,
                );
            }
        }

        // special case for range check over lazy init address columns
        if memory_layout.shuffle_ram_inits_and_teardowns.len() > 0 {
            let lazy_init_address_range_check_16 = stage_2_layout
                .lazy_init_address_range_check_16
                .expect("must exist if we do lazy init");
            let exprs = transform_shuffle_ram_lazy_init_range_checks(
                lazy_init_address_range_check_16,
                &memory_layout.shuffle_ram_inits_and_teardowns,
                &idents,
                &stage_2_layout,
                &mut every_row_except_last_stream,
            );
        }

        // now remainders
        // Acc(x) * (witness(x) + gamma) - 1
        if let Some(_remainder_for_range_check_16) = stage_2_layout.remainder_for_range_check_16 {
            todo!();
        }
    }

    // timestamp range checks
    {
        let bound = stage_2_layout
            .intermediate_polys_for_timestamp_range_checks
            .num_pairs;
        assert_eq!(
            bound,
            witness_layout
                .timestamp_range_check_lookup_expressions
                .len()
                / 2
        );
        let num_shuffle_ram_accesses = memory_layout.shuffle_ram_access_sets.len();
        let shuffle_ram_special_case_bound = bound - num_shuffle_ram_accesses;
        assert!(
            witness_layout
                .timestamp_range_check_lookup_expressions
                .len()
                % 2
                == 0
        );
        for (i, pair) in witness_layout
            .timestamp_range_check_lookup_expressions
            .as_chunks::<2>()
            .0
            .iter()
            .enumerate()
        {
            if i < shuffle_ram_special_case_bound {
                let (common, exprs) = transform_width_1_range_checks_pair(
                    pair,
                    i,
                    stage_2_layout.intermediate_polys_for_timestamp_range_checks,
                    &idents,
                    &stage_2_layout,
                    false,
                );

                accumulate_contributions(
                    &mut every_row_except_last_stream,
                    Some(common),
                    exprs,
                    &idents,
                );
            } else {
                let (common, exprs) = transform_width_1_range_checks_pair(
                    pair,
                    i,
                    stage_2_layout.intermediate_polys_for_timestamp_range_checks,
                    &idents,
                    &stage_2_layout,
                    true,
                );

                accumulate_contributions(
                    &mut every_row_except_last_stream,
                    Some(common),
                    exprs,
                    &idents,
                );
            }
        }
    }

    // now generic lookup
    {
        let exprs =
            transform_generic_lookup(&witness_layout, &stage_2_layout, &setup_layout, &idents);
        accumulate_contributions(&mut every_row_except_last_stream, None, exprs, &idents);
    }

    // multiplicities
    {
        let exprs =
            transform_multiplicities(&witness_layout, &stage_2_layout, &setup_layout, &idents);
        accumulate_contributions(&mut every_row_except_last_stream, None, exprs, &idents);
    }

    // if we work with delegation argument - then transform them

    // creating of requests
    if memory_layout.delegation_request_layout.is_some() {
        let exprs = transform_delegation_requests_creation(
            &memory_layout,
            &stage_2_layout,
            &setup_layout,
            &idents,
        );
        accumulate_contributions(&mut every_row_except_last_stream, None, exprs, &idents);
    }

    // processing of requests
    if memory_layout.delegation_processor_layout.is_some() {
        let exprs =
            transform_delegation_requests_processing(&memory_layout, &stage_2_layout, &idents);
        accumulate_contributions(&mut every_row_except_last_stream, None, exprs, &idents);
    }

    // check padding of lazy-init
    if memory_layout.shuffle_ram_inits_and_teardowns.len() > 0 {
        transform_shuffle_ram_lazy_init_padding(
            &memory_layout.shuffle_ram_inits_and_teardowns,
            &lazy_init_address_aux_vars,
            &idents,
            &mut every_row_except_last_stream,
        );
    }

    // Memory and machines state related accumulators
    {
        transform_grand_product_accumulators(
            &memory_layout,
            &stage_2_layout,
            &setup_layout,
            &idents,
            &mut every_row_except_last_stream,
        );
    }

    let divisor_idx = DIVISOR_EVERYWHERE_EXCEPT_LAST_ROW_INDEX;

    let divisors_ident = &idents.divisors_ident;
    let terms_accumulator_ident = &idents.terms_accumulator_ident;

    let every_row_except_last = if every_row_except_last_stream.is_empty() {
        quote! {
            let every_row_except_last_contribution = Mersenne31Quartic::ZERO;
        }
    } else {
        quote! {
            let every_row_except_last_contribution = {
                #every_row_except_last_stream

                // now divide
                let divisor = #divisors_ident[#divisor_idx];
                #terms_accumulator_ident.mul_assign(&divisor);

                #terms_accumulator_ident
            };
        }
    };

    // now evert row except the last two

    let mut every_row_except_last_two_stream = TokenStream::new();
    // linking constraints
    if state_linkage_constraints.len() > 0 {
        let exprs = transform_linking_constraints(&state_linkage_constraints, &idents);
        accumulate_contributions(&mut every_row_except_last_two_stream, None, exprs, &idents);
    }

    // and shuffle RAM lazy init if it exists
    if memory_layout.shuffle_ram_inits_and_teardowns.len() > 0 {
        transform_shuffle_ram_lazy_init(
            &memory_layout.shuffle_ram_inits_and_teardowns,
            &lazy_init_address_aux_vars,
            &idents,
            &mut every_row_except_last_two_stream,
        );
    }

    let divisor_idx = DIVISOR_EVERYWHERE_EXCEPT_LAST_TWO_ROWS_INDEX;

    let every_row_except_two_last = if every_row_except_last_two_stream.is_empty() == false {
        quote! {
            let every_row_except_two_last_contribution = {
                #every_row_except_last_two_stream

                // now divide
                let divisor = #divisors_ident[#divisor_idx];
                #terms_accumulator_ident.mul_assign(&divisor);

                #terms_accumulator_ident
            };
        }
    } else {
        quote! {
            let every_row_except_two_last_contribution = Mersenne31Quartic::ZERO;
        }
    };

    // first, one before last, last and last+0 cases

    let (first_row, one_before_last_row, last_row, last_row_and_zero) =
        transform_first_or_last_rows(&memory_layout, &stage_2_layout, &public_inputs, &idents);

    let divisor_idx = DIVISOR_FIRST_ROW_INDEX;

    let first_row = if first_row.is_empty() == false {
        quote! {
            let first_row_contribution = {
                #first_row

                // now divide
                let divisor = #divisors_ident[#divisor_idx];
                #terms_accumulator_ident.mul_assign(&divisor);

                #terms_accumulator_ident
            };
        }
    } else {
        quote! {
            let first_row_contribution = Mersenne31Quartic::ZERO;
        }
    };

    let divisor_idx = DIVISOR_ONE_BEFORE_LAST_ROW_INDEX;

    let one_before_last_row = if one_before_last_row.is_empty() == false {
        quote! {
            let one_before_last_row_contribution = {
                #one_before_last_row

                // now divide
                let divisor = #divisors_ident[#divisor_idx];
                #terms_accumulator_ident.mul_assign(&divisor);

                #terms_accumulator_ident
            };
        }
    } else {
        quote! {
            let one_before_last_row_contribution = Mersenne31Quartic::ZERO;
        }
    };

    let divisor_idx = DIVISOR_LAST_ROW_INDEX;

    let last_row = if last_row.is_empty() == false {
        quote! {
            let last_row_contribution = {
                #last_row

                // now divide
                let divisor = #divisors_ident[#divisor_idx];
                #terms_accumulator_ident.mul_assign(&divisor);

                #terms_accumulator_ident
            };
        }
    } else {
        quote! {
            let last_row_contribution = Mersenne31Quartic::ZERO;
        }
    };

    let divisor_idx = DIVISOR_LAST_ROW_AND_ZERO_INDEX;

    let last_row_and_zero = if last_row_and_zero.is_empty() == false {
        quote! {
            let last_row_and_zero_contribution = {
                #last_row_and_zero

                // now divide
                let divisor = #divisors_ident[#divisor_idx];
                #terms_accumulator_ident.mul_assign(&divisor);

                #terms_accumulator_ident
            };
        }
    } else {
        quote! {
            let last_row_and_zero_contribution = Mersenne31Quartic::ZERO;
        }
    };

    let Idents {
        random_point_ident,
        witness_values_ident,
        memory_values_ident,
        setup_values_ident,
        stage_2_values_ident,
        witness_values_next_row_ident,
        memory_values_next_row_ident,
        stage_2_values_next_row_ident,
        quotient_alpha_ident,
        quotient_beta_ident,
        // individual_term_ident,
        // terms_accumulator_ident,
        divisors_ident,
        memory_argument_linearization_challenges_ident,
        memory_argument_gamma_ident,
        lookup_argument_linearization_challenges_ident,
        lookup_argument_gamma_ident,
        lookup_argument_two_gamma_ident,
        delegation_argument_linearization_challenges_ident,
        delegation_argument_gamma_ident,
        memory_timestamp_high_from_sequence_idx_ident,
        public_inputs_ident,
        // external_values_ident,
        aux_proof_values_ident,
        aux_boundary_values_ident,
        delegation_type_ident,
        delegation_argument_interpolant_linear_coeff_ident,
        ..
    } = idents;

    let num_different_divisors = NUM_DIFFERENT_DIVISORS;
    let num_aux_boundary_values = memory_layout.shuffle_ram_inits_and_teardowns.len();

    quote! {

        #[allow(unused_braces, unused_mut, unused_variables)]
        unsafe fn evaluate_every_row_except_last(
            #random_point_ident: Mersenne31Quartic,
            #witness_values_ident: &[Mersenne31Quartic],
            #memory_values_ident: &[Mersenne31Quartic],
            #setup_values_ident: &[Mersenne31Quartic],
            #stage_2_values_ident: &[Mersenne31Quartic],
            #witness_values_next_row_ident: &[Mersenne31Quartic],
            #memory_values_next_row_ident: &[Mersenne31Quartic],
            #stage_2_values_next_row_ident: &[Mersenne31Quartic],
            #quotient_alpha_ident: Mersenne31Quartic,
            #quotient_beta_ident: Mersenne31Quartic,
            #divisors_ident: &[Mersenne31Quartic; #num_different_divisors],
            #lookup_argument_linearization_challenges_ident: [Mersenne31Quartic; NUM_LOOKUP_ARGUMENT_LINEARIZATION_CHALLENGES],
            #lookup_argument_gamma_ident: Mersenne31Quartic,
            #lookup_argument_two_gamma_ident: Mersenne31Quartic,
            #memory_argument_linearization_challenges_ident: [Mersenne31Quartic; NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES],
            #memory_argument_gamma_ident: Mersenne31Quartic,
            #delegation_argument_linearization_challenges_ident: [Mersenne31Quartic; NUM_DELEGATION_ARGUMENT_LINEARIZATION_CHALLENGES],
            #delegation_argument_gamma_ident: Mersenne31Quartic,
            #public_inputs_ident: &[Mersenne31Field; #num_public_inputs],
            #aux_proof_values_ident: &ProofAuxValues,
            #aux_boundary_values_ident: &[AuxArgumentsBoundaryValues; #num_aux_boundary_values],
            #memory_timestamp_high_from_sequence_idx_ident: Mersenne31Field,
            #delegation_type_ident: Mersenne31Field,
            #delegation_argument_interpolant_linear_coeff_ident: Mersenne31Quartic,
        ) -> Mersenne31Quartic {
            #every_row_except_last

            every_row_except_last_contribution
        }

        #[allow(unused_braces, unused_mut, unused_variables)]
        unsafe fn evaluate_every_row_except_two(
            #random_point_ident: Mersenne31Quartic,
            #witness_values_ident: &[Mersenne31Quartic],
            #memory_values_ident: &[Mersenne31Quartic],
            #setup_values_ident: &[Mersenne31Quartic],
            #stage_2_values_ident: &[Mersenne31Quartic],
            #witness_values_next_row_ident: &[Mersenne31Quartic],
            #memory_values_next_row_ident: &[Mersenne31Quartic],
            #stage_2_values_next_row_ident: &[Mersenne31Quartic],
            #quotient_alpha_ident: Mersenne31Quartic,
            #quotient_beta_ident: Mersenne31Quartic,
            #divisors_ident: &[Mersenne31Quartic; #num_different_divisors],
            #lookup_argument_linearization_challenges_ident: [Mersenne31Quartic; NUM_LOOKUP_ARGUMENT_LINEARIZATION_CHALLENGES],
            #lookup_argument_gamma_ident: Mersenne31Quartic,
            #lookup_argument_two_gamma_ident: Mersenne31Quartic,
            #memory_argument_linearization_challenges_ident: [Mersenne31Quartic; NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES],
            #memory_argument_gamma_ident: Mersenne31Quartic,
            #delegation_argument_linearization_challenges_ident: [Mersenne31Quartic; NUM_DELEGATION_ARGUMENT_LINEARIZATION_CHALLENGES],
            #delegation_argument_gamma_ident: Mersenne31Quartic,
            #public_inputs_ident: &[Mersenne31Field; #num_public_inputs],
            #aux_proof_values_ident: &ProofAuxValues,
            #aux_boundary_values_ident: &[AuxArgumentsBoundaryValues; #num_aux_boundary_values],
            #memory_timestamp_high_from_sequence_idx_ident: Mersenne31Field,
            #delegation_type_ident: Mersenne31Field,
            #delegation_argument_interpolant_linear_coeff_ident: Mersenne31Quartic,
        ) -> Mersenne31Quartic {
            #every_row_except_two_last

            every_row_except_two_last_contribution
        }

        #[allow(unused_braces, unused_mut, unused_variables)]
        unsafe fn evaluate_last_row_and_zero(
            #random_point_ident: Mersenne31Quartic,
            #witness_values_ident: &[Mersenne31Quartic],
            #memory_values_ident: &[Mersenne31Quartic],
            #setup_values_ident: &[Mersenne31Quartic],
            #stage_2_values_ident: &[Mersenne31Quartic],
            #witness_values_next_row_ident: &[Mersenne31Quartic],
            #memory_values_next_row_ident: &[Mersenne31Quartic],
            #stage_2_values_next_row_ident: &[Mersenne31Quartic],
            #quotient_alpha_ident: Mersenne31Quartic,
            #quotient_beta_ident: Mersenne31Quartic,
            #divisors_ident: &[Mersenne31Quartic; #num_different_divisors],
            #lookup_argument_linearization_challenges_ident: [Mersenne31Quartic; NUM_LOOKUP_ARGUMENT_LINEARIZATION_CHALLENGES],
            #lookup_argument_gamma_ident: Mersenne31Quartic,
            #lookup_argument_two_gamma_ident: Mersenne31Quartic,
            #memory_argument_linearization_challenges_ident: [Mersenne31Quartic; NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES],
            #memory_argument_gamma_ident: Mersenne31Quartic,
            #delegation_argument_linearization_challenges_ident: [Mersenne31Quartic; NUM_DELEGATION_ARGUMENT_LINEARIZATION_CHALLENGES],
            #delegation_argument_gamma_ident: Mersenne31Quartic,
            #public_inputs_ident: &[Mersenne31Field; #num_public_inputs],
            #aux_proof_values_ident: &ProofAuxValues,
            #aux_boundary_values_ident: &[AuxArgumentsBoundaryValues; #num_aux_boundary_values],
            #memory_timestamp_high_from_sequence_idx_ident: Mersenne31Field,
            #delegation_type_ident: Mersenne31Field,
            #delegation_argument_interpolant_linear_coeff_ident: Mersenne31Quartic,
        ) -> Mersenne31Quartic {
            #last_row_and_zero

            last_row_and_zero_contribution
        }

        #[allow(unused_braces, unused_mut, unused_variables)]
        pub unsafe fn evaluate_quotient(
            #random_point_ident: Mersenne31Quartic,
            #witness_values_ident: &[Mersenne31Quartic],
            #memory_values_ident: &[Mersenne31Quartic],
            #setup_values_ident: &[Mersenne31Quartic],
            #stage_2_values_ident: &[Mersenne31Quartic],
            #witness_values_next_row_ident: &[Mersenne31Quartic],
            #memory_values_next_row_ident: &[Mersenne31Quartic],
            #stage_2_values_next_row_ident: &[Mersenne31Quartic],
            #quotient_alpha_ident: Mersenne31Quartic,
            #quotient_beta_ident: Mersenne31Quartic,
            #divisors_ident: &[Mersenne31Quartic; #num_different_divisors],
            #lookup_argument_linearization_challenges_ident: [Mersenne31Quartic; NUM_LOOKUP_ARGUMENT_LINEARIZATION_CHALLENGES],
            #lookup_argument_gamma_ident: Mersenne31Quartic,
            #lookup_argument_two_gamma_ident: Mersenne31Quartic,
            #memory_argument_linearization_challenges_ident: [Mersenne31Quartic; NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES],
            #memory_argument_gamma_ident: Mersenne31Quartic,
            #delegation_argument_linearization_challenges_ident: [Mersenne31Quartic; NUM_DELEGATION_ARGUMENT_LINEARIZATION_CHALLENGES],
            #delegation_argument_gamma_ident: Mersenne31Quartic,
            #public_inputs_ident: &[Mersenne31Field; #num_public_inputs],
            #aux_proof_values_ident: &ProofAuxValues,
            #aux_boundary_values_ident: &[AuxArgumentsBoundaryValues; #num_aux_boundary_values],
            #memory_timestamp_high_from_sequence_idx_ident: Mersenne31Field,
            #delegation_type_ident: Mersenne31Field,
            #delegation_argument_interpolant_linear_coeff_ident: Mersenne31Quartic,
        ) -> Mersenne31Quartic {
            let every_row_except_last_contribution = evaluate_every_row_except_last(
                #random_point_ident,
                #witness_values_ident,
                #memory_values_ident,
                #setup_values_ident,
                #stage_2_values_ident,
                #witness_values_next_row_ident,
                #memory_values_next_row_ident,
                #stage_2_values_next_row_ident,
                #quotient_alpha_ident,
                #quotient_beta_ident,
                #divisors_ident,
                #lookup_argument_linearization_challenges_ident,
                #lookup_argument_gamma_ident,
                #lookup_argument_two_gamma_ident,
                #memory_argument_linearization_challenges_ident,
                #memory_argument_gamma_ident,
                #delegation_argument_linearization_challenges_ident,
                #delegation_argument_gamma_ident,
                #public_inputs_ident,
                #aux_proof_values_ident,
                #aux_boundary_values_ident,
                #memory_timestamp_high_from_sequence_idx_ident,
                #delegation_type_ident,
                #delegation_argument_interpolant_linear_coeff_ident,
            );

            let every_row_except_two_last_contribution = evaluate_every_row_except_two(
                #random_point_ident,
                #witness_values_ident,
                #memory_values_ident,
                #setup_values_ident,
                #stage_2_values_ident,
                #witness_values_next_row_ident,
                #memory_values_next_row_ident,
                #stage_2_values_next_row_ident,
                #quotient_alpha_ident,
                #quotient_beta_ident,
                #divisors_ident,
                #lookup_argument_linearization_challenges_ident,
                #lookup_argument_gamma_ident,
                #lookup_argument_two_gamma_ident,
                #memory_argument_linearization_challenges_ident,
                #memory_argument_gamma_ident,
                #delegation_argument_linearization_challenges_ident,
                #delegation_argument_gamma_ident,
                #public_inputs_ident,
                #aux_proof_values_ident,
                #aux_boundary_values_ident,
                #memory_timestamp_high_from_sequence_idx_ident,
                #delegation_type_ident,
                #delegation_argument_interpolant_linear_coeff_ident,
            );

            let last_row_and_zero_contribution = evaluate_last_row_and_zero(
                #random_point_ident,
                #witness_values_ident,
                #memory_values_ident,
                #setup_values_ident,
                #stage_2_values_ident,
                #witness_values_next_row_ident,
                #memory_values_next_row_ident,
                #stage_2_values_next_row_ident,
                #quotient_alpha_ident,
                #quotient_beta_ident,
                #divisors_ident,
                #lookup_argument_linearization_challenges_ident,
                #lookup_argument_gamma_ident,
                #lookup_argument_two_gamma_ident,
                #memory_argument_linearization_challenges_ident,
                #memory_argument_gamma_ident,
                #delegation_argument_linearization_challenges_ident,
                #delegation_argument_gamma_ident,
                #public_inputs_ident,
                #aux_proof_values_ident,
                #aux_boundary_values_ident,
                #memory_timestamp_high_from_sequence_idx_ident,
                #delegation_type_ident,
                #delegation_argument_interpolant_linear_coeff_ident,
            );

            #first_row

            #one_before_last_row

            #last_row

            let mut quotient = every_row_except_last_contribution;
            quotient.mul_assign(&#quotient_beta_ident);
            quotient.add_assign(&every_row_except_two_last_contribution);
            quotient.mul_assign(&#quotient_beta_ident);
            quotient.add_assign(&first_row_contribution);
            quotient.mul_assign(&#quotient_beta_ident);
            quotient.add_assign(&one_before_last_row_contribution);
            quotient.mul_assign(&#quotient_beta_ident);
            quotient.add_assign(&last_row_contribution);
            quotient.mul_assign(&#quotient_beta_ident);
            quotient.add_assign(&last_row_and_zero_contribution);

            quotient
        }
    }
}
