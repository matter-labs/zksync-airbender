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

pub mod mersenne_wrapper;
pub use mersenne_wrapper::{DefaultMersenne31Field, MersenneWrapper};

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
    state_permutation_argument_linearization_challenges_ident: Ident,
    state_permutation_argument_gamma_ident: Ident,
    decoder_lookup_argument_linearization_challenges_ident: Ident,
    decoder_lookup_argument_gamma_ident: Ident,
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
    generate_inlined_configured::<DefaultMersenne31Field>(compiled_circuit)
}

pub fn generate_inlined_configured<MW: MersenneWrapper>(
    compiled_circuit: CompiledCircuitArtifact<Mersenne31Field>,
) -> TokenStream {
    // we need to prepare a description for quotient evaluator, so we will assign the layout to the constant, and will also
    // will transform a description of the constraints to the literals

    let field_struct = MW::field_struct();
    let complex_struct = MW::complex_struct();
    let quartic_struct = MW::quartic_struct();
    let quartic_zero = MW::quartic_zero();

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

    let state_permutation_argument_linearization_challenges_ident = Ident::new(
        "state_permutation_argument_linearization_challenges",
        Span::call_site(),
    );
    let state_permutation_argument_gamma_ident =
        Ident::new("state_permutation_argument_gamma", Span::call_site());

    let decoder_lookup_argument_linearization_challenges_ident = Ident::new(
        "decoder_lookup_argument_linearization_challenges",
        Span::call_site(),
    );
    let decoder_lookup_argument_gamma_ident =
        Ident::new("decoder_lookup_argument_gamma", Span::call_site());

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
        state_permutation_argument_linearization_challenges_ident,
        state_permutation_argument_gamma_ident,
        decoder_lookup_argument_linearization_challenges_ident,
        decoder_lookup_argument_gamma_ident,
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
        let expr = produce_boolean_constraint::<MW>(column_index, &idents);
        common_constraints.push(expr);
    }
    // constraints themselves, skipping boolean
    for el in degree_2_constraints
        .into_iter()
        .skip(num_boolean_constraints)
    {
        let expr = transform_degree_2_constraint::<MW>(el, &idents);
        common_constraints.push(expr);
    }

    for el in degree_1_constraints.into_iter() {
        let expr = transform_degree_1_constraint::<MW>(el, &idents);
        common_constraints.push(expr);
    }
    accumulate_contributions::<MW>(
        &mut every_row_except_last_stream,
        None,
        common_constraints,
        &idents,
    );

    // special compiler-defined constraints. Note that all timestamp comparisons are effectively
    // merged with width-16 range checks

    // if we process delegations - we should process checks in case if processing doesn't happen
    if memory_layout.delegation_processor_layout.is_some() {
        let (common, exprs) = transform_delegation_ram_conventions::<MW>(&memory_layout, &idents);
        accumulate_contributions::<MW>(
            &mut every_row_except_last_stream,
            Some(common),
            exprs,
            &idents,
        );
    }

    // now lookup width 1
    if stage_2_layout
        .intermediate_poly_for_range_check_16_multiplicity
        .num_elements()
        > 0
    {
        // range check 16
        if stage_2_layout
            .intermediate_polys_for_range_check_16
            .num_pairs
            > 0
        {
            let bound = stage_2_layout
                .intermediate_polys_for_range_check_16
                .num_pairs;
            assert_eq!(
                bound,
                witness_layout.range_check_16_lookup_expressions.len() / 2
            );
            assert!(witness_layout.range_check_16_lookup_expressions.len() % 2 == 0);
            for (i, pair) in witness_layout
                .range_check_16_lookup_expressions
                .as_chunks::<2>()
                .0
                .iter()
                .enumerate()
            {
                let (common, exprs) = transform_width_1_range_checks_pair::<MW>(
                    pair,
                    i,
                    stage_2_layout.intermediate_polys_for_range_check_16,
                    &idents,
                    &stage_2_layout,
                    false,
                );
                accumulate_contributions::<MW>(
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
            transform_shuffle_ram_lazy_init_range_checks::<MW>(
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
    if stage_2_layout
        .intermediate_poly_for_timestamp_range_check_multiplicity
        .num_elements()
        > 0
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
        let shuffle_ram_special_case_bound =
            witness_layout.offset_for_special_shuffle_ram_timestamps_range_check_expressions;
        assert_eq!(shuffle_ram_special_case_bound % 2, 0);
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
            if i < shuffle_ram_special_case_bound / 2 {
                let (common, exprs) = transform_width_1_range_checks_pair::<MW>(
                    pair,
                    i,
                    stage_2_layout.intermediate_polys_for_timestamp_range_checks,
                    &idents,
                    &stage_2_layout,
                    false,
                );

                accumulate_contributions::<MW>(
                    &mut every_row_except_last_stream,
                    Some(common),
                    exprs,
                    &idents,
                );
            } else {
                let (common, exprs) = transform_width_1_range_checks_pair::<MW>(
                    pair,
                    i,
                    stage_2_layout.intermediate_polys_for_timestamp_range_checks,
                    &idents,
                    &stage_2_layout,
                    true,
                );

                accumulate_contributions::<MW>(
                    &mut every_row_except_last_stream,
                    Some(common),
                    exprs,
                    &idents,
                );
            }
        }
    }

    // decoder lookup
    if stage_2_layout
        .intermediate_polys_for_decoder_multiplicities
        .num_elements()
        > 0
    {
        let offset = stage_2_layout
            .get_intermediate_poly_for_decoder_lookup_absolute_poly_idx_for_verifier();
        let accumulator_expr = read_stage_2_value_expr(offset, &idents, false);

        // depending on the location we generate columns

        let intermediate_state_layout = memory_layout.intermediate_state_layout.as_ref().unwrap();
        let IntermediateStatePermutationVariables {
            execute,
            pc,
            timestamp: _,
            rs1_index,
            rs2_index,
            rd_index,
            decoder_witness_is_in_memory,
            rd_is_zero,
            imm,
            funct3,
            funct7,
            circuit_family,
            circuit_family_extra_mask,
        } = *intermediate_state_layout;

        let multiplicity_expr = read_value_expr(
            ColumnAddress::MemorySubtree(execute.start()),
            &idents,
            false,
        );

        assert!(funct7.num_elements() == 0);
        assert!(circuit_family.num_elements() == 0);

        let pc_0 = ColumnAddress::MemorySubtree(pc.start());
        let pc_1 = ColumnAddress::MemorySubtree(pc.start() + 1);
        let rs1_index = ColumnAddress::MemorySubtree(rs1_index.start());

        // rs2 and rd are column addresses explicily

        // then we need to make it conditionally
        let [rd_is_zero, imm_0, imm_1, funct3] = [
            rd_is_zero.start(),
            imm.start(),
            imm.start() + 1,
            funct3.start(),
        ]
        .map(|el| {
            if decoder_witness_is_in_memory {
                unreachable!()
                // ColumnAddress::MemorySubtree(el)
            } else {
                ColumnAddress::WitnessSubtree(el)
            }
        });

        let key_values_to_aggregate = [
            pc_0,
            pc_1,
            rs1_index,
            rs2_index,
            rd_index,
            rd_is_zero,
            imm_0,
            imm_1,
            funct3,
            circuit_family_extra_mask,
        ];

        assert_eq!(
            key_values_to_aggregate.len(),
            EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_WIDTH
        );
        let c0_expr = read_value_expr(key_values_to_aggregate[0], &idents, false);

        let decoder_lookup_argument_gamma_ident = &idents.decoder_lookup_argument_gamma_ident;
        let denom_add_assign_c0_expr = MW::add_assign(quote! {denom}, c0_expr);
        let mut accumulation_expr = quote! {
            let mut denom = #decoder_lookup_argument_gamma_ident;
            #denom_add_assign_c0_expr;
        };

        // now in the cycle
        for i in 1..EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_WIDTH {
            let challenge_idx = i - 1;
            let column = key_values_to_aggregate[i];
            let column_expr = read_value_expr(column, &idents, false);

            let decoder_lookup_argument_linearization_challenges_ident =
                &idents.decoder_lookup_argument_linearization_challenges_ident;
            let t_mul_assign_column_expr = MW::mul_assign(quote! { t }, column_expr);
            let denom_add_assign_t = MW::add_assign(quote! {denom}, quote! { t });
            accumulation_expr.extend(quote! {
                let mut t = #decoder_lookup_argument_linearization_challenges_ident[#challenge_idx];
                #t_mul_assign_column_expr;
                #denom_add_assign_t;
            });
        }

        let individual_term_ident = &idents.individual_term_ident;
        let individual_term_ident_mul_assign_accumulator_expr = MW::mul_assign(
            quote! { #individual_term_ident },
            quote! { #accumulator_expr },
        );
        let individual_term_ident_sub_assign_m =
            MW::sub_assign(quote! { #individual_term_ident }, quote! { m });
        let t = quote! {
            let #individual_term_ident = {
                let m = #multiplicity_expr;

                #accumulation_expr

                let mut #individual_term_ident = denom;
                #individual_term_ident_mul_assign_accumulator_expr;
                #individual_term_ident_sub_assign_m;

                #individual_term_ident
            };
        };

        accumulate_contributions::<MW>(&mut every_row_except_last_stream, None, vec![t], &idents);
    }

    // now generic lookup
    if stage_2_layout
        .intermediate_polys_for_generic_lookup
        .num_elements()
        > 0
    {
        let exprs = transform_generic_lookup::<MW>(
            &witness_layout,
            &stage_2_layout,
            &setup_layout,
            &idents,
        );
        accumulate_contributions::<MW>(&mut every_row_except_last_stream, None, exprs, &idents);
    }

    // multiplicities
    {
        let exprs = transform_multiplicities::<MW>(
            &witness_layout,
            &stage_2_layout,
            &setup_layout,
            &idents,
        );
        accumulate_contributions::<MW>(&mut every_row_except_last_stream, None, exprs, &idents);
    }

    // if we work with delegation argument - then transform them

    // creating of requests
    if memory_layout.delegation_request_layout.is_some() {
        let exprs = transform_delegation_requests_creation::<MW>(
            &memory_layout,
            &stage_2_layout,
            &setup_layout,
            &idents,
        );
        accumulate_contributions::<MW>(&mut every_row_except_last_stream, None, exprs, &idents);
    }

    // processing of requests
    if memory_layout.delegation_processor_layout.is_some() {
        let exprs = transform_delegation_requests_processing::<MW>(
            &memory_layout,
            &stage_2_layout,
            &idents,
        );
        accumulate_contributions::<MW>(&mut every_row_except_last_stream, None, exprs, &idents);
    }

    // check padding of lazy-init
    if memory_layout.shuffle_ram_inits_and_teardowns.len() > 0 {
        transform_shuffle_ram_lazy_init_padding::<MW>(
            &memory_layout.shuffle_ram_inits_and_teardowns,
            &lazy_init_address_aux_vars,
            &idents,
            &mut every_row_except_last_stream,
        );
    }

    // Memory and machines state related accumulators
    {
        transform_grand_product_accumulators::<MW>(
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
            let every_row_except_last_contribution = #quartic_zero;
        }
    } else {
        let terms_accumulator_ident_mul_assign_divisor =
            MW::mul_assign(quote! { #terms_accumulator_ident }, quote! { divisor });
        quote! {
            let every_row_except_last_contribution = {
                #every_row_except_last_stream

                // now divide
                let divisor = #divisors_ident[#divisor_idx];
                #terms_accumulator_ident_mul_assign_divisor;

                #terms_accumulator_ident
            };
        }
    };

    // now evert row except the last two

    let mut every_row_except_last_two_stream = TokenStream::new();
    // linking constraints
    if state_linkage_constraints.len() > 0 {
        let exprs = transform_linking_constraints::<MW>(&state_linkage_constraints, &idents);
        accumulate_contributions::<MW>(&mut every_row_except_last_two_stream, None, exprs, &idents);
    }

    // and shuffle RAM lazy init if it exists
    if memory_layout.shuffle_ram_inits_and_teardowns.len() > 0 {
        transform_shuffle_ram_lazy_init_address_ordering::<MW>(
            &memory_layout.shuffle_ram_inits_and_teardowns,
            &lazy_init_address_aux_vars,
            &idents,
            &mut every_row_except_last_two_stream,
        );
    }

    let divisor_idx = DIVISOR_EVERYWHERE_EXCEPT_LAST_TWO_ROWS_INDEX;

    let every_row_except_two_last = if every_row_except_last_two_stream.is_empty() == false {
        let terms_accumulator_ident_mul_assign_divisor =
            MW::mul_assign(quote! { #terms_accumulator_ident }, quote! { divisor });
        quote! {
            let every_row_except_two_last_contribution = {
                #every_row_except_last_two_stream

                // now divide
                let divisor = #divisors_ident[#divisor_idx];
                #terms_accumulator_ident_mul_assign_divisor;

                #terms_accumulator_ident
            };
        }
    } else {
        quote! {
            let every_row_except_two_last_contribution = #quartic_zero;
        }
    };

    // first, one before last, last and last+0 cases

    let (first_row, one_before_last_row, last_row, last_row_and_zero) =
        transform_first_or_last_rows::<MW>(
            &memory_layout,
            &stage_2_layout,
            &public_inputs,
            &idents,
        );

    let divisor_idx = DIVISOR_FIRST_ROW_INDEX;

    let first_row = if first_row.is_empty() == false {
        let terms_accumulator_ident_mul_assign_divisor =
            MW::mul_assign(quote! { #terms_accumulator_ident }, quote! { divisor });
        quote! {
            let first_row_contribution = {
                #first_row

                // now divide
                let divisor = #divisors_ident[#divisor_idx];
                #terms_accumulator_ident_mul_assign_divisor;

                #terms_accumulator_ident
            };
        }
    } else {
        quote! {
            let first_row_contribution = #quartic_zero;
        }
    };

    let divisor_idx = DIVISOR_ONE_BEFORE_LAST_ROW_INDEX;

    let one_before_last_row = if one_before_last_row.is_empty() == false {
        let terms_accumulator_ident_mul_assign_divisor =
            MW::mul_assign(quote! { #terms_accumulator_ident }, quote! { divisor });
        quote! {
            let one_before_last_row_contribution = {
                #one_before_last_row

                // now divide
                let divisor = #divisors_ident[#divisor_idx];
                #terms_accumulator_ident_mul_assign_divisor;

                #terms_accumulator_ident
            };
        }
    } else {
        quote! {
            let one_before_last_row_contribution = #quartic_zero;
        }
    };

    let divisor_idx = DIVISOR_LAST_ROW_INDEX;

    let last_row = if last_row.is_empty() == false {
        let terms_accumulator_ident_mul_assign_divisor =
            MW::mul_assign(quote! { #terms_accumulator_ident }, quote! { divisor });
        quote! {
            let last_row_contribution = {
                #last_row

                // now divide
                let divisor = #divisors_ident[#divisor_idx];
                #terms_accumulator_ident_mul_assign_divisor;

                #terms_accumulator_ident
            };
        }
    } else {
        quote! {
            let last_row_contribution = #quartic_zero;
        }
    };

    let divisor_idx = DIVISOR_LAST_ROW_AND_ZERO_INDEX;

    let last_row_and_zero = if last_row_and_zero.is_empty() == false {
        let terms_accumulator_ident_mul_assign_divisor =
            MW::mul_assign(quote! { #terms_accumulator_ident }, quote! { divisor });
        quote! {
            let last_row_and_zero_contribution = {
                #last_row_and_zero

                // now divide
                let divisor = #divisors_ident[#divisor_idx];
                #terms_accumulator_ident_mul_assign_divisor;

                #terms_accumulator_ident
            };
        }
    } else {
        quote! {
            let last_row_and_zero_contribution = #quartic_zero;
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
        aux_proof_values_ident,
        aux_boundary_values_ident,
        delegation_type_ident,
        delegation_argument_interpolant_linear_coeff_ident,
        state_permutation_argument_linearization_challenges_ident,
        state_permutation_argument_gamma_ident,
        decoder_lookup_argument_linearization_challenges_ident,
        decoder_lookup_argument_gamma_ident,
        ..
    } = idents;

    let num_different_divisors = NUM_DIFFERENT_DIVISORS;
    let num_aux_boundary_values = memory_layout.shuffle_ram_inits_and_teardowns.len();

    let generic_function_parameters = MW::generic_function_parameters();
    let additional_function_arguments = MW::additional_function_arguments();
    let additional_definition_function_arguments = MW::additional_definition_function_arguments();
    let proof_aux_values_struct = MW::proof_aux_values_struct();
    let aux_arguments_boundary_values_struct = MW::aux_arguments_boundary_values_struct();

    let quotient_mul_assign_beta = MW::mul_assign(quote! {quotient}, quote! {#quotient_beta_ident});
    let quotient_add_assign_every_row_except_two_last_contribution = MW::add_assign(
        quote! {quotient},
        quote! {every_row_except_two_last_contribution},
    );
    let quotient_add_assign_first_row_contribution =
        MW::add_assign(quote! {quotient}, quote! {first_row_contribution});
    let quotient_add_assign_one_before_last_row_contribution =
        MW::add_assign(quote! {quotient}, quote! {one_before_last_row_contribution});
    let quotient_add_assign_last_row_contribution =
        MW::add_assign(quote! {quotient}, quote! {last_row_contribution});
    let quotient_add_assign_last_row_and_zero_contribution =
        MW::add_assign(quote! {quotient}, quote! {last_row_and_zero_contribution});

    // This module provides wrappers for field operations that
    // are either inlined or not depending on the platform.
    // This is done to retain the performance on RISC-V, while keeping compile speed
    // for the host platform sane.
    let field_ops_shim = quote! {
        use ::verifier_common::field_ops;
    };

    quote! {
        #field_ops_shim

        #[allow(unused_braces, unused_mut, unused_variables)]
        unsafe fn evaluate_every_row_except_last #generic_function_parameters (
            #additional_definition_function_arguments
            #random_point_ident: #quartic_struct,
            #witness_values_ident: &[#quartic_struct],
            #memory_values_ident: &[#quartic_struct],
            #setup_values_ident: &[#quartic_struct],
            #stage_2_values_ident: &[#quartic_struct],
            #witness_values_next_row_ident: &[#quartic_struct],
            #memory_values_next_row_ident: &[#quartic_struct],
            #stage_2_values_next_row_ident: &[#quartic_struct],
            #quotient_alpha_ident: #quartic_struct,
            #quotient_beta_ident: #quartic_struct,
            #divisors_ident: &[#quartic_struct; #num_different_divisors],
            #lookup_argument_linearization_challenges_ident: &[#quartic_struct; NUM_LOOKUP_ARGUMENT_LINEARIZATION_CHALLENGES],
            #lookup_argument_gamma_ident: #quartic_struct,
            #lookup_argument_two_gamma_ident: #quartic_struct,
            #memory_argument_linearization_challenges_ident: &[#quartic_struct; NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES],
            #memory_argument_gamma_ident: #quartic_struct,
            #delegation_argument_linearization_challenges_ident: &[#quartic_struct; NUM_DELEGATION_ARGUMENT_LINEARIZATION_CHALLENGES],
            #delegation_argument_gamma_ident: #quartic_struct,
            #decoder_lookup_argument_linearization_challenges_ident: &[#quartic_struct; EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_LINEARIZATION_CHALLENGES],
            #decoder_lookup_argument_gamma_ident: #quartic_struct,
            #state_permutation_argument_linearization_challenges_ident: &[#quartic_struct; NUM_MACHINE_STATE_LINEARIZATION_CHALLENGES],
            #state_permutation_argument_gamma_ident: #quartic_struct,
            #public_inputs_ident: &[#field_struct; #num_public_inputs],
            #aux_proof_values_ident: &#proof_aux_values_struct,
            #aux_boundary_values_ident: &[#aux_arguments_boundary_values_struct; #num_aux_boundary_values],
            #memory_timestamp_high_from_sequence_idx_ident: #field_struct,
            #delegation_type_ident: #field_struct,
            #delegation_argument_interpolant_linear_coeff_ident: #quartic_struct,
        ) -> #quartic_struct {
            #every_row_except_last

            every_row_except_last_contribution
        }

        #[allow(unused_braces, unused_mut, unused_variables)]
        unsafe fn evaluate_every_row_except_two #generic_function_parameters (
            #additional_definition_function_arguments
            #random_point_ident: #quartic_struct,
            #witness_values_ident: &[#quartic_struct],
            #memory_values_ident: &[#quartic_struct],
            #setup_values_ident: &[#quartic_struct],
            #stage_2_values_ident: &[#quartic_struct],
            #witness_values_next_row_ident: &[#quartic_struct],
            #memory_values_next_row_ident: &[#quartic_struct],
            #stage_2_values_next_row_ident: &[#quartic_struct],
            #quotient_alpha_ident: #quartic_struct,
            #quotient_beta_ident: #quartic_struct,
            #divisors_ident: &[#quartic_struct; #num_different_divisors],
            #lookup_argument_linearization_challenges_ident: &[#quartic_struct; NUM_LOOKUP_ARGUMENT_LINEARIZATION_CHALLENGES],
            #lookup_argument_gamma_ident: #quartic_struct,
            #lookup_argument_two_gamma_ident: #quartic_struct,
            #memory_argument_linearization_challenges_ident: &[#quartic_struct; NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES],
            #memory_argument_gamma_ident: #quartic_struct,
            #delegation_argument_linearization_challenges_ident: &[#quartic_struct; NUM_DELEGATION_ARGUMENT_LINEARIZATION_CHALLENGES],
            #delegation_argument_gamma_ident: #quartic_struct,
            #decoder_lookup_argument_linearization_challenges_ident: &[#quartic_struct; EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_LINEARIZATION_CHALLENGES],
            #decoder_lookup_argument_gamma_ident: #quartic_struct,
            #state_permutation_argument_linearization_challenges_ident: &[#quartic_struct; NUM_MACHINE_STATE_LINEARIZATION_CHALLENGES],
            #state_permutation_argument_gamma_ident: #quartic_struct,
            #public_inputs_ident: &[#field_struct; #num_public_inputs],
            #aux_proof_values_ident: &#proof_aux_values_struct,
            #aux_boundary_values_ident: &[#aux_arguments_boundary_values_struct; #num_aux_boundary_values],
            #memory_timestamp_high_from_sequence_idx_ident: #field_struct,
            #delegation_type_ident: #field_struct,
            #delegation_argument_interpolant_linear_coeff_ident: #quartic_struct,
        ) -> #quartic_struct {
            #every_row_except_two_last

            every_row_except_two_last_contribution
        }

        #[allow(unused_braces, unused_mut, unused_variables)]
        unsafe fn evaluate_last_row_and_zero #generic_function_parameters (
            #additional_definition_function_arguments
            #random_point_ident: #quartic_struct,
            #witness_values_ident: &[#quartic_struct],
            #memory_values_ident: &[#quartic_struct],
            #setup_values_ident: &[#quartic_struct],
            #stage_2_values_ident: &[#quartic_struct],
            #witness_values_next_row_ident: &[#quartic_struct],
            #memory_values_next_row_ident: &[#quartic_struct],
            #stage_2_values_next_row_ident: &[#quartic_struct],
            #quotient_alpha_ident: #quartic_struct,
            #quotient_beta_ident: #quartic_struct,
            #divisors_ident: &[#quartic_struct; #num_different_divisors],
            #lookup_argument_linearization_challenges_ident: &[#quartic_struct; NUM_LOOKUP_ARGUMENT_LINEARIZATION_CHALLENGES],
            #lookup_argument_gamma_ident: #quartic_struct,
            #lookup_argument_two_gamma_ident: #quartic_struct,
            #memory_argument_linearization_challenges_ident: &[#quartic_struct; NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES],
            #memory_argument_gamma_ident: #quartic_struct,
            #delegation_argument_linearization_challenges_ident: &[#quartic_struct; NUM_DELEGATION_ARGUMENT_LINEARIZATION_CHALLENGES],
            #delegation_argument_gamma_ident: #quartic_struct,
            #decoder_lookup_argument_linearization_challenges_ident: &[#quartic_struct; EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_LINEARIZATION_CHALLENGES],
            #decoder_lookup_argument_gamma_ident: #quartic_struct,
            #state_permutation_argument_linearization_challenges_ident: &[#quartic_struct; NUM_MACHINE_STATE_LINEARIZATION_CHALLENGES],
            #state_permutation_argument_gamma_ident: #quartic_struct,
            #public_inputs_ident: &[#field_struct; #num_public_inputs],
            #aux_proof_values_ident: &#proof_aux_values_struct,
            #aux_boundary_values_ident: &[#aux_arguments_boundary_values_struct; #num_aux_boundary_values],
            #memory_timestamp_high_from_sequence_idx_ident: #field_struct,
            #delegation_type_ident: #field_struct,
            #delegation_argument_interpolant_linear_coeff_ident: #quartic_struct,
        ) -> #quartic_struct {
            #last_row_and_zero

            last_row_and_zero_contribution
        }

        #[allow(unused_braces, unused_mut, unused_variables)]
        pub unsafe fn evaluate_quotient #generic_function_parameters (
            #additional_definition_function_arguments
            #random_point_ident: #quartic_struct,
            #witness_values_ident: &[#quartic_struct],
            #memory_values_ident: &[#quartic_struct],
            #setup_values_ident: &[#quartic_struct],
            #stage_2_values_ident: &[#quartic_struct],
            #witness_values_next_row_ident: &[#quartic_struct],
            #memory_values_next_row_ident: &[#quartic_struct],
            #stage_2_values_next_row_ident: &[#quartic_struct],
            #quotient_alpha_ident: #quartic_struct,
            #quotient_beta_ident: #quartic_struct,
            #divisors_ident: &[#quartic_struct; #num_different_divisors],
            #lookup_argument_linearization_challenges_ident: &[#quartic_struct; NUM_LOOKUP_ARGUMENT_LINEARIZATION_CHALLENGES],
            #lookup_argument_gamma_ident: #quartic_struct,
            #lookup_argument_two_gamma_ident: #quartic_struct,
            #memory_argument_linearization_challenges_ident: &[#quartic_struct; NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES],
            #memory_argument_gamma_ident: #quartic_struct,
            #delegation_argument_linearization_challenges_ident: &[#quartic_struct; NUM_DELEGATION_ARGUMENT_LINEARIZATION_CHALLENGES],
            #delegation_argument_gamma_ident: #quartic_struct,
            #decoder_lookup_argument_linearization_challenges_ident: &[#quartic_struct; EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_LINEARIZATION_CHALLENGES],
            #decoder_lookup_argument_gamma_ident: #quartic_struct,
            #state_permutation_argument_linearization_challenges_ident: &[#quartic_struct; NUM_MACHINE_STATE_LINEARIZATION_CHALLENGES],
            #state_permutation_argument_gamma_ident: #quartic_struct,
            #public_inputs_ident: &[#field_struct; #num_public_inputs],
            #aux_proof_values_ident: &#proof_aux_values_struct,
            #aux_boundary_values_ident: &[#aux_arguments_boundary_values_struct; #num_aux_boundary_values],
            #memory_timestamp_high_from_sequence_idx_ident: #field_struct,
            #delegation_type_ident: #field_struct,
            #delegation_argument_interpolant_linear_coeff_ident: #quartic_struct,
        ) -> #quartic_struct {
            let every_row_except_last_contribution = evaluate_every_row_except_last(
                #additional_function_arguments
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
                #decoder_lookup_argument_linearization_challenges_ident,
                #decoder_lookup_argument_gamma_ident,
                #state_permutation_argument_linearization_challenges_ident,
                #state_permutation_argument_gamma_ident,
                #public_inputs_ident,
                #aux_proof_values_ident,
                #aux_boundary_values_ident,
                #memory_timestamp_high_from_sequence_idx_ident,
                #delegation_type_ident,
                #delegation_argument_interpolant_linear_coeff_ident,
            );

            let every_row_except_two_last_contribution = evaluate_every_row_except_two(
                #additional_function_arguments
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
                #decoder_lookup_argument_linearization_challenges_ident,
                #decoder_lookup_argument_gamma_ident,
                #state_permutation_argument_linearization_challenges_ident,
                #state_permutation_argument_gamma_ident,
                #public_inputs_ident,
                #aux_proof_values_ident,
                #aux_boundary_values_ident,
                #memory_timestamp_high_from_sequence_idx_ident,
                #delegation_type_ident,
                #delegation_argument_interpolant_linear_coeff_ident,
            );

            let last_row_and_zero_contribution = evaluate_last_row_and_zero(
                #additional_function_arguments
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
                #decoder_lookup_argument_linearization_challenges_ident,
                #decoder_lookup_argument_gamma_ident,
                #state_permutation_argument_linearization_challenges_ident,
                #state_permutation_argument_gamma_ident,
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
            #quotient_mul_assign_beta;
            #quotient_add_assign_every_row_except_two_last_contribution;
            #quotient_mul_assign_beta;
            #quotient_add_assign_first_row_contribution;
            #quotient_mul_assign_beta;
            #quotient_add_assign_one_before_last_row_contribution;
            #quotient_mul_assign_beta;
            #quotient_add_assign_last_row_contribution;
            #quotient_mul_assign_beta;
            #quotient_add_assign_last_row_and_zero_contribution;

            quotient
        }
    }
}
