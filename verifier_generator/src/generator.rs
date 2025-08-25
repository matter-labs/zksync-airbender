use super::*;

use cs::definitions::{LookupExpression, LookupSetDescription};
use proc_macro2::TokenStream;
use quote::{quote, ToTokens, TokenStreamExt};

pub fn generate_from_parts(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
) -> TokenStream {
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
        trace_len,
        ..
    } = compiled_circuit;

    assert!(trace_len.is_power_of_two());

    // eventually we can unroll the quotient itself

    let witness_tree = transform_witness_layout(witness_layout.clone());
    let memory_tree = transform_memory_layout(memory_layout.clone());
    let setup_tree = transform_setup_layout(setup_layout.clone());
    let stage_2_tree = transform_stage_2_layout(stage_2_layout.clone());

    let mut degree_2_constraints_stream = TokenStream::new();
    degree_2_constraints_stream.append_separated(
        degree_2_constraints
            .into_iter()
            .cloned()
            .map(|el| transform_degree_2_constraint(el)),
        quote! {,},
    );

    let mut degree_1_constraints_stream = TokenStream::new();
    degree_1_constraints_stream.append_separated(
        degree_1_constraints
            .into_iter()
            .cloned()
            .map(|el| transform_degree_1_constraint(el)),
        quote! {,},
    );

    let mut state_linkage_constraints_stream = TokenStream::new();
    state_linkage_constraints_stream.append_separated(
        state_linkage_constraints.into_iter().map(|el| {
            let (a, b) = el;
            quote! {
                (#a, #b)
            }
        }),
        quote! {,},
    );

    let mut public_inputs_stream = TokenStream::new();
    public_inputs_stream.append_separated(
        public_inputs.into_iter().map(|el| {
            let (a, b) = el;
            quote! {
                (#a, #b)
            }
        }),
        quote! {,},
    );

    let mut lazy_init_address_aux_vars_stream = TokenStream::new();
    lazy_init_address_aux_vars_stream.append_separated(
        lazy_init_address_aux_vars.into_iter().map(|el| {
            quote! {
                #el
            }
        }),
        quote! {,},
    );
    let trace_len_log2 = trace_len.trailing_zeros() as usize;

    let result = quote! {
        #witness_tree

        #memory_tree

        #setup_tree

        #stage_2_tree

        pub const VERIFIER_COMPILED_LAYOUT: VerifierCompiledCircuitArtifact<'static, Mersenne31Field> = VerifierCompiledCircuitArtifact {
            witness_layout: COMPILED_WITNESS_LAYOUT,
            memory_layout: COMPILED_MEMORY_LAYOUT,
            setup_layout: COMPILED_SETUP_LAYOUT,
            stage_2_layout: COMPILED_STAGE_2_LAYOUT,
            degree_2_constraints: &[#degree_2_constraints_stream],
            degree_1_constraints: &[#degree_1_constraints_stream],
            state_linkage_constraints: &[#state_linkage_constraints_stream],
            public_inputs: &[#public_inputs_stream],
            lazy_init_address_aux_vars: &[#lazy_init_address_aux_vars_stream],
            trace_len_log2: #trace_len_log2,
        };

    };

    result
}

fn transform_witness_layout(witness_layout: WitnessSubtree<Mersenne31Field>) -> TokenStream {
    let WitnessSubtree {
        multiplicities_columns_for_range_check_16,
        multiplicities_columns_for_timestamp_range_check,
        multiplicities_columns_for_decoder_in_executor_families,
        multiplicities_columns_for_generic_lookup,
        range_check_8_columns: _,
        range_check_16_columns,
        range_check_16_lookup_expressions,
        timestamp_range_check_lookup_expressions,
        offset_for_special_shuffle_ram_timestamps_range_check_expressions,
        width_3_lookups,
        boolean_vars_columns_range,
        scratch_space_columns_range,
        total_width,
    } = witness_layout;

    let mut width_3_lookups_stream = TokenStream::new();
    width_3_lookups_stream.append_separated(
        width_3_lookups
            .into_iter()
            .map(|el| transform_lookup_set_description(el)),
        quote! {,},
    );

    let mut range_check_16_lookup_expressions_stream = TokenStream::new();
    range_check_16_lookup_expressions_stream.append_separated(
        range_check_16_lookup_expressions
            .into_iter()
            .map(|el| transform_lookup_expression(el)),
        quote! {,},
    );

    let mut timestamp_range_check_lookup_expressions_stream = TokenStream::new();
    timestamp_range_check_lookup_expressions_stream.append_separated(
        timestamp_range_check_lookup_expressions
            .into_iter()
            .map(|el| transform_lookup_expression(el)),
        quote! {,},
    );

    quote! {
        const COMPILED_WITNESS_LAYOUT: CompiledWitnessSubtree<Mersenne31Field> = CompiledWitnessSubtree {
            multiplicities_columns_for_range_check_16: #multiplicities_columns_for_range_check_16,
            multiplicities_columns_for_timestamp_range_check: #multiplicities_columns_for_timestamp_range_check,
            multiplicities_columns_for_decoder_in_executor_families: #multiplicities_columns_for_decoder_in_executor_families,
            multiplicities_columns_for_generic_lookup: #multiplicities_columns_for_generic_lookup,
            range_check_16_columns: #range_check_16_columns,
            width_3_lookups: &[#width_3_lookups_stream],
            range_check_16_lookup_expressions: &[#range_check_16_lookup_expressions_stream],
            timestamp_range_check_lookup_expressions: &[#timestamp_range_check_lookup_expressions_stream],
            offset_for_special_shuffle_ram_timestamps_range_check_expressions: #offset_for_special_shuffle_ram_timestamps_range_check_expressions,
            boolean_vars_columns_range: #boolean_vars_columns_range,
            scratch_space_columns_range: #scratch_space_columns_range,
            total_width: #total_width,
        };
    }
}

fn transform_memory_layout(memory_layout: MemorySubtree) -> TokenStream {
    let MemorySubtree {
        shuffle_ram_inits_and_teardowns,
        delegation_request_layout,
        delegation_processor_layout,
        shuffle_ram_access_sets,
        machine_state_layout,
        intermediate_state_layout,
        batched_ram_accesses,
        register_and_indirect_accesses,
        total_width,
    } = memory_layout;

    let shuffle_ram_access_sets_stream = slice_to_tokens(&shuffle_ram_access_sets);
    let batched_ram_accesses_stream = slice_to_tokens(&batched_ram_accesses);
    let register_and_indirect_accesses_stream = slice_to_tokens(&register_and_indirect_accesses);
    let shuffle_ram_inits_and_teardowns = slice_to_tokens(&shuffle_ram_inits_and_teardowns);

    let delegation_request_layout = transform_option(delegation_request_layout);
    let delegation_processor_layout = transform_option(delegation_processor_layout);
    let machine_state_layout = transform_option(machine_state_layout);
    let intermediate_state_layout = transform_option(intermediate_state_layout);

    quote! {
        const COMPILED_MEMORY_LAYOUT: CompiledMemorySubtree<'static> = CompiledMemorySubtree {
            shuffle_ram_inits_and_teardowns: #shuffle_ram_inits_and_teardowns,
            delegation_request_layout: #delegation_request_layout,
            delegation_processor_layout: #delegation_processor_layout,
            shuffle_ram_access_sets: #shuffle_ram_access_sets_stream,
            machine_state_layout: #machine_state_layout,
            intermediate_state_layout: #intermediate_state_layout,
            batched_ram_accesses: #batched_ram_accesses_stream,
            register_and_indirect_accesses: #register_and_indirect_accesses_stream,
            total_width: #total_width,
        };
    }
}

fn transform_setup_layout(setup_layout: SetupLayout) -> TokenStream {
    let SetupLayout {
        timestamp_setup_columns,
        timestamp_range_check_setup_column,
        range_check_16_setup_column,
        generic_lookup_setup_columns,
        preprocessed_decoder_setup_columns,
        total_width,
    } = setup_layout;

    quote! {
        const COMPILED_SETUP_LAYOUT: SetupLayout = SetupLayout {
            timestamp_setup_columns: #timestamp_setup_columns,
            timestamp_range_check_setup_column: #timestamp_range_check_setup_column,
            range_check_16_setup_column: #range_check_16_setup_column,
            generic_lookup_setup_columns: #generic_lookup_setup_columns,
            preprocessed_decoder_setup_columns: #preprocessed_decoder_setup_columns,
            total_width: #total_width,
        };
    }
}

fn transform_stage_2_layout(layoyt: LookupAndMemoryArgumentLayout) -> TokenStream {
    let LookupAndMemoryArgumentLayout {
        intermediate_polys_for_range_check_16,
        remainder_for_range_check_16,
        lazy_init_address_range_check_16,
        intermediate_polys_for_timestamp_range_checks,
        intermediate_polys_for_generic_lookup,
        intermediate_poly_for_decoder_accesses,
        intermediate_poly_for_range_check_16_multiplicity,
        intermediate_poly_for_timestamp_range_check_multiplicity,
        intermediate_polys_for_generic_multiplicities,
        intermediate_polys_for_decoder_multiplicities,
        delegation_processing_aux_poly,
        intermediate_polys_for_memory_init_teardown,
        intermediate_polys_for_memory_argument,
        intermediate_polys_for_state_permutation,
        intermediate_polys_for_permutation_masking,
        intermediate_poly_for_grand_product,
        ext4_polys_offset,
        total_width,
    } = layoyt;

    let remainder_for_range_check_16 = transform_option(remainder_for_range_check_16);
    let delegation_processing_aux_poly = transform_option(delegation_processing_aux_poly);
    let lazy_init_address_range_check_16 = transform_option(lazy_init_address_range_check_16);

    quote! {
        const COMPILED_STAGE_2_LAYOUT: LookupAndMemoryArgumentLayout = LookupAndMemoryArgumentLayout {
            intermediate_polys_for_range_check_16: #intermediate_polys_for_range_check_16,
            remainder_for_range_check_16: #remainder_for_range_check_16,
            lazy_init_address_range_check_16: #lazy_init_address_range_check_16,
            intermediate_polys_for_timestamp_range_checks: #intermediate_polys_for_timestamp_range_checks,
            intermediate_polys_for_generic_lookup: #intermediate_polys_for_generic_lookup,
            intermediate_poly_for_decoder_accesses: #intermediate_poly_for_decoder_accesses,
            intermediate_poly_for_range_check_16_multiplicity: #intermediate_poly_for_range_check_16_multiplicity,
            intermediate_poly_for_timestamp_range_check_multiplicity: #intermediate_poly_for_timestamp_range_check_multiplicity,
            intermediate_polys_for_generic_multiplicities: #intermediate_polys_for_generic_multiplicities,
            intermediate_polys_for_decoder_multiplicities: #intermediate_polys_for_decoder_multiplicities,
            delegation_processing_aux_poly: #delegation_processing_aux_poly,
            intermediate_polys_for_memory_init_teardown: #intermediate_polys_for_memory_init_teardown,
            intermediate_polys_for_memory_argument: #intermediate_polys_for_memory_argument,
            intermediate_polys_for_state_permutation: #intermediate_polys_for_state_permutation,
            intermediate_polys_for_permutation_masking: #intermediate_polys_for_permutation_masking,
            intermediate_poly_for_grand_product: #intermediate_poly_for_grand_product,
            ext4_polys_offset: #ext4_polys_offset,
            total_width: #total_width,
        };
    }
}

fn transform_option<T: ToTokens>(el: Option<T>) -> TokenStream {
    match el {
        Some(el) => quote! {
            Some(#el)
        },
        None => quote! {
            None
        },
    }
}

fn transform_degree_2_constraint(
    constraint: CompiledDegree2Constraint<Mersenne31Field>,
) -> TokenStream {
    let CompiledDegree2Constraint {
        quadratic_terms,
        linear_terms,
        constant_term,
    } = constraint;
    let constant_term = constant_term.to_reduced_u32();

    let mut quadratic_terms_stream = TokenStream::new();
    quadratic_terms_stream.append_separated(
        quadratic_terms.iter().map(|el| {
            let (coeff, a, b) = el;
            let coeff = coeff.to_reduced_u32();
            quote! {
                (Mersenne31Field(#coeff), #a, #b)
            }
        }),
        quote! {,},
    );

    let mut linear_terms_stream = TokenStream::new();
    linear_terms_stream.append_separated(
        linear_terms.iter().map(|el| {
            let (coeff, a) = el;
            let coeff = coeff.to_reduced_u32();
            quote! {
                (Mersenne31Field(#coeff), #a)
            }
        }),
        quote! {,},
    );

    quote! {
        StaticVerifierCompiledDegree2Constraint {
            quadratic_terms: &[#quadratic_terms_stream],
            linear_terms: &[#linear_terms_stream],
            constant_term: Mersenne31Field(#constant_term),
        }
    }
}

// transforms CompiledDegree1Constraint into StaticVerifierCompiledDegree1Constraint literal
fn transform_degree_1_constraint(
    constraint: CompiledDegree1Constraint<Mersenne31Field>,
) -> TokenStream {
    let CompiledDegree1Constraint {
        linear_terms,
        constant_term,
    } = constraint;
    let constant_term = constant_term.to_reduced_u32();

    let mut linear_terms_stream = TokenStream::new();
    linear_terms_stream.append_separated(
        linear_terms.iter().map(|el| {
            let (coeff, a) = el;
            let coeff = coeff.to_reduced_u32();
            quote! {
                (Mersenne31Field(#coeff), #a)
            }
        }),
        quote! {,},
    );

    quote! {
        StaticVerifierCompiledDegree1Constraint {
            linear_terms: &[#linear_terms_stream],
            constant_term: Mersenne31Field(#constant_term),
        }
    }
}

// Transformrs LookupExpression into VerifierCompiledLookupExpression<'static>
fn transform_lookup_expression(expression: LookupExpression<Mersenne31Field>) -> TokenStream {
    match expression {
        LookupExpression::Variable(place) => {
            quote! {
                VerifierCompiledLookupExpression::Variable(#place)
            }
        }
        LookupExpression::Expression(constraint) => {
            let constraint_stream = transform_degree_1_constraint(constraint);
            quote! {
                VerifierCompiledLookupExpression::Expression(#constraint_stream)
            }
        }
    }
}

// transforms LookupSetDescription into VerifierCompiledLookupSetDescription literal
fn transform_lookup_set_description(
    description: LookupSetDescription<Mersenne31Field, 3>,
) -> TokenStream {
    let LookupSetDescription {
        input_columns,
        table_index,
    } = description;

    let input_columns = array_to_tokens(&input_columns.map(|el| transform_lookup_expression(el)));

    quote! {
        VerifierCompiledLookupSetDescription {
            input_columns: #input_columns,
            table_index: #table_index,
        }
    }
}
