use super::*;

pub(crate) fn transform_first_or_last_rows(
    memory_layout: &MemorySubtree,
    stage_2_layout: &LookupAndMemoryArgumentLayout,
    public_inputs: &[(BoundaryConstraintLocation, ColumnAddress)],
    idents: &Idents,
) -> (TokenStream, TokenStream, TokenStream, TokenStream) {
    // first lazy init, then public inputs

    let Idents {
        random_point_ident,
        individual_term_ident,
        public_inputs_ident,
        aux_proof_values_ident,
        aux_boundary_values_ident,
        delegation_argument_interpolant_linear_coeff_ident,
        ..
    } = idents;

    let mut first_row_boundary_constraints = vec![];
    let mut one_before_last_row_boundary_constraints = vec![];

    if memory_layout.shuffle_ram_inits_and_teardowns.len() > 0 {
        for (init_idx, init_and_teardown) in memory_layout
            .shuffle_ram_inits_and_teardowns
            .iter()
            .enumerate()
        {
            let lazy_init_address_start = init_and_teardown.lazy_init_addresses_columns.start();
            let lazy_teardown_values_columns_start =
                init_and_teardown.lazy_teardown_values_columns.start();
            let lazy_teardown_timestamps_columns_start =
                init_and_teardown.lazy_teardown_timestamps_columns.start();

            first_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(lazy_init_address_start),
                quote! {
                    #aux_boundary_values_ident[#init_idx].lazy_init_first_row[0]
                },
            ));
            first_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(lazy_init_address_start + 1),
                quote! {
                    #aux_boundary_values_ident[#init_idx].lazy_init_first_row[1]
                },
            ));

            first_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(lazy_teardown_values_columns_start),
                quote! {
                    #aux_boundary_values_ident[#init_idx].teardown_value_first_row[0]
                },
            ));
            first_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(lazy_teardown_values_columns_start + 1),
                quote! {
                    #aux_boundary_values_ident[#init_idx].teardown_value_first_row[1]
                },
            ));

            first_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(lazy_teardown_timestamps_columns_start),
                quote! {
                    #aux_boundary_values_ident[#init_idx].teardown_timestamp_first_row[0]
                },
            ));
            first_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(lazy_teardown_timestamps_columns_start + 1),
                quote! {
                    #aux_boundary_values_ident[#init_idx].teardown_timestamp_first_row[1]
                },
            ));

            one_before_last_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(lazy_init_address_start),
                quote! {
                    #aux_boundary_values_ident[#init_idx].lazy_init_one_before_last_row[0]
                },
            ));
            one_before_last_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(lazy_init_address_start + 1),
                quote! {
                    #aux_boundary_values_ident[#init_idx].lazy_init_one_before_last_row[1]
                },
            ));

            one_before_last_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(lazy_teardown_values_columns_start),
                quote! {
                    #aux_boundary_values_ident[#init_idx].teardown_value_one_before_last_row[0]
                },
            ));
            one_before_last_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(lazy_teardown_values_columns_start + 1),
                quote! {
                    #aux_boundary_values_ident[#init_idx].teardown_value_one_before_last_row[1]
                },
            ));

            one_before_last_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(lazy_teardown_timestamps_columns_start),
                quote! {
                    #aux_boundary_values_ident[#init_idx].teardown_timestamp_one_before_last_row[0]
                },
            ));
            one_before_last_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(lazy_teardown_timestamps_columns_start + 1),
                quote! {
                    #aux_boundary_values_ident[#init_idx].teardown_timestamp_one_before_last_row[1]
                },
            ));
        }
    }

    for (i, (location, column_address)) in public_inputs.iter().enumerate() {
        match location {
            BoundaryConstraintLocation::FirstRow => {
                first_row_boundary_constraints.push((
                    *column_address,
                    quote! {
                        #public_inputs_ident[#i]
                    },
                ));
            }
            BoundaryConstraintLocation::OneBeforeLastRow => {
                one_before_last_row_boundary_constraints.push((
                    *column_address,
                    quote! {
                        #public_inputs_ident[#i]
                    },
                ));
            }
            BoundaryConstraintLocation::LastRow => {
                panic!("public inputs on the last row are not supported");
            }
        }
    }

    let first_row = {
        let mut first_row_stream = TokenStream::new();

        for (_i, (place, expected_value)) in first_row_boundary_constraints.iter().enumerate() {
            let value_expr = read_value_expr(*place, idents, false);

            let t = quote! {
                let #individual_term_ident = {
                    let mut #individual_term_ident = #value_expr;
                    let t = #expected_value;
                    #individual_term_ident.sub_assign_base(&t);

                    #individual_term_ident
                };
            };

            accumulate_contributions(&mut first_row_stream, None, vec![t], idents);
        }

        // 1 constraint for memory accumulator initial value == 1
        {
            let offset = stage_2_layout
                .get_intermediate_polys_for_grand_product_accumulation_absolute_poly_idx_for_verifier();
            let value_expr = read_stage_2_value_expr(offset, idents, false);

            let t = quote! {
                let #individual_term_ident = {
                    let mut #individual_term_ident = #value_expr;
                    #individual_term_ident.sub_assign_base(&Mersenne31Field::ONE);

                    #individual_term_ident
                };
            };

            accumulate_contributions(&mut first_row_stream, None, vec![t], idents);
        }

        first_row_stream
    };

    let one_before_last_row = {
        let mut one_before_last_row_stream = TokenStream::new();

        for (_i, (place, expected_value)) in
            one_before_last_row_boundary_constraints.iter().enumerate()
        {
            let value_expr = read_value_expr(*place, idents, false);

            let t = quote! {
                let #individual_term_ident = {
                    let mut #individual_term_ident = #value_expr;
                    let t = #expected_value;
                    #individual_term_ident.sub_assign_base(&t);

                    #individual_term_ident
                };
            };

            accumulate_contributions(&mut one_before_last_row_stream, None, vec![t], idents);
        }

        one_before_last_row_stream
    };

    let last_row = {
        let mut last_row_streams = TokenStream::new();

        let offset = stage_2_layout
            .get_intermediate_polys_for_grand_product_accumulation_absolute_poly_idx_for_verifier();
        let value_expr = read_stage_2_value_expr(offset, idents, false);

        let t = quote! {
            let #individual_term_ident = {
                let mut #individual_term_ident = #value_expr;
                let t = #aux_proof_values_ident.grand_product_accumulator_final_value;
                #individual_term_ident.sub_assign(&t);

                #individual_term_ident
            };
        };
        accumulate_contributions(&mut last_row_streams, None, vec![t], idents);

        last_row_streams
    };

    let last_row_and_zero = {
        let mut last_row_and_zero_streams = TokenStream::new();

        // range checks
        {
            // range check 16
            if stage_2_layout
                .intermediate_poly_for_range_check_16_multiplicity
                .num_elements()
                > 0
            {
                let offset = stage_2_layout
                    .range_check_16_intermediate_poly_for_multiplicities_absolute_poly_idx_for_verifier();
                let multiplicities_acc_expr = read_stage_2_value_expr(offset, idents, false);

                let mut substream = quote! {
                    let mut #individual_term_ident = #multiplicities_acc_expr;
                };

                let num_pairs = stage_2_layout
                    .intermediate_polys_for_range_check_16
                    .num_pairs;

                for i in 0..num_pairs {
                    let offset = stage_2_layout
                        .intermediate_polys_for_range_check_16
                        .get_ext4_poly_index_in_openings(i, stage_2_layout);
                    let el_expr = read_stage_2_value_expr(offset, idents, false);

                    let t = quote! {
                        let t = #el_expr;
                        #individual_term_ident.sub_assign(&t);
                    };
                    substream.extend(t);
                }

                if let Some(lazy_init_address_range_check_16) =
                    stage_2_layout.lazy_init_address_range_check_16
                {
                    for i in 0..lazy_init_address_range_check_16.num_pairs {
                        let offset = lazy_init_address_range_check_16
                            .get_ext4_poly_index_in_openings(i, stage_2_layout);
                        let el_expr = read_stage_2_value_expr(offset, idents, false);

                        let t = quote! {
                            let t = #el_expr;
                            #individual_term_ident.sub_assign(&t);
                        };
                        substream.extend(t);
                    }
                }

                if let Some(_remainder) = stage_2_layout.remainder_for_range_check_16 {
                    todo!();
                }

                let t = quote! {
                    let #individual_term_ident = {
                        #substream

                        #individual_term_ident
                    };
                };

                accumulate_contributions(&mut last_row_and_zero_streams, None, vec![t], idents);
            }

            // timestamp range checks
            if stage_2_layout
                .intermediate_poly_for_timestamp_range_check_multiplicity
                .num_elements()
                > 0
            {
                let offset = stage_2_layout
                    .timestamp_range_check_intermediate_poly_for_multiplicities_absolute_poly_idx_for_verifier();
                let multiplicities_acc_expr = read_stage_2_value_expr(offset, idents, false);

                let mut substream = quote! {
                    let mut #individual_term_ident = #multiplicities_acc_expr;
                };

                let num_pairs = stage_2_layout
                    .intermediate_polys_for_timestamp_range_checks
                    .num_pairs;

                for i in 0..num_pairs {
                    let offset = stage_2_layout
                        .intermediate_polys_for_timestamp_range_checks
                        .get_ext4_poly_index_in_openings(i, stage_2_layout);
                    let el_expr = read_stage_2_value_expr(offset, idents, false);

                    let t = quote! {
                        let t = #el_expr;
                        #individual_term_ident.sub_assign(&t);
                    };
                    substream.extend(t);
                }

                let t = quote! {
                    let #individual_term_ident = {
                        #substream

                        #individual_term_ident
                    };
                };

                accumulate_contributions(&mut last_row_and_zero_streams, None, vec![t], idents);
            }
        }

        // Decoder lookups
        if stage_2_layout
            .intermediate_poly_for_decoder_accesses
            .num_elements()
            > 0
        {
            let offset = stage_2_layout
                .decoder_lookup_intermediate_poly_for_multiplicities_absolute_poly_idx_for_verifier(
                );
            let multiplicities_acc_expr = read_stage_2_value_expr(offset, idents, false);

            let offset = stage_2_layout
                .get_intermediate_poly_for_decoder_lookup_absolute_poly_idx_for_verifier();
            let lookup_acc_expr = read_stage_2_value_expr(offset, idents, false);

            let t = quote! {
                let #individual_term_ident = {
                    let mut #individual_term_ident = #multiplicities_acc_expr;
                    #individual_term_ident.sub_assign(&#lookup_acc_expr);

                    #individual_term_ident
                };
            };

            accumulate_contributions(&mut last_row_and_zero_streams, None, vec![t], idents);
        }

        // generic lookup
        if stage_2_layout
            .intermediate_polys_for_generic_multiplicities
            .num_elements()
            > 0
        {
            let bound = stage_2_layout
                .intermediate_polys_for_generic_multiplicities
                .num_elements();
            let offset = stage_2_layout
                .generic_width_3_lookup_intermediate_polys_for_multiplicities_absolute_poly_idx_for_verifier(0);
            let multiplicities_acc_expr = read_stage_2_value_expr(offset, idents, false);

            let mut substream = quote! {
                let mut #individual_term_ident = #multiplicities_acc_expr;
            };

            for i in 1..bound {
                let offset = stage_2_layout
                    .generic_width_3_lookup_intermediate_polys_for_multiplicities_absolute_poly_idx_for_verifier(i);
                let multiplicities_acc_expr = read_stage_2_value_expr(offset, idents, false);
                let t = quote! {
                    let t = #multiplicities_acc_expr;
                    #individual_term_ident.add_assign(&t);
                };
                substream.extend(t);
            }

            for i in 0..stage_2_layout
                .intermediate_polys_for_generic_lookup
                .num_elements()
            {
                let offset = stage_2_layout
                    .get_intermediate_polys_for_generic_lookup_absolute_poly_idx_for_verifier(i);
                let el_expr = read_stage_2_value_expr(offset, idents, false);

                let t = quote! {
                    let t = #el_expr;
                    #individual_term_ident.sub_assign(&t);
                };
                substream.extend(t);
            }

            let t = quote! {
                let #individual_term_ident = {
                    #substream

                    #individual_term_ident
                };
            };

            accumulate_contributions(&mut last_row_and_zero_streams, None, vec![t], idents);
        }

        // and delegation creation/processing
        if memory_layout.delegation_request_layout.is_some()
            || memory_layout.delegation_processor_layout.is_some()
        {
            // we need to show the sum of the values everywhere except the last row,
            // so we show that intermediate poly - interpolant((0, 0), (omega^-1, `value``)) is divisible
            // by our selected divisor

            // interpolant is literally 1/omega^-1 * value * X (as one can see it's 0 at 0 and `value` at omega^-1)
            let acc = stage_2_layout
                .get_aux_polys_for_gelegation_argument_absolute_poly_idx_for_verifier()
                .expect("must exist");
            let accumulator_expr = read_stage_2_value_expr(acc, idents, false);

            let t = quote! {
                let #individual_term_ident = {
                    let mut #individual_term_ident = #accumulator_expr;
                    // coeff should be accumulator value / omega^-1
                    let mut t = #random_point_ident;
                    t.mul_assign(& #delegation_argument_interpolant_linear_coeff_ident);
                    #individual_term_ident.sub_assign(&t);

                    #individual_term_ident
                };
            };

            accumulate_contributions(&mut last_row_and_zero_streams, None, vec![t], idents);
        }

        last_row_and_zero_streams
    };

    (first_row, one_before_last_row, last_row, last_row_and_zero)
}
