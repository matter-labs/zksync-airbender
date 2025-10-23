use super::*;

pub(crate) fn transform_grand_product_accumulators(
    memory_layout: &MemorySubtree,
    stage_2_layout: &LookupAndMemoryArgumentLayout,
    setup_layout: &SetupLayout,
    idents: &Idents,
    into: &mut TokenStream,
) {
    let Idents {
        individual_term_ident,
        memory_argument_linearization_challenges_ident,
        memory_argument_gamma_ident,
        memory_timestamp_high_from_sequence_idx_ident,
        state_permutation_argument_linearization_challenges_ident,
        state_permutation_argument_gamma_ident,
        ..
    } = idents;

    assert!(memory_layout.batched_ram_accesses.is_empty(), "deprecated");

    // and now we work with memory multiplicative accumulators
    // Numerator is write set, denom is read set

    // Sequence is always as
    // - init/teardown
    // - memory accesses (whether shuffle RAM or special register/indirect)
    // - machine state
    // - masking
    // - grand product accumulation

    let mut streams = vec![];
    let mut previous_acc_value_offset = None;

    // sequence of keys is in general is_reg || address_low || address_high || timestamp low || timestamp_high || value_low || value_high

    // Assemble P(x) = write init set / read teardown set

    if memory_layout.shuffle_ram_access_sets.len() > 0 {
        assert!(memory_layout.register_and_indirect_accesses.is_empty());
        // now we can continue to accumulate
        for (access_idx, memory_access_columns) in
            memory_layout.shuffle_ram_access_sets.iter().enumerate()
        {
            // address is always the same
            let access_idx_u32 = access_idx as u32;

            let address_columns = memory_access_columns.get_address();

            let address_contribution = match address_columns {
                ShuffleRamAddress::RegisterOnly(RegisterOnlyAccessAddress { register_index }) => {
                    let register_index_expr = read_value_expr(
                        ColumnAddress::MemorySubtree(register_index.start()),
                        idents,
                        false,
                    );

                    quote! {
                        let address_contribution = {
                            let address_low = #register_index_expr;
                            let mut address_contribution = #memory_argument_linearization_challenges_ident
                                [#MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                            address_contribution.mul_assign(&address_low);

                            // considered is register always
                            address_contribution.add_assign_base(&Mersenne31Field::ONE);

                            address_contribution
                        };
                    }
                }
                ShuffleRamAddress::RegisterOrRam(RegisterOrRamAccessAddress {
                    is_register,
                    address,
                }) => {
                    let is_register_expr = read_value_expr(
                        ColumnAddress::MemorySubtree(is_register.start()),
                        idents,
                        false,
                    );

                    let address_low_expr = read_value_expr(
                        ColumnAddress::MemorySubtree(address.start()),
                        idents,
                        false,
                    );
                    let address_high_expr = read_value_expr(
                        ColumnAddress::MemorySubtree(address.start() + 1),
                        idents,
                        false,
                    );

                    quote! {
                        let address_contribution = {
                            let address_low = #address_low_expr;
                            let mut address_contribution = #memory_argument_linearization_challenges_ident
                                [#MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                            address_contribution.mul_assign(&address_low);

                            let address_high = #address_high_expr;
                            let mut t = #memory_argument_linearization_challenges_ident
                                [#MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                            t.mul_assign(&address_high);
                            address_contribution.add_assign(&t);

                            let is_register = #is_register_expr;
                            address_contribution.add_assign(&is_register);

                            address_contribution
                        };
                    }
                }
            };

            let read_value_columns = memory_access_columns.get_read_value_columns();
            let read_value_low_expr = read_value_expr(
                ColumnAddress::MemorySubtree(read_value_columns.start()),
                idents,
                false,
            );
            let read_value_high_expr = read_value_expr(
                ColumnAddress::MemorySubtree(read_value_columns.start() + 1),
                idents,
                false,
            );

            let read_timestamp_columns = memory_access_columns.get_read_timestamp_columns();
            let read_timestamp_low_expr = read_value_expr(
                ColumnAddress::MemorySubtree(read_timestamp_columns.start()),
                idents,
                false,
            );
            let read_timestamp_high_expr = read_value_expr(
                ColumnAddress::MemorySubtree(read_timestamp_columns.start() + 1),
                idents,
                false,
            );

            let offset = stage_2_layout
                .get_intermediate_polys_for_memory_argument_absolute_poly_idx_for_verifier(
                    access_idx,
                );
            let accumulator_expr = read_stage_2_value_expr(offset, idents, false);

            let (
                write_timestamp_low_expr,
                write_timestamp_high_expr,
                contribution_from_circuit_timestamp,
            ) = if let Some(intermediate_state_layout) =
                memory_layout.intermediate_state_layout.as_ref()
            {
                let write_timestamp_low_expr = read_value_expr(
                    ColumnAddress::MemorySubtree(intermediate_state_layout.timestamp.start()),
                    idents,
                    false,
                );
                let write_timestamp_high_expr = read_value_expr(
                    ColumnAddress::MemorySubtree(intermediate_state_layout.timestamp.start() + 1),
                    idents,
                    false,
                );

                (
                    write_timestamp_low_expr,
                    write_timestamp_high_expr,
                    quote! {},
                )
            } else {
                let write_timestamp_low_expr = read_value_expr(
                    ColumnAddress::SetupSubtree(setup_layout.timestamp_setup_columns.start()),
                    idents,
                    false,
                );
                let write_timestamp_high_expr = read_value_expr(
                    ColumnAddress::SetupSubtree(setup_layout.timestamp_setup_columns.start() + 1),
                    idents,
                    false,
                );

                let from_circuit_idx = quote! {
                    write_timestamp_high.add_assign_base(&#memory_timestamp_high_from_sequence_idx_ident);
                };

                (
                    write_timestamp_low_expr,
                    write_timestamp_high_expr,
                    from_circuit_idx,
                )
            };

            let baseline_quote = match memory_access_columns {
                ShuffleRamQueryColumns::Readonly(_) => {
                    quote! {
                            #address_contribution

                            let value_low = #read_value_low_expr;
                            let mut value_contribution = #memory_argument_linearization_challenges_ident
                                [#MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                            value_contribution.mul_assign(&value_low);

                            let value_high = #read_value_high_expr;
                            let mut t = #memory_argument_linearization_challenges_ident
                                [#MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                            t.mul_assign(&value_high);
                            value_contribution.add_assign(&t);

                            let mut numerator = #memory_argument_gamma_ident;
                            numerator.add_assign(&address_contribution);
                            numerator.add_assign(&value_contribution);

                            let mut denom = numerator;

                            // read and write set only differ in timestamp contribution

                            let read_timestamp_low = #read_timestamp_low_expr;
                            let mut read_timestamp_contribution =
                                #memory_argument_linearization_challenges_ident
                                    [#MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                            read_timestamp_contribution
                                .mul_assign(&read_timestamp_low);

                            let read_timestamp_high = #read_timestamp_high_expr;
                            let mut t = #memory_argument_linearization_challenges_ident
                                [#MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                            t.mul_assign(&read_timestamp_high);
                            read_timestamp_contribution.add_assign(&t);

                            let mut write_timestamp_low = #write_timestamp_low_expr;
                            write_timestamp_low.add_assign_base(
                                &Mersenne31Field(#access_idx_u32),
                            );
                            let mut write_timestamp_contribution =
                                #memory_argument_linearization_challenges_ident
                                    [#MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                            write_timestamp_contribution
                                .mul_assign(&write_timestamp_low);

                            let mut write_timestamp_high = #write_timestamp_high_expr;
                            // maybe use circuit index for timestamps
                            #contribution_from_circuit_timestamp

                            let mut t = #memory_argument_linearization_challenges_ident
                                [#MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                            t.mul_assign(&write_timestamp_high);
                            write_timestamp_contribution.add_assign(&t);

                            numerator.add_assign(&write_timestamp_contribution);
                            denom.add_assign(&read_timestamp_contribution);
                    }
                }
                ShuffleRamQueryColumns::Write(columns) => {
                    let write_value_low_expr = read_value_expr(
                        ColumnAddress::MemorySubtree(columns.write_value.start()),
                        idents,
                        false,
                    );
                    let write_value_high_expr = read_value_expr(
                        ColumnAddress::MemorySubtree(columns.write_value.start() + 1),
                        idents,
                        false,
                    );

                    quote! {
                            #address_contribution

                            let mut numerator = #memory_argument_gamma_ident;
                            numerator.add_assign(&address_contribution);

                            let mut denom = numerator;

                            // we differ in value and timestamp

                            let read_value_low = #read_value_low_expr;
                            let mut read_value_contribution = #memory_argument_linearization_challenges_ident
                                [#MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                            read_value_contribution.mul_assign(&read_value_low);

                            let read_value_high = #read_value_high_expr;
                            let mut t = #memory_argument_linearization_challenges_ident
                                [#MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                            t.mul_assign(&read_value_high);
                            read_value_contribution.add_assign(&t);

                            let write_value_low = #write_value_low_expr;
                            let mut write_value_contribution = #memory_argument_linearization_challenges_ident
                                [#MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                            write_value_contribution.mul_assign(&write_value_low);

                            let write_value_high = #write_value_high_expr;
                            let mut t = #memory_argument_linearization_challenges_ident
                                [#MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                            t.mul_assign(&write_value_high);
                            write_value_contribution.add_assign(&t);

                            numerator.add_assign(&write_value_contribution);
                            denom.add_assign(&read_value_contribution);

                            let read_timestamp_low = #read_timestamp_low_expr;
                            let mut read_timestamp_contribution =
                                #memory_argument_linearization_challenges_ident
                                    [#MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                            read_timestamp_contribution
                                .mul_assign(&read_timestamp_low);

                            let read_timestamp_high = #read_timestamp_high_expr;
                            let mut t = #memory_argument_linearization_challenges_ident
                                [#MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                            t.mul_assign(&read_timestamp_high);
                            read_timestamp_contribution.add_assign(&t);

                            let mut write_timestamp_low = #write_timestamp_low_expr;
                            write_timestamp_low.add_assign_base(
                                &Mersenne31Field(#access_idx_u32),
                            );
                            let mut write_timestamp_contribution =
                                #memory_argument_linearization_challenges_ident
                                    [#MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                            write_timestamp_contribution
                                .mul_assign(&write_timestamp_low);

                            let mut write_timestamp_high = #write_timestamp_high_expr;
                            // maybe use circuit index for timestamps
                            #contribution_from_circuit_timestamp

                            let mut t = #memory_argument_linearization_challenges_ident
                                [#MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                            t.mul_assign(&write_timestamp_high);
                            write_timestamp_contribution.add_assign(&t);

                            numerator.add_assign(&write_timestamp_contribution);
                            denom.add_assign(&read_timestamp_contribution);
                    }
                }
            };

            if let Some(previous_acc_value_offset) = previous_acc_value_offset.take() {
                let previous_acc_expr =
                    read_stage_2_value_expr(previous_acc_value_offset, idents, false);

                let t = quote! {
                    let #individual_term_ident = {
                        #baseline_quote;

                        let accumulator = #accumulator_expr;
                        let previous = #previous_acc_expr;

                        // this * demon - previous * numerator
                        // or just this * denom - numerator
                        let mut #individual_term_ident = accumulator;
                        #individual_term_ident.mul_assign(&denom);
                        let mut t = previous;
                        t.mul_assign(&numerator);
                        #individual_term_ident.sub_assign(&t);

                        #individual_term_ident
                    };
                };

                streams.push(t);
            } else {
                assert_eq!(access_idx, 0);

                let t = quote! {
                    let #individual_term_ident = {
                        #baseline_quote;

                        let accumulator = #accumulator_expr;

                        let mut #individual_term_ident = accumulator;
                        #individual_term_ident.mul_assign(&denom);
                        #individual_term_ident.sub_assign(&numerator);

                        #individual_term_ident
                    };
                };

                streams.push(t);
            }

            assert!(previous_acc_value_offset.is_none());
            previous_acc_value_offset = Some(offset);
        }
    }

    accumulate_contributions(into, None, streams, idents);

    // register/indirects in delegation
    if memory_layout.register_and_indirect_accesses.len() > 0 {
        assert!(memory_layout.shuffle_ram_inits_and_teardowns.is_empty());
        assert!(memory_layout.shuffle_ram_access_sets.is_empty());
        assert_eq!(
            stage_2_layout
                .intermediate_polys_for_state_permutation
                .num_elements(),
            0
        );
        assert_eq!(
            stage_2_layout
                .intermediate_polys_for_permutation_masking
                .num_elements(),
            0
        );

        transform_delegation_ram_memory_accumulators(
            memory_layout,
            stage_2_layout,
            idents,
            &mut previous_acc_value_offset,
            into,
        );
    }

    // machine state
    if stage_2_layout
        .intermediate_polys_for_state_permutation
        .num_elements()
        > 0
    {
        // sequence of keys is pc_low || pc_high || timestamp low || timestamp_high

        // we assemble P(x) = write set / read set

        let previous_offset = previous_acc_value_offset
            .take()
            .expect("some value to accumulate");

        let initial_machine_state = memory_layout.intermediate_state_layout.unwrap();
        let final_machine_state = memory_layout.machine_state_layout.unwrap();
        assert_eq!(
            stage_2_layout
                .intermediate_polys_for_state_permutation
                .num_elements(),
            1
        );
        let offset = stage_2_layout
            .get_intermediate_polys_for_machine_state_permutation_absolute_poly_idx_for_verifier();
        let previous_expr = read_stage_2_value_expr(previous_offset, idents, false);
        let accumulator_expr = read_stage_2_value_expr(offset, idents, false);

        let final_c0 = read_value_expr(
            ColumnAddress::MemorySubtree(final_machine_state.pc.start()),
            idents,
            false,
        );
        let final_c1 = read_value_expr(
            ColumnAddress::MemorySubtree(final_machine_state.pc.start() + 1),
            idents,
            false,
        );
        let final_c2 = read_value_expr(
            ColumnAddress::MemorySubtree(final_machine_state.timestamp.start()),
            idents,
            false,
        );
        let final_c3 = read_value_expr(
            ColumnAddress::MemorySubtree(final_machine_state.timestamp.start() + 1),
            idents,
            false,
        );

        let initial_c0 = read_value_expr(
            ColumnAddress::MemorySubtree(initial_machine_state.pc.start()),
            idents,
            false,
        );
        let initial_c1 = read_value_expr(
            ColumnAddress::MemorySubtree(initial_machine_state.pc.start() + 1),
            idents,
            false,
        );
        let initial_c2 = read_value_expr(
            ColumnAddress::MemorySubtree(initial_machine_state.timestamp.start()),
            idents,
            false,
        );
        let initial_c3 = read_value_expr(
            ColumnAddress::MemorySubtree(initial_machine_state.timestamp.start() + 1),
            idents,
            false,
        );

        let assembly_quote = quote! {
            let mut numerator = #state_permutation_argument_gamma_ident;
            numerator.add_assign(&#final_c0);

            let mut t = #state_permutation_argument_linearization_challenges_ident
                [0];
            t.mul_assign(&#final_c1);
            numerator.add_assign(&t);

            let mut t = #state_permutation_argument_linearization_challenges_ident
                [1];
            t.mul_assign(&#final_c2);
            numerator.add_assign(&t);

            let mut t = #state_permutation_argument_linearization_challenges_ident
                [2];
            t.mul_assign(&#final_c3);
            numerator.add_assign(&t);

            let mut denom = #state_permutation_argument_gamma_ident;
            denom.add_assign(&#initial_c0);

            let mut t = #state_permutation_argument_linearization_challenges_ident
                [0];
            t.mul_assign(&#initial_c1);
            denom.add_assign(&t);

            let mut t = #state_permutation_argument_linearization_challenges_ident
                [1];
            t.mul_assign(&#initial_c2);
            denom.add_assign(&t);

            let mut t = #state_permutation_argument_linearization_challenges_ident
                [2];
            t.mul_assign(&#initial_c3);
            denom.add_assign(&t);
        };

        let t = quote! {
            let #individual_term_ident = {
                #assembly_quote

                // this * demon - previous * numerator
                let mut #individual_term_ident = #accumulator_expr;
                #individual_term_ident.mul_assign(&denom);
                let mut t = #previous_expr;
                t.mul_assign(&numerator);
                #individual_term_ident.sub_assign(&t);

                #individual_term_ident
            };
        };

        previous_acc_value_offset = Some(offset);
        accumulate_contributions(into, None, vec![t], idents);
    }

    // masking
    if stage_2_layout
        .intermediate_polys_for_permutation_masking
        .num_elements()
        > 0
    {
        let previous_offset = previous_acc_value_offset
            .take()
            .expect("some value to accumulate");
        let execute = memory_layout
            .intermediate_state_layout
            .expect("must be present")
            .execute;
        let execute_expr =
            read_value_expr(ColumnAddress::MemorySubtree(execute.start()), idents, false);
        let offset = stage_2_layout
            .get_intermediate_polys_for_permutation_masking_absolute_poly_idx_for_verifier();
        let previous_expr = read_stage_2_value_expr(previous_offset, idents, false);
        let accumulator_expr = read_stage_2_value_expr(offset, idents, false);

        let t = quote! {
            let #individual_term_ident = {
                // this = execute * previous + (1 - execute) * 1
                // this - execute * previous + execute - 1;

                let mut #individual_term_ident = #accumulator_expr;
                let predicate = #execute_expr;
                let mut t = #previous_expr;
                t.mul_assign(&predicate);
                #individual_term_ident.sub_assign(&t);
                #individual_term_ident.add_assign(&predicate);
                #individual_term_ident.sub_assign_base(&Mersenne31Field::ONE);

                #individual_term_ident
            };
        };

        previous_acc_value_offset = Some(offset);
        accumulate_contributions(into, None, vec![t], idents);
    }

    let mut streams = vec![];

    // init-teardown if present
    if memory_layout.shuffle_ram_inits_and_teardowns.len() > 0 {
        for (init_idx, init_and_teardown) in memory_layout
            .shuffle_ram_inits_and_teardowns
            .iter()
            .enumerate()
        {
            let ShuffleRamInitAndTeardownLayout {
                lazy_init_addresses_columns,
                lazy_teardown_values_columns,
                lazy_teardown_timestamps_columns,
            } = init_and_teardown;
            let address_low_expr = read_value_expr(
                ColumnAddress::MemorySubtree(lazy_init_addresses_columns.start()),
                idents,
                false,
            );
            let address_high_expr = read_value_expr(
                ColumnAddress::MemorySubtree(lazy_init_addresses_columns.start() + 1),
                idents,
                false,
            );

            let value_low_expr = read_value_expr(
                ColumnAddress::MemorySubtree(lazy_teardown_values_columns.start()),
                idents,
                false,
            );
            let value_high_expr = read_value_expr(
                ColumnAddress::MemorySubtree(lazy_teardown_values_columns.start() + 1),
                idents,
                false,
            );

            let timestamp_low_expr = read_value_expr(
                ColumnAddress::MemorySubtree(lazy_teardown_timestamps_columns.start()),
                idents,
                false,
            );
            let timestamp_high_expr = read_value_expr(
                ColumnAddress::MemorySubtree(lazy_teardown_timestamps_columns.start() + 1),
                idents,
                false,
            );

            let offset = stage_2_layout
                .get_intermediate_polys_for_memory_init_teardown_absolute_poly_idx_for_verifier(
                    init_idx,
                );
            let accumulator_expr = read_stage_2_value_expr(offset, idents, false);

            let baseline_quote = quote! {
                let address_low = #address_low_expr;
                let mut t = #memory_argument_linearization_challenges_ident
                    [#MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                t.mul_assign(&address_low);
                let mut numerator = t;

                let address_high = #address_high_expr;
                let mut t = #memory_argument_linearization_challenges_ident
                    [#MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                t.mul_assign(&address_high);
                numerator.add_assign(&t);

                numerator.add_assign(&memory_argument_gamma);

                // lazy init and teardown sets have same addresses
                let mut denom = numerator;

                let value_low = #value_low_expr;
                let mut t = #memory_argument_linearization_challenges_ident
                    [#MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                t.mul_assign(&value_low);
                denom.add_assign(&t);

                let value_high = #value_high_expr;
                let mut t = #memory_argument_linearization_challenges_ident
                    [#MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                t.mul_assign_by_base(&value_high);
                denom.add_assign(&t);

                let timestamp_low = #timestamp_low_expr;
                let mut t = #memory_argument_linearization_challenges_ident
                    [#MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                t.mul_assign(&timestamp_low);
                denom.add_assign(&t);

                let timestamp_high = #timestamp_high_expr;
                let mut t = #memory_argument_linearization_challenges_ident
                    [#MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                t.mul_assign(&timestamp_high);
                denom.add_assign(&t);

                let accumulator = #accumulator_expr;
            };

            if let Some(previous_acc_value_offset) = previous_acc_value_offset.take() {
                let previous_acc_expr =
                    read_stage_2_value_expr(previous_acc_value_offset, idents, false);

                let t = quote! {
                    let #individual_term_ident = {
                        #baseline_quote;

                        let previous = #previous_acc_expr;

                        // this * demon - previous * numerator
                        // or just this * denom - numerator
                        let mut #individual_term_ident = accumulator;
                        #individual_term_ident.mul_assign(&denom);
                        let mut t = previous;
                        t.mul_assign(&numerator);
                        #individual_term_ident.sub_assign(&t);

                        #individual_term_ident
                    };
                };

                streams.push(t);
            } else {
                assert_eq!(init_idx, 0);

                let t = quote! {
                    let #individual_term_ident = {
                        #baseline_quote;

                        let mut #individual_term_ident = accumulator;
                        #individual_term_ident.mul_assign(&denom);
                        #individual_term_ident.sub_assign(&numerator);

                        #individual_term_ident
                    };
                };

                streams.push(t);
            }

            assert!(previous_acc_value_offset.is_none());
            previous_acc_value_offset = Some(offset);
        }
    }

    accumulate_contributions(into, None, streams, idents);

    // and now we need to make Z(next) = Z(this) * previous(this)
    {
        let previous_offset = previous_acc_value_offset.expect("some value to accumulate");
        let previous_accumulator_expr = read_stage_2_value_expr(previous_offset, idents, false);
        let idx = stage_2_layout
            .get_intermediate_polys_for_grand_product_accumulation_absolute_poly_idx_for_verifier();
        let accumulator_expr = read_stage_2_value_expr(idx, idents, false);
        let accumulator_next_expr = read_stage_2_value_expr(idx, idents, true);

        let t = quote! {
            let #individual_term_ident = {
                let mut #individual_term_ident = #accumulator_next_expr;
                let mut t = #accumulator_expr;
                t.mul_assign(&#previous_accumulator_expr);
                #individual_term_ident.sub_assign(&t);

                #individual_term_ident
            };
        };

        accumulate_contributions(into, None, vec![t], idents);
    }
}

pub(crate) fn transform_delegation_ram_memory_accumulators(
    memory_layout: &MemorySubtree,
    stage_2_layout: &LookupAndMemoryArgumentLayout,
    idents: &Idents,
    previous_acc_value_offset: &mut Option<usize>,
    into: &mut TokenStream,
) {
    let Idents {
        individual_term_ident,
        memory_argument_linearization_challenges_ident,
        memory_argument_gamma_ident,
        ..
    } = idents;

    // and now we work with memory multiplicative accumulators
    // Numerator is write set, denom is read set

    let mut streams = vec![];

    // and memory grand product accumulation identities

    // sequence of keys is in general is_reg || address_low || address_high || timestamp low || timestamp_high || value_low || value_high

    // Assemble P(x) = write init set / read teardown set, except the first one where previous accumulator is "1"

    let delegation_processor_layout = memory_layout
        .delegation_processor_layout
        .expect("must exist");
    let predicate_expr = read_value_expr(
        ColumnAddress::MemorySubtree(delegation_processor_layout.multiplicity.start()),
        idents,
        false,
    );
    let address_high_expr = read_value_expr(
        ColumnAddress::MemorySubtree(delegation_processor_layout.abi_mem_offset_high.start()),
        idents,
        false,
    );
    let write_timestamp_low_expr = read_value_expr(
        ColumnAddress::MemorySubtree(delegation_processor_layout.write_timestamp.start()),
        idents,
        false,
    );
    let write_timestamp_high_expr = read_value_expr(
        ColumnAddress::MemorySubtree(delegation_processor_layout.write_timestamp.start() + 1),
        idents,
        false,
    );

    let common_stream = quote! {
        let predicate = #predicate_expr;
        let address_high = #address_high_expr;
        let write_timestamp_low = #write_timestamp_low_expr;
        let write_timestamp_high = #write_timestamp_high_expr;

        // all common contributions involve witness values, and need to be added before scalign by tau^H/2
        let mut delegation_address_high_common_contribution = #memory_argument_linearization_challenges_ident
            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
        delegation_address_high_common_contribution.mul_assign(&address_high);

        let mut t = #memory_argument_linearization_challenges_ident
            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        t.mul_assign(&write_timestamp_low);
        let mut write_timestamp_contribution = t;

        let mut t = #memory_argument_linearization_challenges_ident
            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        t.mul_assign(&write_timestamp_high);
        write_timestamp_contribution.add_assign(&t);
    };

    let mut accumulation_idx = 0;

    assert!(memory_layout.batched_ram_accesses.is_empty(), "deprecated");

    {
        // now we can continue to accumulate
        for (access_idx, register_access_columns) in memory_layout
            .register_and_indirect_accesses
            .iter()
            .enumerate()
        {
            let read_value_columns = register_access_columns
                .register_access
                .get_read_value_columns();
            let read_timestamp_columns = register_access_columns
                .register_access
                .get_read_timestamp_columns();
            // memory address low is literal constant
            let register_index = register_access_columns.register_access.get_register_index();
            assert!(register_index > 0);
            assert!(register_index < 32);

            let read_value_low_expr = read_value_expr(
                ColumnAddress::MemorySubtree(read_value_columns.start()),
                idents,
                false,
            );
            let read_value_high_expr = read_value_expr(
                ColumnAddress::MemorySubtree(read_value_columns.start() + 1),
                idents,
                false,
            );

            let read_timestamp_low_expr = read_value_expr(
                ColumnAddress::MemorySubtree(read_timestamp_columns.start()),
                idents,
                false,
            );
            let read_timestamp_high_expr = read_value_expr(
                ColumnAddress::MemorySubtree(read_timestamp_columns.start() + 1),
                idents,
                false,
            );

            let common_part_stream = quote! {
                let mut address_contribution = #memory_argument_linearization_challenges_ident
                    [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                address_contribution.mul_assign_by_base(&Mersenne31Field(#register_index));

                // is register
                address_contribution.add_assign_base(&Mersenne31Field::ONE);

                let read_value_low = #read_value_low_expr;
                let mut read_value_contribution = #memory_argument_linearization_challenges_ident
                    [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                read_value_contribution.mul_assign(&read_value_low);

                let read_value_high = #read_value_high_expr;
                let mut t = #memory_argument_linearization_challenges_ident
                    [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                t.mul_assign(&read_value_high);
                read_value_contribution.add_assign(&t);

                let read_timestamp_low = #read_timestamp_low_expr;
                let mut read_timestamp_contribution =
                    #memory_argument_linearization_challenges_ident
                        [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                read_timestamp_contribution
                    .mul_assign(&read_timestamp_low);

                let read_timestamp_high = #read_timestamp_high_expr;
                let mut t = #memory_argument_linearization_challenges_ident
                    [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                t.mul_assign(&read_timestamp_high);
                read_timestamp_contribution.add_assign(&t);

                // this is "address high"
                let mut numerator = #memory_argument_gamma_ident;
                // and other common additive terms
                numerator.add_assign(&address_contribution);
            };

            let previous_contribution_stream =
                if let Some(previous_offset) = previous_acc_value_offset.take() {
                    let previous_accumulator_expr =
                        read_stage_2_value_expr(previous_offset, idents, false);

                    quote! {
                        let previous = #previous_accumulator_expr;
                    }
                } else {
                    assert_eq!(accumulation_idx, 0);
                    assert_eq!(access_idx, 0);

                    quote! {
                        let previous = Mersenne31Quartic::ONE;
                    }
                };

            let offset = stage_2_layout
                .get_intermediate_polys_for_memory_argument_absolute_poly_idx_for_verifier(
                    accumulation_idx,
                );
            let accumulator_expr = read_stage_2_value_expr(offset, idents, false);
            accumulation_idx += 1;
            assert!(previous_acc_value_offset.is_none());
            *previous_acc_value_offset = Some(offset);

            match register_access_columns.register_access {
                RegisterAccessColumns::ReadAccess { .. } => {
                    let t = quote! {
                        let #individual_term_ident = {
                            #common_part_stream

                            #previous_contribution_stream

                            // both read and write set share value
                            numerator.add_assign(&read_value_contribution);

                            let mut denom = numerator;

                            numerator.add_assign(&write_timestamp_contribution);
                            denom.add_assign(&read_timestamp_contribution);

                            // this * demon - previous * numerator
                            // or just this * denom - numerator
                            let mut #individual_term_ident = #accumulator_expr;
                            #individual_term_ident.mul_assign(&denom);
                            let mut t = previous;
                            t.mul_assign(&numerator);
                            #individual_term_ident.sub_assign(&t);

                            #individual_term_ident
                        };
                    };

                    streams.push(t);
                }
                RegisterAccessColumns::WriteAccess { write_value, .. } => {
                    let write_value_low_expr = read_value_expr(
                        ColumnAddress::MemorySubtree(write_value.start()),
                        idents,
                        false,
                    );
                    let write_value_high_expr = read_value_expr(
                        ColumnAddress::MemorySubtree(write_value.start() + 1),
                        idents,
                        false,
                    );

                    let t = quote! {
                        let #individual_term_ident = {
                            #common_part_stream

                            #previous_contribution_stream

                            let write_value_low = #write_value_low_expr;
                            let mut write_value_contribution = #memory_argument_linearization_challenges_ident
                                [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                            write_value_contribution.mul_assign(&write_value_low);

                            let write_value_high = #write_value_high_expr;
                            let mut t = #memory_argument_linearization_challenges_ident
                                [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                            t.mul_assign(&write_value_high);
                            write_value_contribution.add_assign(&t);

                            let mut denom = numerator;

                            // read and write sets differ in value and timestamp

                            numerator.add_assign(&write_value_contribution);
                            denom.add_assign(&read_value_contribution);

                            numerator.add_assign(&write_timestamp_contribution);
                            denom.add_assign(&read_timestamp_contribution);

                            // this * demon - previous * numerator
                            // or just this * denom - numerator
                            let mut #individual_term_ident = #accumulator_expr;
                            #individual_term_ident.mul_assign(&denom);
                            let mut t = previous;
                            t.mul_assign(&numerator);
                            #individual_term_ident.sub_assign(&t);

                            #individual_term_ident
                        };
                    };

                    streams.push(t);
                }
            }

            if register_access_columns.indirect_accesses.len() > 0 {
                let register_read_value_columns = register_access_columns
                    .register_access
                    .get_read_value_columns();

                // NOTE: we can not have a common part here, and will have to copy into separate substreams
                for (indirect_access_idx, indirect_access) in
                    register_access_columns.indirect_accesses.iter().enumerate()
                {
                    let read_value_columns = indirect_access.get_read_value_columns();
                    let read_timestamp_columns = indirect_access.get_read_timestamp_columns();
                    let carry_bit_column =
                        indirect_access.get_address_derivation_carry_bit_column();
                    let constant_offset = indirect_access.offset_constant();
                    assert!(constant_offset < 1 << 16);
                    assert_eq!(
                        constant_offset % 4,
                        0,
                        "constant offset must be a multiple of u32 word size, but it is {}",
                        constant_offset
                    );

                    let register_read_value_low_expr = read_value_expr(
                        ColumnAddress::MemorySubtree(register_read_value_columns.start()),
                        idents,
                        false,
                    );
                    let register_read_value_high_expr = read_value_expr(
                        ColumnAddress::MemorySubtree(register_read_value_columns.start() + 1),
                        idents,
                        false,
                    );

                    let read_value_low_expr = read_value_expr(
                        ColumnAddress::MemorySubtree(read_value_columns.start()),
                        idents,
                        false,
                    );
                    let read_value_high_expr = read_value_expr(
                        ColumnAddress::MemorySubtree(read_value_columns.start() + 1),
                        idents,
                        false,
                    );

                    let read_timestamp_low_expr = read_value_expr(
                        ColumnAddress::MemorySubtree(read_timestamp_columns.start()),
                        idents,
                        false,
                    );
                    let read_timestamp_high_expr = read_value_expr(
                        ColumnAddress::MemorySubtree(read_timestamp_columns.start() + 1),
                        idents,
                        false,
                    );

                    let common_part_stream = if carry_bit_column.num_elements() == 0 {
                        let add_variable_offset_quote =
                            if let Some((coeff, var, _)) = indirect_access.variable_dependent() {
                                assert!(var.num_elements() == 1);
                                assert!(coeff < 1 << 16);
                                let variable_offset_expr = read_value_expr(
                                    ColumnAddress::MemorySubtree(var.start()),
                                    idents,
                                    false,
                                );
                                quote! {
                                    // add variable-dependent contribution
                                    let mut variable_offset = #variable_offset_expr;
                                    variable_offset.mul_assign_by_base(&Mersenne31Field(#coeff));
                                    address_low.add_assign(&variable_offset);
                                }
                            } else {
                                quote! {
                                    // no variable offset
                                }
                            };
                        quote! {
                            let mut address_low = #register_read_value_low_expr;
                            address_low.add_assign_base(&Mersenne31Field(#constant_offset));

                            #add_variable_offset_quote

                            let mut address_contribution = #memory_argument_linearization_challenges_ident
                                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                            address_contribution.mul_assign(&address_low);

                            let address_high = #register_read_value_high_expr;
                            let mut address_high_contribution = #memory_argument_linearization_challenges_ident
                                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                            address_high_contribution.mul_assign(&address_high);
                            address_contribution.add_assign(&address_high_contribution);

                            let read_value_low = #read_value_low_expr;
                            let mut read_value_contribution = #memory_argument_linearization_challenges_ident
                                [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                            read_value_contribution.mul_assign(&read_value_low);

                            let read_value_high = #read_value_high_expr;
                            let mut t = #memory_argument_linearization_challenges_ident
                                [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                            t.mul_assign(&read_value_high);
                            read_value_contribution.add_assign(&t);

                            let read_timestamp_low = #read_timestamp_low_expr;
                            let mut read_timestamp_contribution =
                                #memory_argument_linearization_challenges_ident
                                    [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                            read_timestamp_contribution
                                .mul_assign(&read_timestamp_low);

                            let read_timestamp_high = #read_timestamp_high_expr;
                            let mut t = #memory_argument_linearization_challenges_ident
                                [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                            t.mul_assign(&read_timestamp_high);
                            read_timestamp_contribution.add_assign(&t);

                            let mut numerator = #memory_argument_gamma_ident;
                            // and other common additive terms
                            numerator.add_assign(&address_contribution);
                        }
                    } else {
                        let carry_bit_expr = read_value_expr(
                            ColumnAddress::MemorySubtree(carry_bit_column.start()),
                            idents,
                            false,
                        );

                        quote! {
                            let mut address_low = #register_read_value_low_expr;
                            address_low.add_assign_base(&Mersenne31Field(#constant_offset));
                            let carry = #carry_bit_expr;
                            let mut carry_bit_shifted = carry;
                            carry_bit_shifted.mul_assign_by_base(&Mersenne31Field(1u32 << 16));
                            address_low.sub_assign(&carry_bit_shifted);

                            let mut address_contribution = #memory_argument_linearization_challenges_ident
                                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                            address_contribution.mul_assign(&address_low);

                            let mut address_high = #register_read_value_high_expr;
                            address_high.add_assign(&carry);
                            let mut address_high_contribution = #memory_argument_linearization_challenges_ident
                                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                            address_high_contribution.mul_assign(&address_high);
                            address_contribution.add_assign(&address_high_contribution);

                            let read_value_low = #read_value_low_expr;
                            let mut read_value_contribution = #memory_argument_linearization_challenges_ident
                                [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                            read_value_contribution.mul_assign(&read_value_low);

                            let read_value_high = #read_value_high_expr;
                            let mut t = #memory_argument_linearization_challenges_ident
                                [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                            t.mul_assign(&read_value_high);
                            read_value_contribution.add_assign(&t);

                            let read_timestamp_low = #read_timestamp_low_expr;
                            let mut read_timestamp_contribution =
                                #memory_argument_linearization_challenges_ident
                                    [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                            read_timestamp_contribution
                                .mul_assign(&read_timestamp_low);

                            let read_timestamp_high = #read_timestamp_high_expr;
                            let mut t = #memory_argument_linearization_challenges_ident
                                [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                            t.mul_assign(&read_timestamp_high);
                            read_timestamp_contribution.add_assign(&t);

                            let mut numerator = #memory_argument_gamma_ident;
                            // and other common additive terms
                            numerator.add_assign(&address_contribution);
                        }
                    };

                    let previous_contribution_stream =
                        if let Some(previous_offset) = previous_acc_value_offset.take() {
                            let previous_accumulator_expr =
                                read_stage_2_value_expr(previous_offset, idents, false);

                            quote! {
                                let previous = #previous_accumulator_expr;
                            }
                        } else {
                            assert_eq!(accumulation_idx, 0);
                            assert_eq!(access_idx, 0);

                            quote! {
                                let previous = Mersenne31Quartic::ONE;
                            }
                        };

                    let offset = stage_2_layout
                        .get_intermediate_polys_for_memory_argument_absolute_poly_idx_for_verifier(
                            accumulation_idx,
                        );
                    let accumulator_expr = read_stage_2_value_expr(offset, idents, false);
                    accumulation_idx += 1;
                    assert!(previous_acc_value_offset.is_none());
                    *previous_acc_value_offset = Some(offset);

                    match indirect_access {
                        IndirectAccessColumns::ReadAccess { .. } => {
                            let t = quote! {
                                let #individual_term_ident = {
                                    #common_part_stream

                                    #previous_contribution_stream

                                    // both read and write set share value
                                    numerator.add_assign(&read_value_contribution);

                                    let mut denom = numerator;

                                    numerator.add_assign(&write_timestamp_contribution);
                                    denom.add_assign(&read_timestamp_contribution);

                                    // this * demon - previous * numerator
                                    // or just this * denom - numerator
                                    let mut #individual_term_ident = #accumulator_expr;
                                    #individual_term_ident.mul_assign(&denom);
                                    let mut t = previous;
                                    t.mul_assign(&numerator);
                                    #individual_term_ident.sub_assign(&t);

                                    #individual_term_ident
                                };
                            };

                            streams.push(t);
                        }
                        IndirectAccessColumns::WriteAccess { write_value, .. } => {
                            let write_value_low_expr = read_value_expr(
                                ColumnAddress::MemorySubtree(write_value.start()),
                                idents,
                                false,
                            );
                            let write_value_high_expr = read_value_expr(
                                ColumnAddress::MemorySubtree(write_value.start() + 1),
                                idents,
                                false,
                            );

                            let t = quote! {
                                let #individual_term_ident = {
                                    #common_part_stream

                                    #previous_contribution_stream

                                    let write_value_low = #write_value_low_expr;
                                    let mut write_value_contribution = #memory_argument_linearization_challenges_ident
                                        [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                                    write_value_contribution.mul_assign(&write_value_low);

                                    let write_value_high = #write_value_high_expr;
                                    let mut t = #memory_argument_linearization_challenges_ident
                                        [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                                    t.mul_assign(&write_value_high);
                                    write_value_contribution.add_assign(&t);

                                    let mut denom = numerator;

                                    // read and write sets differ in value and timestamp

                                    numerator.add_assign(&write_value_contribution);
                                    denom.add_assign(&read_value_contribution);

                                    numerator.add_assign(&write_timestamp_contribution);
                                    denom.add_assign(&read_timestamp_contribution);

                                    // this * demon - previous * numerator
                                    // or just this * denom - numerator
                                    let mut #individual_term_ident = #accumulator_expr;
                                    #individual_term_ident.mul_assign(&denom);
                                    let mut t = previous;
                                    t.mul_assign(&numerator);
                                    #individual_term_ident.sub_assign(&t);

                                    #individual_term_ident
                                };
                            };

                            streams.push(t);
                        }
                    }
                }
            };
        }
    }

    accumulate_contributions(into, Some(common_stream), streams, idents);
}
