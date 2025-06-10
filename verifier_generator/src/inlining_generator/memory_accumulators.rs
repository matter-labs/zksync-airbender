use super::*;

pub(crate) fn transform_shuffle_ram_memory_accumulators(
    memory_layout: &MemorySubtree,
    stage_2_layout: &LookupAndMemoryArgumentLayout,
    setup_layout: &SetupLayout,
    idents: &Idents,
) -> Vec<TokenStream> {
    let Idents {
        individual_term_ident,
        memory_argument_linearization_challenges_ident,
        memory_argument_gamma_ident,
        memory_timestamp_high_from_sequence_idx_ident,
        ..
    } = idents;

    // and now we work with memory multiplicative accumulators
    // Numerator is write set, denom is read set

    let mut streams = vec![];

    // first lazy init from read set / lazy teardown

    let shuffle_ram_inits_and_teardowns = memory_layout
        .shuffle_ram_inits_and_teardowns
        .expect("must exist if we process shuffle RAM");
    assert!(memory_layout.shuffle_ram_access_sets.len() > 0);

    let lazy_init_address_start = shuffle_ram_inits_and_teardowns
        .lazy_init_addresses_columns
        .start();
    let lazy_teardown_value_start = shuffle_ram_inits_and_teardowns
        .lazy_teardown_values_columns
        .start();
    let lazy_teardown_timestamp_start = shuffle_ram_inits_and_teardowns
        .lazy_teardown_timestamps_columns
        .start();

    // and memory grand product accumulation identities

    // sequence of keys is in general is_reg || address_low || address_high || timestamp low || timestamp_high || value_low || value_high

    // Assemble P(x) = write init set / read teardown set

    let mut i = 0;

    {
        let address_low_expr = read_value_expr(
            ColumnAddress::MemorySubtree(lazy_init_address_start),
            idents,
            false,
        );
        let address_high_expr = read_value_expr(
            ColumnAddress::MemorySubtree(lazy_init_address_start + 1),
            idents,
            false,
        );

        let value_low_expr = read_value_expr(
            ColumnAddress::MemorySubtree(lazy_teardown_value_start),
            idents,
            false,
        );
        let value_high_expr = read_value_expr(
            ColumnAddress::MemorySubtree(lazy_teardown_value_start + 1),
            idents,
            false,
        );

        let timestamp_low_expr = read_value_expr(
            ColumnAddress::MemorySubtree(lazy_teardown_timestamp_start),
            idents,
            false,
        );
        let timestamp_high_expr = read_value_expr(
            ColumnAddress::MemorySubtree(lazy_teardown_timestamp_start + 1),
            idents,
            false,
        );

        let offset = stage_2_layout
            .get_intermediate_polys_for_memory_argument_absolute_poly_idx_for_verifier(i);
        let accumulator_expr = read_stage_2_value_expr(offset, idents, false);

        let t = quote! {
            let #individual_term_ident = {
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

                let mut #individual_term_ident = accumulator;
                #individual_term_ident.mul_assign(&denom);
                #individual_term_ident.sub_assign(&numerator);

                #individual_term_ident
            };
        };

        streams.push(t);
    }

    {
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

            let previous_offset = stage_2_layout
                .get_intermediate_polys_for_memory_argument_absolute_poly_idx_for_verifier(i);
            let previous_accumulator_expr = read_stage_2_value_expr(previous_offset, idents, false);
            i += 1;
            let offset = stage_2_layout
                .get_intermediate_polys_for_memory_argument_absolute_poly_idx_for_verifier(i);
            let accumulator_expr = read_stage_2_value_expr(offset, idents, false);

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

            match memory_access_columns {
                ShuffleRamQueryColumns::Readonly(_) => {
                    let t = quote! {
                        let #individual_term_ident = {
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
                            write_timestamp_high.add_assign_base(&#memory_timestamp_high_from_sequence_idx_ident);
                            let mut t = #memory_argument_linearization_challenges_ident
                                [#MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                            t.mul_assign(&write_timestamp_high);
                            write_timestamp_contribution.add_assign(&t);

                            numerator.add_assign(&write_timestamp_contribution);
                            denom.add_assign(&read_timestamp_contribution);

                            // this * demon - previous * numerator
                            let accumulator = #accumulator_expr;
                            let previous = #previous_accumulator_expr;

                            let mut #individual_term_ident = accumulator;
                            #individual_term_ident.mul_assign(&denom);
                            let mut t = previous;
                            t.mul_assign(&numerator);
                            #individual_term_ident.sub_assign(&t);

                            #individual_term_ident
                        };
                    };

                    streams.push(t);
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

                    let t = quote! {
                        let #individual_term_ident = {
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
                            write_timestamp_high.add_assign_base(&#memory_timestamp_high_from_sequence_idx_ident);
                            let mut t = #memory_argument_linearization_challenges_ident
                                [#MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                            t.mul_assign(&write_timestamp_high);
                            write_timestamp_contribution.add_assign(&t);

                            numerator.add_assign(&write_timestamp_contribution);
                            denom.add_assign(&read_timestamp_contribution);

                            // this * demon - previous * numerator
                            let accumulator = #accumulator_expr;
                            let previous = #previous_accumulator_expr;

                            let mut #individual_term_ident = accumulator;
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
    }

    // and now we need to make Z(next) = Z(this) * previous(this)
    {
        let previous_offset = stage_2_layout
            .get_intermediate_polys_for_memory_argument_absolute_poly_idx_for_verifier(i);
        let previous_accumulator_expr = read_stage_2_value_expr(previous_offset, idents, false);
        i += 1;
        let offset = stage_2_layout
            .get_intermediate_polys_for_memory_argument_absolute_poly_idx_for_verifier(i);
        let accumulator_expr = read_stage_2_value_expr(offset, idents, false);
        let accumulator_next_expr = read_stage_2_value_expr(offset, idents, true);

        let t = quote! {
            let #individual_term_ident = {
                let mut #individual_term_ident = #accumulator_next_expr;
                let mut t = #accumulator_expr;
                t.mul_assign(&#previous_accumulator_expr);
                #individual_term_ident.sub_assign(&t);

                #individual_term_ident
            };
        };

        streams.push(t);
    }

    assert_eq!(i, memory_layout.shuffle_ram_access_sets.len() + 1);

    streams
}

pub(crate) fn transform_delegation_ram_memory_accumulators(
    memory_layout: &MemorySubtree,
    stage_2_layout: &LookupAndMemoryArgumentLayout,
    idents: &Idents,
) -> (TokenStream, Vec<TokenStream>) {
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

    let mut i = 0;

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

    {
        // now we can continue to accumulate
        for (access_idx, memory_access_columns) in
            memory_layout.batched_ram_accesses.iter().enumerate()
        {
            let read_value_columns = memory_access_columns.get_read_value_columns();
            let read_timestamp_columns = memory_access_columns.get_read_timestamp_columns();
            // memory address low is literal constant
            let mem_offset_low = (access_idx * std::mem::size_of::<u32>()) as u32;

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
                let mut address_low_contribution = #memory_argument_linearization_challenges_ident
                    [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                address_low_contribution.mul_assign_by_base(&Mersenne31Field(#mem_offset_low));

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
                let mut numerator = delegation_address_high_common_contribution;
                // and other common additive terms
                numerator.add_assign(&#memory_argument_gamma_ident);
                numerator.add_assign(&address_low_contribution);
            };

            let previous_contribution_stream = if access_idx == 0 {
                assert_eq!(i, 0);

                quote! {
                    let previous = Mersenne31Quartic::ONE;
                }
            } else {
                let previous_offset = stage_2_layout
                    .get_intermediate_polys_for_memory_argument_absolute_poly_idx_for_verifier(i);
                let previous_accumulator_expr =
                    read_stage_2_value_expr(previous_offset, idents, false);
                i += 1;

                quote! {
                    let previous = #previous_accumulator_expr;
                }
            };

            let offset = stage_2_layout
                .get_intermediate_polys_for_memory_argument_absolute_poly_idx_for_verifier(i);
            let accumulator_expr = read_stage_2_value_expr(offset, idents, false);

            match memory_access_columns {
                BatchedRamAccessColumns::ReadAccess { .. } => {
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
                BatchedRamAccessColumns::WriteAccess { write_value, .. } => {
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
    }

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

            let previous_contribution_stream = if access_idx == 0
                && memory_layout.batched_ram_accesses.is_empty()
            {
                assert_eq!(i, 0);

                quote! {
                    let previous = Mersenne31Quartic::ONE;
                }
            } else {
                let previous_offset = stage_2_layout
                    .get_intermediate_polys_for_memory_argument_absolute_poly_idx_for_verifier(i);
                let previous_accumulator_expr =
                    read_stage_2_value_expr(previous_offset, idents, false);
                i += 1;

                quote! {
                    let previous = #previous_accumulator_expr;
                }
            };

            let offset = stage_2_layout
                .get_intermediate_polys_for_memory_argument_absolute_poly_idx_for_verifier(i);
            let accumulator_expr = read_stage_2_value_expr(offset, idents, false);

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
                    let offset = indirect_access.get_offset();
                    assert!(offset < 1 << 16);
                    assert_eq!(offset % 4, 0);
                    assert_eq!(offset as usize, indirect_access_idx * 4);

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

                    let common_part_stream = if indirect_access_idx == 0
                        || carry_bit_column.num_elements() == 0
                    {
                        quote! {
                            let mut address_low = #register_read_value_low_expr;
                            address_low.add_assign_base(&Mersenne31Field(#offset));

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
                        assert!(carry_bit_column.num_elements() > 0);
                        let carry_bit_expr = read_value_expr(
                            ColumnAddress::MemorySubtree(carry_bit_column.start()),
                            idents,
                            false,
                        );

                        quote! {
                            let mut address_low = #register_read_value_low_expr;
                            address_low.add_assign_base(&Mersenne31Field(#offset));
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

                    let previous_contribution_stream = {
                        let previous_offset = stage_2_layout
                            .get_intermediate_polys_for_memory_argument_absolute_poly_idx_for_verifier(i);
                        let previous_accumulator_expr =
                            read_stage_2_value_expr(previous_offset, idents, false);
                        i += 1;

                        quote! {
                            let previous = #previous_accumulator_expr;
                        }
                    };

                    let offset = stage_2_layout
                        .get_intermediate_polys_for_memory_argument_absolute_poly_idx_for_verifier(
                            i,
                        );
                    let accumulator_expr = read_stage_2_value_expr(offset, idents, false);

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

    // and now we need to make Z(next) = Z(this) * previous(this)
    {
        let previous_offset = stage_2_layout
            .get_intermediate_polys_for_memory_argument_absolute_poly_idx_for_verifier(i);
        let previous_accumulator_expr = read_stage_2_value_expr(previous_offset, idents, false);
        i += 1;
        let offset = stage_2_layout
            .get_intermediate_polys_for_memory_argument_absolute_poly_idx_for_verifier(i);
        let accumulator_expr = read_stage_2_value_expr(offset, idents, false);
        let accumulator_next_expr = read_stage_2_value_expr(offset, idents, true);

        let t = quote! {
            let #individual_term_ident = {
                let mut #individual_term_ident = #accumulator_next_expr;
                let mut t = #accumulator_expr;
                t.mul_assign(&#previous_accumulator_expr);
                #individual_term_ident.sub_assign(&t);

                #individual_term_ident
            };
        };

        streams.push(t);
    }

    let mut expected_num_accesses = memory_layout.batched_ram_accesses.len();
    expected_num_accesses += memory_layout.register_and_indirect_accesses.len();
    expected_num_accesses += memory_layout
        .register_and_indirect_accesses
        .iter()
        .map(|el| el.indirect_accesses.len())
        .sum::<usize>();
    assert_eq!(i, expected_num_accesses);

    (common_stream, streams)
}
