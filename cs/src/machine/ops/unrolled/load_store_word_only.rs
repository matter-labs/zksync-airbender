use super::*;

pub fn word_only_load_store_tables() -> Vec<TableType> {
    vec![
        TableType::ZeroEntry, // as we use lookups via optimization context
                              // these get dynamically allocated by instance of the circuit depending on the machine configuration
                              //      TableType::RomAddressSpaceSeparator,
                              //      TableType::RomRead,
    ]
}

pub fn word_only_load_store_table_addition_fn<F: PrimeField, CS: Circuit<F>>(cs: &mut CS) {
    for el in word_only_load_store_tables() {
        cs.materialize_table(el);
    }
}

pub fn word_only_load_store_table_driver_fn<F: PrimeField>(table_driver: &mut TableDriver<F>) {
    for el in word_only_load_store_tables() {
        table_driver.materialize_table(el);
    }
}

pub fn create_word_only_load_store_special_tables<
    F: PrimeField,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    bytecode: &[u32],
) -> [(TableType, LookupWrapper<F>); 2] {
    use crate::machine::machine_configurations::create_table_for_rom_image;
    use crate::tables::create_rom_separator_table;

    let id = TableType::RomAddressSpaceSeparator.to_table_id();
    let rom_separator_table = LookupWrapper::Dimensional3(create_rom_separator_table::<
        F,
        ROM_ADDRESS_SPACE_SECOND_WORD_BITS,
    >(id));

    let id = TableType::RomRead.to_table_id();
    let bytecode_words_table = LookupWrapper::Dimensional3(create_table_for_rom_image::<
        F,
        ROM_ADDRESS_SPACE_SECOND_WORD_BITS,
    >(bytecode, id));

    [
        (TableType::RomAddressSpaceSeparator, rom_separator_table),
        (TableType::RomRead, bytecode_words_table),
    ]
}

fn apply_word_only_load_store<
    F: PrimeField,
    CS: Circuit<F>,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    cs: &mut CS,
    inputs: OpcodeFamilyCircuitState<F>,
) {
    let decoder = <WordOnlyMemoryFamilyDecoder as OpcodeFamilyDecoder>::BitmaskCircuitParser::parse(
        cs,
        inputs.decoder_data.circuit_family_extra_mask,
    );

    let is_store = decoder.perform_write();
    let is_load = is_store.toggle();

    // GET OPERANDS
    let immediate = Register(inputs.decoder_data.imm.map(Num::Var));
    let is_rd_x0 = Boolean::Is(inputs.decoder_data.rd_is_zero);
    let (rs1_reg, rs1_mem_query) = get_rs1_as_shuffle_ram(
        cs,
        Num::Var(inputs.decoder_data.rs1_index),
        OPCODES_ARE_IN_ROM,
    );
    cs.add_shuffle_ram_query(rs1_mem_query);

    // We need to derive address in any case
    let unclean_addr = get_reg_add_and_overflow(cs, rs1_reg, immediate).0;

    // For ROM we need 2 outputs:
    // - check high word of the offset, and trap if we try to write
    // - produce a mask whether it's indeed ROM or RAM access

    let [is_ram_range, address_high_bits_for_rom] = {
        let clean_addr_high = unclean_addr.0[1].get_variable();
        let lookup_inputs = [LookupInput::Variable(clean_addr_high)];
        cs.get_variables_from_lookup_constrained(
            &lookup_inputs,
            TableType::RomAddressSpaceSeparator,
        )
    };

    // We tran if it's a store into ROM
    cs.add_constraint(Term::from(is_store) * (Term::from(1) - Term::from(is_ram_range)));

    // Now we will produce two aux bits - one to understand whether it's a load from ROM, and another - from RAM

    let load_from_rom = Boolean::and(&is_load, &Boolean::Not(is_ram_range), cs);
    let load_from_ram = Boolean::and(&is_load, &Boolean::Is(is_ram_range), cs);
    // Branches below are orthogonal, but before proceeding we will manually create queries for RS2/LOAD_RAM_ACCESS and RD/STORE_RAM_ACCESS

    // NOTE: we have a RomRead table that only contains addresses 0 mod 4,
    // so by trying to read from it - we trap the case of unaligned addresses

    let [rom_load_low, rom_load_high] = {
        // it's enough to perform a single lookup from the combination of RAM offset (unaligned - it gives us all the information) + funct3,
        // but such table is potentially too large (21 + 3 bits or more),
        // so we would need to select again, and use another table

        // This combination is always aligned, so we can shift another 2 bits to the right
        let input = Term::from(1 << 16) * Term::from(address_high_bits_for_rom)
            + Term::from(unclean_addr.0[0]); // potentially unaligned

        // These values will be used if we do full LW
        let [rom_load_low, rom_load_high] = cs
            .get_variables_from_lookup_constrained(&[LookupInput::from(input)], TableType::RomRead);

        [rom_load_low, rom_load_high]
    };

    // Below this point we know that address is aligned

    // NOTE: construction of this circuit REQUIRES non-trivial padding of memory query values if we do NOT
    // execute (so we pad circuits for capacity). Such queries do NOT contribute to memory accumulators due to
    // predication on `execute`, but we still do not want to spend too many variables to make extra masking here

    let rs2_or_load_ram_access_query = {
        let rs2_or_load_ram_access_query_is_register = is_store;
        // we model ROM loads as loads from 0
        let rs2_or_load_ram_access_query_address_low = cs.add_variable_from_constraint(
            Term::from(unclean_addr.0[0]) * Term::from(load_from_ram) + // load from RAM
            Term::from(inputs.decoder_data.rs2_index) * Term::from(is_store), // RS2 index in case of STORE
        );
        let rs2_or_load_ram_access_query_address_high = cs.add_variable_from_constraint(
            Term::from(unclean_addr.0[1]) * Term::from(load_from_ram), // load from RAM, and 0 in case of STORE
        );

        // We will make read/write values and for purposes of witness evaluation just mark them as "known".
        // We also do not need to range check them as for reads it's ensured by permutation,
        // and for writes - we will add constraints
        let rs2_or_load_ram_access_query_read_value = std::array::from_fn(|_| cs.add_variable());

        let rs2_or_load_ram_access_query = ShuffleRamMemQuery {
            query_type: ShuffleRamQueryType::RegisterOrRam {
                is_register: rs2_or_load_ram_access_query_is_register,
                address: [
                    rs2_or_load_ram_access_query_address_low,
                    rs2_or_load_ram_access_query_address_high,
                ],
            },
            local_timestamp_in_cycle: RS2_LOAD_LOCAL_TIMESTAMP,
            read_value: rs2_or_load_ram_access_query_read_value,
            write_value: rs2_or_load_ram_access_query_read_value,
        };

        // mark as known inputs
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            use crate::cs::witness_placer::*;
            placer.assume_assigned(rs2_or_load_ram_access_query_read_value[0]);
            placer.assume_assigned(rs2_or_load_ram_access_query_read_value[1]);

            if crate::cs::cs_reference::RESOLVE_WITNESS {
                let value = placer.get_oracle_u32(Placeholder::SecondRegMem);
                placer.assign_u32_from_u16_parts(rs2_or_load_ram_access_query_read_value, &value);
            }
        };
        cs.set_values(value_fn);

        cs.add_shuffle_ram_query(rs2_or_load_ram_access_query);

        rs2_or_load_ram_access_query
    };

    // same for RD
    let rd_or_store_ram_access_query = {
        let rd_or_store_ram_access_query_is_register = cs
            .add_variable_from_constraint_allow_explicit_linear(
                Term::from(1) - Term::from(is_store),
            );
        let rd_or_store_ram_access_query_address_low = cs.add_variable_from_constraint(
            Term::from(unclean_addr.0[0]) * Term::from(is_store) + // store into RAM
            Term::from(inputs.decoder_data.rd_index) * (Term::from(1) - Term::from(is_store)), // RD index in case of any LOAD
        );
        let rd_or_store_ram_access_query_address_high = cs.add_variable_from_constraint(
            Term::from(unclean_addr.0[1]) * Term::from(is_store), // store into RAM, and 0 in case of LOAD
        );

        // We will make read/write values and for purposes of witness evaluation just mark them as "known".
        // We also do not need to range check them as for reads it's ensured by permutation,
        // and for writes - we will add constraints
        let rd_or_store_ram_access_query_read_value = std::array::from_fn(|_| cs.add_variable());
        let rd_or_store_ram_access_query_write_value = std::array::from_fn(|_| cs.add_variable());

        let rd_or_store_ram_access_query = ShuffleRamMemQuery {
            query_type: ShuffleRamQueryType::RegisterOrRam {
                is_register: Boolean::Is(rd_or_store_ram_access_query_is_register),
                address: [
                    rd_or_store_ram_access_query_address_low,
                    rd_or_store_ram_access_query_address_high,
                ],
            },
            local_timestamp_in_cycle: RD_STORE_LOCAL_TIMESTAMP,
            read_value: rd_or_store_ram_access_query_read_value,
            write_value: rd_or_store_ram_access_query_write_value,
        };

        // mark as known inputs
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            use crate::cs::witness_placer::*;
            placer.assume_assigned(rd_or_store_ram_access_query_read_value[0]);
            placer.assume_assigned(rd_or_store_ram_access_query_read_value[1]);

            placer.assume_assigned(rd_or_store_ram_access_query_write_value[0]);
            placer.assume_assigned(rd_or_store_ram_access_query_write_value[1]);

            if crate::cs::cs_reference::RESOLVE_WITNESS {
                let value = placer.get_oracle_u32(Placeholder::WriteRegMemReadWitness);
                placer.assign_u32_from_u16_parts(rd_or_store_ram_access_query_read_value, &value);

                let value = placer.get_oracle_u32(Placeholder::WriteRegMemWriteValue);
                placer.assign_u32_from_u16_parts(rd_or_store_ram_access_query_write_value, &value);
            }
        };
        cs.set_values(value_fn);

        cs.add_shuffle_ram_query(rd_or_store_ram_access_query);

        rd_or_store_ram_access_query
    };

    // now we just need to constraint memory query values

    // if we LOAD, then RD write query WRITE value must be equal to the corresponding RAM or ROM read value if we do read,
    // and we also need to mask into writing into X0
    let rd_candidate_low = cs.add_variable_from_constraint(
        Term::from(load_from_ram) * Term::from(rs2_or_load_ram_access_query.read_value[0])
            + Term::from(load_from_rom) * Term::from(rom_load_low),
    );
    let rd_candidate_high = cs.add_variable_from_constraint(
        Term::from(load_from_ram) * Term::from(rs2_or_load_ram_access_query.read_value[1])
            + Term::from(load_from_rom) * Term::from(rom_load_high),
    );
    let rd_masked_low = cs.add_variable_from_constraint(
        Term::from(rd_candidate_low) * (Term::from(1) - Term::from(is_rd_x0)),
    );
    let rd_masked_high = cs.add_variable_from_constraint(
        Term::from(rd_candidate_high) * (Term::from(1) - Term::from(is_rd_x0)),
    );
    // so if we load, then it must be equal to RD query's write value
    cs.add_constraint(
        (Term::from(rd_masked_low) - Term::from(rd_or_store_ram_access_query.write_value[0]))
            * (Term::from(1) - Term::from(is_store)),
    );
    cs.add_constraint(
        (Term::from(rd_masked_high) - Term::from(rd_or_store_ram_access_query.write_value[1]))
            * (Term::from(1) - Term::from(is_store)),
    );

    // and if we store, than stored values must be equal to RD query write values
    cs.add_constraint(
        (Term::from(Term::from(rs2_or_load_ram_access_query.read_value[0]))
            - Term::from(rd_or_store_ram_access_query.write_value[0]))
            * Term::from(is_store),
    );
    cs.add_constraint(
        (Term::from(Term::from(rs2_or_load_ram_access_query.read_value[1]))
            - Term::from(rd_or_store_ram_access_query.write_value[1]))
            * Term::from(is_store),
    );

    // write to PC
    let pc = Register(inputs.cycle_start_state.pc.map(|x| Num::Var(x)));
    let pc_next = Register(inputs.cycle_end_state.pc.map(Num::Var));
    bump_pc_no_range_checks_explicit(cs, pc, pc_next);
}

pub fn word_only_load_store_circuit_with_preprocessed_bytecode<
    F: PrimeField,
    CS: Circuit<F>,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    cs: &mut CS,
) {
    let input = cs.allocate_execution_circuit_state::<true>();
    apply_word_only_load_store::<F, CS, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(cs, input);
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::utils::serialize_to_file;

    const SECOND_WORD_BITS: usize = 4;
    const DUMMY_BYTECODE: &[u32] = &[UNIMP_OPCODE];

    #[test]
    fn compile_word_only_load_store_circuit() {
        use ::field::Mersenne31Field;

        let compiled = compile_unrolled_circuit_state_transition::<Mersenne31Field>(
            &|cs| {
                word_only_load_store_table_addition_fn(cs);

                let extra_tables = create_word_only_load_store_special_tables::<_, SECOND_WORD_BITS>(
                    DUMMY_BYTECODE,
                );
                for (table_type, table) in extra_tables {
                    cs.add_table_with_content(table_type, table);
                }
            },
            &|cs| {
                word_only_load_store_circuit_with_preprocessed_bytecode::<_, _, SECOND_WORD_BITS>(
                    cs,
                )
            },
            1 << (16 + SECOND_WORD_BITS),
            24,
        );

        serialize_to_file(&compiled, "word_only_load_store_preprocessed_layout.json");
    }

    #[test]
    fn compile_word_only_load_store_witness_graph() {
        use ::field::Mersenne31Field;

        let ssa_forms = dump_ssa_witness_eval_form_for_unrolled_circuit::<Mersenne31Field>(
            &|cs| {
                word_only_load_store_table_addition_fn(cs);

                let extra_tables = create_word_only_load_store_special_tables::<_, SECOND_WORD_BITS>(
                    DUMMY_BYTECODE,
                );
                for (table_type, table) in extra_tables {
                    cs.add_table_with_content(table_type, table);
                }
            },
            &|cs| {
                word_only_load_store_circuit_with_preprocessed_bytecode::<_, _, SECOND_WORD_BITS>(
                    cs,
                )
            },
        );
        serialize_to_file(&ssa_forms, "word_only_load_store_preprocessed_ssa.json");
    }
}
