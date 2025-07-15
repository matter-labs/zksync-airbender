use crate::tables::create_rom_separator_table;

use super::*;

pub const MEMORY_GET_OFFSET_AND_MASK_NUM_BITS_NO_TRAP: usize = 2;
pub const MEMORY_GET_OFFSET_AND_MASK_NUM_BITS_WITH_TRAP: usize =
    MEMORY_GET_OFFSET_AND_MASK_NUM_BITS_NO_TRAP + 1;

pub fn load_store_tables() -> Vec<TableType> {
    vec![
        TableType::ZeroEntry, // as we use lookups via optimization context
        TableType::MemoryGetOffsetAndMaskWithTrap,
        // these get dynamically allocated by instance of the circuit depending on the machine configuration
        //      TableType::RomAddressSpaceSeparator,
        //      TableType::AlignedRomRead,
        TableType::MemoryLoadHalfwordOrByte,
        TableType::MemStoreClearOriginalRamValueLimb,
        TableType::MemStoreClearWrittenValueLimb,
    ]
}

pub fn load_store_table_addition_fn<F: PrimeField, CS: Circuit<F>>(cs: &mut CS) {
    for el in load_store_tables() {
        cs.materialize_table(el);
    }
}

pub fn load_store_table_driver_fn<F: PrimeField>(table_driver: &mut TableDriver<F>) {
    for el in load_store_tables() {
        table_driver.materialize_table(el);
    }
}

pub fn create_load_store_special_tables<
    F: PrimeField,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    bytecode: &[u32],
) -> [(TableType, LookupWrapper<F>); 2] {
    use crate::machine::machine_configurations::create_table_for_aligned_rom_image;

    let id = TableType::RomAddressSpaceSeparator.to_table_id();
    let rom_separator_table = LookupWrapper::Dimensional3(create_rom_separator_table::<
        F,
        ROM_ADDRESS_SPACE_SECOND_WORD_BITS,
    >(id));

    let id = TableType::AlignedRomRead.to_table_id();
    let bytecode_words_table = LookupWrapper::Dimensional3(create_table_for_aligned_rom_image::<
        F,
        ROM_ADDRESS_SPACE_SECOND_WORD_BITS,
    >(bytecode, id));

    [
        (TableType::RomAddressSpaceSeparator, rom_separator_table),
        (TableType::AlignedRomRead, bytecode_words_table),
    ]
}

fn apply_load_store<
    F: PrimeField,
    CS: Circuit<F>,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    cs: &mut CS,
    inputs: OpcodeFamilyCircuitState<F>,
) {
    let decoder = <MemoryFamilyDecoder as OpcodeFamilyDecoder>::BitmaskCircuitParser::parse(
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

    // Special note about `MemoryGetOffsetAndMask` table - it maps offset_low || funct3 || is_load || rd_is_zero into
    // - lowest 2 bits of the offset, so we can form an address of aligned word (and also use these 2 bit integer in other places)
    // - `MEMORY_GET_OFFSET_AND_MASK_NUM_BITS_WITH_TRAP` - wide bitmask

    // Later on we use a trick, that instead of decomposing bitmask into `MEMORY_GET_OFFSET_AND_MASK_NUM_BITS_WITH_TRAP` bits,
    // we instead decompose into 1 less bits, so if trap happened - it's unsatisfiable

    let [offset_low_bits, mem_offset_with_trap_table_bitmask] = {
        let unclean_addr_low = unclean_addr.0[0];
        let lookup_inputs = [Constraint::from(unclean_addr_low)
            + Term::from(1 << 16) * Term::from(inputs.decoder_data.funct3)
            + Term::from(1 << 19) * Constraint::from(is_load)
            + Term::from(1 << 20) * Constraint::from(is_rd_x0)]
        .map(LookupInput::from);
        cs.get_variables_from_lookup_constrained(
            &lookup_inputs,
            TableType::MemoryGetOffsetAndMaskWithTrap,
        )
    };

    let [less_than_word_op, use_high_word_in_mem_ops] =
        Boolean::split_into_bitmask::<_, _, MEMORY_GET_OFFSET_AND_MASK_NUM_BITS_NO_TRAP>(
            cs,
            Num::Var(mem_offset_with_trap_table_bitmask),
        );

    // Below that line the only trap that can happen is an attempt to store into ROM (offsets are irrelevant)

    let clean_addr = {
        let unclean_addr_low = unclean_addr.0[0];
        let unclean_addr_high = unclean_addr.0[1];
        // This constraint is guaranteed to cleanup lowest bits as `offset_low_bits` is true 2 lowest bits of `unclean_addr_low`
        let low = Constraint::from(unclean_addr_low) - Term::from(offset_low_bits);
        let high = Constraint::from(unclean_addr_high);
        [low, high]
    };

    // For ROM we need 2 outputs:
    // - check high word of the offset, and trap if we try to write
    // - produce a mask whether it's indeed ROM or RAM access

    let [is_ram_range, address_high_bits_for_rom] = {
        let clean_addr_high = clean_addr[1].clone();
        let lookup_inputs = [clean_addr_high].map(LookupInput::from);
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

    // NOTE: construction of this circuit REQUIRES non-trivial padding of memro query values if we do NOT
    // execute (so we pad circuits for capacity). Such queries do NOT contribute to memory accumulators due to
    // predication on `execute`, but we still do not want to spend too many variables to make extra masking here

    let rs2_or_load_ram_access_query = {
        let rs2_or_load_ram_access_query_is_register = is_store;
        // we model ROM loads as loads from 0
        let rs2_or_load_ram_access_query_address_low = cs.add_variable_from_constraint(
            clean_addr[0].clone() * Term::from(load_from_ram) + // load from RAM
            Term::from(inputs.decoder_data.rs2_index) * Term::from(is_store), // RS2 index in case of STORE
        );
        let rs2_or_load_ram_access_query_address_high = cs.add_variable_from_constraint(
            clean_addr[1].clone() * Term::from(load_from_ram), // load from RAM, and 0 in case of STORE
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
            use cs::witness_placer::*;
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
            clean_addr[0].clone() * Term::from(is_store) + // store into RAM
            Term::from(inputs.decoder_data.rd_index) * (Term::from(1) - Term::from(is_store)), // RD index in case of any LOAD
        );
        let rd_or_store_ram_access_query_address_high = cs.add_variable_from_constraint(
            clean_addr[1].clone() * Term::from(is_store), // store into RAM, and 0 in case of LOAD
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
            use cs::witness_placer::*;
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

    // // we still need witness for RAM read - and we range-check it, as we may fully copy it into outputs
    // let ram_read_witness = Register::new_from_placeholder(cs, Placeholder::LoadStoreRamValue);

    // // - if we load from RAM, then witness is equal to RS2 query read value
    // for (a, b) in ram_read_witness.0.iter().zip(rs2_or_load_ram_access_query.read_value.iter()) {
    //     cs.add_constraint((Term::from(*a) - Term::from(*b)) * Term::from(load_from_ram));
    // }

    // let ram_limb_for_subword_size_ops = cs.choose(use_high_word_in_mem_load, ram_read_witness.0[1], ram_read_witness.0[0]);

    // now we can actually use optimization context
    let mut opt_ctx = OptimizationContext::new();
    // three independent cases

    // LOAD from ROM
    opt_ctx.reset_indexers();
    let [rom_load_low, rom_load_high] = {
        // it's enough to perform a single lookup from the combination of RAM offset (unaligned - it gives us all the information) + funct3,
        // but such table is potentially too large (21 + 3 bits or more),
        // so we would need to select again, and use another table

        // This combination is always aligned, so we can shift another 2 bits to the right
        let mut input =
            clean_addr[0].clone() + Term::from(1 << 16) * Term::from(address_high_bits_for_rom);
        input.scale(F::from_u64_unchecked(1u64 << 2).inverse().unwrap());

        // These values will be used if we do full LW
        let [rom_load_low, rom_load_high] = opt_ctx.append_lookup_relation_from_linear_terms(
            cs,
            &[input],
            TableType::AlignedRomRead.to_num(),
            load_from_rom,
        );

        let rom_limb_for_subword_size_ops = cs.choose(
            use_high_word_in_mem_ops,
            Num::Var(rom_load_high),
            Num::Var(rom_load_low),
        );
        // now we can use single table call, and then select results for full word or less than word

        let [rom_less_than_word_load_low, rom_less_than_word_load_high] = opt_ctx
            .append_lookup_relation_from_linear_terms(
                cs,
                &[Constraint::from(rom_limb_for_subword_size_ops)
                    + Term::from(1 << 16) * Term::from(offset_low_bits)
                    + Term::from(1 << 18) * Term::from(inputs.decoder_data.funct3)],
                TableType::MemoryLoadHalfwordOrByte.to_num(),
                load_from_rom,
            );

        let low = cs.add_variable_from_constraint(
            Term::from(rom_less_than_word_load_low) * Term::from(less_than_word_op)
                + Term::from(rom_load_low) * (Term::from(1) - Term::from(less_than_word_op)),
        );

        let high = cs.add_variable_from_constraint(
            Term::from(rom_less_than_word_load_high) * Term::from(less_than_word_op)
                + Term::from(rom_load_high) * (Term::from(1) - Term::from(less_than_word_op)),
        );

        [low, high]
    };

    // LOAD from RAM
    opt_ctx.reset_indexers();
    let [ram_load_low, ram_load_high] = {
        // we already have a full word, so it's enough to use selected limb and output the case of less than word

        // NOTE: this interpretation works fine even if we STORE - it's just a value, and we didn't constraint anything yet. We treat is as a witness in some sense.
        // We already make query addresses, so we only will need to add constraint on the RS/STORE query write value!
        let ram_limb_for_subword_size_ops = cs.choose(
            use_high_word_in_mem_ops,
            Num::Var(rs2_or_load_ram_access_query.read_value[1]),
            Num::Var(rs2_or_load_ram_access_query.read_value[0]),
        );

        let [ram_less_than_word_load_low, ram_less_than_word_load_high] = opt_ctx
            .append_lookup_relation_from_linear_terms(
                cs,
                &[Constraint::from(ram_limb_for_subword_size_ops)
                    + Term::from(1 << 16) * Term::from(offset_low_bits)
                    + Term::from(1 << 18) * Term::from(inputs.decoder_data.funct3)],
                TableType::MemoryLoadHalfwordOrByte.to_num(),
                load_from_ram,
            );

        let low = cs.add_variable_from_constraint(
            Term::from(ram_less_than_word_load_low) * Term::from(less_than_word_op)
                + Term::from(rs2_or_load_ram_access_query.read_value[0])
                    * (Term::from(1) - Term::from(less_than_word_op)),
        );

        let high = cs.add_variable_from_constraint(
            Term::from(ram_less_than_word_load_high) * Term::from(less_than_word_op)
                + Term::from(rs2_or_load_ram_access_query.read_value[1])
                    * (Term::from(1) - Term::from(less_than_word_op)),
        );

        [low, high]
    };

    // STORE
    opt_ctx.reset_indexers();
    let [store_value_low, store_value_high] = {
        // For STORE the same logic applies - we can just use query value as witness-style input, and only constraint how we write

        // In the contrast to LOADS, we just need to make
        let updated_limb_in_store = cs.choose(
            use_high_word_in_mem_ops,
            Num::Var(rd_or_store_ram_access_query.read_value[1]),
            Num::Var(rd_or_store_ram_access_query.read_value[0]),
        );
        // now we need to update it - we can do it with 2 lookups - one will cleanup the source word in case of subword sized update,
        // another will cut a part of the value that we want to store

        let [original_ram_limb_cleaned, _unused] = opt_ctx
            .append_lookup_relation_from_linear_terms(
                cs,
                &[Constraint::from(updated_limb_in_store)
                    + Term::from(1 << 16) * Term::from(offset_low_bits)
                    + Term::from(1 << 18) * Term::from(inputs.decoder_data.funct3)],
                TableType::MemStoreClearOriginalRamValueLimb.to_num(),
                is_store,
            );

        let [value_to_write_limb_cleaned, _unused] = opt_ctx
            .append_lookup_relation_from_linear_terms(
                cs,
                &[Constraint::from(rs2_or_load_ram_access_query.read_value[0])
                    + Term::from(1 << 16) * Term::from(offset_low_bits)
                    + Term::from(1 << 18) * Term::from(inputs.decoder_data.funct3)],
                TableType::MemStoreClearWrittenValueLimb.to_num(),
                is_store,
            );

        let store_less_than_word_value_low = cs.add_variable_from_constraint(
            Term::from(rd_or_store_ram_access_query.read_value[0])
                * Term::from(use_high_word_in_mem_ops)
                + (Term::from(original_ram_limb_cleaned) + Term::from(value_to_write_limb_cleaned))
                    * (Term::from(1) - Term::from(use_high_word_in_mem_ops)),
        );

        let store_less_than_word_value_high = cs.add_variable_from_constraint(
            Term::from(rd_or_store_ram_access_query.read_value[1])
                * (Term::from(1) - Term::from(use_high_word_in_mem_ops))
                + (Term::from(original_ram_limb_cleaned) + Term::from(value_to_write_limb_cleaned))
                    * Term::from(use_high_word_in_mem_ops),
        );

        let low = cs.add_variable_from_constraint(
            Term::from(store_less_than_word_value_low) * Term::from(less_than_word_op)
                + Term::from(rs2_or_load_ram_access_query.read_value[0])
                    * (Term::from(1) - Term::from(less_than_word_op)),
        );

        let high = cs.add_variable_from_constraint(
            Term::from(store_less_than_word_value_high) * Term::from(less_than_word_op)
                + Term::from(rs2_or_load_ram_access_query.read_value[1])
                    * (Term::from(1) - Term::from(less_than_word_op)),
        );

        [low, high]
    };

    opt_ctx.enforce_all(cs);

    // now we just need to constraint memory query values

    // if we LOAD, then RD write query WRITE value must be equal to the corresponding RAM or ROM read value if we do read,
    // and we also need to mask into writing into X0
    let rd_candidate_low = cs.add_variable_from_constraint(
        Term::from(load_from_ram) * Term::from(ram_load_low)
            + Term::from(load_from_rom) * Term::from(rom_load_low),
    );
    let rd_candidate_high = cs.add_variable_from_constraint(
        Term::from(load_from_ram) * Term::from(ram_load_high)
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
        (Term::from(store_value_low) - Term::from(rd_or_store_ram_access_query.write_value[0]))
            * Term::from(is_store),
    );
    cs.add_constraint(
        (Term::from(store_value_high) - Term::from(rd_or_store_ram_access_query.write_value[1]))
            * Term::from(is_store),
    );

    // write to PC
    let pc = Register(inputs.cycle_start_state.pc.map(|x| Num::Var(x)));
    let pc_next = Register(inputs.cycle_end_state.pc.map(Num::Var));
    bump_pc_no_range_checks_explicit(cs, pc, pc_next);
}

pub fn load_store_circuit_with_preprocessed_bytecode<
    F: PrimeField,
    CS: Circuit<F>,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    cs: &mut CS,
) {
    let input = cs.allocate_execution_circuit_state::<true>();
    apply_load_store::<F, CS, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(cs, input);
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::utils::serialize_to_file;

    const SECOND_WORD_BITS: usize = 4;
    const DUMMY_BYTECODE: &[u32] = &[UNIMP_OPCODE];

    #[test]
    fn compile_load_store_circuit() {
        use ::field::Mersenne31Field;

        let compiled = compile_unrolled_circuit_state_transition::<Mersenne31Field>(
            &|cs| {
                load_store_table_addition_fn(cs);

                let extra_tables =
                    create_load_store_special_tables::<_, SECOND_WORD_BITS>(DUMMY_BYTECODE);
                for (table_type, table) in extra_tables {
                    cs.add_table_with_content(table_type, table);
                }
            },
            &|cs| load_store_circuit_with_preprocessed_bytecode::<_, _, SECOND_WORD_BITS>(cs),
            1 << (16 + SECOND_WORD_BITS),
            24,
        );

        serialize_to_file(&compiled, "load_store_preprocessed_layout.json");
    }

    #[test]
    fn compile_load_store_witness_graph() {
        use ::field::Mersenne31Field;

        let ssa_forms = dump_ssa_witness_eval_form_for_unrolled_circuit::<Mersenne31Field>(
            &|cs| {
                load_store_table_addition_fn(cs);

                let extra_tables =
                    create_load_store_special_tables::<_, SECOND_WORD_BITS>(DUMMY_BYTECODE);
                for (table_type, table) in extra_tables {
                    cs.add_table_with_content(table_type, table);
                }
            },
            &|cs| load_store_circuit_with_preprocessed_bytecode::<_, _, SECOND_WORD_BITS>(cs),
        );
        serialize_to_file(&ssa_forms, "load_store_preprocessed_ssa.json");
    }
}
