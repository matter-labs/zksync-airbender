use super::*;
use crate::constraint::Constraint;
use crate::constraint::Term;
use crate::cs::circuit::LookupQueryTableType;
use crate::cs::circuit_trait::*;
use crate::oracle::Placeholder;
use crate::tables::TableDriver;
use crate::types::*;
use crate::witness_placer::{WitnessPlacer, WitnessComputationalInteger};
use field::PrimeField;

const TABLES_TOTAL_WIDTH: usize = 3; // TODO: strict enough?

pub fn mem_subword_only_tables() -> Vec<TableType> {
    vec![
        // all the ROM tables are initialised with a special method, tests use dummy ROM bytecode
        TableType::ZeroEntry, // we need it, as we use conditional lookup enforcements
        // TableType::RomAddressSpaceSeparator, (2^16)
        TableType::StoreByteExistingContribution, // "clear" table (2^17)
        // TableType::LoadHalfwordRomRead, // ROM*H table (2^22)
        // TableType::LoadByteRomRead, // ROM*B table (2^23)
        TableType::LoadHalfwordSignextend, // RAM*H table (2^17)
        TableType::LoadByteSignextend, // RAM*B table (2^18)
        TableType::StoreByteSourceContribution, // "keep" or STORE*B table (2^17)
    ]
}

pub fn mem_subword_only_table_addition_fn<F: PrimeField, CS: Circuit<F>>(cs: &mut CS) {
    for el in mem_subword_only_tables() {
        cs.materialize_table::<TABLES_TOTAL_WIDTH>(el);
    }
}

pub fn mem_subword_only_table_driver_fn<F: PrimeField>(table_driver: &mut TableDriver<F>) {
    for el in mem_subword_only_tables() {
        table_driver.materialize_table::<TABLES_TOTAL_WIDTH>(el);
    }
}

pub fn create_mem_subword_only_special_tables<
    F: PrimeField,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    bytecode: &[u32],
) -> [(TableType, crate::tables::LookupWrapper<F>); 3] {
    use crate::tables::{
        create_load_byte_from_rom_table, create_load_halfword_from_rom_table,
        create_rom_separator_table,
    };

    let id = TableType::RomAddressSpaceSeparator.to_table_id();
    let rom_separator_table = crate::tables::LookupWrapper::Initialized(
        create_rom_separator_table::<F, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(id),
    );

    let id = TableType::LoadHalfwordRomRead.to_table_id();
    let rom_halfword_table = crate::tables::LookupWrapper::Initialized(
        create_load_halfword_from_rom_table::<F, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(bytecode, id),
    );

    let id = TableType::LoadByteRomRead.to_table_id();
    let rom_byte_table = crate::tables::LookupWrapper::Initialized(
        create_load_byte_from_rom_table::<F, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(bytecode, id),
    );

    [
        (TableType::RomAddressSpaceSeparator, rom_separator_table),
        (TableType::LoadHalfwordRomRead, rom_halfword_table),
        (TableType::LoadByteRomRead, rom_byte_table),
    ]
}

#[allow(non_snake_case)]
fn apply_mem_subword_only_inner<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    inputs: OpcodeFamilyCircuitState<F>,
    decoder: SubwordOnlyMemoryFamilyCircuitMask,
) {
    // LH :                       rd <- sext(mem1/2[addr] || rom1/2[addr])  with +0/2     offsets accepted
    // LHU:                       rd <- zext(mem1/2[addr] || rom1/2[addr])  with +0/2     offsets accepted
    // LB :                       rd <- sext(mem1/4[addr] || rom1/4[addr])  with +0/1/2/3 offsets accepted
    // LBU:                       rd <- zext(mem1/4[addr] || rom1/4[addr])  with +0/1/2/3 offsets accepted
    // SH : mem1/2[addr] || trap rom <- rs2_1/2                             with +0/2     offsets accepted
    // SB : mem1/4[addr] || trap rom <- rs2_1/4                             with +0/1/2/3 offsets accepted

    // NOTE: by preprocessing (decoder lookup) we have rd == 0 for loads not possible
    // so we do NOT need to mask rd value

    if let Some(circuit_family_extra_mask) =
        cs.get_value(inputs.decoder_data.circuit_family_extra_mask)
    {
        println!(
            "circuit_family_extra_mask = 0b{:08b}",
            circuit_family_extra_mask.as_u32_reduced()
        );
    }

    // read rs1, to compute address
    let MemoryAccess::RegisterOnly(RegisterAccess { read_value: WordRepresentation::U16Limbs(rs1), .. }) = cs.request_mem_access(
        MemoryAccessRequest::RegisterRead {
            reg_idx: inputs.decoder_data.rs1_index,
            read_value_placeholder: Placeholder::ShuffleRamReadValue(0),
            split_as_u8: false,
        },
        "rs1",
        0,
    ) else {unreachable!()};


    

    // strategies:
    // - we perform an initial setup: computing the addr + cleanup, and fetching rom data.
    //   the addr is implicitly computed from the mem accesses, where it should be clean
    //   the offset bits (b1, b0) are implicitly determined via bool check + addition constraints
    //   and the decoder lets us know whether we're in byte or halfword, and whether we signextend or not.
    //   finally store*rom and b0*halfword cases are trapped
    // - then we manage 3 orthogonal edge cases: load*!rom, load*rom, store*!rom (each split into 2 for byte/halfword tables)
    //   the orthogonal edge cases are primarily managed by 1 shared lookup that "writes" to 2 outputs.
    //   the outputs are implicitly selecting the variables that must be overwritten in the memory accesses.
    //   in the case of store, the output variables can get masked to ==0 constraints instead of just selection.
    //   in the case of store*b we require one extra witness variable (and lookup) :(
    // - bump pc

    // scratch space
    // - just the 1 variable ("clear") for store*byte case

    let isstore = decoder.perform_write();
    let isload = isstore.toggle();
    let isbyte = decoder.perform_byte_operation();
    let ishalfword = isbyte.toggle();
    let issext = decoder.perform_signextension();


    // read mem/rs2
    let memread_addr = core::array::from_fn(|i| cs.add_named_variable(&format!("memread_addr[{i}]")));
    {
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let value = placer.get_oracle_u32(Placeholder::ShuffleRamAddress(1));
            placer.assign_u32_from_u16_parts(memread_addr, &value);
        };
        cs.set_values(value_fn);
    }
    let MemoryAccess::RegisterOrRam(RegisterOrRamAccess { read_value: WordRepresentation::U16Limbs(memread), .. }) = cs.request_mem_access(
        MemoryAccessRequest::RegisterOrRamRead { is_register: isstore, address: memread_addr, read_value_placeholder: Placeholder::ShuffleRamReadValue(1), split_as_u8: false }, 
        "mem/rs2 read", 
        1
    ) else {unreachable!()};

    // overwrite rd/mem
    let memwrite_addr = core::array::from_fn(|i| cs.add_named_variable(&format!("memwrite_addr[{i}]")));
    {
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let value = placer.get_oracle_u32(Placeholder::ShuffleRamAddress(2));
            placer.assign_u32_from_u16_parts(memwrite_addr, &value);
        };
        cs.set_values(value_fn);
    }
    let MemoryAccess::RegisterOrRam(RegisterOrRamAccess { read_value: WordRepresentation::U16Limbs(oldread), write_value: WordRepresentation::U16Limbs(memwrite), .. }) = cs.request_mem_access(
        MemoryAccessRequest::RegisterOrRamReadWrite { is_register: isload, address: memwrite_addr, read_value_placeholder: Placeholder::ShuffleRamReadValue(2), write_value_placeholder: Placeholder::ShuffleRamWriteValue(2), split_read_as_u8: false, split_write_as_u8: false }, 
        "mem/rd write", 
        2) else {unreachable!()};



    let (cleanaddr, offset_bits) = {
        // first we gotta enforce the register address
        let load = Constraint::from(isload);
        let store = Constraint::from(isstore);
        let [readaddr_lo, readaddr_hi] = memread_addr.map(Term::from);
        let [writeaddr_lo, writeaddr_hi] = memwrite_addr.map(Term::from);
        cs.add_constraint(
            store.clone() * (readaddr_lo - Term::from(inputs.decoder_data.rs2_index))
                + load.clone() * (writeaddr_lo - Term::from(inputs.decoder_data.rd_index)),
        );
        cs.add_constraint(store.clone() * readaddr_hi + load.clone() * writeaddr_hi);

        // now we can enforce the ram address
        let [rs1_lo, rs1_hi] = rs1.map(Term::from);
        let [imm_lo, imm_hi] = inputs.decoder_data.imm.map(Term::from);
        let cleanaddr_lo = load.clone() * readaddr_lo + store.clone() * writeaddr_lo;
        let cleanaddr_hi = load * readaddr_hi + store * writeaddr_hi;
        let isbit0 = cs.add_named_boolean_variable("address bit0");
        let isbit1 = cs.add_named_boolean_variable("address bit1");
        let b0 = Term::from(isbit0);
        let b1 = Term::from(isbit1);
        {
            // explicit wit.gen
            let value_fn = move |placer: &mut CS::WitnessPlacer| {
                let rs1_lo = placer.get_u16(rs1[0]);
                let imm_lo = placer.get_u16(inputs.decoder_data.imm[0]);
                let (addr_lo, _of_lo) = rs1_lo.overflowing_add(&imm_lo);
                let bit0 = addr_lo.get_bit(0);
                let bit1 = addr_lo.get_bit(1);
                placer.assign_mask(isbit0.get_variable().unwrap(), &bit0);
                placer.assign_mask(isbit1.get_variable().unwrap(), &bit1);
            };
            cs.set_values(value_fn);
        }
        let shift16_inv = Term::from_field(F::from_u32(1 << 16).unwrap().inverse().unwrap());
        let of_lo =
            shift16_inv.clone() * (rs1_lo + imm_lo - cleanaddr_lo.clone() - b0 - Term::from(2) * b1);
        let of_hi = shift16_inv * (of_lo.clone() + rs1_hi + imm_hi - cleanaddr_hi.clone());
        let L2_of_lo = Term::from(cs.add_intermediate_named_variable_from_constraint(of_lo, "addr ofL (L2)"));
        let L2_of_hi = Term::from(cs.add_intermediate_named_variable_from_constraint(of_hi, "addr ofH (L2)"));
        cs.add_constraint(L2_of_lo.clone() * (Term::from(1) - L2_of_lo)); // booleanity of overflow (low)
        cs.add_constraint(L2_of_hi.clone() * (Term::from(1) - L2_of_hi)); // booleanity of overflow (high)
        // trap halfword*b0
        cs.add_constraint(Constraint::from(ishalfword) * Constraint::from(isbit0));
        ([cleanaddr_lo, cleanaddr_hi], [isbit0, isbit1])
    };
    let [isrom, romaddr_hi] = {
        let isrom = cs.add_named_variable("flag: are we in rom addr range?");
        let romaddr_hi = cs.add_named_variable("address high 16bits truncated/wrapped to rom range (eg 6 bits)");
        let [_, cleanaddr_hi] = cleanaddr;
        {
            // extra explicit wit.gen due to L1->L2 transition
            let inputs = &[cleanaddr_hi.clone()];
            let output_variables = &[isrom, romaddr_hi];
            let table_type = Constraint::from(TableType::RomAddressSpaceSeparator.to_num());
            cs::lookup_utils::peek_lookup_values_unconstrained_into_variables_from_constraints(cs, inputs, output_variables, table_type);
        }
        let L2_isrom = cs.add_intermediate_named_variable_from_constraint(Constraint::from(isrom), "isrom (L2)");
        let L2_romaddr_hi = cs.add_intermediate_named_variable_from_constraint(Constraint::from(romaddr_hi), "romaddr_hi (L2)");
        let L2_cleanaddr_hi = cs.add_intermediate_named_variable_from_constraint(cleanaddr_hi, "cleanaddr_hi (L2)");
        let tuple = [
            LookupInput::from(L2_cleanaddr_hi),
            LookupInput::from(L2_isrom),
            LookupInput::from(L2_romaddr_hi),
        ];
        cs.enforce_lookup_tuple_for_fixed_table(&tuple, TableType::RomAddressSpaceSeparator, false);
        // trap store*rom
        cs.add_constraint(Constraint::from(isrom) * Constraint::from(isstore));
        [isrom, romaddr_hi]
    };
    let romaddr = {
        let [cleanaddr_lo, _] = cleanaddr;
        cleanaddr_lo + Term::from(1<<16) * Term::from(romaddr_hi)
    };




    // now we may proceed with our "write" calculations
    // due to SB opcode limitations, we will be creating 1 new witness variable "clear" (plus lookup)
    let clear = {
        let clear = cs.add_named_variable("clear (SB: mem[addr] halfword byte gets set to 0)");
        let [oldread_lo, oldread_hi] = oldread.map(Term::from);
        let [b0, b1] = offset_bits.map(Term::from);
        let shift16 = Term::from(1 << 16);
        let selected_oldread_halfword =
            b1.clone() * oldread_hi + (Term::from(1) - b1) * oldread_lo;
        let input = selected_oldread_halfword + shift16 * b0;
        {
            // extra explicit wit.gen due to L1->L2 transition
            let inputs = &[input.clone()];
            let output_variables = &[clear];
            let table_type = Constraint::from(TableType::StoreByteExistingContribution.to_num());
            cs::lookup_utils::peek_lookup_values_unconstrained_into_variables_from_constraints(cs, inputs, output_variables, table_type);
        }
        let L2_input = cs.add_intermediate_named_variable_from_constraint(input, "STORE*B: clear's table input: SEL(b1, OLDH, OLDL) || b0 (L2)");
        let L2_clear = cs.add_intermediate_named_variable_from_constraint(Constraint::from(clear), "clear (L2)");
        let tuple = [LookupInput::from(L2_input), LookupInput::from(L2_clear)];
        cs.enforce_lookup_tuple_for_fixed_table(&tuple, TableType::StoreByteExistingContribution, false);
        clear
    };
    // WRITE == halfwordsignext(romaddr || S || b1      )                   | LOAD*ROM*H  == ROM*H
    //              bytesignext(romaddr || S || b1 || b0)                   | LOAD*ROM*B  == ROM*B
    //          halfwordsignext(SEL(b1, MEMH, MEML) || S      )             | LOAD*!ROM*H == (LOAD - ROM)*H
    //              bytesignext(SEL(b1, MEMH, MEML) || S || b0)             | LOAD*!ROM*B == (LOAD - ROM)*B
    //          SEL(b1, OLDL, RS2L        ) || SEL(b1, RS2L        , OLDH)  | STORE*H
    //          SEL(b1, OLDL, clear + keep) || SEL(b1, clear + keep, OLDH)  | STORE*B
    // NB: for STORE, we directly use constraints on the halfword that needs to change vs stay, not on low vs high
    {
        let rom = Constraint::from(isrom);
        let ram = Constraint::from(isload) - rom.clone();
        let store = Constraint::from(isstore);
        let s = Term::from(issext);
        let b = Term::from(isbyte);
        let h = Term::from(1) - b.clone();
        let romhalfword = rom.clone() * h.clone();
        let rombyte = rom.clone() * b.clone();
        let ramhalfword = ram.clone() * h.clone();
        let rambyte = ram.clone() * b.clone();
        let storebyte = store.clone() * b.clone();
        let [b0, b1] = offset_bits.map(Term::from);
        let [oldread_lo, oldread_hi] = oldread.map(Term::from);
        let [memread_lo, memread_hi] = memread.map(Term::from);
        let [memwrite_lo, memwrite_hi] = memwrite.map(Constraint::from);
        let selected_memread_halfword =
            b1.clone() * memread_hi + (Term::from(1) - b1.clone()) * memread_lo.clone();
        let selected_memwrite_halfword =
            b1.clone() * memwrite_hi.clone() + (Term::from(1) - b1.clone()) * memwrite_lo.clone();
        let constrained_memwrite_halfword = b1 * (memwrite_lo.clone() - oldread_lo)
            + (Term::from(1) - b1.clone()) * (memwrite_hi.clone() - oldread_hi);
        let rs2_lo = Constraint::from(memread_lo);
        let keep = selected_memwrite_halfword - b.clone() * Term::from(clear) - h.clone() * rs2_lo.clone();

        let L2_rom = Term::from(cs.add_intermediate_named_variable_from_constraint(rom, "rom (L2)"));
        let L2_ram = Term::from(cs.add_intermediate_named_variable_from_constraint(ram, "ram (L2)"));
        let L2_store = Term::from(cs.add_intermediate_named_variable_from_constraint(store, "store (L2)"));
        let L2_load = L2_rom.clone() + L2_ram.clone();
        let L3_input = {
            let shiftrom = Term::from(1 << (16 + common_constants::ROM_SECOND_WORD_BITS));
            let shiftrom1 = Term::from(1 << (16 + common_constants::ROM_SECOND_WORD_BITS + 1));
            let shiftrom2 = Term::from(1 << (16 + common_constants::ROM_SECOND_WORD_BITS + 2));
            let shift16 = Term::from(1 << 16);
            let shift17 = Term::from(1 << 17);
            let rom_input =
                romaddr.clone() + shiftrom * s.clone() + shiftrom1 * b1.clone() + shiftrom2 * b0.clone();
            let ram_input =
                selected_memread_halfword + shift16 * s + shift17 * b0.clone();
            let store_bytemask_input = b * (rs2_lo + shift16 * b0);
            let L2_rom_input = Term::from(cs.add_intermediate_named_variable_from_constraint(rom_input, "rom_input (L2)"));
            let L2_ram_input = Term::from(cs.add_intermediate_named_variable_from_constraint(ram_input, "ram_input (L2)"));
            let L2_store_bytemasked_input = Term::from(cs.add_intermediate_named_variable_from_constraint(store_bytemask_input, "store_bytemasked_input (L2)"));
            let input = L2_rom * L2_rom_input + L2_ram * L2_ram_input + L2_store.clone() * L2_store_bytemasked_input;
            cs.add_intermediate_named_variable_from_constraint(input, "final lookup input (L3)")
        };
        let L3_output1 = {
            let L2_memwrite_lo = Term::from(cs.add_intermediate_named_variable_from_constraint(memwrite_lo, "memwrite_lo (L2)"));
            let L2_keep = Term::from(cs.add_intermediate_named_variable_from_constraint(keep, "keep (L2)"));
            let output1 = L2_load.clone() * L2_memwrite_lo + L2_store.clone() * L2_keep;
            cs.add_intermediate_named_variable_from_constraint(output1, "final lookup output1 (L3)")
        };
        let L3_output2 = {
            let L2_memwrite_hi = Term::from(cs.add_intermediate_named_variable_from_constraint(memwrite_hi, "memwrite_hi (L2)"));
            let L2_constrained_memwrite_halfword = Term::from(cs.add_intermediate_named_variable_from_constraint(constrained_memwrite_halfword, "constrained_memwrite_halfword (L2)"));
            let output2 = L2_load * L2_memwrite_hi + L2_store * L2_constrained_memwrite_halfword;
            cs.add_intermediate_named_variable_from_constraint(output2, "final lookup output2 (L3)")
        };
        let L3_table_id = {
            let romhalfword_table = Term::from(TableType::LoadHalfwordRomRead.to_num());
            let rombyte_table = Term::from(TableType::LoadByteRomRead.to_num());
            let ramhalfword_table = Term::from(TableType::LoadHalfwordSignextend.to_num());
            let rambyte_table = Term::from(TableType::LoadByteSignextend.to_num());
            let storebyte_table = Term::from(TableType::StoreByteSourceContribution.to_num());
            // NB: missing storehalfword masks to ZeroEntry table. a crucial mask!
            let table_id = romhalfword * romhalfword_table
                + rombyte * rombyte_table
                + ramhalfword * ramhalfword_table
                + rambyte * rambyte_table
                + storebyte * storebyte_table; 
            let L2_table_id = Constraint::from(cs.add_intermediate_named_variable_from_constraint(table_id, "table_id (L2)"));
            let L2_execute = Constraint::from(cs.add_intermediate_named_variable_from_constraint(
                Constraint::from(inputs.execute),
                "execute (L2)",
            ));
            // NB: to avoid scenarios where romread!=0 but we're in padding so ROM*H==1 and memwrite==0, 
            // we patch this to zero table
            cs.add_intermediate_named_variable_from_constraint(
                L2_execute * L2_table_id,
                "final lookup table_id (L3)",
            )
        };
        let tuple = [
            LookupInput::from(L3_input),
            LookupInput::from(L3_output1),
            LookupInput::from(L3_output2),
        ];
        cs.enforce_lookup_tuple_for_variable_table(&tuple, L3_table_id);
    }




    // bump PC
    use crate::gkr_circuits::utils::calculate_pc_next_no_overflows_with_range_checks;
    calculate_pc_next_no_overflows_with_range_checks(
        cs,
        inputs.cycle_start_state.pc,
        inputs.cycle_end_state.pc,
    );
}

pub fn mem_subword_only_circuit_with_preprocessed_bytecode_for_gkr<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
) {
    let (input, bitmask) = cs.allocate_machine_state(false, false, SUBWORD_ONLY_MEMORY_FAMILY_NUM_FLAGS);
    let bitmask: [_; SUBWORD_ONLY_MEMORY_FAMILY_NUM_FLAGS] = bitmask.try_into().unwrap();
    let bitmask = bitmask.map(|el| Boolean::Is(el));
    let decoder = SubwordOnlyMemoryFamilyCircuitMask::from_mask(bitmask);
    apply_mem_subword_only_inner(cs, input, decoder);
}

#[cfg(test)]
mod test {
    use test_utils::skip_if_ci;

    use super::*;
    use crate::gkr_compiler::{compile_unrolled_circuit_state_transition_into_gkr, dump_ssa_witness_eval_form};
    // use crate::gkr_compiler::dump_ssa_witness_eval_form_for_unrolled_circuit;
    use crate::utils::serialize_to_file;

    #[test]
    fn compile_mem_subword_only_circuit_into_gkr() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let gkr_compiled = compile_unrolled_circuit_state_transition_into_gkr::<BabyBearField>(
            &|cs| {
                mem_subword_only_table_addition_fn(cs);
                // ROM tables must be added here (with dummy bytecode) so that
                // offset_for_decoder_table in the compiled JSON reflects the correct
                // total_tables_len at prove time, when real ROM tables are present.
                for (table_type, table) in create_mem_subword_only_special_tables::<
                    BabyBearField,
                    { common_constants::ROM_SECOND_WORD_BITS },
                >(&[]) {
                    cs.add_table_with_content(table_type, table);
                }
            },
            &|cs| mem_subword_only_circuit_with_preprocessed_bytecode_for_gkr(cs),
            1 << 20,
            24,
        );

        serialize_to_file(
            &gkr_compiled,
            "compiled_circuits/mem_subword_only_preprocessed_layout_gkr.json",
        );
    }

    #[test]
    fn compile_mem_subword_only_gkr_witness_graph() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let ssa_forms = dump_ssa_witness_eval_form::<BabyBearField>(
            &|cs| {
                mem_subword_only_table_addition_fn(cs);
                // ROM tables must be added here (with dummy bytecode) so that
                // offset_for_decoder_table in the compiled JSON reflects the correct
                // total_tables_len at prove time, when real ROM tables are present.
                for (table_type, table) in create_mem_subword_only_special_tables::<
                    BabyBearField,
                    { common_constants::ROM_SECOND_WORD_BITS },
                >(&[]) {
                    cs.add_table_with_content(table_type, table);
                }
            },
            &|cs| mem_subword_only_circuit_with_preprocessed_bytecode_for_gkr(cs),
        );
        serialize_to_file(
            &ssa_forms,
            "compiled_circuits/mem_subword_only_preprocessed_ssa_gkr.json",
        );
    }
}
