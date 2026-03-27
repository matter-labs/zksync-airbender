use super::*;
use crate::constraint::Constraint;
use crate::constraint::Term;
use crate::cs::circuit::LookupQueryTableType;
use crate::cs::circuit_trait::*;
use crate::oracle::Placeholder;
use crate::tables::TableDriver;
use crate::types::*;
use crate::witness_placer::*;
use field::PrimeField;

const TABLES_TOTAL_WIDTH: usize = 3;

pub fn mem_word_only_tables() -> Vec<TableType> {
    vec![
        // all rom tables gotta be added in the prover code when bytecode data is available
        TableType::ZeroEntry, // we need it for romread's conditional lookup enforcement
        // TableType::RomAddressSpaceSeparator
        // TableType::RomRead
    ]
}

pub fn mem_word_only_table_addition_fn<F: PrimeField, CS: Circuit<F>>(cs: &mut CS) {
    for el in mem_word_only_tables() {
        cs.materialize_table::<TABLES_TOTAL_WIDTH>(el);
    }
}

pub fn mem_word_only_table_driver_fn<F: PrimeField>(table_driver: &mut TableDriver<F>) {
    for el in mem_word_only_tables() {
        table_driver.materialize_table::<TABLES_TOTAL_WIDTH>(el);
    }
}

pub fn create_mem_word_only_special_tables<
    F: PrimeField,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    bytecode: &[u32],
) -> [(TableType, crate::tables::LookupWrapper<F>); 2] {
    use crate::tables::{create_table_for_rom_image, create_rom_separator_table};

    let id = TableType::RomRead.to_table_id();
    let rom_table = crate::tables::LookupWrapper::Initialized(
        create_table_for_rom_image::<F, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(bytecode, id),
    );

    let id = TableType::RomAddressSpaceSeparator.to_table_id();
    let rom_separator_table = crate::tables::LookupWrapper::Initialized(
        create_rom_separator_table::<F, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(id),
    );

    [
        (TableType::RomRead, rom_table),
        (TableType::RomAddressSpaceSeparator, rom_separator_table),
    ]
}

fn apply_mem_word_only_inner<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    inputs: OpcodeFamilyCircuitState<F>,
    decoder: WordOnlyMemoryFamilyCircuitMask,
) {
    // LW: rd                          <- mem[addr] || rom[addr]  with +0 offset accepted
    // SW: mem[addr] || trap rom[addr] <- rs2                     with +0 offset accepted
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
    // - we perform an initial setup: computing the addr, and fetching rom data.
    //   we get rom data from a lookup (that also manages traps),
    // - then we manage 3 orthogonal edge cases: load*!rom, load*rom, store*!rom (and store*rom is trapped)
    // - bump pc

    let isstore = decoder.perform_write();
    let isload = decoder.perform_write().toggle();
    let addr = {
        let [rs1_low, rs1_high] = rs1;
        let [imm_low, imm_high] = inputs.decoder_data.imm;
        let low: Variable = cs.add_named_variable("addr_low"); // range checked by memory accesses
        let high = cs.add_named_variable("addr_high"); // range checked by memory accesses
        // cs.require_invariant(low, Invariant::RangeChecked { width: 16 });
        // cs.require_invariant(high, Invariant::RangeChecked { width: 16 });
        let of_low = cs.add_named_boolean_variable("low overflow: rs1 +u16 imm");
        let of_high = cs.add_named_boolean_variable("high overflow: rs1 +u16 imm");
        let shift16 = Term::from(1<<16);
        {
            // explicit wit.gen
            let value_fn = move |placer: &mut CS::WitnessPlacer| {
                let [rs1_lo, rs1_hi] = rs1.map(|var| placer.get_u16(var));
                let [imm_lo, imm_hi] = inputs.decoder_data.imm.map(|var| placer.get_u16(var));
                let (addr_lo, of_lo) = rs1_lo.overflowing_add(&imm_lo);
                let (addr_hi, of_hi) = rs1_hi.overflowing_add_with_carry(&imm_hi, &of_lo);
                placer.assign_mask(of_low.get_variable().unwrap(), &of_lo);
                placer.assign_mask(of_high.get_variable().unwrap(), &of_hi);
                placer.assign_u16(low, &addr_lo);
                placer.assign_u16(high, &addr_hi);
            };
            cs.set_values(value_fn);
        }
        cs.add_constraint_allow_explicit_linear(Term::from(rs1_low) + Term::from(imm_low) - Term::from(low) - shift16*Term::from(of_low));
        cs.add_constraint_allow_explicit_linear(Term::from(of_low) + Term::from(rs1_high) + Term::from(imm_high) - Term::from(high) - shift16*Term::from(of_high));
        [low, high]
    };
    let [isrom, romaddr_hi] = {
        let isrom = cs.add_named_variable("flag: are we in rom addr range?");
        let romaddr_hi = cs.add_named_variable("address high 16bits truncated/wrapped to rom range (eg 6 bits)");
        let [_, addr_hi] = addr;
        let inputs = &[addr_hi].map(LookupInput::from);
        let output_variables = &[isrom, romaddr_hi];
        let table_type = LookupQueryTableType::Constant(TableType::RomAddressSpaceSeparator);
        cs.set_variables_from_lookup_constrained(inputs, output_variables, table_type);
        // trap store*rom
        cs.add_constraint(Constraint::from(isrom) * Constraint::from(isstore));
        [isrom, romaddr_hi]
    };
    let romread = {
        let lo = cs.add_named_variable("romread low 16bits");
        let hi = cs.add_named_variable("romread high 16bits");
        // also traps +1/2/3 word offsets
        let [addr_lo, _] = addr;
        // NB: to avoid scenarios where romread!=0 but we're inpadding so memwrite==0, we paatch this to zero table
        let exe = inputs.execute;
        let inputs = &[Constraint::from(addr_lo) + Term::from(1 << 16) * Term::from(romaddr_hi)].map(LookupInput::from);
        let output_variables = &[lo, hi];
        // let table_type = LookupQueryTableType::Constant(TableType::RomRead);
        let table_type = LookupQueryTableType::Expression(LookupInput::from(Term::from(exe)*Term::from(TableType::RomRead.to_num())));
        cs.set_variables_from_lookup_constrained(inputs, output_variables, table_type);
        [lo, hi]
    };

    // now we are ready to read mem/rs2
    let memread_addr = {
        let rs2_addr = Register([Num::Var(inputs.decoder_data.rs2_index), Num::Constant(F::ZERO)]);
        let ram_addr = Register(addr.map(Num::Var));
        // NB: Register::choose might be outdated now..
        Register::choose(cs, &isstore, &rs2_addr, &ram_addr).0.each_ref().map(Num::get_variable)
    };
    let MemoryAccess::RegisterOrRam(RegisterOrRamAccess { read_value: WordRepresentation::U16Limbs(memread), .. }) = cs.request_mem_access(
        MemoryAccessRequest::RegisterOrRamRead { is_register: isstore, address: memread_addr, read_value_placeholder: Placeholder::ShuffleRamReadValue(1), split_as_u8: false }, 
        "mem/rs2 read", 
        1
    ) else {unreachable!()};

    // now we may overwrite rd/mem
    let memwrite_addr = {
        let rd_addr = Register([Num::Var(inputs.decoder_data.rd_index), Num::Constant(F::ZERO)]);
        let ram_addr = Register(addr.map(Num::Var));
        // NB: Register::choose might be outdated now..
        Register::choose(cs, &isstore, &ram_addr, &rd_addr).0.each_ref().map(Num::get_variable)
    };
    let MemoryAccess::RegisterOrRam(RegisterOrRamAccess { read_value: WordRepresentation::U16Limbs(_oldread), write_value: WordRepresentation::U16Limbs(memwrite), .. }) = cs.request_mem_access(
        MemoryAccessRequest::RegisterOrRamReadWrite { is_register: isload, address: memwrite_addr, read_value_placeholder: Placeholder::ShuffleRamReadValue(2), write_value_placeholder: Placeholder::ShuffleRamWriteValue(2), split_read_as_u8: false, split_write_as_u8: false }, 
        "mem/rd write", 
        2) else {unreachable!()};

    // now we may proceed with our "write" calculations
    // WRITE == memread | STORE*!ROM
    //          trap    | STORE*ROM
    //          romread | LOAD*ROM
    //          memread | LOAD*!ROM
    //       == romread | LOAD*ROM
    //          memread | else
    //       == romread | ROM
    //          memread | else
    {
        let [memread_lo, memread_hi] = memread.map(Constraint::from);
        let [romread_lo, romread_hi] = romread.map(Constraint::from).map(Constraint::from);
        let [memwrite_lo, memwrite_hi] = memwrite.map(Constraint::from).map(Constraint::from);
        let notrom = Constraint::from(Boolean::Is(isrom).toggle());
        let isrom = Term::from(isrom);
        cs.add_constraint(isrom * romread_lo + notrom.clone() * memread_lo - memwrite_lo);
        cs.add_constraint(isrom * romread_hi + notrom * memread_hi - memwrite_hi);
    }


    // bump PC
    use crate::gkr_circuits::utils::calculate_pc_next_no_overflows_with_range_checks;
    calculate_pc_next_no_overflows_with_range_checks(
        cs,
        inputs.cycle_start_state.pc,
        inputs.cycle_end_state.pc,
    );
}

pub fn mem_word_only_circuit_with_preprocessed_bytecode_for_gkr<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
) {
    let (input, bitmask) = cs.allocate_machine_state(false, false, WORD_ONLY_MEMORY_FAMILY_NUM_FLAGS);
    let bitmask: [_; WORD_ONLY_MEMORY_FAMILY_NUM_FLAGS] = bitmask.try_into().unwrap();
    let bitmask = bitmask.map(|el| Boolean::Is(el));
    let decoder = WordOnlyMemoryFamilyCircuitMask::from_mask(bitmask);
    apply_mem_word_only_inner(cs, input, decoder);
}

#[cfg(test)]
mod test {
    use test_utils::skip_if_ci;

    use super::*;
    use crate::gkr_compiler::{compile_unrolled_circuit_state_transition_into_gkr, dump_ssa_witness_eval_form};
    // use crate::gkr_compiler::dump_ssa_witness_eval_form_for_unrolled_circuit;
    use crate::utils::serialize_to_file;

    #[test]
    fn compile_mem_word_only_circuit_into_gkr() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let gkr_compiled = compile_unrolled_circuit_state_transition_into_gkr::<BabyBearField>(
            &|cs| {
                mem_word_only_table_addition_fn(cs);
                // ROM tables must be added here (with dummy bytecode) so that
                // offset_for_decoder_table in the compiled JSON reflects the correct
                // total_tables_len at prove time, when real ROM tables are present.
                for (table_type, table) in create_mem_word_only_special_tables::<
                    BabyBearField,
                    { common_constants::ROM_SECOND_WORD_BITS },
                >(&[]) {
                    cs.add_table_with_content(table_type, table);
                }
            },
            &|cs| mem_word_only_circuit_with_preprocessed_bytecode_for_gkr(cs),
            1 << 20,
            24,
        );

        serialize_to_file(
            &gkr_compiled,
            "compiled_circuits/mem_word_only_preprocessed_layout_gkr.json",
        );
    }

    #[test]
    fn compile_mem_word_only_gkr_witness_graph() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let ssa_forms = dump_ssa_witness_eval_form::<BabyBearField>(
            &|cs| {
                mem_word_only_table_addition_fn(cs);
                // ROM tables must be added here (with dummy bytecode) so that
                // offset_for_decoder_table in the compiled JSON reflects the correct
                // total_tables_len at prove time, when real ROM tables are present.
                for (table_type, table) in create_mem_word_only_special_tables::<
                    BabyBearField,
                    { common_constants::ROM_SECOND_WORD_BITS },
                >(&[]) {
                    cs.add_table_with_content(table_type, table);
                }
            },
            &|cs| mem_word_only_circuit_with_preprocessed_bytecode_for_gkr(cs),
        );
        serialize_to_file(
            &ssa_forms,
            "compiled_circuits/mem_word_only_preprocessed_ssa_gkr.json",
        );
    }
}
