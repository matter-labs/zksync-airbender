use super::*;
use crate::constraint::Constraint;
use crate::constraint::Term;
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
) -> [(TableType, crate::tables::LookupWrapper<F>); 1] {
    use crate::tables::create_table_for_rom_image;

    let id = TableType::RomRead.to_table_id();
    let rom_table = crate::tables::LookupWrapper::Initialized(create_table_for_rom_image::<
        F,
        ROM_ADDRESS_SPACE_SECOND_WORD_BITS,
    >(bytecode, id));

    [(TableType::RomRead, rom_table)]
}

// TODO: this circuit would benefit from the separation of mem accesses according to reg/ram:
// - intermediate layer logic would be reduced (small memory saving)
// - +1 variable saving for the high address limb of the register-only access
#[allow(non_snake_case)]
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
    let MemoryAccess::RegisterOnly(RegisterAccess {
        read_value: WordRepresentation::U16Limbs(rs1),
        ..
    }) = cs.request_mem_access(
        MemoryAccessRequest::RegisterRead {
            reg_idx: inputs.decoder_data.rs1_index,
            read_value_placeholder: Placeholder::ShuffleRamReadValue(0),
            split_as_u8: false,
        },
        "rs1",
        0,
    )
    else {
        unreachable!()
    };

    // strategies:
    // - we perform an initial setup: computing the addr, and fetching rom data.
    //   the addr is implicitly computed from the mem accesses, where it should be clean
    //
    //   we get rom data from a lookup (that also manages traps),
    //   finally store*rom is trapped
    // - then we manage 3 orthogonal edge cases: load*!rom, load*rom, store*!rom (and store*rom is trapped)
    //   the orthogonal edge cases are primarily managed by 1 shared lookup that "writes" to 2 outputs.
    //   the outputs are implicitly selecting the variables that must be overwritten in the memory accesses.
    //   in case of load*rom we simply perform the RomRead lookup
    //   in all other cases the output expressions get masked to ==0 constraints
    // - bump pc

    let is_store = decoder.perform_write();
    let is_load = is_store.toggle();

    // read mem/rs2
    let memread_addr =
        core::array::from_fn(|i| cs.add_named_variable(&format!("memread_addr[{i}]")));
    {
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let value = placer.get_oracle_u32(Placeholder::ShuffleRamAddress(1));
            placer.assign_u32_from_u16_parts(memread_addr, &value);
        };
        cs.set_values(value_fn);
    }
    let MemoryAccess::RegisterOrRam(RegisterOrRamAccess {
        read_value: WordRepresentation::U16Limbs(memread),
        ..
    }) = cs.request_mem_access(
        MemoryAccessRequest::RegisterOrRamRead {
            is_register: is_store,
            address: memread_addr,
            read_value_placeholder: Placeholder::ShuffleRamReadValue(1),
            split_as_u8: false,
        },
        "mem/rs2 read",
        1,
    )
    else {
        unreachable!()
    };

    // overwrite rd/mem
    let memwrite_addr =
        core::array::from_fn(|i| cs.add_named_variable(&format!("memwrite_addr[{i}]")));
    {
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let value = placer.get_oracle_u32(Placeholder::ShuffleRamAddress(2));
            placer.assign_u32_from_u16_parts(memwrite_addr, &value);
        };
        cs.set_values(value_fn);
    }
    let MemoryAccess::RegisterOrRam(RegisterOrRamAccess {
        read_value: WordRepresentation::U16Limbs(_oldread),
        write_value: WordRepresentation::U16Limbs(memwrite),
        ..
    }) = cs.request_mem_access(
        MemoryAccessRequest::RegisterOrRamReadWrite {
            is_register: is_load,
            address: memwrite_addr,
            read_value_placeholder: Placeholder::ShuffleRamReadValue(2),
            write_value_placeholder: Placeholder::ShuffleRamWriteValue(2),
            split_read_as_u8: false,
            split_write_as_u8: false,
        },
        "mem/rd write",
        2,
    )
    else {
        unreachable!()
    };

    let cleanaddr = {
        // first we gotta enforce the register address
        let load = Constraint::from(is_load);
        let store = Constraint::from(is_store);
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
        let shift16_inv = Term::from_field(F::from_u32(1 << 16).unwrap().inverse().unwrap());
        let of_lo = shift16_inv.clone() * (rs1_lo + imm_lo - cleanaddr_lo.clone());
        let of_hi = shift16_inv * (of_lo.clone() + rs1_hi + imm_hi - cleanaddr_hi.clone());
        // push them to the next layer and constraint there
        assert_eq!(of_lo.degree(), 2);
        assert_eq!(of_hi.degree(), 2);

        let layer_2_copied_of_lo =
            Term::from(cs.add_intermediate_named_variable_from_constraint(of_lo, "addr: ofL (L2)"));
        let layer_2_copied_of_hi =
            Term::from(cs.add_intermediate_named_variable_from_constraint(of_hi, "addr: ofH (L2)"));
        cs.add_constraint(layer_2_copied_of_lo.clone() * (Term::from(1) - layer_2_copied_of_lo)); // booleanity of overflow (low)
        cs.add_constraint(layer_2_copied_of_hi.clone() * (Term::from(1) - layer_2_copied_of_hi)); // booleanity of overflow (high)
        [cleanaddr_lo, cleanaddr_hi]
    };
    let (is_rom, romaddr) = {
        let is_rom = cs.add_named_boolean_variable("flag: are we in rom addr range?");
        let rom = Term::from(is_rom);
        // whether it's a ROM access or not is decided by comparing high part
        // of the address with 2^ROM_SECOND_WORD_BITS constant via subtraction with carry
        // effectively
        let [cleanaddr_lo, cleanaddr_hi] = cleanaddr;
        {
            // explicit wit.gen
            let cleanaddr_hi = cleanaddr_hi.clone();
            let value_fn = move |placer: &mut CS::WitnessPlacer| {
                let cleanaddr_hi = cleanaddr_hi.evaluate_with_placer(placer);
                let extrabits = cleanaddr_hi
                    .as_integer()
                    .shr(common_constants::ROM_SECOND_WORD_BITS as u32);
                let rom = extrabits.is_zero();
                placer.assign_mask(is_rom.get_variable().unwrap(), &rom);
            };
            cs.set_values(value_fn);
        }
        let shift16 = Term::from(1 << 16);
        let shiftromaddr_hi = Term::from(1 << common_constants::ROM_SECOND_WORD_BITS);
        let residue = cleanaddr_hi.clone() - shiftromaddr_hi + shift16 * rom;
        assert_eq!(residue.degree(), 2);
        let layer_2_copied_residue =
            cs.add_intermediate_named_variable_from_constraint(residue, "residue (L2)");
        cs.require_invariant_from_lookup_input(
            LookupInput::from(layer_2_copied_residue),
            Invariant::RangeChecked { width: 16 },
        );
        // trap store*rom
        cs.add_constraint(Constraint::from(is_rom) * Constraint::from(is_store));
        (is_rom, cleanaddr_lo + shift16 * cleanaddr_hi)
    };

    // now we may proceed with our "write" calculations
    // WRITE == memread | STORE*!ROM
    //          trap    | STORE*ROM
    //          romread | LOAD*ROM
    //          memread | LOAD*!ROM
    //       == romread | LOAD*ROM
    //          memread | else
    //       == romread | ROM
    //          memread | else
    // NB: we just hide it all in one lookup like we did for the subword circuit
    {
        let [memread_lo, memread_hi] = memread.map(Constraint::from);
        let [memwrite_lo, memwrite_hi] = memwrite.map(Constraint::from);
        let rom = Constraint::from(is_rom);
        let not_rom = Constraint::from(is_rom.toggle());

        let layer_2_copied_is_rom =
            Term::from(cs.add_intermediate_named_variable_from_constraint(rom, "ROM (L2)"));
        let layer_3_selected_input = {
            let layer_2_copied_romaddr = Term::from(
                cs.add_intermediate_named_variable_from_constraint(romaddr, "romaddr (L2)"),
            );
            let input = layer_2_copied_is_rom * layer_2_copied_romaddr;
            cs.add_intermediate_named_variable_from_constraint(input, "final lookup input (L3)")
        };
        let layer_3_selected_output1 = {
            let output1 = memwrite_lo - not_rom.clone() * memread_lo;
            let L2_output1 = Constraint::from(cs.add_intermediate_named_variable_from_constraint(
                output1,
                "final lookup output1 (L2)",
            ));
            cs.add_intermediate_named_variable_from_constraint(
                L2_output1,
                "final lookup output1 (L3)",
            )
        };
        let layer_3_selected_output2 = {
            let output2 = memwrite_hi - not_rom * memread_hi;
            let layer_2_copied_output2 =
                Constraint::from(cs.add_intermediate_named_variable_from_constraint(
                    output2,
                    "final lookup output2 (L2)",
                ));
            cs.add_intermediate_named_variable_from_constraint(
                layer_2_copied_output2,
                "final lookup output2 (L3)",
            )
        };
        let layer_3_selected_table_id = {
            let romread_table = Term::from(TableType::RomRead.to_num());
            let layer_2_copied_execute =
                Constraint::from(cs.add_intermediate_named_variable_from_constraint(
                    Constraint::from(inputs.execute),
                    "execute (L2)",
                ));
            // NB: to avoid scenarios where romread!=0 but we're in padding so ROM==1 and memwrite==0,
            // we patch this to zero table
            let table_id = layer_2_copied_execute * layer_2_copied_is_rom * romread_table;
            cs.add_intermediate_named_variable_from_constraint(
                table_id,
                "final lookup table_id (L3)",
            )
        };
        let tuple = [
            LookupInput::from(layer_3_selected_input),
            LookupInput::from(layer_3_selected_output1),
            LookupInput::from(layer_3_selected_output2),
        ];
        cs.enforce_lookup_tuple_for_variable_table(&tuple, layer_3_selected_table_id);
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
    let (input, bitmask) =
        cs.allocate_machine_state(false, false, WORD_ONLY_MEMORY_FAMILY_NUM_FLAGS);
    let bitmask: [_; WORD_ONLY_MEMORY_FAMILY_NUM_FLAGS] = bitmask.try_into().unwrap();
    let bitmask = bitmask.map(|el| Boolean::Is(el));
    let decoder = WordOnlyMemoryFamilyCircuitMask::from_mask(bitmask);
    apply_mem_word_only_inner(cs, input, decoder);
}

#[cfg(test)]
mod test {
    use test_utils::skip_if_ci;

    use super::*;
    use crate::gkr_compiler::{
        compile_unrolled_circuit_state_transition_into_gkr, dump_ssa_witness_eval_form,
    };
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
                >(&[])
                {
                    cs.add_table_with_content(table_type, table);
                }
            },
            &|cs| mem_word_only_circuit_with_preprocessed_bytecode_for_gkr(cs),
            common_constants::ROM_WORD_SIZE,
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
                >(&[])
                {
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
