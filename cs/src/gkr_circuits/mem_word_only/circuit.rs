use super::*;
use crate::cs::circuit_trait::*;
use crate::oracle::Placeholder;
use crate::structured_expr::Expr;
use crate::tables::TableDriver;
use crate::types::*;
use crate::witness_placer::*;
use field::PrimeField;

const TABLES_TOTAL_WIDTH: usize = 3;

fn table_id_expr<F: PrimeField>(table_type: TableType) -> Expr<F> {
    Expr::constant(F::from_u32(table_type as u32).expect("must fit"))
}

pub fn mem_word_only_tables() -> Vec<TableType> {
    vec![
        // all rom tables gotta be added in the prover code when bytecode data is available
        TableType::ZeroEntry, // we need it for romread's conditional lookup enforcement

                              // TableType::AlignedRomRead
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
    use crate::tables::create_table_for_word_aligned_rom_image;

    let id = TableType::AlignedRomRead.to_table_id();
    let rom_table =
        crate::tables::LookupWrapper::Initialized(create_table_for_word_aligned_rom_image::<
            F,
            ROM_ADDRESS_SPACE_SECOND_WORD_BITS,
        >(bytecode, id));

    [(TableType::AlignedRomRead, rom_table)]
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

    // NOTE on both addresses below: we allocate them from witness and assume range-checked limbs.
    // We can do so by induction: if memory argument passes, then:
    // - if timestamp inequiaities are enforced
    // - and initial set of addresses (inits) is range checked by construction, and so are teardowns
    // - then for memory argument to pass we can not have intermediate non-range checked read + write pairs
    // as there is no init and teardown for them

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
            is_register: is_store, // if the boolean value is 1, then address space is "register" == 0
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
            is_register: is_load, // if the boolean value is 1, then address space is "register" == 0
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
        let load = Expr::<F>::from(is_load);
        let store = Expr::<F>::from(is_store);
        let [readaddr_lo, readaddr_hi] = memread_addr.map(Expr::var);
        let [writeaddr_lo, writeaddr_hi] = memwrite_addr.map(Expr::var);
        cs.add_constraint_expr(
            store.clone() * (readaddr_lo.clone() - Expr::var(inputs.decoder_data.rs2_index))
                + load.clone() * (writeaddr_lo.clone() - Expr::var(inputs.decoder_data.rd_index)),
        );
        cs.add_constraint_expr(
            store.clone() * readaddr_hi.clone() + load.clone() * writeaddr_hi.clone(),
        );

        // now we can enforce the ram address
        let [rs1_lo, rs1_hi] = rs1.map(Expr::var);
        let [imm_lo, imm_hi] = inputs.decoder_data.imm.map(Expr::var);
        let cleanaddr_lo = load.clone() * readaddr_lo + store.clone() * writeaddr_lo;
        let cleanaddr_hi = load * readaddr_hi + store * writeaddr_hi;
        let shift16_inv = F::from_u32(1 << 16).unwrap().inverse().unwrap();
        let of_lo = (rs1_lo + imm_lo - cleanaddr_lo.clone()) * shift16_inv;
        let of_hi = (of_lo.clone() + rs1_hi + imm_hi - cleanaddr_hi.clone()) * shift16_inv;
        // push them to the next layer and constraint there
        assert_eq!(of_lo.degree(), 2);
        assert_eq!(of_hi.degree(), 2);

        let layer_2_copied_of_lo =
            cs.add_intermediate_named_variable_from_expr(of_lo, "addr: ofL (L2)");
        let layer_2_copied_of_hi =
            cs.add_intermediate_named_variable_from_expr(of_hi, "addr: ofH (L2)");
        let layer_2_copied_of_lo = Expr::var(layer_2_copied_of_lo);
        let layer_2_copied_of_hi = Expr::var(layer_2_copied_of_hi);
        // booleanity of overflow (low)
        cs.add_constraint_expr(
            layer_2_copied_of_lo.clone() * (Expr::<F>::one() - layer_2_copied_of_lo),
        );
        // booleanity of overflow (high)
        cs.add_constraint_expr(
            layer_2_copied_of_hi.clone() * (Expr::<F>::one() - layer_2_copied_of_hi),
        );
        [cleanaddr_lo, cleanaddr_hi]
    };
    let (is_rom_base_layer, rom_addr_constraint) = {
        let is_rom = cs.add_named_boolean_variable("flag: are we in rom addr range?");
        // whether it's a ROM access or not is decided by comparing high part
        // of the address with 2^ROM_SECOND_WORD_BITS constant via subtraction with carry
        // effectively
        let [cleanaddr_lo, cleanaddr_hi] = cleanaddr;
        {
            // explicit wit.gen
            let cleanaddr_hi = cleanaddr_hi.clone().to_max_quadratic_constraint();
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
        let shift16 = F::from_u32_with_reduction(1 << 16);
        let rom_bound_high =
            F::from_u32_with_reduction(1 << common_constants::ROM_SECOND_WORD_BITS);
        // addr_hi < `1 << common_constants::ROM_SECOND_WORD_BITS` via subtraction, and `rom` is carry
        let residue = Expr::<F>::from(is_rom) * shift16 + cleanaddr_hi.clone()
            - Expr::constant(rom_bound_high);
        assert_eq!(residue.degree(), 2);
        let layer_2_copied_residue =
            cs.add_intermediate_named_variable_from_expr(residue, "residue (L2)");
        // it's enough to check that subtraction result is range checked
        cs.require_invariant_from_lookup_input(
            LookupInput::from(layer_2_copied_residue),
            Invariant::RangeChecked { width: 16 },
        );
        // trap store*rom
        cs.add_constraint_expr(Expr::<F>::from(is_rom) * Expr::from(is_store));
        (is_rom, cleanaddr_lo + cleanaddr_hi * shift16)
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
        let [memread_lo, memread_hi] = memread.map(Expr::var);
        let [memwrite_lo, memwrite_hi] = memwrite.map(Expr::var);
        let rom = Expr::<F>::from(is_rom_base_layer);
        let not_rom = Expr::<F>::from(is_rom_base_layer.toggle());

        let layer_2_copied_is_rom = cs.add_intermediate_named_variable_from_expr(rom, "ROM (L2)");
        let layer_3_selected_input = {
            assert_eq!(rom_addr_constraint.degree(), 2);
            let layer_2_copied_rom_addr =
                cs.add_intermediate_named_variable_from_expr(rom_addr_constraint, "romaddr (L2)");
            let input = Expr::var(layer_2_copied_is_rom) * Expr::var(layer_2_copied_rom_addr);
            cs.add_intermediate_named_variable_from_expr(input, "final lookup input (L3)")
        };
        let layer_3_selected_output1 = {
            let output1 = memwrite_lo - not_rom.clone() * memread_lo;
            let L2_output1 =
                cs.add_intermediate_named_variable_from_expr(output1, "final lookup output1 (L2)");
            cs.add_intermediate_named_variable_from_expr(
                Expr::var(L2_output1),
                "final lookup output1 (L3)",
            )
        };
        let layer_3_selected_output2 = {
            let output2 = memwrite_hi - not_rom * memread_hi;
            let layer_2_copied_output2 =
                cs.add_intermediate_named_variable_from_expr(output2, "final lookup output2 (L2)");
            cs.add_intermediate_named_variable_from_expr(
                Expr::var(layer_2_copied_output2),
                "final lookup output2 (L3)",
            )
        };
        let layer_3_selected_table_id = {
            let layer_2_copied_execute = cs.add_intermediate_named_variable_from_expr(
                Expr::var(inputs.execute),
                "execute (L2)",
            );
            // NB: to avoid scenarios where romread!=0 but we're in padding so ROM==1 and memwrite==0,
            // we patch this to zero table
            let table_id = Expr::var(layer_2_copied_execute)
                * Expr::var(layer_2_copied_is_rom)
                * table_id_expr::<F>(TableType::AlignedRomRead);
            cs.add_intermediate_named_variable_from_expr(table_id, "final lookup table_id (L3)")
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
    use crate::cs::circuit_impl::BasicAssembly;
    use crate::gkr_compiler::compile_unrolled_circuit_state_transition_into_unrolled_gkr_without_caches;
    use crate::gkr_compiler::{
        compile_unrolled_circuit_state_transition_into_gkr, dump_ssa_witness_eval_form,
    };
    use crate::structured_expr::StructuredStatement;
    use crate::utils::serialize_to_file;

    type F = ::field::Mersenne31Field;

    fn named_variable(
        output: &crate::cs::circuit_output::CircuitOutput<F>,
        expected_name: &str,
    ) -> Variable {
        output
            .variable_names
            .iter()
            .find_map(|(variable, name)| (name == expected_name).then_some(*variable))
            .expect("named variable must exist")
    }

    fn contains_shifted_address_limb(expr: &Expr<F>) -> bool {
        let shift16 = F::from_u32_with_reduction(1 << 16);

        match expr {
            Expr::Product(factors) => {
                let has_shift = factors
                    .iter()
                    .any(|factor| matches!(factor, Expr::Constant(value) if *value == shift16));
                let has_selected_limb = factors
                    .iter()
                    .any(|factor| matches!(factor, Expr::Sum(terms) if terms.len() >= 2));

                has_shift && has_selected_limb || factors.iter().any(contains_shifted_address_limb)
            }
            Expr::Sum(terms) => terms.iter().any(contains_shifted_address_limb),
            Expr::Constant(_) | Expr::Var(_) => false,
        }
    }

    fn is_product_of_two_variables(expr: &Expr<F>) -> bool {
        matches!(
            expr,
            Expr::Product(factors)
                if factors.len() == 2 && factors.iter().all(|factor| matches!(factor, Expr::Var(_)))
        )
    }

    #[test]
    fn mem_word_only_records_structured_rom_lookup_path() {
        let mut cs = BasicAssembly::<F>::new();
        mem_word_only_circuit_with_preprocessed_bytecode_for_gkr(&mut cs);
        let (output, _) = cs.finalize();

        let romaddr = named_variable(&output, "romaddr (L2)");
        let final_lookup_input = named_variable(&output, "final lookup input (L3)");

        assert!(output
            .structured_statements
            .iter()
            .any(|statement| matches!(
                statement,
                StructuredStatement::Define { dst, expr }
                    if *dst == romaddr && contains_shifted_address_limb(expr)
            )));
        assert!(output
            .structured_statements
            .iter()
            .any(|statement| matches!(
                statement,
                StructuredStatement::Define { dst, expr }
                    if *dst == final_lookup_input && is_product_of_two_variables(expr)
            )));
    }

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
            "compiled_circuits/mem_word_only_layout_gkr.json",
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
        serialize_to_file(&ssa_forms, "compiled_circuits/mem_word_only_ssa_gkr.json");
    }

    #[test]
    fn compile_mem_word_only_circuit_into_no_caches_gkr() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let gkr_compiled =
            compile_unrolled_circuit_state_transition_into_unrolled_gkr_without_caches::<
                BabyBearField,
            >(
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
            "compiled_circuits/mem_word_only_layout_no_caches_gkr.json",
        );
    }
}
