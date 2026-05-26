use super::*;
use crate::cs::circuit_trait::*;
use crate::oracle::Placeholder;
use crate::structured_expr::Expr;
use crate::tables::TableDriver;
use crate::types::*;
use crate::witness_placer::*;
use field::PrimeField;

const TABLES_TOTAL_WIDTH: usize = 3; // TODO: strict enough?

pub fn mem_subword_only_tables() -> Vec<TableType> {
    vec![
        // all the ROM tables are initialised with a special method, tests use dummy ROM bytecode
        TableType::ZeroEntry, // we need it, as we use conditional lookup enforcements
        TableType::StoreByteExistingContribution, // "clear" table (2^17)
        // TableType::LoadHalfwordRomRead, // ROM*H table (2^22)
        // TableType::LoadByteRomRead, // ROM*B table (2^23)
        TableType::LoadHalfwordSignextend, // RAM*H table (2^17)
        TableType::LoadByteSignextend,     // RAM*B table (2^18)
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
) -> [(TableType, crate::tables::LookupWrapper<F>); 2] {
    use crate::tables::{create_load_byte_from_rom_table, create_load_halfword_from_rom_table};

    let id = TableType::LoadHalfwordRomRead.to_table_id();
    let rom_halfword_table =
        crate::tables::LookupWrapper::Initialized(create_load_halfword_from_rom_table::<
            F,
            ROM_ADDRESS_SPACE_SECOND_WORD_BITS,
        >(bytecode, id));

    let id = TableType::LoadByteRomRead.to_table_id();
    let rom_byte_table =
        crate::tables::LookupWrapper::Initialized(create_load_byte_from_rom_table::<
            F,
            ROM_ADDRESS_SPACE_SECOND_WORD_BITS,
        >(bytecode, id));

    [
        (TableType::LoadHalfwordRomRead, rom_halfword_table),
        (TableType::LoadByteRomRead, rom_byte_table),
    ]
}

// TODO: this circuit would benefit from the separation of mem accesses according to reg/ram:
// - intermediate layer logic would be reduced (small memory saving)
// - +1 variable saving for the high address limb of the register-only access
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

    let is_store = decoder.perform_write();
    let is_load = is_store.toggle();
    let is_byte = decoder.perform_byte_operation();
    let is_halfword = is_byte.toggle();
    let is_sext = decoder.perform_sign_extension();

    // we allocate variables that are memory queries addresses, and constraint equality
    // instead of selecting them for convenience

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
        read_value: WordRepresentation::U16Limbs(oldread),
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

    let (cleanaddr, offset_bits) = {
        // first we gotta enforce the register address
        let load = Expr::<F>::from(is_load);
        let store = Expr::<F>::from(is_store);
        let [readaddr_lo, readaddr_hi] = memread_addr.map(Expr::var);
        let [writeaddr_lo, writeaddr_hi] = memwrite_addr.map(Expr::var);
        // lower part of the address in case it should be register
        cs.add_constraint_expr(
            store.clone() * (readaddr_lo.clone() - Expr::var(inputs.decoder_data.rs2_index))
                + load.clone() * (writeaddr_lo.clone() - Expr::var(inputs.decoder_data.rd_index)),
        );
        // higher part of the address in case it should be register - it should be 0
        cs.add_constraint_expr(
            store.clone() * readaddr_hi.clone() + load.clone() * writeaddr_hi.clone(),
        );

        // now we can enforce the ram address
        let [rs1_lo, rs1_hi] = rs1.map(Expr::var);
        let [imm_lo, imm_hi] = inputs.decoder_data.imm.map(Expr::var);
        let cleanaddr_lo = load.clone() * readaddr_lo + store.clone() * writeaddr_lo;
        let cleanaddr_hi = load * readaddr_hi + store * writeaddr_hi;
        let is_bit0 = cs.add_named_boolean_variable("address bit0");
        let is_bit1 = cs.add_named_boolean_variable("address bit1");
        let b0 = Expr::<F>::from(is_bit0);
        let b1 = Expr::<F>::from(is_bit1);
        {
            // explicit wit.gen
            let value_fn = move |placer: &mut CS::WitnessPlacer| {
                let rs1_lo = placer.get_u16(rs1[0]);
                let imm_lo = placer.get_u16(inputs.decoder_data.imm[0]);
                let (addr_lo, _of_lo) = rs1_lo.overflowing_add(&imm_lo);
                let bit0 = addr_lo.get_bit(0);
                let bit1 = addr_lo.get_bit(1);
                placer.assign_mask(is_bit0.get_variable().unwrap(), &bit0);
                placer.assign_mask(is_bit1.get_variable().unwrap(), &bit1);
            };
            cs.set_values(value_fn);
        }
        let shift16_inv = F::from_u32(1 << 16).unwrap().inverse().unwrap();
        let of_lo = (rs1_lo + imm_lo - cleanaddr_lo.clone() - b0 - Expr::<F>::from(2u32) * b1)
            * shift16_inv;

        // check booleanity of carry bits

        // push to the intermedaite and constraint there
        assert_eq!(of_lo.degree(), 2);
        let next_layer_copied_of_lo = Expr::<F>::var(
            cs.add_intermediate_named_variable_from_expr(of_lo.clone(), "addr ofL (L2)"),
        );
        cs.add_constraint_expr(
            next_layer_copied_of_lo.clone() * (Expr::<F>::one() - next_layer_copied_of_lo),
        ); // booleanity of overflow (low)

        let of_hi = (of_lo.clone() + rs1_hi + imm_hi - cleanaddr_hi.clone()) * shift16_inv;
        assert_eq!(of_hi.degree(), 2);
        let next_layer_copied_of_hi =
            Expr::<F>::var(cs.add_intermediate_named_variable_from_expr(of_hi, "addr ofH (L2)"));
        cs.add_constraint_expr(
            next_layer_copied_of_hi.clone() * (Expr::<F>::one() - next_layer_copied_of_hi),
        ); // booleanity of overflow (high)

        // trap halfword*b0
        cs.add_constraint_expr(Expr::<F>::from(is_halfword) * Expr::from(is_bit0));
        ([cleanaddr_lo, cleanaddr_hi], [is_bit0, is_bit1])
    };
    let (is_rom, rom_addr) = {
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
        let shiftromaddr_hi =
            F::from_u32_with_reduction(1 << common_constants::ROM_SECOND_WORD_BITS);
        let residue = cleanaddr_hi.clone() - Expr::constant(shiftromaddr_hi)
            + Expr::<F>::from(is_rom) * shift16;
        assert_eq!(residue.degree(), 2);
        let next_layer_copied_residue =
            cs.add_intermediate_named_variable_from_expr(residue, "residue (L2)");
        cs.require_invariant_from_lookup_input(
            LookupInput::from(next_layer_copied_residue),
            Invariant::RangeChecked { width: 16 },
        );
        // trap store*rom
        cs.add_constraint_expr(Expr::<F>::from(is_rom) * Expr::from(is_store));
        (is_rom, cleanaddr_lo + cleanaddr_hi * shift16)
    };

    // now we may proceed with our "write" calculations
    // due to SB opcode limitations, we will be creating 1 new witness variable "clear" (plus lookup)
    let clear = {
        let clear = cs.add_named_variable("clear (SB: mem[addr] halfword byte gets set to 0)");
        let [oldread_lo, oldread_hi] = oldread.map(Expr::var);
        let [b0, b1] = offset_bits.map(Expr::<F>::from);
        let shift16 = F::from_u32_with_reduction(1 << 16);
        let selected_oldread_halfword =
            b1.clone() * oldread_hi + (Expr::<F>::one() - b1) * oldread_lo;
        let input = selected_oldread_halfword + b0 * shift16;
        {
            // extra explicit wit.gen due to L1->L2 transition
            let input_constraint = input.clone().to_max_quadratic_constraint();
            let inputs = &[input_constraint];
            let output_variables = &[clear];
            let table_type = Expr::<F>::from(TableType::StoreByteExistingContribution)
                .to_max_quadratic_constraint();
            cs::lookup_utils::peek_lookup_values_unconstrained_into_variables_from_constraints(
                cs,
                inputs,
                output_variables,
                table_type,
            );
        }
        assert_eq!(input.degree(), 2);
        let next_layer_copied_input = cs.add_intermediate_named_variable_from_expr(
            input,
            "STORE*B: clear's table input: SEL(b1, OLDH, OLDL) || b0 (L2)",
        );
        let next_layer_copied_clear =
            cs.add_intermediate_named_variable_from_expr(Expr::var(clear), "clear (L2)");
        let tuple = [
            LookupInput::from(next_layer_copied_input),
            LookupInput::from(next_layer_copied_clear),
        ];
        cs.enforce_lookup_tuple_for_fixed_table(
            &tuple,
            TableType::StoreByteExistingContribution,
            false,
        );
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
        let rom = Expr::<F>::from(is_rom);
        let ram = Expr::<F>::from(is_load) - rom.clone();
        let store = Expr::<F>::from(is_store);
        let s = Expr::<F>::from(is_sext);
        let b = Expr::<F>::from(is_byte);
        let h = Expr::<F>::one() - b.clone();
        let rom_halfword = rom.clone() * h.clone();
        let rom_byte = rom.clone() * b.clone();
        let ram_halfword = ram.clone() * h.clone();
        let ram_byte = ram.clone() * b.clone();
        let store_byte = store.clone() * b.clone();
        let [b0, b1] = offset_bits.map(Expr::<F>::from);
        let [oldread_lo, oldread_hi] = oldread.map(Expr::var);
        let [memread_lo, memread_hi] = memread.map(Expr::var);
        let [memwrite_lo, memwrite_hi] = memwrite.map(Expr::var);
        let selected_memread_halfword =
            b1.clone() * memread_hi + (Expr::<F>::one() - b1.clone()) * memread_lo.clone();
        let selected_memwrite_halfword = b1.clone() * memwrite_hi.clone()
            + (Expr::<F>::one() - b1.clone()) * memwrite_lo.clone();
        let constrained_memwrite_halfword = b1.clone() * (memwrite_lo.clone() - oldread_lo)
            + (Expr::<F>::one() - b1.clone()) * (memwrite_hi.clone() - oldread_hi);
        let rs2_lo = memread_lo;
        let keep =
            selected_memwrite_halfword - b.clone() * Expr::var(clear) - h.clone() * rs2_lo.clone();

        let layer_2_copied_rom =
            Expr::<F>::var(cs.add_intermediate_named_variable_from_expr(rom, "rom (L2)"));
        let layer_2_copied_ram =
            Expr::<F>::var(cs.add_intermediate_named_variable_from_expr(ram, "ram (L2)"));
        let layer_2_copied_store =
            Expr::<F>::var(cs.add_intermediate_named_variable_from_expr(store, "store (L2)"));
        let layer_2_copied_load = layer_2_copied_rom.clone() + layer_2_copied_ram.clone();
        let layer_3_selected_input = {
            let shiftrom =
                F::from_u32_with_reduction(1 << (16 + common_constants::ROM_SECOND_WORD_BITS));
            let shiftrom1 =
                F::from_u32_with_reduction(1 << (16 + common_constants::ROM_SECOND_WORD_BITS + 1));
            let shiftrom2 =
                F::from_u32_with_reduction(1 << (16 + common_constants::ROM_SECOND_WORD_BITS + 2));
            let shift16 = F::from_u32_with_reduction(1 << 16);
            let shift17 = F::from_u32_with_reduction(1 << 17);
            let rom_input = rom_addr.clone()
                + s.clone() * shiftrom
                + b1.clone() * shiftrom1
                + b0.clone() * shiftrom2;
            let ram_input = selected_memread_halfword + s * shift16 + b0.clone() * shift17;
            let store_bytemask_input = b * (rs2_lo + b0 * shift16);
            let next_layer_copied_rom_input = Expr::<F>::var(
                cs.add_intermediate_named_variable_from_expr(rom_input, "rom_input (L2)"),
            );
            let next_layer_copied_ram_input = Expr::<F>::var(
                cs.add_intermediate_named_variable_from_expr(ram_input, "ram_input (L2)"),
            );
            let next_layer_copied_store_bytemasked_input =
                Expr::<F>::var(cs.add_intermediate_named_variable_from_expr(
                    store_bytemask_input,
                    "store_bytemasked_input (L2)",
                ));
            let input = layer_2_copied_rom * next_layer_copied_rom_input
                + layer_2_copied_ram * next_layer_copied_ram_input
                + layer_2_copied_store.clone() * next_layer_copied_store_bytemasked_input;
            cs.add_intermediate_named_variable_from_expr(input, "final lookup input (L3)")
        };
        let layer_3_selected_output1 = {
            let layer_2_copied_memwrite_lo = Expr::<F>::var(
                cs.add_intermediate_named_variable_from_expr(memwrite_lo, "memwrite_lo (L2)"),
            );
            let layer_2_copied_keep =
                Expr::<F>::var(cs.add_intermediate_named_variable_from_expr(keep, "keep (L2)"));
            let output1 = layer_2_copied_load.clone() * layer_2_copied_memwrite_lo
                + layer_2_copied_store.clone() * layer_2_copied_keep;
            cs.add_intermediate_named_variable_from_expr(output1, "final lookup output1 (L3)")
        };
        let layer_3_selected_output2 = {
            let layer_2_copied_memwrite_hi = Expr::<F>::var(
                cs.add_intermediate_named_variable_from_expr(memwrite_hi, "memwrite_hi (L2)"),
            );
            let layer_2_copied_constrained_memwrite_halfword =
                Expr::<F>::var(cs.add_intermediate_named_variable_from_expr(
                    constrained_memwrite_halfword,
                    "constrained_memwrite_halfword (L2)",
                ));
            let output2 = layer_2_copied_load * layer_2_copied_memwrite_hi
                + layer_2_copied_store * layer_2_copied_constrained_memwrite_halfword;
            cs.add_intermediate_named_variable_from_expr(output2, "final lookup output2 (L3)")
        };
        let layer_3_selected_table_id = {
            // NB: missing storehalfword masks to ZeroEntry table. a crucial mask!
            let table_id = rom_halfword * Expr::<F>::from(TableType::LoadHalfwordRomRead)
                + rom_byte * Expr::<F>::from(TableType::LoadByteRomRead)
                + ram_halfword * Expr::<F>::from(TableType::LoadHalfwordSignextend)
                + ram_byte * Expr::<F>::from(TableType::LoadByteSignextend)
                + store_byte * Expr::<F>::from(TableType::StoreByteSourceContribution);
            let layer_2_copied_table_id = Expr::<F>::var(
                cs.add_intermediate_named_variable_from_expr(table_id, "table_id (L2)"),
            );
            let layer_2_copied_execute =
                Expr::<F>::var(cs.add_intermediate_named_variable_from_expr(
                    Expr::var(inputs.execute),
                    "execute (L2)",
                ));
            // NB: to avoid scenarios where romread!=0 but we're in padding so ROM*H==1 and memwrite==0,
            // we patch this to zero table
            cs.add_intermediate_named_variable_from_expr(
                layer_2_copied_execute * layer_2_copied_table_id,
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

pub fn mem_subword_only_circuit_with_preprocessed_bytecode_for_gkr<
    F: PrimeField,
    CS: Circuit<F>,
>(
    cs: &mut CS,
) {
    let (input, bitmask) =
        cs.allocate_machine_state(false, false, SUBWORD_ONLY_MEMORY_FAMILY_NUM_FLAGS);
    let bitmask: [_; SUBWORD_ONLY_MEMORY_FAMILY_NUM_FLAGS] = bitmask.try_into().unwrap();
    let bitmask = bitmask.map(|el| Boolean::Is(el));
    let decoder = SubwordOnlyMemoryFamilyCircuitMask::from_mask(bitmask);
    apply_mem_subword_only_inner(cs, input, decoder);
}

#[cfg(test)]
mod test {
    use test_utils::skip_if_ci;

    use super::*;
    use crate::cs::circuit_impl::BasicAssembly;
    use crate::cs::circuit_output::CircuitOutput;
    use crate::gkr_compiler::compile_unrolled_circuit_state_transition_into_unrolled_gkr_without_caches;
    use crate::gkr_compiler::{
        compile_unrolled_circuit_state_transition_into_gkr, dump_ssa_witness_eval_form,
    };
    use crate::structured_expr::StructuredStatement;
    use crate::utils::serialize_to_file;

    type F = ::field::Mersenne31Field;

    // fn named_variable(output: &CircuitOutput<F>, expected_name: &str) -> Variable {
    //     output
    //         .variable_names
    //         .iter()
    //         .find_map(|(variable, name)| (name == expected_name).then_some(*variable))
    //         .expect("named variable must exist")
    // }

    // fn defined_expr_for<'a>(output: &'a CircuitOutput<F>, expected_name: &str) -> &'a Expr<F> {
    //     let variable = named_variable(output, expected_name);

    //     output
    //         .structured_statements
    //         .iter()
    //         .find_map(|statement| match statement {
    //             StructuredStatement::Define { dst, expr } if *dst == variable => Some(expr),
    //             StructuredStatement::Define { .. } | StructuredStatement::AssertZero { .. } => None,
    //         })
    //         .expect("named variable must have structured definition")
    // }

    // fn contains_product_with_sum_factor(expr: &Expr<F>) -> bool {
    //     match expr {
    //         Expr::Product(factors) => {
    //             factors.iter().any(|factor| matches!(factor, Expr::Sum(_)))
    //                 || factors.iter().any(contains_product_with_sum_factor)
    //         }
    //         Expr::Sum(terms) => terms.iter().any(contains_product_with_sum_factor),
    //         Expr::Constant(_) | Expr::Var(_) => false,
    //     }
    // }

    // fn contains_shifted_variable(expr: &Expr<F>, shift: F) -> bool {
    //     match expr {
    //         Expr::Product(factors) => {
    //             let has_shift = factors
    //                 .iter()
    //                 .any(|factor| matches!(factor, Expr::Constant(value) if *value == shift));
    //             let has_variable = factors.iter().any(|factor| matches!(factor, Expr::Var(_)));

    //             has_shift && has_variable
    //                 || factors
    //                     .iter()
    //                     .any(|factor| contains_shifted_variable(factor, shift))
    //         }
    //         Expr::Sum(terms) => terms
    //             .iter()
    //             .any(|term| contains_shifted_variable(term, shift)),
    //         Expr::Constant(_) | Expr::Var(_) => false,
    //     }
    // }

    // fn is_sum_of_binary_variable_products(expr: &Expr<F>) -> bool {
    //     fn is_binary_var_product<F: PrimeField>(expr: &Expr<F>) -> bool {
    //         let Expr::Product(factors) = expr else {
    //             return false;
    //         };

    //         factors.len() == 2 && factors.iter().all(|factor| matches!(factor, Expr::Var(_)))
    //     }

    //     let Expr::Sum(terms) = expr else {
    //         return false;
    //     };

    //     terms.len() == 3 && terms.iter().all(is_binary_var_product)
    // }

    // #[test]
    // fn mem_subword_only_records_structured_lookup_parentheses() {
    //     let mut cs = BasicAssembly::<F>::new();
    //     mem_subword_only_circuit_with_preprocessed_bytecode_for_gkr(&mut cs);
    //     let (output, _) = cs.finalize();

    //     let clear_table_input = defined_expr_for(
    //         &output,
    //         "STORE*B: clear's table input: SEL(b1, OLDH, OLDL) || b0 (L2)",
    //     );
    //     let store_bytemasked_input = defined_expr_for(&output, "store_bytemasked_input (L2)");
    //     let final_lookup_input = defined_expr_for(&output, "final lookup input (L3)");
    //     let shift16 = F::from_u32_with_reduction(1 << 16);

    //     assert!(contains_product_with_sum_factor(clear_table_input));
    //     assert!(contains_product_with_sum_factor(store_bytemasked_input));
    //     assert!(contains_shifted_variable(store_bytemasked_input, shift16));
    //     assert!(is_sum_of_binary_variable_products(final_lookup_input));
    // }

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
                >(&[])
                {
                    cs.add_table_with_content(table_type, table);
                }
            },
            &|cs| mem_subword_only_circuit_with_preprocessed_bytecode_for_gkr(cs),
            common_constants::ROM_WORD_SIZE,
            24,
        );

        serialize_to_file(
            &gkr_compiled,
            "compiled_circuits/mem_subword_only_layout_gkr.json",
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
                >(&[])
                {
                    cs.add_table_with_content(table_type, table);
                }
            },
            &|cs| mem_subword_only_circuit_with_preprocessed_bytecode_for_gkr(cs),
        );
        serialize_to_file(
            &ssa_forms,
            "compiled_circuits/mem_subword_only_ssa_gkr.json",
        );
    }

    #[test]
    fn compile_mem_subword_only_circuit_into_no_caches_gkr() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let gkr_compiled =
            compile_unrolled_circuit_state_transition_into_unrolled_gkr_without_caches::<
                BabyBearField,
            >(
                &|cs| {
                    mem_subword_only_table_addition_fn(cs);
                    // ROM tables must be added here (with dummy bytecode) so that
                    // offset_for_decoder_table in the compiled JSON reflects the correct
                    // total_tables_len at prove time, when real ROM tables are present.
                    for (table_type, table) in create_mem_subword_only_special_tables::<
                        BabyBearField,
                        { common_constants::ROM_SECOND_WORD_BITS },
                    >(&[])
                    {
                        cs.add_table_with_content(table_type, table);
                    }
                },
                &|cs| mem_subword_only_circuit_with_preprocessed_bytecode_for_gkr(cs),
                common_constants::ROM_WORD_SIZE,
                24,
            );

        serialize_to_file(
            &gkr_compiled,
            "compiled_circuits/mem_subword_only_layout_no_caches_gkr.json",
        );
    }
}
