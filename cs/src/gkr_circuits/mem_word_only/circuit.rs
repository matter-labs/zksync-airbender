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

/// accepts pre-allocated rs1 U8 limbs and the two
/// `RegisterOrRam` accesses (memread, memwrite) for the rs2/mem and rd/mem slots.
/// Caller (standalone wrapper or unified body) is responsible for allocating
/// the `memread_addr` / `memwrite_addr` witness vars and passing them inside the
/// access objects.
///
/// Two Booleans control gating:
/// - `is_lw` = 1 iff Family 4 LW fires (memread = RAM, memwrite = rd register).
/// - `is_sw` = 1 iff Family 4 SW fires (memread = rs2 register, memwrite = RAM).
/// - Both 0 ⇒ a different family fires (or padding); Family-4-specific work
///   (cleanaddr / ROM check / data lookup) gets multiplied by `is_lw + is_sw`
///   so it collapses to 0 = 0.
///
/// Register-side address binding (`memread_addr` to `rs2_index`, `memwrite_addr`
/// to `rd_index`) is gated by `(1 - is_lw)` / `(1 - is_sw)` so it fires for
/// Families 1-3 plus the matching half of Family 4.
#[allow(non_snake_case)]
pub(crate) fn apply_mem_word_only_inner<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    inputs: OpcodeFamilyCircuitState<F>,
    is_lw: Boolean,
    is_sw: Boolean,
    rs1_limbs: [Variable; REGISTER_SIZE * 2],
    memread_access: RegisterOrRamAccess,
    memwrite_access: RegisterOrRamAccess,
) {
    // LW: rd                          <- mem[addr] || rom[addr]  with +0 offset accepted
    // SW: mem[addr] || trap rom[addr] <- rs2                     with +0 offset accepted
    // NOTE: by preprocessing (decoder lookup) we have rd == 0 for loads not possible
    // so we do NOT need to mask rd value

    // U16 views of rs1/memread reassembled from U8 bytes
    let byte_shift = F::from_u32_unchecked(1 << 8);
    let rs1_low_c: Constraint<F> =
        Constraint::from(rs1_limbs[0]) + Term::from((byte_shift, rs1_limbs[1]));
    let rs1_high_c: Constraint<F> =
        Constraint::from(rs1_limbs[2]) + Term::from((byte_shift, rs1_limbs[3]));

    let WordRepresentation::U8Limbs(memread_u8) = memread_access.read_value else {
        unreachable!("memread access must be allocated as U8Limbs")
    };
    let memread_low_c: Constraint<F> =
        Constraint::from(memread_u8[0]) + Term::from((byte_shift, memread_u8[1]));
    let memread_high_c: Constraint<F> =
        Constraint::from(memread_u8[2]) + Term::from((byte_shift, memread_u8[3]));

    let WordRepresentation::U16Limbs(memwrite) = memwrite_access.write_value else {
        unreachable!("memwrite access must be allocated with U16 write limbs")
    };
    let memread_addr = memread_access.address;
    let memwrite_addr = memwrite_access.address;

    let load = Constraint::from(is_lw);
    let store = Constraint::from(is_sw);

    let is_fam4 = cs.add_named_boolean_variable("is_fam4");
    cs.add_constraint_allow_explicit_linear(
        Constraint::from(is_fam4) - load.clone() - store.clone(),
    );

    let [readaddr_lo, readaddr_hi] = memread_addr.map(Term::from);
    let [writeaddr_lo, writeaddr_hi] = memwrite_addr.map(Term::from);

    let memread_is_reg: Constraint<F> = Constraint::from(is_lw.toggle());
    cs.add_constraint(
        memread_is_reg.clone()
            * (readaddr_lo - Term::from(inputs.decoder_data.rs2_index)),
    );
    cs.add_constraint(memread_is_reg * readaddr_hi);

    // memwrite_addr is a register slot for Families 1-3 (rd) and Family 4 LW.
    let memwrite_is_reg: Constraint<F> = Constraint::from(is_sw.toggle());
    cs.add_constraint(
        memwrite_is_reg.clone()
            * (writeaddr_lo - Term::from(inputs.decoder_data.rd_index)),
    );
    cs.add_constraint(memwrite_is_reg * writeaddr_hi);

    // For Family 4 LW the memread address is the RAM address (rs1 + imm).
    // For Family 4 SW the memwrite address is the RAM address (rs1 + imm).
    // For non-Family-4 cycles is_lw and is_sw are both 0 so the constraints below
    // collapse to 0 = 0.
    //
    // We allocate `of_lo` / `of_hi` as fresh L0 booleans (carry bits of rs1+imm in
    // each 16-bit limb) and use the combined form
    //
    //     is_lw * (rs1_lo + imm_lo - memread_addr_lo  - 2^16*of_lo)
    //   + is_sw * (rs1_lo + imm_lo - memwrite_addr_lo - 2^16*of_lo)  =  0
    //
    // which is degree 2 (single Boolean times degree-1 expression). Going through
    // L1 commits would force the gate constraint into degree 3.
    let [imm_var_lo, imm_var_hi] = inputs.decoder_data.imm;
    let imm_lo: Term<F> = imm_var_lo.into();
    let imm_hi: Term<F> = imm_var_hi.into();
    let shift16_term: Term<F> = Term::from(1 << 16);
    let of_lo = cs.add_named_boolean_variable("addr: ofL");
    let of_hi = cs.add_named_boolean_variable("addr: ofH");

    // Witness for of_lo / of_hi: actual carry bits of (rs1 + imm) when Family 4
    // fires, 0 otherwise. The constraints below are gated so the value is unused
    // for non-Family-4 cycles; we still need booleanity.
    let (is_lw_var, is_lw_neg) = is_lw.variable_and_negation_constant();
    let (is_sw_var, is_sw_neg) = is_sw.variable_and_negation_constant();
    {
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let rs1_lo_val =
                placer.get_u16_from_u8_parts([rs1_limbs[0], rs1_limbs[1]]);
            let rs1_hi_val =
                placer.get_u16_from_u8_parts([rs1_limbs[2], rs1_limbs[3]]);
            let imm_lo_val = placer.get_u16(imm_var_lo);
            let imm_hi_val = placer.get_u16(imm_var_hi);
            let (_, carry_lo) = rs1_lo_val.overflowing_add(&imm_lo_val);
            let (_, carry_hi) =
                rs1_hi_val.overflowing_add_with_carry(&imm_hi_val, &carry_lo);

            let is_lw_raw = placer.get_boolean(is_lw_var);
            let is_lw_val = if is_lw_neg {
                is_lw_raw.negate()
            } else {
                is_lw_raw
            };
            let is_sw_raw = placer.get_boolean(is_sw_var);
            let is_sw_val = if is_sw_neg {
                is_sw_raw.negate()
            } else {
                is_sw_raw
            };
            let is_active = is_lw_val.or(&is_sw_val);
            let off = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false);
            let of_lo_val =
                <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(&is_active, &carry_lo, &off);
            let of_hi_val =
                <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(&is_active, &carry_hi, &off);
            placer.assign_mask(of_lo.get_variable().unwrap(), &of_lo_val);
            placer.assign_mask(of_hi.get_variable().unwrap(), &of_hi_val);
            placer.assign_mask(is_fam4.get_variable().unwrap(), &is_active);
        };
        cs.set_values(value_fn);
    }

    // Constraint on of_lo: combined LW + SW form, degree 2.
    let of_lo_term = Term::from(of_lo);
    let of_hi_term = Term::from(of_hi);
    cs.add_constraint(
        load.clone()
            * (rs1_low_c.clone() + imm_lo - readaddr_lo - shift16_term * of_lo_term)
            + store.clone()
                * (rs1_low_c.clone() + imm_lo - writeaddr_lo - shift16_term * of_lo_term),
    );
    // Constraint on of_hi: same shape with the carry from of_lo folded in.
    cs.add_constraint(
        load.clone()
            * (rs1_high_c.clone()
                + imm_hi
                + Term::from(of_lo)
                - readaddr_hi
                - shift16_term * of_hi_term)
            + store.clone()
                * (rs1_high_c.clone()
                    + imm_hi
                    + Term::from(of_lo)
                    - writeaddr_hi
                    - shift16_term * of_hi_term),
    );

    // The "cleanaddr" expression — the RAM address when Family 4 fires, 0 otherwise.
    // Used purely for the ROM check witness + ROM-table lookup index. is_lw / is_sw
    // gating already collapses this to 0 for non-Family-4 cycles.
    let cleanaddr_lo: Constraint<F> = load.clone() * readaddr_lo + store.clone() * writeaddr_lo;
    let cleanaddr_hi: Constraint<F> = load.clone() * readaddr_hi + store.clone() * writeaddr_hi;

    let (is_rom_base_layer, rom_addr_constraint) = {
        let is_rom = cs.add_named_boolean_variable("flag: are we in rom addr range?");
        let rom_term = Term::from(is_rom);
        // whether it's a ROM access or not is decided by comparing high part
        // of the address with 2^ROM_SECOND_WORD_BITS constant via subtraction with carry.
        // For non-Family-4 cycles cleanaddr_hi = 0 < rom_bound_high, so witness gen
        // sets is_rom = 1 and the residue is 2^16 - rom_bound_high (still a 16-bit value).
        // The ROM lookup itself is gated below via the `gate_fam4_rom` helper.
        {
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
        let rom_bound_high = Term::from(1 << common_constants::ROM_SECOND_WORD_BITS);
        let residue = shift16_term * rom_term + cleanaddr_hi.clone() - rom_bound_high;
        assert_eq!(residue.degree(), 2);
        let layer_2_copied_residue =
            cs.add_intermediate_named_variable_from_constraint(residue, "residue (L2)");
        cs.require_invariant_from_lookup_input(
            LookupInput::from(layer_2_copied_residue),
            Invariant::RangeChecked { width: 16 },
        );
        // trap store*rom — only fires when is_sw = 1 (Family 4 SW) and is_rom = 1.
        cs.add_constraint(Constraint::from(is_rom) * Constraint::from(is_sw));
        (is_rom, cleanaddr_lo + shift16_term * cleanaddr_hi)
    };

    // ----- ROM-or-data lookup -----
    //
    // Standalone Family 4 expresses the data write as a single lookup that both
    // bridges the load/store/ROM cases and substitutes ROM contents when needed.
    // For unified non-Family-4 cycles we need the lookup to degenerate to
    // (0, 0, 0) ∈ ZeroEntry — that requires gating both the table_id and the
    // outputs by `is_fam4 = is_lw + is_sw`. To keep every commit at degree ≤ 2
    // and to mirror the standalone layer structure, we allocate two L0 helper
    // booleans (witnesses set in the same value_fn below) and use them in the
    // L0 expressions for output1/output2 + the L1 expression for table_id:
    //
    //   - `gate_fam4_rom     = is_fam4 AND is_rom`        (boolean AND)
    //   - `gate_fam4_not_rom = is_fam4 AND NOT is_rom`    (boolean AND)
    //
    // Constraints below pin them to the right algebra (deg-2 each).
    let gate_fam4_rom = cs.add_named_boolean_variable("gate_fam4_rom");
    cs.add_constraint(
        Constraint::from(gate_fam4_rom)
            - Constraint::from(is_fam4) * Constraint::from(is_rom_base_layer),
    );
    let gate_fam4_not_rom = cs.add_named_boolean_variable("gate_fam4_not_rom");
    // is_fam4 * (1 - is_rom) = is_fam4 - is_fam4 * is_rom; equivalent to
    // gate_fam4_not_rom + is_fam4*is_rom - is_fam4 = 0  (deg 2).
    cs.add_constraint(
        Constraint::from(gate_fam4_not_rom)
            + Constraint::from(is_fam4) * Constraint::from(is_rom_base_layer)
            - Constraint::from(is_fam4),
    );
    {
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let is_fam4_val = placer.get_boolean(is_fam4.get_variable().unwrap());
            let is_rom_val = placer.get_boolean(is_rom_base_layer.get_variable().unwrap());
            let gate_rom_val = is_fam4_val.and(&is_rom_val);
            let gate_not_rom_val = is_fam4_val.and(&is_rom_val.negate());
            placer.assign_mask(gate_fam4_rom.get_variable().unwrap(), &gate_rom_val);
            placer.assign_mask(
                gate_fam4_not_rom.get_variable().unwrap(),
                &gate_not_rom_val,
            );
        };
        cs.set_values(value_fn);
    }

    {
        let [memwrite_lo_var, memwrite_hi_var] = memwrite;

        let layer_3_selected_input = {
            assert_eq!(rom_addr_constraint.degree(), 2);
            let layer_2_copied_rom_addr =
                Term::from(cs.add_intermediate_named_variable_from_constraint(
                    rom_addr_constraint,
                    "romaddr (L2)",
                ));
            let layer_2_copied_is_rom =
                Term::from(cs.add_intermediate_named_variable_from_constraint(
                    Constraint::from(is_rom_base_layer),
                    "ROM (L2)",
                ));
            let input = layer_2_copied_is_rom * layer_2_copied_rom_addr;
            cs.add_intermediate_named_variable_from_constraint(input, "final lookup input (L3)")
        };
        // output_k = is_fam4 * memwrite_k - gate_fam4_not_rom * memread_k.
        // All factors are L0 vars / Constraints; output expression is deg 2 in L0.
        let layer_3_selected_output1 = {
            let output1 = Constraint::from(is_fam4) * Constraint::from(memwrite_lo_var)
                - Constraint::from(gate_fam4_not_rom) * memread_low_c.clone();
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
            let output2 = Constraint::from(is_fam4) * Constraint::from(memwrite_hi_var)
                - Constraint::from(gate_fam4_not_rom) * memread_high_c.clone();
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
            let romread_table = Term::from(TableType::AlignedRomRead.to_num());
            let layer_2_copied_execute =
                Constraint::from(cs.add_intermediate_named_variable_from_constraint(
                    Constraint::from(inputs.execute),
                    "execute (L2)",
                ));
            let layer_2_gate_fam4_rom =
                Term::from(cs.add_intermediate_named_variable_from_constraint(
                    Constraint::from(gate_fam4_rom),
                    "gate_fam4_rom (L2)",
                ));
            // NB: to avoid scenarios where romread!=0 but we're in padding so ROM==1 and
            // memwrite==0, we patch this to zero table. Multiplying by gate_fam4_rom also
            // collapses table_id to 0 (ZeroEntry) for cycles where another family fires.
            let table_id = layer_2_copied_execute * layer_2_gate_fam4_rom * romread_table;
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

    // PC bump is owned by the caller (standalone wrapper or unified body) — see the
    // analogous note in `apply_add_sub_lui_auipc_mop_inner`.
}

pub fn mem_word_only_circuit_with_preprocessed_bytecode_for_gkr<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
) {
    let (input, bitmask) =
        cs.allocate_machine_state(false, false, WORD_ONLY_MEMORY_FAMILY_NUM_FLAGS);
    let bitmask: [_; WORD_ONLY_MEMORY_FAMILY_NUM_FLAGS] = bitmask.try_into().unwrap();
    let bitmask = bitmask.map(|el| Boolean::Is(el));
    let decoder = WordOnlyMemoryFamilyCircuitMask::from_mask(bitmask);

    let is_sw = decoder.perform_write();
    // Standalone: only Family 4 fires (or padding via execute=0). is_lw and is_sw
    // are complements derived from the single decoder bit.
    let is_lw = is_sw.toggle();

    // rs1 register read — committed as U8 bytes for symmetry with the unified circuit
    // (Family 4's body algebraically reassembles U16 from the bytes, free in committed-column
    // terms).
    let rs1_access = cs.request_mem_access(
        MemoryAccessRequest::RegisterRead {
            reg_idx: input.decoder_data.rs1_index,
            read_value_placeholder: Placeholder::ShuffleRamReadValue(0),
            split_as_u8: true,
        },
        "rs1",
        0,
    );
    let MemoryAccess::RegisterOnly(rs1_access) = rs1_access else {
        unreachable!()
    };
    let WordRepresentation::U8Limbs(rs1_limbs) = rs1_access.read_value else {
        unreachable!()
    };

    // memread (rs2 register on SW, RAM on LW)
    let memread_addr =
        core::array::from_fn(|i| cs.add_named_variable(&format!("memread_addr[{i}]")));
    {
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let value = placer.get_oracle_u32(Placeholder::ShuffleRamAddress(1));
            placer.assign_u32_from_u16_parts(memread_addr, &value);
        };
        cs.set_values(value_fn);
    }
    let memread_access = cs.request_mem_access(
        MemoryAccessRequest::RegisterOrRamRead {
            // is_register = 1 ⇒ register address space; SW (is_sw=1) reads rs2 register,
            // LW (is_lw=1) reads RAM. Equivalently is_register = NOT is_lw = is_sw.
            is_register: is_sw,
            address: memread_addr,
            read_value_placeholder: Placeholder::ShuffleRamReadValue(1),
            split_as_u8: true,
        },
        "mem/rs2 read",
        1,
    );
    let MemoryAccess::RegisterOrRam(memread_access) = memread_access else {
        unreachable!()
    };

    // memwrite (rd register on LW, RAM on SW)
    let memwrite_addr =
        core::array::from_fn(|i| cs.add_named_variable(&format!("memwrite_addr[{i}]")));
    {
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let value = placer.get_oracle_u32(Placeholder::ShuffleRamAddress(2));
            placer.assign_u32_from_u16_parts(memwrite_addr, &value);
        };
        cs.set_values(value_fn);
    }
    let memwrite_access = cs.request_mem_access(
        MemoryAccessRequest::RegisterOrRamReadWrite {
            // is_register = NOT is_sw = is_lw.
            is_register: is_lw,
            address: memwrite_addr,
            read_value_placeholder: Placeholder::ShuffleRamReadValue(2),
            write_value_placeholder: Placeholder::ShuffleRamWriteValue(2),
            split_read_as_u8: false,
            split_write_as_u8: false,
        },
        "mem/rd write",
        2,
    );
    let MemoryAccess::RegisterOrRam(memwrite_access) = memwrite_access else {
        unreachable!()
    };

    let pc_in = input.cycle_start_state.pc;
    let pc_out = input.cycle_end_state.pc;
    apply_mem_word_only_inner(
        cs,
        input,
        is_lw,
        is_sw,
        rs1_limbs,
        memread_access,
        memwrite_access,
    );

    // Standalone PC bump — every LW/SW op is pc_next = pc + 4.
    use crate::gkr_circuits::utils::calculate_pc_next_no_overflows_with_range_checks;
    calculate_pc_next_no_overflows_with_range_checks(cs, pc_in, pc_out);
}

#[cfg(test)]
mod test {
    use test_utils::skip_if_ci;

    use super::*;
    use crate::gkr_compiler::compile_unrolled_circuit_state_transition_into_unrolled_gkr_without_caches;
    use crate::gkr_compiler::{
        compile_unrolled_circuit_state_transition_into_gkr, dump_ssa_witness_eval_form,
    };
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
