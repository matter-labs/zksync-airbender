use super::*;
use crate::constraint::{Constraint, Term};
use crate::cs::circuit_trait::*;
use crate::types::*;
use crate::witness_placer::*;
use field::PrimeField;
use super::circuit::LookupRequest;

/// Per-cycle Family-4 LW/SW constraints (the data-path piece). Caller
/// (`mem_word_only.rs`) has already done the register/RAM dispatch.
///
/// Constraints added here:
/// 1. rs1+imm = mem-side address — combined LW/SW form, gated on `is_lw + is_sw`
///    (deg 2 with carry bits `of_lo`, `of_hi`).
/// 2. ROM-vs-data dispatch — `is_rom` boolean + range check on the residue,
///    plus `is_sw * is_rom = 0` (no SW into ROM).
/// 3. ROM-or-data value lookup — gated via `gate_fam4_rom` (and the inline
///    expression `is_fam4 - gate_fam4_rom` for the not-rom case).
/// 4. SW alignment trap — `is_sw * (bit_0 + bit_1) = 0`.
///
/// `is_fam4` is inlined as `(is_lw + is_sw)` everywhere it appears; no
/// committed Boolean column.
#[allow(non_snake_case)]
pub(super) fn apply_unified_mem_word_only_lw_sw_data_path<
    F: PrimeField,
    CS: Circuit<F>,
    const N: usize,
>(
    cs: &mut CS,
    inputs: &OpcodeFamilyCircuitState<F>,
    is_lw: Boolean,
    is_sw: Boolean,
    rs1_limbs: [Variable; REGISTER_SIZE * 2],
    memread_u8: [Variable; REGISTER_SIZE * 2],
    memwrite_u16: [Variable; REGISTER_SIZE],
    memread_addr: [Variable; REGISTER_SIZE],
    memwrite_addr: [Variable; REGISTER_SIZE],
    of_slots: [Boolean; N],
) -> Vec<LookupRequest<F>> {
    let byte_shift = F::from_u32_unchecked(1 << 8);
    let rs1_low_c: Constraint<F> =
        Constraint::from(rs1_limbs[0]) + Term::from((byte_shift, rs1_limbs[1]));
    let rs1_high_c: Constraint<F> =
        Constraint::from(rs1_limbs[2]) + Term::from((byte_shift, rs1_limbs[3]));
    let memread_low_c: Constraint<F> =
        Constraint::from(memread_u8[0]) + Term::from((byte_shift, memread_u8[1]));
    let memread_high_c: Constraint<F> =
        Constraint::from(memread_u8[2]) + Term::from((byte_shift, memread_u8[3]));

    let load = Constraint::from(is_lw);
    let store = Constraint::from(is_sw);

    let [readaddr_lo, readaddr_hi] = memread_addr.map(Term::from);
    let [writeaddr_lo, writeaddr_hi] = memwrite_addr.map(Term::from);

    // For non-Family-4 cycles is_lw and is_sw are both 0 so the constraints
    // below collapse to 0 = 0.
    //
    // Combined LW/SW form:
    //   is_lw * (rs1_lo + imm_lo - memread_addr_lo  - 2^16*of_lo)
    // + is_sw * (rs1_lo + imm_lo - memwrite_addr_lo - 2^16*of_lo)  =  0
    //
    // Degree 2 (one Boolean × deg-1 expression). Going through L1 commits
    // would force the gate constraint into degree 3.
    let [imm_var_lo, imm_var_hi] = inputs.decoder_data.imm;
    let imm_lo: Term<F> = imm_var_lo.into();
    let imm_hi: Term<F> = imm_var_hi.into();
    let shift16_term: Term<F> = Term::from(1 << 16);
    let of_lo = of_slots[0];
    let of_hi = of_slots[1];
    let of_lo_slot_var = of_lo.expect_variable();
    let of_hi_slot_var = of_hi.expect_variable();

    // Witness for of_lo / of_hi: actual carry bits of (rs1 + imm) when Family 4
    // fires. We conditionally assign only on active rows; the shared pool's
    // default-0 covers non-Family-4 rows. The constraints below are gated so the
    // value is unused for non-Family-4 cycles.
    let (is_lw_var, is_lw_neg) = is_lw.variable_and_negation_constant();
    let (is_sw_var, is_sw_neg) = is_sw.variable_and_negation_constant();
    {
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let rs1_lo_val = placer.get_u16_from_u8_parts([rs1_limbs[0], rs1_limbs[1]]);
            let rs1_hi_val = placer.get_u16_from_u8_parts([rs1_limbs[2], rs1_limbs[3]]);
            let imm_lo_val = placer.get_u16(imm_var_lo);
            let imm_hi_val = placer.get_u16(imm_var_hi);
            let (_, carry_lo) = rs1_lo_val.overflowing_add(&imm_lo_val);
            let (_, carry_hi) = rs1_hi_val.overflowing_add_with_carry(&imm_hi_val, &carry_lo);

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
            placer.conditionally_assign_mask(of_lo_slot_var, &is_active, &carry_lo);
            placer.conditionally_assign_mask(of_hi_slot_var, &is_active, &carry_hi);
        };
        cs.set_values(value_fn);
    }

    // Constraint on of_lo: combined LW + SW form, degree 2.
    let of_lo_term = Term::from(of_lo);
    let of_hi_term = Term::from(of_hi);
    cs.add_constraint(
        load.clone() * (rs1_low_c.clone() + imm_lo - readaddr_lo - shift16_term * of_lo_term)
            + store.clone()
                * (rs1_low_c.clone() + imm_lo - writeaddr_lo - shift16_term * of_lo_term),
    );
    // Constraint on of_hi: same shape with the carry from of_lo folded in.
    cs.add_constraint(
        load.clone()
            * (rs1_high_c.clone() + imm_hi + Term::from(of_lo)
                - readaddr_hi
                - shift16_term * of_hi_term)
            + store.clone()
                * (rs1_high_c.clone() + imm_hi + Term::from(of_lo)
                    - writeaddr_hi
                    - shift16_term * of_hi_term),
    );

    let cleanaddr_lo_expr: Constraint<F> =
        load.clone() * readaddr_lo + store.clone() * writeaddr_lo;
    let cleanaddr_hi_expr: Constraint<F> =
        load.clone() * readaddr_hi + store.clone() * writeaddr_hi;

    let ram_addr: [Variable; REGISTER_SIZE] =
        core::array::from_fn(|i| cs.add_named_variable(&format!("ram_addr[{i}]")));
    {
        let cleanaddr_lo_expr = cleanaddr_lo_expr.clone();
        let cleanaddr_hi_expr = cleanaddr_hi_expr.clone();
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let lo = cleanaddr_lo_expr.evaluate_with_placer(placer);
            let hi = cleanaddr_hi_expr.evaluate_with_placer(placer);
            placer.assign_field(ram_addr[0], &lo);
            placer.assign_field(ram_addr[1], &hi);
        };
        cs.set_values(value_fn);
    }
    cs.add_constraint(Constraint::from(ram_addr[0]) - cleanaddr_lo_expr.clone());
    cs.add_constraint(Constraint::from(ram_addr[1]) - cleanaddr_hi_expr.clone());

    let (is_rom_base_layer, rom_addr_constraint) = {
        let is_rom = cs.add_named_boolean_variable("flag: are we in rom addr range?");
        let rom_term = Term::from(is_rom);
        // ROM-vs-data is decided by comparing the address high limb with
        // 2^ROM_SECOND_WORD_BITS via subtraction with carry. For non-Family-4
        // cycles ram_addr_hi = 0 < rom_bound_high, so witness gen sets is_rom = 1
        // and the residue is 2^16 - rom_bound_high (still a 16-bit value). The ROM
        // lookup itself is gated below via `gate_fam4_rom`.
        {
            let cleanaddr_hi_expr = cleanaddr_hi_expr.clone();
            let value_fn = move |placer: &mut CS::WitnessPlacer| {
                let cleanaddr_hi = cleanaddr_hi_expr.evaluate_with_placer(placer);
                let extrabits = cleanaddr_hi
                    .as_integer()
                    .shr(common_constants::ROM_SECOND_WORD_BITS as u32);
                let rom = extrabits.is_zero();
                placer.assign_mask(is_rom.expect_variable(), &rom);
            };
            cs.set_values(value_fn);
        }
        let rom_bound_high = Term::from(1 << common_constants::ROM_SECOND_WORD_BITS);
        // residue is now degree-1 (ram_addr_hi is a committed base var). The
        // range-check compiler requires a single Variable input, so commit it to
        // a variable; both inputs (is_rom, ram_addr_hi) are base layer so this
        // lands one layer up — same as the baseline residue placement.
        let residue: Constraint<F> =
            shift16_term * rom_term + Term::from(ram_addr[1]) - rom_bound_high;
        assert_eq!(residue.degree(), 1);
        let residue_var = cs.add_intermediate_named_variable_from_constraint(residue, "rom residue");
        cs.require_invariant_from_lookup_input(
            LookupInput::from(residue_var),
            Invariant::RangeChecked { width: 16 },
        );
        // trap store*rom — only fires when is_sw = 1 (Family 4 SW) and is_rom = 1.
        cs.add_constraint(Constraint::from(is_rom) * Constraint::from(is_sw));
        // rom_addr = ram_addr_lo + 2^16 * ram_addr_hi — degree-1 over base vars.
        let rom_addr: Constraint<F> =
            Constraint::from(ram_addr[0]) + shift16_term * Term::from(ram_addr[1]);
        (is_rom, rom_addr)
    };

    // For non-Family-4 cycles the tuple degenerates to (0, 0, 0) ∈ ZeroEntry —
    // gating is applied to both the table_id and the outputs via the inlined
    // `is_fam4 = is_lw + is_sw` sum and the single committed helper:
    //
    //   - `gate_fam4_rom     = (is_lw + is_sw) AND is_rom`
    //   - `gate_fam4_not_rom = (is_lw + is_sw) - gate_fam4_rom` (inlined at use)
    //
    // The "not_rom" gate is inlined at its use sites (output1 / output2 below)
    // as the degree-1 expression `(is_lw + is_sw) - gate_fam4_rom`. Saves 1
    // committed col vs the previous shape where both were base-layer Booleans.
    let is_fam4_sum = || -> Constraint<F> {
        Constraint::from(is_lw) + Constraint::from(is_sw)
    };
    let gate_fam4_rom = cs.add_named_boolean_variable("gate_fam4_rom");
    cs.add_constraint(
        Constraint::from(gate_fam4_rom)
            - is_fam4_sum() * Constraint::from(is_rom_base_layer),
    );
    {
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
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
            let is_fam4_val = is_lw_val.or(&is_sw_val);
            let is_rom_val = placer.get_boolean(is_rom_base_layer.expect_variable());
            let gate_rom_val = is_fam4_val.and(&is_rom_val);
            placer.assign_mask(gate_fam4_rom.expect_variable(), &gate_rom_val);
        };
        cs.set_values(value_fn);
    }

    let rom_request = {
        let [memwrite_lo_var, memwrite_hi_var] = memwrite_u16;
        assert_eq!(rom_addr_constraint.degree(), 1);
        // input = is_rom * rom_addr
        let input = Constraint::from(is_rom_base_layer) * rom_addr_constraint;
        // output_k = is_fam4 * memwrite_k - gate_fam4_not_rom * memread_k, with
        // is_fam4 = (is_lw + is_sw) and gate_fam4_not_rom = (is_fam4 - gate_fam4_rom).
        let output1 = is_fam4_sum() * Constraint::from(memwrite_lo_var)
            - (is_fam4_sum() - Constraint::from(gate_fam4_rom)) * memread_low_c.clone();
        let output2 = is_fam4_sum() * Constraint::from(memwrite_hi_var)
            - (is_fam4_sum() - Constraint::from(gate_fam4_rom)) * memread_high_c.clone();
        let romread_table = Term::from(TableType::AlignedRomRead.to_num());
        // table_id = execute * gate_fam4_rom * romread_table — collapses to 0
        // (ZeroEntry) when another family fires or on padding.
        let table_id =
            Constraint::from(inputs.execute) * Term::from(gate_fam4_rom) * romread_table;
        LookupRequest {
            table_id,
            inputs: vec![input, output1, output2],
        }
    };

    // When `is_sw = 1`, `writeaddr_lo` must be a multiple of 4 (RISC-V word
    // aligned). We decompose `writeaddr_lo` into `4 * top_14 + 2 * bit_1 + bit_0` and
    // force `is_sw * (bit_0 + bit_1) = 0`. The decomposition itself is ungated
    // — it just splits whatever `writeaddr_lo` is for any row — and is enforced
    // for every cycle. Cost: 3 cols + 2 constraints.
    //
    // For SW=0 rows `writeaddr_lo = rd_index ∈ {0..31}` so bit_0/bit_1 may be 1;
    // the alignment constraint trivially passes. For SW=1 rows `writeaddr_lo`
    // is the RAM write address; the constraint forces its low 2 bits to be 0.
    //
    // Algebraic soundness: on SW rows, the trap `is_sw * (bit_0 + bit_1) = 0`
    // combined with Booleanity of bit_0 / bit_1 (each in {0, 1}) forces the
    // field sum bit_0 + bit_1 = 0, which means both = 0. Then the decomposition
    // pins `writeaddr_lo = 4 * top_14`; with `top_14` range-checked to 16 bits,
    // `writeaddr_lo ∈ [0, 2^18)` and is a multiple of 4.
    //
    // The trap is structurally sound regardless of `writeaddr_lo`'s range. Its
    // 16-bit RC (added explicitly above and also transitively present via the
    // RAM-permutation U16 limb structure) is required for memory-address
    // validity, not for the alignment check itself.
    {
        let bit_0 = cs.add_named_boolean_variable("sw align bit_0");
        let bit_1 = cs.add_named_boolean_variable("sw align bit_1");
        let top_14 = cs.add_named_variable("sw align: writeaddr_lo >> 2");
        cs.require_invariant(
            top_14,
            Invariant::RangeChecked {
                width: LIMB_WIDTH as u32,
            },
        );

        let writeaddr_lo_var = memwrite_addr[0];
        let bit_0_var = bit_0.expect_variable();
        let bit_1_var = bit_1.expect_variable();
        {
            let value_fn = move |placer: &mut CS::WitnessPlacer| {
                let lo = placer.get_u16(writeaddr_lo_var);
                let b0 = lo.get_lowest_bits(1).is_one();
                let b1 = lo.shr(1).get_lowest_bits(1).is_one();
                let top = lo.shr(2);
                placer.assign_mask(bit_0_var, &b0);
                placer.assign_mask(bit_1_var, &b1);
                placer.assign_u16(top_14, &top);
            };
            cs.set_values(value_fn);
        }

        // Decomposition (deg 1, ungated): 4 * top_14 + 2 * bit_1 + bit_0 = writeaddr_lo.
        cs.add_constraint_allow_explicit_linear(
            Term::from(4u32) * Term::from(top_14)
                + Term::from(2u32) * Term::from(bit_1)
                + Term::from(bit_0)
                - Term::from(writeaddr_lo_var),
        );
        // Alignment trap (deg 2, gated on is_sw): bit_0 + bit_1 = 0 when SW fires.
        cs.add_constraint(
            Constraint::from(is_sw) * (Constraint::from(bit_0) + Constraint::from(bit_1)),
        );
    }

    vec![rom_request]
}
