use super::circuit::{LookupRequest, F4_SCRATCH_BOOLS, F4_SCRATCH_VARS};
use super::*;
use crate::constraint::{Constraint, Term};
use crate::cs::circuit_trait::*;
use crate::structured_expr::Expr;
use crate::types::*;
use crate::witness_placer::*;
use field::PrimeField;

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
pub(super) fn apply_unified_mem_word_only_lw_sw_data_path<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    inputs: &OpcodeFamilyCircuitState<F>,
    is_lw: Boolean,
    is_sw: Boolean,
    rs1_limbs: [Variable; REGISTER_SIZE],
    rs2_read_or_lw_mem_value_u16: [Variable; REGISTER_SIZE],
    rd_write_or_sw_mem_value_u16: [Variable; REGISTER_SIZE],
    memread_addr: [Variable; REGISTER_SIZE],
    memwrite_addr: [Variable; REGISTER_SIZE],
    of_slots: [Boolean; F4_SCRATCH_BOOLS],
    scratch_vars: [Variable; F4_SCRATCH_VARS],
    // Shared RC-16 slot (limb 0 of the F1/F2/F4 Register) for the SW-align `top_14`.
    top_14_slot: Variable,
) -> Vec<LookupRequest<F>> {
    let rs1_low_e: Expr<F> = Expr::var(rs1_limbs[0]);
    let rs1_high_e: Expr<F> = Expr::var(rs1_limbs[1]);

    // `load`/`store` stay Constraint-typed: they feed the out-of-scope
    // `cleanaddr_lo_expr`/`cleanaddr_hi_expr` witness expressions below.
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
            let rs1_lo_val = placer.get_u16(rs1_limbs[0]);
            let rs1_hi_val = placer.get_u16(rs1_limbs[1]);
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
    cs.add_constraint_expr(
        Expr::from(is_lw)
            * (rs1_low_e.clone() + Expr::from(imm_lo)
                - Expr::from(readaddr_lo)
                - Expr::from(shift16_term) * Expr::from(of_lo_term))
            + Expr::from(is_sw)
                * (rs1_low_e.clone() + Expr::from(imm_lo)
                    - Expr::from(writeaddr_lo)
                    - Expr::from(shift16_term) * Expr::from(of_lo_term)),
    );
    // Constraint on of_hi: same shape with the carry from of_lo folded in.
    cs.add_constraint_expr(
        Expr::from(is_lw)
            * (rs1_high_e.clone() + Expr::from(imm_hi) + Expr::from(of_lo)
                - Expr::from(readaddr_hi)
                - Expr::from(shift16_term) * Expr::from(of_hi_term))
            + Expr::from(is_sw)
                * (rs1_high_e.clone() + Expr::from(imm_hi) + Expr::from(of_lo)
                    - Expr::from(writeaddr_hi)
                    - Expr::from(shift16_term) * Expr::from(of_hi_term)),
    );

    let cleanaddr_lo_expr: Constraint<F> =
        load.clone() * readaddr_lo + store.clone() * writeaddr_lo;
    let cleanaddr_hi_expr: Constraint<F> =
        load.clone() * readaddr_hi + store.clone() * writeaddr_hi;

    // ram_addr aliases shared scratch-Variable pool slots [0],[1] (shared with F2's
    // lookup outputs + F3's scratch — all mutually exclusive per row). Witnessed
    // conditionally on is_fam4 and bound by the SELECT-TRICK below, so it is free on
    // non-Family-4 rows.
    let ram_addr: [Variable; REGISTER_SIZE] = [scratch_vars[0], scratch_vars[1]];
    {
        let cleanaddr_lo_expr = cleanaddr_lo_expr.clone();
        let cleanaddr_hi_expr = cleanaddr_hi_expr.clone();
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
            let is_active = is_lw_val.or(&is_sw_val);
            let lo = cleanaddr_lo_expr.evaluate_with_placer(placer);
            let hi = cleanaddr_hi_expr.evaluate_with_placer(placer);
            placer.conditionally_assign_field(ram_addr[0], &is_active, &lo);
            placer.conditionally_assign_field(ram_addr[1], &is_active, &hi);
        };
        cs.set_values(value_fn);
    }
    // Select-trick: rewrite the ungated select `ram_addr = load*read + store*write`
    // as two flag-gated degree-2 constraints per limb. On LW: ram_addr = read addr;
    // on SW: ram_addr = write addr; on non-Family-4 rows neither fires ⇒ ram_addr is
    // unconstrained (poolable). Each constraint stays degree 2 (flag × degree-1).
    cs.add_constraint_expr(Expr::from(is_lw) * (Expr::var(ram_addr[0]) - Expr::from(readaddr_lo)));
    cs.add_constraint_expr(Expr::from(is_sw) * (Expr::var(ram_addr[0]) - Expr::from(writeaddr_lo)));
    cs.add_constraint_expr(Expr::from(is_lw) * (Expr::var(ram_addr[1]) - Expr::from(readaddr_hi)));
    cs.add_constraint_expr(Expr::from(is_sw) * (Expr::var(ram_addr[1]) - Expr::from(writeaddr_hi)));

    let is_fam4: Constraint<F> = Constraint::from(is_lw) + Constraint::from(is_sw);
    let is_fam4_expr = Expr::from(is_lw) + Expr::from(is_sw);

    let (is_rom_base_layer, rom_addr_constraint) = {
        // is_rom aliases shared scratch-Boolean pool slot [2]. Witnessed conditionally
        // on is_fam4 and constrained ONLY through the is_fam4-gated residue below + the
        // is_sw-gated trap, so it is free on non-Family-4 rows (poolable).
        let is_rom = of_slots[2];
        // ROM-vs-data is decided by comparing the address high limb with
        // 2^ROM_SECOND_WORD_BITS. On non-Family-4 rows is_rom is a don't-care (the
        // residue is gated to 0 below), so we only assign it on Family-4 rows.
        {
            let cleanaddr_hi_expr = cleanaddr_hi_expr.clone();
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
                let is_active = is_lw_val.or(&is_sw_val);
                let cleanaddr_hi = cleanaddr_hi_expr.evaluate_with_placer(placer);
                let extrabits = cleanaddr_hi
                    .as_integer()
                    .shr(common_constants::ROM_SECOND_WORD_BITS as u32);
                let rom = extrabits.is_zero();
                placer.conditionally_assign_mask(is_rom.expect_variable(), &is_active, &rom);
            };
            cs.set_values(value_fn);
        }
        // residue gated by is_fam4: on non-Family-4 rows it is 0 (a valid 16-bit value)
        // regardless of the pooled is_rom/ram_addr[1] junk; on Family-4 rows (is_fam4=1)
        // it equals `2^16*is_rom + ram_addr_hi - rom_bound`, and the RC forces is_rom to
        // correctly indicate ram_addr_hi < rom_bound — identical soundness to the
        // ungated form, but with is_rom/ram_addr[1] now free off-Family-4. Degree 2
        // (is_fam4 × degree-1).

        let residue_inner: Expr<F> = Expr::constant(F::from_u32_with_reduction(1 << 16))
            * Expr::from(is_rom)
            + Expr::from(ram_addr[1])
            - Expr::constant(F::from_u32_with_reduction(
                1 << common_constants::ROM_SECOND_WORD_BITS,
            ));
        let residue: Expr<F> = is_fam4_expr.clone() * residue_inner;
        assert_eq!(residue.degree(), 2);
        let residue_var = cs.add_intermediate_named_variable_from_expr(residue, "rom residue");
        cs.require_invariant_from_lookup_input(
            LookupInput::from(residue_var),
            Invariant::RangeChecked { width: 16 },
        );
        // trap store*rom — only fires when is_sw = 1 (Family 4 SW) and is_rom = 1.
        cs.add_constraint_expr(Expr::from(is_rom) * Expr::from(is_sw));
        // rom_addr = ram_addr_lo + 2^16 * ram_addr_hi — degree-1 over base vars.
        let rom_addr: Expr<F> =
            Expr::from(ram_addr[0]) + Expr::from(ram_addr[1]) * F::from_u32_with_reduction(1 << 16);
        (is_rom, rom_addr)
    };

    // For non-Family-4 cycles the tuple degenerates to (0, 0, 0) ∈ ZeroEntry —
    // gating is applied to both the table_id and the outputs via the inlined
    // `is_fam4 = is_lw + is_sw` sum and the single committed helper:
    //
    //   - `gate_fam4_rom     = is_lw AND is_rom`
    //   - `gate_fam4_not_rom = (is_lw + is_sw) - gate_fam4_rom` (inlined at use)
    //
    // The "not_rom" gate is inlined at its use sites (output1 / output2 below)
    // as the degree-1 expression `(is_lw + is_sw) - gate_fam4_rom`. Saves 1
    // committed col vs the previous shape where both were base-layer Booleans.

    // Also one can never STORE into ROM region, so is_sw AND is_rom is unreachable
    cs.add_constraint_expr(Expr::from(is_sw) * Expr::from(is_rom_base_layer));

    let gate_fam4_rom_read = cs.add_named_boolean_variable("gate_fam4_rom_read");
    {
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let is_lw_raw = placer.get_boolean(is_lw_var);
            let is_lw_val = if is_lw_neg {
                is_lw_raw.negate()
            } else {
                is_lw_raw
            };
            let is_rom_val = placer.get_boolean(is_rom_base_layer.expect_variable());
            let gate_rom_val = is_lw_val.and(&is_rom_val);
            placer.assign_mask(gate_fam4_rom_read.expect_variable(), &gate_rom_val);
        };
        cs.set_values(value_fn);
    }
    cs.add_constraint_expr(
        Expr::from(gate_fam4_rom_read) - Expr::from(is_lw) * Expr::from(is_rom_base_layer),
    );

    // Self-generating witness (no-ASSUME contract, see jump_branch_slt.rs):
    // derive the Family-4 write value instead of trusting the oracle for it.
    // LW from RAM and SW copy the read value (w = r — the same relation the
    // inlined `(is_lw + is_sw) - gate_fam4_rom_read` copy-zerochecks below enforce);
    // LW from ROM reads the word from the AlignedRomRead table (mask-gated lookup:
    // on non-ROM rows the pooled address holds junk and must not be looked up).
    // Gated on is_lw | is_sw.
    if !CS::ASSUME_MEMORY_VALUES_ASSIGNED {
        let [r_lo_var, r_hi_var] = rs2_read_or_lw_mem_value_u16;
        let [w_lo_var, w_hi_var] = rd_write_or_sw_mem_value_u16;
        // ROM-read predicate is the committed `gate_fam4_rom_read` (= is_lw AND is_rom).
        let gate_rom_read_var = gate_fam4_rom_read.expect_variable();
        let [ram_addr_lo_var, ram_addr_hi_var] = ram_addr;
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            type Fld<CS, F> = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field;
            let is_lw_raw = placer.get_boolean(is_lw_var);
            let is_lw_m = if is_lw_neg {
                is_lw_raw.negate()
            } else {
                is_lw_raw
            };
            let is_sw_raw = placer.get_boolean(is_sw_var);
            let is_sw_m = if is_sw_neg {
                is_sw_raw.negate()
            } else {
                is_sw_raw
            };
            let is_f4 = is_lw_m.or(&is_sw_m);
            let rom_read = placer.get_boolean(gate_rom_read_var);

            // default: copy the read value (LW-RAM: rd := M[addr]; SW: M[addr] := rs2)
            let mut low = placer.get_field(r_lo_var);
            let mut high = placer.get_field(r_hi_var);

            // ROM override: w := ROM[addr], addr = ram_addr_lo + 2^16 * ram_addr_hi
            let mut addr = placer.get_field(ram_addr_hi_var);
            addr.mul_assign(&Fld::<CS, F>::constant(F::from_u32_with_reduction(1 << 16)));
            addr.add_assign(&placer.get_field(ram_addr_lo_var));
            let table_id = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(
                TableType::AlignedRomRead.to_table_id() as u16,
            );
            let [rom_lo, rom_hi] = placer.maybe_lookup::<1, 2>(&[addr], &table_id, &rom_read);
            low.assign_masked(&rom_read, &rom_lo);
            high.assign_masked(&rom_read, &rom_hi);

            placer.conditionally_assign_field(w_lo_var, &is_f4, &low);
            placer.conditionally_assign_field(w_hi_var, &is_f4, &high);
        };
        cs.set_values(value_fn);
    }

    let rom_request = {
        let [source_low, source_high] = rs2_read_or_lw_mem_value_u16;
        let [destination_low, destination_high] = rd_write_or_sw_mem_value_u16;

        assert_eq!(rom_addr_constraint.degree(), 1);
        // input = gate_fam4_rom * rom_addr.
        // We gate by `gate_fam4_rom` (forced to 0 off-Family-4 by its ungated def at
        // line 248) rather than the now-pooled `is_rom`/`ram_addr` (which hold junk on
        // non-Family-4 rows). This keeps the pooled-lookup input at 0 on non-Family-4
        // rows so it does not pollute the shared lookup-pool slot. On Family-4 rows
        // gate_fam4_rom == is_rom, so this equals the original `is_rom * rom_addr`.
        let input = Expr::from(gate_fam4_rom_read) * rom_addr_constraint;
        // we want a constraint such that it's if we do ROM read then it's equal to destination value
        // (what we write to RD), otherwise (RAM read or SW) - it's 0. We need in mind that SW * is_ROM is
        // unreachable combiantion, so we freely treat is as 0. We also want to ensure that
        // if we do RAM read or SW, then source and destination values are the same

        // ROM read case
        let output1 = Expr::from(gate_fam4_rom_read) * Expr::from(destination_low);
        let output2 = Expr::from(gate_fam4_rom_read) * Expr::from(destination_high);
        // RAM read or SW - then if LW == 1 and we do not touch ROM, then it's 1 in predicate
        cs.add_constraint_expr(
            (Expr::from(is_lw.expect_variable()) + Expr::from(is_sw.expect_variable())
                - Expr::from(gate_fam4_rom_read))
                * (Expr::from(destination_low) - Expr::from(source_low)),
        );
        cs.add_constraint_expr(
            (Expr::from(is_lw.expect_variable()) + Expr::from(is_sw.expect_variable())
                - Expr::from(gate_fam4_rom_read))
                * (Expr::from(destination_high) - Expr::from(source_high)),
        );

        // table_id = execute * gate_fam4_rom * romread_table — collapses to 0
        // (ZeroEntry) when another family fires or on padding.
        let table_id = Expr::from(inputs.execute)
            * Expr::from(gate_fam4_rom_read)
            * Expr::from(TableType::AlignedRomRead.to_num());
        LookupRequest::new(table_id, vec![input, output1, output2])
    };

    // Word alignment for BOTH Family-4 memory ops (RISC-V: word accesses must
    // have addr ≡ 0 mod 4; this VM makes misaligned word accesses unprovable
    // — "no misaligned word accesses").
    //
    //   LW (`is_lw = 1`): `readaddr_lo`  must be a multiple of 4;
    //   SW (`is_sw = 1`): `writeaddr_lo` must be a multiple of 4.
    //
    // One shared decomposition triple serves both: bit_0/bit_1/top_14 split the
    // SELECTED low limb (readaddr_lo on LW rows, writeaddr_lo on SW rows —
    // is_lw/is_sw are mutually exclusive decoder bits), via two gated
    // decompositions and one shared trap:
    //
    //   is_lw * (4*top_14 + 2*bit_1 + bit_0 - readaddr_lo)  = 0   (deg 2)
    //   is_sw * (4*top_14 + 2*bit_1 + bit_0 - writeaddr_lo) = 0   (deg 2)
    //   (is_lw + is_sw) * (bit_0 + bit_1)                   = 0   (deg 2)
    //
    // Algebraic soundness: on an LW (resp. SW) row the trap plus Booleanity of
    // bit_0/bit_1 forces bit_0 = bit_1 = 0, so the active decomposition pins
    // `addr_lo = 4 * top_14` — a multiple of 4. With `top_14` range-checked to
    // 16 bits the decomposition is a genuine integer split (no field wrap).
    // Aligning the LOW limb aligns the full 32-bit byte address because
    // 2^16 ≡ 0 (mod 4): addr = lo + 2^16*hi ≡ lo (mod 4).
    // On non-Family-4 rows both gates are 0 and the slots stay free (pooled).
    // Note the ROM-read path needs no separate trap: the AlignedRomRead table
    // contains only word-aligned addresses (see tables/rom_related.rs), so a
    // misaligned LW routed to ROM already has no satisfying lookup row; the
    // is_lw gate here covers it uniformly anyway.
    //
    // Cost: 3 pooled slots + 3 constraints (was 2 constraints when SW-only;
    // LW coverage costs +1 constraint and 0 committed columns).
    {
        // bit_0/bit_1 alias shared scratch-Boolean pool slots [3],[4]; witnessed
        // conditionally on is_lw∨is_sw and pinned only by the gated decompositions +
        // trap below, so they are free on non-Family-4 rows (poolable).
        //
        // top_14 (RC-16) borrows limb 0 of the shared F1/F2/F4 Register (so - range-checked) —
        // free on F4 rows since F1/F2 are idle. That limb is already range-checked to
        // 16 bits by the Register, so no require_invariant here. top_14 is consumed only
        // by the gated decompositions, so its value is irrelevant on non-F4 rows;
        // its witness is conditional on is_lw∨is_sw so the Register limb is free for
        // F1/F2 on their rows (the shared-slot pattern needs all writers conditional).
        let bit_0 = of_slots[3];
        let bit_1 = of_slots[4];
        let top_14 = top_14_slot;

        let readaddr_lo_var = memread_addr[0];
        let writeaddr_lo_var = memwrite_addr[0];
        let bit_0_var = bit_0.expect_variable();
        let bit_1_var = bit_1.expect_variable();
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
                let is_f4_val = is_lw_val.or(&is_sw_val);
                // Selected low limb: readaddr_lo on LW, writeaddr_lo otherwise.
                let mut lo = placer.get_u16(writeaddr_lo_var);
                let read_lo = placer.get_u16(readaddr_lo_var);
                lo.assign_masked(&is_lw_val, &read_lo);
                let b0 = lo.get_lowest_bits(1).is_one();
                let b1 = lo.shr(1).get_lowest_bits(1).is_one();
                let top = lo.shr(2);
                placer.conditionally_assign_mask(bit_0_var, &is_f4_val, &b0);
                placer.conditionally_assign_mask(bit_1_var, &is_f4_val, &b1);
                placer.conditionally_assign_u16(top_14, &is_f4_val, &top);
            };
            cs.set_values(value_fn);
        }

        // Decomposition gated on is_lw (deg 2): only LW rows bind it to readaddr_lo.
        cs.add_constraint_expr(
            Expr::from(is_lw)
                * (Expr::constant(F::from_u32_with_reduction(4)) * Expr::var(top_14)
                    + Expr::constant(F::from_u32_with_reduction(2)) * Expr::from(bit_1)
                    + Expr::from(bit_0)
                    - Expr::var(readaddr_lo_var)),
        );
        // Decomposition gated on is_sw (deg 2): only SW rows bind it to writeaddr_lo.
        cs.add_constraint_expr(
            Expr::from(is_sw)
                * (Expr::constant(F::from_u32_with_reduction(4)) * Expr::var(top_14)
                    + Expr::constant(F::from_u32_with_reduction(2)) * Expr::from(bit_1)
                    + Expr::from(bit_0)
                    - Expr::var(writeaddr_lo_var)),
        );
        // Alignment trap (deg 2, gated on is_lw + is_sw — mutually exclusive
        // Booleans, so the gate is itself Boolean): bit_0 + bit_1 = 0 when
        // either Family-4 memory op fires.
        cs.add_constraint_expr(
            (Expr::from(is_lw) + Expr::from(is_sw)) * (Expr::from(bit_0) + Expr::from(bit_1)),
        );
    }

    vec![rom_request]
}
