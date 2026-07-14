use super::circuit::{LookupRequest, F4_SCRATCH_BOOLS, F4_SCRATCH_VARS};
use super::*;
use crate::constraint::{Constraint, Term};
use crate::cs::circuit_trait::*;
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
    let rs1_low_c: Constraint<F> = Constraint::from(rs1_limbs[0]);
    let rs1_high_c: Constraint<F> = Constraint::from(rs1_limbs[1]);

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
    cs.add_constraint(load.clone() * (Constraint::from(ram_addr[0]) - readaddr_lo));
    cs.add_constraint(store.clone() * (Constraint::from(ram_addr[0]) - writeaddr_lo));
    cs.add_constraint(load.clone() * (Constraint::from(ram_addr[1]) - readaddr_hi));
    cs.add_constraint(store.clone() * (Constraint::from(ram_addr[1]) - writeaddr_hi));

    let (is_rom_base_layer, rom_addr_constraint) = {
        // is_rom aliases shared scratch-Boolean pool slot [2]. Witnessed conditionally
        // on is_fam4 and constrained ONLY through the is_fam4-gated residue below + the
        // is_sw-gated trap, so it is free on non-Family-4 rows (poolable).
        let is_rom = of_slots[2];
        let rom_term = Term::from(is_rom);
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
        let is_fam4: Constraint<F> = Constraint::from(is_lw) + Constraint::from(is_sw);
        let rom_bound_high = Term::from(1 << common_constants::ROM_SECOND_WORD_BITS);
        // residue gated by is_fam4: on non-Family-4 rows it is 0 (a valid 16-bit value)
        // regardless of the pooled is_rom/ram_addr[1] junk; on Family-4 rows (is_fam4=1)
        // it equals `2^16*is_rom + ram_addr_hi - rom_bound`, and the RC forces is_rom to
        // correctly indicate ram_addr_hi < rom_bound — identical soundness to the
        // ungated form, but with is_rom/ram_addr[1] now free off-Family-4. Degree 2
        // (is_fam4 × degree-1).

        let residue_inner: Constraint<F> =
            shift16_term * rom_term + Term::from(ram_addr[1]) - rom_bound_high;
        let residue: Constraint<F> = is_fam4.clone() * residue_inner;
        assert_eq!(residue.degree(), 2);
        let residue_var =
            cs.add_intermediate_named_variable_from_constraint(residue, "rom residue");
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

    // Self-generating witness (no-ASSUME contract, see jump_branch_slt.rs):
    // derive the Family-4 write value instead of trusting the oracle for it.
    // LW from RAM and SW copy the read value (w = r — the same relation the
    // ZeroEntry lookup enforces); LW from ROM reads the word from the
    // AlignedRomRead table (mask-gated lookup: on non-ROM rows the pooled
    // address holds junk and must not be looked up). Gated on is_lw | is_sw.
    if CS::ASSUME_MEMORY_VALUES_ASSIGNED == false {
        let [r_lo_var, r_hi_var] = rs2_read_or_lw_mem_value_u16;
        let [w_lo_var, w_hi_var] = rd_write_or_sw_mem_value_u16;
        let is_rom_var = is_rom_base_layer.expect_variable();
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
            let is_rom_m = placer.get_boolean(is_rom_var);
            let rom_read = is_lw_m.and(&is_rom_m);

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
    let is_fam4_sum = || -> Constraint<F> { Constraint::from(is_lw) + Constraint::from(is_sw) };
    let gate_fam4_rom = cs.add_named_boolean_variable("gate_fam4_rom");
    cs.add_constraint(
        Constraint::from(gate_fam4_rom) - is_fam4_sum() * Constraint::from(is_rom_base_layer),
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

    // ZeroEntry-as-equality: the request below is NOT merely a conditional ROM
    // lookup — when the merged table_id evaluates to 0 it selects the ZeroEntry
    // table (id 0, single all-zero row), turning the tuple into forced
    // equalities. Case analysis over all row types (each case pinned by the
    // constraints above, not assumed):
    //
    //   Case A — f4 = is_lw+is_sw = 0 (other family fires, or padding):
    //     gate_fam4_rom = f4*is_rom = 0 regardless of pooled is_rom/ram_addr
    //     junk, so t = 0, in0 = 0*(..) = 0, in1 = 0*w - 0*r = 0, in2 = 0 —
    //     identically zero as field expressions; nothing leaks into the shared
    //     pooled lookup slot.
    //   Case B — f4 = 1, is_rom = 0 (LW from RAM, or any SW — the store*rom
    //     trap kills SW∧ROM): g = 0 ⇒ t = 0 ⇒ ZeroEntry forces
    //     in1 = w_lo - r_lo = 0 and in2 = w_hi - r_hi = 0, i.e. w = r
    //     limb-wise. This IS the data-copy constraint (LW: rd := M[addr];
    //     SW: M[addr] := rs2) and the ONLY constraint binding both write-value
    //     limbs on these rows — do not "mask it to zero".
    //   Case C — f4 = 1, is_rom = 1 (necessarily LW from ROM): g = 1
    //     annihilates the r terms and (addr, w_lo, w_hi) must be a row of
    //     AlignedRomRead (word-aligned addresses only).
    //
    // A witness violating Case B shows up as "table id 0 but nonzero inputs" /
    // padding-element errors from the lookup argument — that is the lookup
    // CORRECTLY rejecting an inconsistent witness (e.g. an ungated debug-mode
    // writer clobbering w on a Family-4 row), not pool pollution.
    let rom_request = {
        // For SW the source is rs2 and the destination is RAM; for LW the
        // source is RAM and the destination is rd — but by the structure of
        // the shared memory queries those are the same two variable pairs.
        let memread_low_c: Constraint<F> = Constraint::from(rs2_read_or_lw_mem_value_u16[0]);
        let memread_high_c: Constraint<F> = Constraint::from(rs2_read_or_lw_mem_value_u16[1]);
        let [memwrite_lo_var, memwrite_hi_var] = rd_write_or_sw_mem_value_u16;
        assert_eq!(rom_addr_constraint.degree(), 1);
        // input = gate_fam4_rom * rom_addr.
        // We gate by `gate_fam4_rom` (forced to 0 off-Family-4 by its ungated
        // definition above) rather than the pooled `is_rom`/`ram_addr` (which
        // hold junk on non-Family-4 rows). On Family-4 rows gate_fam4_rom ==
        // is_rom, so this equals the original `is_rom * rom_addr`.
        let input = Constraint::from(gate_fam4_rom) * rom_addr_constraint;
        // output_k = is_fam4 * memwrite_k - gate_fam4_not_rom * memread_k, with
        // is_fam4 = (is_lw + is_sw) and gate_fam4_not_rom = (is_fam4 - gate_fam4_rom).
        let output1 = is_fam4_sum() * Constraint::from(memwrite_lo_var)
            - (is_fam4_sum() - Constraint::from(gate_fam4_rom)) * memread_low_c.clone();
        let output2 = is_fam4_sum() * Constraint::from(memwrite_hi_var)
            - (is_fam4_sum() - Constraint::from(gate_fam4_rom)) * memread_high_c.clone();
        let romread_table = Term::from(TableType::AlignedRomRead.to_num());
        // table_id = execute * gate_fam4_rom * romread_table — collapses to 0
        // (ZeroEntry) when another family fires or on padding.
        let table_id = Constraint::from(inputs.execute) * Term::from(gate_fam4_rom) * romread_table;
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
        // top_14 (RC-16) borrows limb 0 of the shared F1/F2/F4 Register —
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
        cs.add_constraint(
            Constraint::from(is_lw)
                * (Term::from(4u32) * Term::from(top_14)
                    + Term::from(2u32) * Term::from(bit_1)
                    + Term::from(bit_0)
                    - Term::from(readaddr_lo_var)),
        );
        // Decomposition gated on is_sw (deg 2): only SW rows bind it to writeaddr_lo.
        cs.add_constraint(
            Constraint::from(is_sw)
                * (Term::from(4u32) * Term::from(top_14)
                    + Term::from(2u32) * Term::from(bit_1)
                    + Term::from(bit_0)
                    - Term::from(writeaddr_lo_var)),
        );
        // Alignment trap (deg 2, gated on is_lw + is_sw — mutually exclusive
        // Booleans, so the gate is itself Boolean): bit_0 + bit_1 = 0 when
        // either Family-4 memory op fires.
        cs.add_constraint(
            (Constraint::from(is_lw) + Constraint::from(is_sw))
                * (Constraint::from(bit_0) + Constraint::from(bit_1)),
        );
    }

    vec![rom_request]
}
