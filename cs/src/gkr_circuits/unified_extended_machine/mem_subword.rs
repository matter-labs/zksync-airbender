//! Memory family of the unified extended machine: LW/LH/LHU/LB/LBU/SW/SH/SB, ROM-free.
//!
//! Every access is a plain RAM access of the word-aligned cell `addr & !3`, where
//! `addr = rs1 + imm` (no ROM range, no ROM tables: `.text` is never read by programs and
//! `.rodata`/`.data` are initialised by other means). The family has 4 flags — the two
//! dispatch bits `is_load` / `is_store` (they also drive the register-or-RAM switch of the
//! shared rs2 and rd access slots) and the two auxiliary bits `is_load_subword` /
//! `is_store_subword` — plus the shared `funct3` column, which carries `byte | sext << 1` for
//! sub-word ops. Everything else lives in the shared scratch pool: 4 Booleans (the two address
//! carries and the two byte-offset bits `b0`, `b1`), the RC-16 register limb 0 for the
//! word-cell index `top_14`, and 2 pool variables for the lookup "parts".
//!
//! Sub-word data path, all at the base layer and degree ≤ 2 (so it pools with the other
//! families' lookups): the halfword of the accessed word is never selected algebraically.
//! Instead each limb of the word gets its own lookup whose key carries a `sel` bit
//! (`1 - b1` for the low limb, `b1` for the high limb) and the tables return (0, …) for the
//! unselected limb:
//!
//! * loads (`is_load_subword`): `LoadSubwordLimb(r_lo || mode || b0 || 1-b1) -> (part_lo, part_hi)`
//!   and `LoadSubwordLimb(r_hi || mode || b0 || b1) -> (w_lo - part_lo, w_hi - part_hi)`, so
//!   `w = ext(selected halfword)`;
//! * stores (`is_store_subword`): `StoreSubwordKeep(o_limb || byte || b0 || sel) -> keep_limb`
//!   for both limbs of the old word and `StoreSubwordSource(rs2_lo || byte || b0 || sel) ->
//!   w_limb - keep_limb`, so `w = keep(old) + src(rs2)` limb-wise;
//! * halfword misalignment (`b0 = 1`) is trapped by the tables' `trap` output column, which
//!   the tuple pins to 0; word ops are trapped algebraically (`b0 + b1 = 0`).
//!
//! Word ops are `(is_load + is_store - is_load_subword - is_store_subword) * (w - r) = 0`.
use super::*;
use crate::cs::circuit_trait::*;
use crate::gkr_circuits::unified_reduced_machine::circuit::LookupRequest;
use crate::structured_expr::Expr;
use crate::tables::{
    LOAD_SUBWORD_LIMB_B0_SHIFT, LOAD_SUBWORD_LIMB_MODE_SHIFT, LOAD_SUBWORD_LIMB_SEL_SHIFT,
    STORE_SUBWORD_B0_SHIFT, STORE_SUBWORD_BYTE_SHIFT, STORE_SUBWORD_SEL_SHIFT,
};
use crate::types::*;
use crate::witness_placer::*;
use field::PrimeField;

use super::decoder::{MEM_FUNCT3_BYTE_BIT, MEM_FUNCT3_SEXT_BIT};

/// Shared scratch-Boolean pool slots: [0] = of_lo, [1] = of_hi (carries of rs1 + imm),
/// [2] = b0, [3] = b1 (byte offset of the access inside the word cell).
pub(super) const MEM_SCRATCH_BOOLS: usize = 4;

#[derive(Clone, Copy, Debug)]
pub(super) struct MemoryFlags {
    pub is_load: Boolean,
    pub is_store: Boolean,
    pub is_load_subword: Boolean,
    pub is_store_subword: Boolean,
}

#[allow(non_snake_case)]
pub(super) fn apply_extended_memory_inner<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    inputs: &OpcodeFamilyCircuitState<F>,
    flags: MemoryFlags,
    rs1_limbs: [Variable; REGISTER_SIZE],
    rs2_or_load_access: &RegisterOrRamAccess, // rs2 (register) or the loaded RAM word
    rd_or_store_access: &RegisterOrRamAccess, // rd (register) or the stored RAM word
    scratch_bools: [Boolean; MEM_SCRATCH_BOOLS],
    // Lookup "parts": low-limb load outputs / store keep values. Free on other rows.
    part_slots: [Variable; 2],
    // RC-16 slot (limb 0 of the shared register) for the word-cell index `addr_lo >> 2`.
    top_slot: Variable,
) -> Vec<LookupRequest<F>> {
    let MemoryFlags {
        is_load,
        is_store,
        is_load_subword,
        is_store_subword,
    } = flags;

    let WordRepresentation::U16Limbs(r_limbs) = rs2_or_load_access.read_value else {
        unreachable!("memread access must be allocated as U16Limbs")
    };
    let WordRepresentation::U16Limbs(o_limbs) = rd_or_store_access.read_value else {
        unreachable!("memwrite access must be allocated with U16 read limbs")
    };
    let WordRepresentation::U16Limbs(w_limbs) = rd_or_store_access.write_value else {
        unreachable!("memwrite access must be allocated with U16 write limbs")
    };
    let memread_addr = rs2_or_load_access.address;
    let memwrite_addr = rd_or_store_access.address;

    // The address limbs are pinned to 16 bits locally so the decomposition below is sound
    // without leaning on the memory argument's induction.
    for var in memread_addr.into_iter().chain(memwrite_addr) {
        cs.require_invariant(var, Invariant::RangeChecked { width: 16 });
    }

    let [readaddr_lo, readaddr_hi] = memread_addr.map(Expr::<F>::var);
    let [writeaddr_lo, writeaddr_hi] = memwrite_addr.map(Expr::<F>::var);

    // Register-slot binding of the two switchable accesses (fires for every non-memory
    // family too): the rs2 slot is a register unless a load, the rd slot unless a store.
    let memread_is_reg: Expr<F> = Expr::from(is_load.toggle());
    cs.add_constraint_expr(
        memread_is_reg.clone() * (readaddr_lo.clone() - Expr::var(inputs.decoder_data.rs2_index)),
    );
    cs.add_constraint_expr(memread_is_reg * readaddr_hi.clone());
    let memwrite_is_reg: Expr<F> = Expr::from(is_store.toggle());
    cs.add_constraint_expr(
        memwrite_is_reg.clone() * (writeaddr_lo.clone() - Expr::var(inputs.decoder_data.rd_index)),
    );
    cs.add_constraint_expr(memwrite_is_reg * writeaddr_hi.clone());

    let load: Expr<F> = Expr::from(is_load);
    let store: Expr<F> = Expr::from(is_store);
    let load_sub: Expr<F> = Expr::from(is_load_subword);
    let store_sub: Expr<F> = Expr::from(is_store_subword);
    // Word op (LW/SW) gate: linear in the flags (the auxiliary bits ride only with their
    // dispatch bit).
    let word = || load.clone() + store.clone() - load_sub.clone() - store_sub.clone();

    let of_lo = scratch_bools[0];
    let of_hi = scratch_bools[1];
    let b0 = scratch_bools[2];
    let b1 = scratch_bools[3];
    let [imm_lo_var, imm_hi_var] = inputs.decoder_data.imm;
    let funct3_var = inputs.decoder_data.funct3.expect("funct3 is present");
    let shift16 = F::from_u32_with_reduction(1 << 16);

    // ---- witness: everything of this family is derived here from the inputs -------------
    {
        let (is_load_var, is_load_neg) = is_load.variable_and_negation_constant();
        let (is_store_var, is_store_neg) = is_store.variable_and_negation_constant();
        let (is_load_sub_var, is_load_sub_neg) = is_load_subword.variable_and_negation_constant();
        let (is_store_sub_var, is_store_sub_neg) =
            is_store_subword.variable_and_negation_constant();
        let of_lo_var = of_lo.expect_variable();
        let of_hi_var = of_hi.expect_variable();
        let b0_var = b0.expect_variable();
        let b1_var = b1.expect_variable();
        let assume_assigned = CS::ASSUME_MEMORY_VALUES_ASSIGNED;

        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            type U16<CS, F> = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16;
            type Mask<CS, F> = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Mask;
            let flag = |placer: &mut CS::WitnessPlacer, var: Variable, neg: bool| {
                let raw = placer.get_boolean(var);
                if neg {
                    raw.negate()
                } else {
                    raw
                }
            };
            let is_load = flag(placer, is_load_var, is_load_neg);
            let is_store = flag(placer, is_store_var, is_store_neg);
            let is_load_sub = flag(placer, is_load_sub_var, is_load_sub_neg);
            let is_store_sub = flag(placer, is_store_sub_var, is_store_sub_neg);
            let is_mem = is_load.or(&is_store);

            // address = rs1 + imm, limb-wise with carries; the cell is `address & !3`
            let rs1_lo = placer.get_u16(rs1_limbs[0]);
            let rs1_hi = placer.get_u16(rs1_limbs[1]);
            let imm_lo = placer.get_u16(imm_lo_var);
            let imm_hi = placer.get_u16(imm_hi_var);
            let (addr_lo, carry_lo) = rs1_lo.overflowing_add(&imm_lo);
            let (_, carry_hi) = rs1_hi.overflowing_add_with_carry(&imm_hi, &carry_lo);
            let bit0 = addr_lo.get_bit(0);
            let bit1 = addr_lo.get_bit(1);
            let top = addr_lo.shr(2);
            placer.conditionally_assign_mask(of_lo_var, &is_mem, &carry_lo);
            placer.conditionally_assign_mask(of_hi_var, &is_mem, &carry_hi);
            placer.conditionally_assign_mask(b0_var, &is_mem, &bit0);
            placer.conditionally_assign_mask(b1_var, &is_mem, &bit1);
            placer.conditionally_assign_u16(top_slot, &is_mem, &top);

            let funct3 = placer.get_u8(funct3_var);
            let byte = funct3.get_bit(0);
            let sext = funct3.get_bit(1);
            let zero = U16::<CS, F>::constant(0);
            let r_lo = placer.get_u16(r_limbs[0]);
            let r_hi = placer.get_u16(r_limbs[1]);
            let o_lo = placer.get_u16(o_limbs[0]);
            let o_hi = placer.get_u16(o_limbs[1]);
            let sel_lo = bit1.negate();
            let sel_hi = bit1.clone();

            // sub-word load: extension of the selected halfword / byte
            let (ext_lo, ext_hi) = {
                let h = U16::<CS, F>::select(&bit1, &r_hi, &r_lo);
                let byte_sel =
                    U16::<CS, F>::select(&bit0, &h.shr(8), &h.and(&U16::<CS, F>::constant(0x00ff)));
                let value = U16::<CS, F>::select(&byte, &byte_sel, &h);
                let sign = Mask::<CS, F>::select(&byte, &byte_sel.get_bit(7), &h.get_bit(15));
                let extend = sext.and(&sign);
                let lo = U16::<CS, F>::select(
                    &extend.and(&byte),
                    &value.or(&U16::<CS, F>::constant(0xff00)),
                    &value,
                );
                let hi = U16::<CS, F>::select(&extend, &U16::<CS, F>::constant(0xffff), &zero);
                (lo, hi)
            };
            // low-limb load lookup outputs: `ext` iff the low limb is the selected one
            let part_a_lo = U16::<CS, F>::select(&sel_lo, &ext_lo, &zero);
            let part_a_hi = U16::<CS, F>::select(&sel_lo, &ext_hi, &zero);
            let w_load_lo = U16::<CS, F>::select(&is_load_sub, &ext_lo, &r_lo);
            let w_load_hi = U16::<CS, F>::select(&is_load_sub, &ext_hi, &r_hi);

            // sub-word store: keep(old limb) + src(rs2 low limb), limb-wise
            let keep = |limb: &U16<CS, F>, sel: &Mask<CS, F>| -> U16<CS, F> {
                let masked = U16::<CS, F>::select(
                    &bit0,
                    &limb.and(&U16::<CS, F>::constant(0x00ff)),
                    &limb.and(&U16::<CS, F>::constant(0xff00)),
                );
                let sub = U16::<CS, F>::select(&byte, &masked, &zero);
                U16::<CS, F>::select(sel, &sub, limb)
            };
            let src = |sel: &Mask<CS, F>| -> U16<CS, F> {
                let low_byte = r_lo.and(&U16::<CS, F>::constant(0x00ff));
                let shifted = U16::<CS, F>::select(&bit0, &low_byte.shl(8), &low_byte);
                let sub = U16::<CS, F>::select(&byte, &shifted, &r_lo);
                U16::<CS, F>::select(sel, &sub, &zero)
            };
            let keep_lo = keep(&o_lo, &sel_lo);
            let keep_hi = keep(&o_hi, &sel_hi);
            let mut w_sub_lo = keep_lo.clone();
            w_sub_lo.add_assign(&src(&sel_lo));
            let mut w_sub_hi = keep_hi.clone();
            w_sub_hi.add_assign(&src(&sel_hi));
            let w_store_lo = U16::<CS, F>::select(&is_store_sub, &w_sub_lo, &r_lo);
            let w_store_hi = U16::<CS, F>::select(&is_store_sub, &w_sub_hi, &r_hi);

            let part_lo = U16::<CS, F>::select(&is_store, &keep_lo, &part_a_lo);
            let part_hi = U16::<CS, F>::select(&is_store, &keep_hi, &part_a_hi);
            placer.conditionally_assign_u16(part_slots[0], &is_mem, &part_lo);
            placer.conditionally_assign_u16(part_slots[1], &is_mem, &part_hi);

            // Self-generating witness (no-ASSUME contract): the write value is derived here,
            // never taken from the oracle.
            if !assume_assigned {
                let w_lo = U16::<CS, F>::select(&is_store, &w_store_lo, &w_load_lo);
                let w_hi = U16::<CS, F>::select(&is_store, &w_store_hi, &w_load_hi);
                placer.conditionally_assign_u16(w_limbs[0], &is_mem, &w_lo);
                placer.conditionally_assign_u16(w_limbs[1], &is_mem, &w_hi);
            }
        };
        cs.set_values(value_fn);
    }

    // ---- address: rs1 + imm = cell + b0 + 2 b1, cell word-aligned ------------------------
    let rs1_lo: Expr<F> = Expr::var(rs1_limbs[0]);
    let rs1_hi: Expr<F> = Expr::var(rs1_limbs[1]);
    let imm_lo: Expr<F> = Expr::var(imm_lo_var);
    let imm_hi: Expr<F> = Expr::var(imm_hi_var);
    let offset = || Expr::from(b0) + Expr::from(b1) * F::from_u32_with_reduction(2);
    let top: Expr<F> = Expr::var(top_slot);

    // is_load * (rs1_lo + imm_lo - readaddr_lo - b0 - 2 b1 - 2^16 of_lo)
    //   + is_store * (rs1_lo + imm_lo - writeaddr_lo - b0 - 2 b1 - 2^16 of_lo) = 0
    cs.add_constraint_expr(
        load.clone()
            * (rs1_lo.clone() + imm_lo.clone()
                - readaddr_lo.clone()
                - offset()
                - Expr::from(of_lo) * shift16)
            + store.clone()
                * (rs1_lo.clone() + imm_lo.clone()
                    - writeaddr_lo.clone()
                    - offset()
                    - Expr::from(of_lo) * shift16),
    );
    // high limb with the carry
    cs.add_constraint_expr(
        load.clone()
            * (rs1_hi.clone() + imm_hi.clone() + Expr::from(of_lo)
                - readaddr_hi.clone()
                - Expr::from(of_hi) * shift16)
            + store.clone()
                * (rs1_hi.clone() + imm_hi.clone() + Expr::from(of_lo)
                    - writeaddr_hi.clone()
                    - Expr::from(of_hi) * shift16),
    );
    // word alignment of the cell: addr_lo = 4 * top_14 (both RC-16, so an integer identity)
    cs.add_constraint_expr(
        load.clone() * (readaddr_lo.clone() - top.clone() * F::from_u32_with_reduction(4))
            + store.clone() * (writeaddr_lo.clone() - top * F::from_u32_with_reduction(4)),
    );
    // With `addr_lo ≡ 0 (mod 4)`, `rs1_lo + imm_lo < 2^17` and `addr_lo < 2^16`, the low-limb
    // equation pins `(of_lo, b0, b1)` uniquely as the carry and the two low bits of rs1 + imm.

    // ---- word ops: w = r and the alignment trap ------------------------------------------
    let [r_lo, r_hi] = r_limbs.map(Expr::<F>::var);
    let [o_lo, o_hi] = o_limbs.map(Expr::<F>::var);
    let [w_lo, w_hi] = w_limbs.map(Expr::<F>::var);
    cs.add_constraint_expr(word() * (w_lo.clone() - r_lo.clone()));
    cs.add_constraint_expr(word() * (w_hi.clone() - r_hi.clone()));
    cs.add_constraint_expr(word() * (Expr::from(b0) + Expr::from(b1)));

    // ---- sub-word ops: per-limb lookups --------------------------------------------------
    let funct3: Expr<F> = Expr::var(funct3_var);
    let [part_lo, part_hi] = part_slots.map(Expr::<F>::var);
    let sel_lo = || Expr::<F>::one() - Expr::from(b1);
    let sel_hi = || Expr::<F>::from(b1);
    let pow2 = |bits: usize| F::from_u32_with_reduction(1 << bits);

    let load_key = |limb: Expr<F>, sel: Expr<F>| -> Expr<F> {
        load_sub.clone()
            * (limb
                + funct3.clone() * pow2(LOAD_SUBWORD_LIMB_MODE_SHIFT)
                + Expr::from(b0) * pow2(LOAD_SUBWORD_LIMB_B0_SHIFT)
                + sel * pow2(LOAD_SUBWORD_LIMB_SEL_SHIFT))
    };
    let store_key = |limb: Expr<F>, sel: Expr<F>| -> Expr<F> {
        store_sub.clone()
            * (limb
                + funct3.clone() * pow2(STORE_SUBWORD_BYTE_SHIFT)
                + Expr::from(b0) * pow2(STORE_SUBWORD_B0_SHIFT)
                + sel * pow2(STORE_SUBWORD_SEL_SHIFT))
    };
    let load_table = || load_sub.clone() * Expr::from(TableType::LoadSubwordLimb);
    let keep_table = || store_sub.clone() * Expr::from(TableType::StoreSubwordKeep);
    let source_table = || store_sub.clone() * Expr::from(TableType::StoreSubwordSource);

    // Table rows are (key, out_lo, out_hi, trap) for loads and (key, keep, trap) for the
    // store keep side: positions the tuple leaves at 0 pin the trap columns to 0.
    let low_limb = LookupRequest::new(
        load_table() + keep_table(),
        vec![
            load_key(r_lo.clone(), sel_lo()) + store_key(o_lo, sel_lo()),
            (load_sub.clone() + store_sub.clone()) * part_lo.clone(),
            load_sub.clone() * part_hi.clone(),
        ],
    );
    let high_limb = LookupRequest::new(
        load_table() + keep_table(),
        vec![
            load_key(r_hi, sel_hi()) + store_key(o_hi, sel_hi()),
            load_sub.clone() * (w_lo.clone() - part_lo.clone())
                + store_sub.clone() * part_hi.clone(),
            load_sub.clone() * (w_hi.clone() - part_hi.clone()),
        ],
    );
    // rs2's low limb is the source of SH/SB (the rs2 slot is a register read on stores)
    let source_low_limb = LookupRequest::new(
        source_table(),
        vec![
            store_key(r_lo.clone(), sel_lo()),
            store_sub.clone() * (w_lo - part_lo),
        ],
    );
    let source_high_limb = LookupRequest::new(
        source_table(),
        vec![
            store_key(r_lo, sel_hi()),
            store_sub.clone() * (w_hi - part_hi),
        ],
    );

    let _ = (MEM_FUNCT3_BYTE_BIT, MEM_FUNCT3_SEXT_BIT); // key layout documented in `decoder.rs`

    vec![low_limb, high_limb, source_low_limb, source_high_limb]
}
