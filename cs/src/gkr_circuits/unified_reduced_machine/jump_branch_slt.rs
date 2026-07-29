use super::*;
use crate::constraint::{Constraint, Term};
use crate::cs::circuit_trait::*;
use crate::cs::lookup_utils::peek_lookup_values_unconstrained_into_variables_from_constraints_conditional;
use crate::gkr_circuits::jump_branch_slt_family::JumpSltBranchFamilyCircuitMask;
use crate::gkr_circuits::utils::update_intermediate_carry_value;
use crate::structured_expr::Expr;
use crate::tables::{
    TableDriver, TableType, CONDITIONAL_RESOLUTION_EQ_BIT_SHIFT,
    CONDITIONAL_RESOLUTION_FUNCT3_BIT_SHIFT, CONDITIONAL_RESOLUTION_SRC1_SIGN_BIT_SHIFT,
    CONDITIONAL_RESOLUTION_UNSIGNED_LT_BIT_SHIFT,
};
use crate::types::*;
use crate::witness_placer::*;
use field::PrimeField;

use super::circuit::{LookupRequest, F2_SCRATCH_BOOLS, F2_SCRATCH_VARS};

const UNIFIED_JUMP_BRANCH_SLT_TABLES_WIDTH: usize = 3;

/// Tables the unified Family-2 (jump/branch/slt) body looks up into. Mirrors the standalone
/// `jump_branch_slt_tables()` but swaps the 2^22 `ConditionalJmpBranchSlt` resolution table
/// for the 2^7 `ConditionalJmpBranchSltUnified` variant (rs2-sign split). The unified circuit
/// pays a separate `U16GetSign` lookup to feed the sign bit;
pub fn jump_branch_slt_unified_tables() -> Vec<TableType> {
    vec![
        TableType::RegIsZero,
        TableType::U16GetSign,
        TableType::ConditionalJmpBranchSltUnified,
        TableType::JumpCleanupOffset,
    ]
}

pub fn jump_branch_slt_unified_table_addition_fn<F: PrimeField, CS: Circuit<F>>(cs: &mut CS) {
    for el in jump_branch_slt_unified_tables() {
        cs.materialize_table::<UNIFIED_JUMP_BRANCH_SLT_TABLES_WIDTH>(el);
    }
}

pub fn jump_branch_slt_unified_table_driver_fn<F: PrimeField>(table_driver: &mut TableDriver<F>) {
    for el in jump_branch_slt_unified_tables() {
        table_driver.materialize_table::<UNIFIED_JUMP_BRANCH_SLT_TABLES_WIDTH>(el);
    }
}

/// Family 2 (jump/branch/slt) constraints for the unified circuit. Mirrors the
/// standalone inner with two unified-specific adaptations:
/// (1) the `JumpCleanupOffset` lookup is gated so non-Family-2 cycles route to
/// `ZeroEntry`, and (2) the rd-write constraints are gated on per-opcode
/// `is_X_writes_rd` Booleans so non-Family-2 cycles don't pin rd_write_limbs.
pub fn apply_unified_jump_branch_slt_inner<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    inputs: OpcodeFamilyCircuitState<F>,
    decoder: JumpSltBranchFamilyCircuitMask,
    rs1_limbs: [Variable; 2],
    rs2_limbs: [Variable; 2],
    rd_write_limbs: [Variable; 2],
    intermediate_reg: Register<F>,
    scratch_bools: [Boolean; F2_SCRATCH_BOOLS],
    scratch_vars: [Variable; F2_SCRATCH_VARS],
) -> Vec<LookupRequest<F>> {
    // U16 views of rs1/rs2 reassembled from U8 bytes via free algebra.
    // Only the high rs1 limb is still needed as a `Constraint` (fed to the
    // out-of-scope lookup plumbing); the other limb views are inlined as
    // `Expr::var(...)` directly at their constraint sites.
    let rs1_high_c: Expr<F> = Expr::from(rs1_limbs[1]);

    // we do NOT need range checks on RD write values, as they will be results of masking
    // based on rd == x0 predicate. But we will need to add some temporary variables to get addition results

    // short note on the opcodes
    // - jal jumps based on current PC (0 mod 4 for all rows that matter)
    // - jalr jumps based on rs1 value
    // - slt loads a value into the RD based on comparison of rs1 and rs2 (or corresponding immediate)
    // - branch jumps using immediate offsets based on the result of comparison of rs1 and rs2

    // we will need to allocate 2 u32 intermediate values
    // first one:
    // for jal/jalr - it's pc + 4 to potentially to write to the output register
    // for branch and slt we use it for intermediate comparison result
    // second one is partial (lower half):
    // for jal/jalr it'll be jump destination address
    // for taken(!) branch it'll be potential jump destination address
    // we will also in the process materialize "not jump" boolean
    // for not taken(!) branch we will do pc + 4
    // for slt it'll be pc + 4
    // because for all jump-like opcodes we only need to cleanup the lowest word,
    // then we can target PC's high part as the output variable

    let carry_shift = F::from_u32_with_reduction(1 << 16);

    // we need range checks on high PC part
    cs.require_invariant(
        inputs.cycle_start_state.pc[1],
        Invariant::RangeChecked { width: 16 },
    );

    let pc_intermediate_addition_tmp_low =
        cs.add_named_variable("Intermedaite low for PC computation");
    cs.require_invariant(
        pc_intermediate_addition_tmp_low,
        Invariant::RangeChecked { width: 16 },
    );

    // and we need 4 intermediate booleans — aliased into the shared scratch-Boolean
    // pool slots [0..4] (branch-local: consumed only inside is_jal/is_jalr/is_branch/is_slt
    // gated add-like constraints, so free on non-Family-2 rows).
    let intermediate_bools: [Boolean; 4] = core::array::from_fn(|i| scratch_bools[i]);

    let is_branch = decoder.perform_branch();
    let is_slt = decoder.perform_slt();
    let is_jal = decoder.perform_jal();
    let is_jalr = decoder.perform_jalr();
    let rd_is_zero = decoder.rd_is_zero();

    // is_fam2 = is_jal + is_jalr + is_slt + is_branch; the decoder one-hot +
    // dispatch constraint keep this sum in {0, 1}. Used to gate F2's lookups so
    // they fold into the shared pool (ZeroEntry / 0-tuple on non-F2 rows).
    // Family-2 mask as an `Expr` so `is_fam2_sum() * input` stays ONE multiplication (a product of
    // the 4-flag sum and the input) rather than the 4 distributed products a `Constraint` yields.
    // Witness-only `peek` sites, which need a `Constraint`, lower it via `to_max_quadratic_constraint`.
    let is_fam2_sum = || -> Expr<F> {
        Expr::from(is_jal) + Expr::from(is_jalr) + Expr::from(is_slt) + Expr::from(is_branch)
    };
    // Family-2 sub-opcode flag variables, OR-ed in-witness to form the is_fam2 mask
    // that gates the conditional pool-slot peeks (lookup outputs share the scratch
    // Variable pool with Family 3, so their witness writes must be conditional).
    let f2_flag_vars = [
        is_jal.expect_variable(),
        is_jalr.expect_variable(),
        is_slt.expect_variable(),
        is_branch.expect_variable(),
    ];

    // NOTE: as usual, for SLT/SLTI if we have immediate variant, then we have x0 as rs2,
    // so we can avoid selections

    // on comparison: assume we want do a < b signed or unsigned
    // unsigned case if easy - we just need to look at the underflow flag
    // signed case if painful: if signs are the same, then underflow flag is enough,
    // but if signs are different, and a < 0, then underflow flag would not be set.
    // Opposite is also true: if a > 0, then underflow flag would not be set too.
    // So we need to inspect signs of both input operands, and we do so using 1 lookup
    // access to get sign of `a`, and then use single lookup table of
    // `b_high` | of flag | zero_flag | funct3 to decide to take branch or not,
    // and to resolve slt/sltu

    // witness generation functions come first, so when constraints are added we can try to evaluate them
    // in debug cases

    let [add_rel_0_intermediate_of, add_rel_0_final_of, add_rel_1_intermediate_of, add_rel_1_final_of] =
        intermediate_bools;

    let [comparison_rel_or_jump_saved_pc_low, comparison_rel_or_jump_saved_pc_high] =
        intermediate_reg.0.map(|el| el.get_variable());

    let add_rel_0_intermediate_of_var = add_rel_0_intermediate_of.expect_variable();
    let add_rel_0_final_of_var = add_rel_0_final_of.expect_variable();

    let add_rel_1_intermediate_of_var = add_rel_1_intermediate_of.expect_variable();
    let add_rel_1_final_of_var = add_rel_1_final_of.expect_variable();

    {
        let imm_vars = inputs.decoder_data.imm;
        let pc_in_vars = inputs.cycle_start_state.pc;
        let rs1_vars = rs1_limbs;
        let rs2_vars = rs2_limbs;

        let is_branch_var = is_branch.expect_variable();
        let is_slt_var = is_slt.expect_variable();
        let is_jal_var = is_jal.expect_variable();
        let is_jalr_var = is_jalr.expect_variable();

        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            // NOTE: it is UNCONDITIONAL assignment, even though we select across multiple variants

            let mut out_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0);
            let mut intermedaite_of_value =
                <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false);
            let mut of_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false);

            let imm_low = placer.get_u16(imm_vars[0]);
            let imm = placer.get_u32_from_u16_parts(imm_vars);
            let rs1_low = placer.get_u16(rs1_vars[0]);
            let rs1_u32 = placer.get_u32_from_u16_parts(rs1_vars);
            let rs2_low = placer.get_u16(rs2_vars[0]);
            let rs2_u32 = placer.get_u32_from_u16_parts(rs2_vars);
            let pc_low = placer.get_u16(pc_in_vars[0]);
            let pc_u32 = placer.get_u32_from_u16_parts(pc_in_vars);

            {
                // UNSIGNED comparison of rs1 and rs2, but IMM is NOT used
                let is_branch = placer.get_boolean(is_branch_var);
                let (sub_result, of0) = rs1_u32.overflowing_sub(&rs2_u32);
                out_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                    &is_branch,
                    &sub_result,
                    &out_value,
                );
                of_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                    &is_branch, &of0, &of_value,
                );
                update_intermediate_carry_value::<F, CS::WitnessPlacer, true>(
                    &mut intermedaite_of_value,
                    &is_branch,
                    &rs1_low,
                    &rs2_low,
                    None,
                );
            }
            {
                // UNSIGNED comparison of rs1 and rs2, but IMM is used(!)
                let is_slt = placer.get_boolean(is_slt_var);
                let (sub_result, of0) = rs1_u32.overflowing_sub(&rs2_u32);
                let (sub_result, of1) = sub_result.overflowing_sub(&imm);
                let of = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::or(&of0, &of1);
                out_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                    &is_slt,
                    &sub_result,
                    &out_value,
                );
                of_value =
                    <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(&is_slt, &of, &of_value);
                update_intermediate_carry_value::<F, CS::WitnessPlacer, true>(
                    &mut intermedaite_of_value,
                    &is_slt,
                    &rs1_low,
                    &rs2_low,
                    Some(&imm_low),
                );
            }
            {
                // for JAL and JALR we compute pc + 4
                let is_jal = placer.get_boolean(is_jal_var);
                let is_jalr = placer.get_boolean(is_jalr_var);
                let is_jump = is_jal.or(&is_jalr);

                let (jump_result, of) = pc_u32.overflowing_add(
                    &<CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(
                        core::mem::size_of::<u32>() as u32,
                    ),
                );
                out_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                    &is_jump,
                    &jump_result,
                    &out_value,
                );
                of_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                    &is_jump, &of, &of_value,
                );
                update_intermediate_carry_value::<F, CS::WitnessPlacer, false>(
                    &mut intermedaite_of_value,
                    &is_jump,
                    &pc_low,
                    &<CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(
                        core::mem::size_of::<u32>() as u16,
                    ),
                    None,
                );
            }

            // Conditional-only write (shared Register with F1's intermediate_tmp):
            // gate on F2-active so non-F2 rows leave the slot to F1 / the chain
            // default (0). out_value is already 0 when no F2 op fires.
            let is_fam2 = {
                let mut m = placer.get_boolean(is_branch_var);
                m = m.or(&placer.get_boolean(is_slt_var));
                m = m.or(&placer.get_boolean(is_jal_var));
                m = m.or(&placer.get_boolean(is_jalr_var));
                m
            };
            placer.conditionally_assign_u32(
                [
                    comparison_rel_or_jump_saved_pc_low,
                    comparison_rel_or_jump_saved_pc_high,
                ],
                &is_fam2,
                &out_value,
            );
            // Conditional on is_fam2: these carry bools alias shared bool-pool slots,
            // so non-Family-2 rows must leave them to the pool default / sibling families.
            placer.conditionally_assign_mask(
                add_rel_0_intermediate_of_var,
                &is_fam2,
                &intermedaite_of_value,
            );
            placer.conditionally_assign_mask(add_rel_0_final_of_var, &is_fam2, &of_value);
        };
        cs.set_values(value_fn);
    }

    // now we can put the constraint for such addition
    {
        let mut add_like_low_constraint = Expr::<F>::zero();
        // first addend
        add_like_low_constraint = add_like_low_constraint
            + Expr::from(is_jal) * Expr::var(inputs.cycle_start_state.pc[0]);
        add_like_low_constraint = add_like_low_constraint
            + Expr::from(is_jalr) * Expr::var(inputs.cycle_start_state.pc[0]);
        // for subtraction 2^16*of + a - b = c -> 2^16*of + a = b + c
        // so we use output for the first addend, and keep second addend unchanged
        add_like_low_constraint = add_like_low_constraint
            + Expr::from(is_branch) * Expr::var(comparison_rel_or_jump_saved_pc_low);
        add_like_low_constraint = add_like_low_constraint
            + Expr::from(is_slt) * Expr::var(comparison_rel_or_jump_saved_pc_low);
        // second addend
        // NOTE: for additions we blindly mix imm and rs2 as preprocessing ensures that if imm !=0 then rs2 = x0
        add_like_low_constraint = add_like_low_constraint
            + Expr::from(is_jal) * Expr::from(common_constants::PC_STEP as u32);
        add_like_low_constraint = add_like_low_constraint
            + Expr::from(is_jalr) * Expr::from(common_constants::PC_STEP as u32);
        add_like_low_constraint =
            add_like_low_constraint + Expr::from(is_branch) * Expr::var(rs2_limbs[0]);
        add_like_low_constraint =
            add_like_low_constraint + Expr::from(is_slt) * Expr::var(rs2_limbs[0]);
        add_like_low_constraint =
            add_like_low_constraint + Expr::from(is_slt) * Expr::var(inputs.decoder_data.imm[0]);
        // out-like var
        add_like_low_constraint = add_like_low_constraint
            - Expr::from(is_jal) * Expr::var(comparison_rel_or_jump_saved_pc_low);
        add_like_low_constraint = add_like_low_constraint
            - Expr::from(is_jalr) * Expr::var(comparison_rel_or_jump_saved_pc_low);
        add_like_low_constraint =
            add_like_low_constraint - Expr::from(is_branch) * Expr::var(rs1_limbs[0]);
        add_like_low_constraint =
            add_like_low_constraint - Expr::from(is_slt) * Expr::var(rs1_limbs[0]);

        // intermediate carry
        add_like_low_constraint = add_like_low_constraint
            - Expr::from(is_jal)
                * Expr::constant(carry_shift)
                * Expr::var(add_rel_0_intermediate_of_var);
        add_like_low_constraint = add_like_low_constraint
            - Expr::from(is_jalr)
                * Expr::constant(carry_shift)
                * Expr::var(add_rel_0_intermediate_of_var);
        add_like_low_constraint = add_like_low_constraint
            - Expr::from(is_branch)
                * Expr::constant(carry_shift)
                * Expr::var(add_rel_0_intermediate_of_var);
        add_like_low_constraint = add_like_low_constraint
            - Expr::from(is_slt)
                * Expr::constant(carry_shift)
                * Expr::var(add_rel_0_intermediate_of_var);
        cs.add_constraint_expr(add_like_low_constraint);

        // high part
        let mut add_like_high_constraint = Expr::<F>::zero();
        // intermediate carry
        add_like_high_constraint = add_like_high_constraint
            + Expr::from(is_jal) * Expr::var(add_rel_0_intermediate_of_var);
        add_like_high_constraint = add_like_high_constraint
            + Expr::from(is_jalr) * Expr::var(add_rel_0_intermediate_of_var);
        add_like_high_constraint = add_like_high_constraint
            + Expr::from(is_branch) * Expr::var(add_rel_0_intermediate_of_var);
        add_like_high_constraint = add_like_high_constraint
            + Expr::from(is_slt) * Expr::var(add_rel_0_intermediate_of_var);
        // first addend
        add_like_high_constraint = add_like_high_constraint
            + Expr::from(is_jal) * Expr::var(inputs.cycle_start_state.pc[1]);
        add_like_high_constraint = add_like_high_constraint
            + Expr::from(is_jalr) * Expr::var(inputs.cycle_start_state.pc[1]);
        add_like_high_constraint = add_like_high_constraint
            + Expr::from(is_branch) * Expr::var(comparison_rel_or_jump_saved_pc_high);
        add_like_high_constraint = add_like_high_constraint
            + Expr::from(is_slt) * Expr::var(comparison_rel_or_jump_saved_pc_high);
        // second addend
        // NOTE: for additions we blindly mix imm and rs2 as preprocessing ensures that if imm !=0 then rs2 = x0
        add_like_high_constraint =
            add_like_high_constraint + Expr::from(is_branch) * Expr::var(rs2_limbs[1]);
        add_like_high_constraint =
            add_like_high_constraint + Expr::from(is_slt) * Expr::var(rs2_limbs[1]);
        add_like_high_constraint =
            add_like_high_constraint + Expr::from(is_slt) * Expr::var(inputs.decoder_data.imm[1]);
        // out-like
        add_like_high_constraint = add_like_high_constraint
            - Expr::from(is_jal) * Expr::var(comparison_rel_or_jump_saved_pc_high);
        add_like_high_constraint = add_like_high_constraint
            - Expr::from(is_jalr) * Expr::var(comparison_rel_or_jump_saved_pc_high);
        add_like_high_constraint =
            add_like_high_constraint - Expr::from(is_branch) * Expr::var(rs1_limbs[1]);
        add_like_high_constraint =
            add_like_high_constraint - Expr::from(is_slt) * Expr::var(rs1_limbs[1]);
        // final carry
        add_like_high_constraint = add_like_high_constraint
            - Expr::from(is_jal) * Expr::constant(carry_shift) * Expr::var(add_rel_0_final_of_var);
        add_like_high_constraint = add_like_high_constraint
            - Expr::from(is_jalr) * Expr::constant(carry_shift) * Expr::var(add_rel_0_final_of_var);
        add_like_high_constraint = add_like_high_constraint
            - Expr::from(is_branch)
                * Expr::constant(carry_shift)
                * Expr::var(add_rel_0_final_of_var);
        add_like_high_constraint = add_like_high_constraint
            - Expr::from(is_slt) * Expr::constant(carry_shift) * Expr::var(add_rel_0_final_of_var);
        cs.add_constraint_expr(add_like_high_constraint);
    }

    // now we should compare the output result to 0,
    // then resolve jump/slt condition

    let comparison_result_is_zero = scratch_vars[0];
    let regiszero_input: Expr<F> = Expr::from(comparison_rel_or_jump_saved_pc_low)
        + Expr::from(comparison_rel_or_jump_saved_pc_high);
    let regiszero_table = || is_fam2_sum() * Expr::from(TableType::RegIsZero.to_num());
    peek_lookup_values_unconstrained_into_variables_from_constraints_conditional(
        cs,
        &[(is_fam2_sum() * regiszero_input.clone()).to_max_quadratic_constraint()],
        &[comparison_result_is_zero],
        regiszero_table().to_max_quadratic_constraint(),
        &f2_flag_vars,
    );
    let regiszero_request = LookupRequest::new(
        regiszero_table(),
        vec![
            is_fam2_sum() * regiszero_input,
            is_fam2_sum() * Expr::from(comparison_result_is_zero),
        ],
    );

    // sign of rs1's high U16 limb (reassembled from the high two bytes — that's
    // exactly `rs1_high_c`). U16GetSign maps the full 16-bit value to its sign.
    let rs1_sign = scratch_vars[1];
    let u16getsign_table = || is_fam2_sum() * Expr::from(TableType::U16GetSign.to_num());
    peek_lookup_values_unconstrained_into_variables_from_constraints_conditional(
        cs,
        &[(is_fam2_sum() * rs1_high_c.clone()).to_max_quadratic_constraint()],
        &[rs1_sign],
        u16getsign_table().to_max_quadratic_constraint(),
        &f2_flag_vars,
    );
    let u16getsign_request = LookupRequest::new(
        u16getsign_table(),
        vec![
            is_fam2_sum() * rs1_high_c.clone(),
            is_fam2_sum() * Expr::from(rs1_sign),
        ],
    );

    // and now we can resolve jump. Note that SLT/SLTU use the same formal(!) funct3 as BLT/BLTU,
    // and for JAL/JALR we formally set funct3 to be such that jump resolution will be always
    // false, so in computing next PC below we can avoid thinking about overlapping
    // boolean conditions. The packed input references rs1_sign +
    // comparison_result_is_zero (peeked above); the witness resolver orders the
    // peeks by data dependency.
    // Second-operand sign source for the comparison table. The second operand's sign
    // bit is extracted from this 16-bit source by the separate U16GetSign lookup below
    // and fed to the resolution table as bit 0 of its 7-bit key. For the immediate
    // variant (SLT/SLTI: the decoder forces rs2 = x0 and carries the operand in `imm`)
    // that sign must come from the immediate's high limb, not rs2's (which is 0) --
    // otherwise signed `slti` with a negative immediate resolves to the wrong value.
    // Gated by `is_slt` so BRANCH keeps rs2's high limb (its `imm` is the jump offset,
    // not a comparison operand). The standalone `jump_branch_slt_family` circuit
    // applies the same fix. Lives in the shared scratch pool (layer 0, like `rs1_sign`,
    // so the pooled lookup input stays single-layer); needs its own slot because the
    // gated term is degree 2 and lookup inputs must be degree 1. NOTE: U16GetSign's
    // 2^16 key domain also preserves the `slt_sign_source < 2^16` range enforcement
    // that the old 2^22 resolution-table key provided — do not swap it for a
    // wider-domain sign table.
    let slt_sign_source = scratch_vars[3];
    let imm_high_var = inputs.decoder_data.imm[1];
    let is_slt_var = is_slt.expect_variable();
    {
        let rs2_high_var = rs2_limbs[1];
        let f2_flags = f2_flag_vars;
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let rs2_high = placer.get_u16(rs2_high_var);
            let imm_high = placer.get_u16(imm_high_var);
            let is_slt = placer.get_boolean(is_slt_var);
            let zero = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(0);
            let addend =
                <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::select(&is_slt, &imm_high, &zero);
            // No overflow: mutual exclusion (imm != 0 => rs2 = x0) keeps the sum <= 0xFFFF.
            let (sign_source, _of) = rs2_high.overflowing_add(&addend);
            // Aliased pool slot (shared with Family 3): write only when F2 fires.
            let is_fam2 = {
                let mut m = placer.get_boolean(f2_flags[0]);
                m = m.or(&placer.get_boolean(f2_flags[1]));
                m = m.or(&placer.get_boolean(f2_flags[2]));
                m = m.or(&placer.get_boolean(f2_flags[3]));
                m
            };
            placer.conditionally_assign_u16(slt_sign_source, &is_fam2, &sign_source);
        };
        cs.set_values(value_fn);
    }
    // Gated binding `slt_sign_source = rs2_high + is_slt * imm_high` on F2 rows. `is_slt` is
    // a decoder one-hot family bit, provably zero on every non-Family-2 row (enforced by the
    // dispatch one-hot in `circuit.rs`), so gating only the rs2_high / slt_sign_source terms
    // by `is_fam2_sum()` keeps this degree 2 while the whole constraint still vanishes on
    // non-F2 rows (leaving the aliased slot free for Family 3).
    cs.add_constraint_expr(
        (Expr::from(is_jal) + Expr::from(is_jalr) + Expr::from(is_slt) + Expr::from(is_branch))
            * Expr::var(slt_sign_source)
            - (Expr::from(is_jal)
                + Expr::from(is_jalr)
                + Expr::from(is_slt)
                + Expr::from(is_branch))
                * Expr::var(rs2_limbs[1])
            - Expr::var(is_slt_var) * Expr::var(imm_high_var),
    );

    // Second operand's sign bit, extracted from the sign source. The resolution table
    // takes the 1-bit sign directly (bit 0 of its 7-bit key); this lookup replaces the
    // old table's internal `bit 15 of the packed sign source` read. The input MUST be
    // `slt_sign_source` (not raw rs2_high) — see the sign-source comment above; the
    // structural tests in both this circuit and the standalone family pin that feed.
    let rs2_sign = scratch_vars[4];
    peek_lookup_values_unconstrained_into_variables_from_constraints_conditional(
        cs,
        &[(is_fam2_sum() * Expr::from(slt_sign_source)).to_max_quadratic_constraint()],
        &[rs2_sign],
        u16getsign_table().to_max_quadratic_constraint(),
        &f2_flag_vars,
    );
    let rs2_sign_request = LookupRequest::new(
        u16getsign_table(),
        vec![
            is_fam2_sum() * Expr::from(slt_sign_source),
            is_fam2_sum() * Expr::from(rs2_sign),
        ],
    );

    let should_jump_or_slt_value = scratch_vars[2];
    let cond_jmp_input: Expr<F> = Expr::from(rs2_sign)
        + Expr::from(rs1_sign)
            * F::from_u32(1 << CONDITIONAL_RESOLUTION_SRC1_SIGN_BIT_SHIFT).unwrap()
        + Expr::from(add_rel_0_final_of_var)
            * F::from_u32(1 << CONDITIONAL_RESOLUTION_UNSIGNED_LT_BIT_SHIFT).unwrap()
        + Expr::from(comparison_result_is_zero)
            * F::from_u32(1 << CONDITIONAL_RESOLUTION_EQ_BIT_SHIFT).unwrap()
        + Expr::from(inputs.decoder_data.funct3.expect("must have funct3"))
            * F::from_u32(1 << CONDITIONAL_RESOLUTION_FUNCT3_BIT_SHIFT).unwrap();
    let cond_jmp_table =
        || is_fam2_sum() * Expr::from(TableType::ConditionalJmpBranchSltUnified.to_num());
    peek_lookup_values_unconstrained_into_variables_from_constraints_conditional(
        cs,
        &[(is_fam2_sum() * cond_jmp_input.clone()).to_max_quadratic_constraint()],
        &[should_jump_or_slt_value],
        cond_jmp_table().to_max_quadratic_constraint(),
        &f2_flag_vars,
    );
    let cond_jmp_request = LookupRequest::new(
        cond_jmp_table(),
        vec![
            is_fam2_sum() * cond_jmp_input,
            is_fam2_sum() * Expr::from(should_jump_or_slt_value),
        ],
    );
    let should_jump_if_branch = cs.add_named_variable("should jump if BRANCH opcode");

    // now we can compute next PC, as well as PC that will be placed into RD for JAL/JALR
    // NOTE: if branch is NOT taken then we treat it as jump by constant offset of 4

    {
        let imm_vars = inputs.decoder_data.imm;
        let pc_in_vars = inputs.cycle_start_state.pc;
        let pc_out_vars = [
            pc_intermediate_addition_tmp_low,
            inputs.cycle_end_state.pc[1],
        ];
        let rs1_vars = rs1_limbs;

        let is_slt_var = is_slt.expect_variable();
        let is_jal_var = is_jal.expect_variable();
        let is_jalr_var = is_jalr.expect_variable();
        let is_branch_var = is_branch.expect_variable();

        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            // NOTE: it is UNCONDITIONAL assignment, even though we select across multiple variants

            let imm_low = placer.get_u16(imm_vars[0]);
            let imm = placer.get_u32_from_u16_parts(imm_vars);
            let rs1_low = placer.get_u16(rs1_vars[0]);
            let rs1_u32 = placer.get_u32_from_u16_parts(rs1_vars);
            let pc_low = placer.get_u16(pc_in_vars[0]);
            let pc_u32 = placer.get_u32_from_u16_parts(pc_in_vars);

            // easy case for extra var if jump
            let should_jump = {
                let is_branch = placer.get_boolean(is_branch_var);
                let jump_resolution = placer.get_boolean(should_jump_or_slt_value);

                is_branch.and(&jump_resolution)
            };
            placer.assign_mask(should_jump_if_branch, &should_jump);

            // NOTE: in case of padding our default case matches "branch not taken" case, so we use different defaults
            let (mut out_value, mut intermedaite_of_value, mut of_value) = {
                let (default_next_pc, default_of_value) = pc_u32.overflowing_add(
                    &<CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(
                        core::mem::size_of::<u32>() as u32,
                    ),
                );
                let (_, default_intermediate_of_value) = pc_low.overflowing_add(
                    &<CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(
                        core::mem::size_of::<u32>() as u16,
                    ),
                );

                (
                    default_next_pc,
                    default_of_value,
                    default_intermediate_of_value,
                )
            };

            {
                // Branch taken(!)
                let (next_pc, of) = pc_u32.overflowing_add(&imm);
                out_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                    &should_jump,
                    &next_pc,
                    &out_value,
                );
                of_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                    &should_jump,
                    &of,
                    &of_value,
                );
                update_intermediate_carry_value::<F, CS::WitnessPlacer, false>(
                    &mut intermedaite_of_value,
                    &should_jump,
                    &pc_low,
                    &imm_low,
                    None,
                );
            }
            {
                // JAL
                let is_jal = placer.get_boolean(is_jal_var);
                let (next_pc, of) = pc_u32.overflowing_add(&imm);
                out_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                    &is_jal, &next_pc, &out_value,
                );
                of_value =
                    <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(&is_jal, &of, &of_value);
                update_intermediate_carry_value::<F, CS::WitnessPlacer, false>(
                    &mut intermedaite_of_value,
                    &is_jal,
                    &pc_low,
                    &imm_low,
                    None,
                );
            }
            {
                // JALR
                let is_jalr = placer.get_boolean(is_jalr_var);
                let (next_pc, of) = rs1_u32.overflowing_add(&imm);
                out_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                    &is_jalr, &next_pc, &out_value,
                );
                of_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                    &is_jalr, &of, &of_value,
                );
                update_intermediate_carry_value::<F, CS::WitnessPlacer, false>(
                    &mut intermedaite_of_value,
                    &is_jalr,
                    &rs1_low,
                    &imm_low,
                    None,
                );
            }
            {
                // for SLT we compute pc + 4
                let is_slt = placer.get_boolean(is_slt_var);
                let (next_pc, of) = pc_u32.overflowing_add(
                    &<CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(
                        core::mem::size_of::<u32>() as u32,
                    ),
                );
                out_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                    &is_slt, &next_pc, &out_value,
                );
                of_value =
                    <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(&is_slt, &of, &of_value);
                update_intermediate_carry_value::<F, CS::WitnessPlacer, false>(
                    &mut intermedaite_of_value,
                    &is_slt,
                    &pc_low,
                    &<CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(
                        core::mem::size_of::<u32>() as u16,
                    ),
                    None,
                );
            }

            placer.assign_u32_from_u16_parts(pc_out_vars, &out_value);
            // Conditional on is_fam2: add_rel_1 carry bools alias shared bool-pool slots.
            let is_fam2 = {
                let mut m = placer.get_boolean(is_branch_var);
                m = m.or(&placer.get_boolean(is_slt_var));
                m = m.or(&placer.get_boolean(is_jal_var));
                m = m.or(&placer.get_boolean(is_jalr_var));
                m
            };
            placer.conditionally_assign_mask(
                add_rel_1_intermediate_of_var,
                &is_fam2,
                &intermedaite_of_value,
            );
            placer.conditionally_assign_mask(add_rel_1_final_of_var, &is_fam2, &of_value);
        };
        cs.set_values(value_fn);
    }

    // enforce the jump if branch value
    cs.add_constraint_expr(
        Expr::from(is_branch) * Expr::var(should_jump_or_slt_value)
            - Expr::var(should_jump_if_branch),
    );

    // and the corresponding constraint
    // NOTE: if we have branch opcode, then `should_jump_or_slt_value` will indicate whether to branch or not,
    // and if we have `should_jump_or_slt_value` it'll indicate the value,
    // but not the presence of jump. That's why we added extra variable above
    {
        let mut add_like_low_constraint = Expr::<F>::zero();
        // first addend - default case
        add_like_low_constraint = add_like_low_constraint
            + Expr::from(is_jal) * Expr::var(inputs.cycle_start_state.pc[0]);
        add_like_low_constraint =
            add_like_low_constraint + Expr::from(is_jalr) * Expr::var(rs1_limbs[0]);
        add_like_low_constraint = add_like_low_constraint
            + Expr::from(is_branch) * Expr::var(inputs.cycle_start_state.pc[0]);
        add_like_low_constraint = add_like_low_constraint
            + Expr::from(is_slt) * Expr::var(inputs.cycle_start_state.pc[0]);
        // second addend
        add_like_low_constraint =
            add_like_low_constraint + Expr::from(is_jal) * Expr::var(inputs.decoder_data.imm[0]);
        add_like_low_constraint =
            add_like_low_constraint + Expr::from(is_jalr) * Expr::var(inputs.decoder_data.imm[0]);
        add_like_low_constraint = add_like_low_constraint
            + Expr::from(is_branch) * Expr::from(common_constants::PC_STEP as u32);
        add_like_low_constraint = add_like_low_constraint
            + Expr::from(should_jump_if_branch)
                * (Expr::var(inputs.decoder_data.imm[0])
                    - Expr::from(common_constants::PC_STEP as u32));
        add_like_low_constraint = add_like_low_constraint
            + Expr::from(is_slt) * Expr::from(common_constants::PC_STEP as u32);
        // out-like var
        add_like_low_constraint = add_like_low_constraint
            - Expr::from(is_jal) * Expr::var(pc_intermediate_addition_tmp_low);
        add_like_low_constraint = add_like_low_constraint
            - Expr::from(is_jalr) * Expr::var(pc_intermediate_addition_tmp_low);
        add_like_low_constraint = add_like_low_constraint
            - Expr::from(is_branch) * Expr::var(pc_intermediate_addition_tmp_low);
        add_like_low_constraint = add_like_low_constraint
            - Expr::from(is_slt) * Expr::var(pc_intermediate_addition_tmp_low);

        // intermediate carry
        add_like_low_constraint = add_like_low_constraint
            - Expr::from(is_jal)
                * Expr::constant(carry_shift)
                * Expr::var(add_rel_1_intermediate_of_var);
        add_like_low_constraint = add_like_low_constraint
            - Expr::from(is_jalr)
                * Expr::constant(carry_shift)
                * Expr::var(add_rel_1_intermediate_of_var);
        add_like_low_constraint = add_like_low_constraint
            - Expr::from(is_branch)
                * Expr::constant(carry_shift)
                * Expr::var(add_rel_1_intermediate_of_var);
        add_like_low_constraint = add_like_low_constraint
            - Expr::from(is_slt)
                * Expr::constant(carry_shift)
                * Expr::var(add_rel_1_intermediate_of_var);
        cs.add_constraint_expr(add_like_low_constraint);

        // high part
        let mut add_like_high_constraint = Expr::<F>::zero();
        // intermediate carry
        add_like_high_constraint = add_like_high_constraint
            + Expr::from(is_jal) * Expr::var(add_rel_1_intermediate_of_var);
        add_like_high_constraint = add_like_high_constraint
            + Expr::from(is_jalr) * Expr::var(add_rel_1_intermediate_of_var);
        add_like_high_constraint = add_like_high_constraint
            + Expr::from(is_branch) * Expr::var(add_rel_1_intermediate_of_var);
        add_like_high_constraint = add_like_high_constraint
            + Expr::from(is_slt) * Expr::var(add_rel_1_intermediate_of_var);
        // first addend
        add_like_high_constraint = add_like_high_constraint
            + Expr::from(is_jal) * Expr::var(inputs.cycle_start_state.pc[1]);
        add_like_high_constraint =
            add_like_high_constraint + Expr::from(is_jalr) * Expr::var(rs1_limbs[1]);
        add_like_high_constraint = add_like_high_constraint
            + Expr::from(is_branch) * Expr::var(inputs.cycle_start_state.pc[1]);
        add_like_high_constraint = add_like_high_constraint
            + Expr::from(is_slt) * Expr::var(inputs.cycle_start_state.pc[1]);
        // second addend
        add_like_high_constraint =
            add_like_high_constraint + Expr::from(is_jal) * Expr::var(inputs.decoder_data.imm[1]);
        add_like_high_constraint =
            add_like_high_constraint + Expr::from(is_jalr) * Expr::var(inputs.decoder_data.imm[1]);
        add_like_high_constraint = add_like_high_constraint
            + Expr::from(should_jump_if_branch) * Expr::var(inputs.decoder_data.imm[1]);
        // out-like
        add_like_high_constraint =
            add_like_high_constraint - Expr::from(is_jal) * Expr::var(inputs.cycle_end_state.pc[1]);
        add_like_high_constraint = add_like_high_constraint
            - Expr::from(is_jalr) * Expr::var(inputs.cycle_end_state.pc[1]);
        add_like_high_constraint = add_like_high_constraint
            - Expr::from(is_branch) * Expr::var(inputs.cycle_end_state.pc[1]);
        add_like_high_constraint =
            add_like_high_constraint - Expr::from(is_slt) * Expr::var(inputs.cycle_end_state.pc[1]);
        // final carry
        add_like_high_constraint = add_like_high_constraint
            - Expr::from(is_jal) * Expr::constant(carry_shift) * Expr::var(add_rel_1_final_of_var);
        add_like_high_constraint = add_like_high_constraint
            - Expr::from(is_jalr) * Expr::constant(carry_shift) * Expr::var(add_rel_1_final_of_var);
        add_like_high_constraint = add_like_high_constraint
            - Expr::from(is_branch)
                * Expr::constant(carry_shift)
                * Expr::var(add_rel_1_final_of_var);
        add_like_high_constraint = add_like_high_constraint
            - Expr::from(is_slt) * Expr::constant(carry_shift) * Expr::var(add_rel_1_final_of_var);
        cs.add_constraint_expr(add_like_high_constraint);
    }

    // next_pc_bit_1 = bit 1 of pc_intermediate_addition_tmp_low. The JumpCleanupOffset
    // lookup tuple is (input, bit_1, pc_out_low) and is enforced against a gated
    // table_id so non-Family-2 cycles match (0, 0, 0) under the ZeroEntry table.
    // Shared bool-pool slot [4] (Family-2-exclusive); witnessed conditionally on is_fam2
    // so non-Family-2 rows leave it at the pool default (0).
    let next_pc_bit_1 = scratch_bools[4];
    {
        let is_branch_var = is_branch.expect_variable();
        let is_slt_var = is_slt.expect_variable();
        let is_jal_var = is_jal.expect_variable();
        let is_jalr_var = is_jalr.expect_variable();
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let tmp_low = placer.get_u16(pc_intermediate_addition_tmp_low);
            let bit_1 = tmp_low.shr(1).get_lowest_bits(1).is_one();
            let is_fam2 = {
                let mut m = placer.get_boolean(is_branch_var);
                m = m.or(&placer.get_boolean(is_slt_var));
                m = m.or(&placer.get_boolean(is_jal_var));
                m = m.or(&placer.get_boolean(is_jalr_var));
                m
            };
            placer.conditionally_assign_mask(next_pc_bit_1.expect_variable(), &is_fam2, &bit_1);
        };
        cs.set_values(value_fn);
    }

    // Assign pc_out[0] = pc_intermediate_addition_tmp_low & ~0x3 (the JumpCleanupOffset
    // table mapping). Non-Family-2 cycles: pc_intermediate defaults to pc+4 which is
    // already 4-aligned, so this is a no-op. Padding (execute=0): no constraint reads
    // pc_out[0]'s value, so the override is harmless.
    {
        let pc_out_low_var = inputs.cycle_end_state.pc[0];
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let tmp_low = placer.get_u16(pc_intermediate_addition_tmp_low);
            let aligned = tmp_low.and(&<CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(
                0xFFFCu16,
            ));
            placer.assign_u16(pc_out_low_var, &aligned);
        };
        cs.set_values(value_fn);
    }

    // JumpCleanupOffset request for the shared pool: tuple
    // (is_fam2*input, is_fam2*bit_1, is_fam2*pc_out_low) under
    // table_id = is_fam2 * JumpCleanupOffset; (0,0,0)/ZeroEntry on non-F2 rows.
    let jump_cleanup_request = LookupRequest::new(
        is_fam2_sum() * Expr::from(TableType::JumpCleanupOffset.to_num()),
        vec![
            is_fam2_sum() * Expr::from(pc_intermediate_addition_tmp_low),
            is_fam2_sum() * Expr::from(next_pc_bit_1),
            is_fam2_sum() * Expr::from(inputs.cycle_end_state.pc[0]),
        ],
    );

    // unaligned jump is unprovable, and we only need to check bit number 1, as jump offset is always 0 mod 2,
    // and PC is 0 mod 4
    cs.add_constraint_expr(
        (Expr::from(is_jal) + Expr::from(is_jalr) + Expr::var(should_jump_if_branch))
            * Expr::from(next_pc_bit_1),
    );

    // Per-opcode rd-write helpers. JAL and JALR are merged into a single helper
    // (`is_jal_or_jalr_writes_rd`) because they always appear summed at the two
    // rd-write use sites and produce the same value (saved_pc); decoder-enforced
    // mutual exclusion keeps the sum Boolean. SLT and the rd=0 gate keep separate
    // helpers because they enter different constraints.
    //   is_jal_or_jalr_writes_rd = (is_jal + is_jalr) * (1 - rd_is_zero)
    //   is_slt_writes_rd         = is_slt           * (1 - rd_is_zero)
    //   gate_fam2_rd_zero        = (any F2 sub-op)  * rd_is_zero
    // Non-Family-2 cycles: all three 0 ⇒ every rd-write constraint below trivially
    // holds, so other families own rd_write_limbs on their own cycles.
    let is_jal_or_jalr_writes_rd = cs.add_named_boolean_variable("is_jal_or_jalr_writes_rd");
    let is_slt_writes_rd = cs.add_named_boolean_variable("is_slt_writes_rd");
    let gate_fam2_rd_zero = cs.add_named_boolean_variable("gate_fam2_rd_zero");

    {
        let is_jal_var = is_jal.expect_variable();
        let is_jalr_var = is_jalr.expect_variable();
        let is_slt_var = is_slt.expect_variable();
        let is_branch_var = is_branch.expect_variable();
        let rd_is_zero_var = rd_is_zero.expect_variable();
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let is_jal_m = placer.get_boolean(is_jal_var);
            let is_jalr_m = placer.get_boolean(is_jalr_var);
            let is_slt_m = placer.get_boolean(is_slt_var);
            let is_branch_m = placer.get_boolean(is_branch_var);
            let rd_is_zero_m = placer.get_boolean(rd_is_zero_var);
            let not_rd_zero = rd_is_zero_m.negate();
            let is_jal_or_jalr = is_jal_m.or(&is_jalr_m);
            placer.assign_mask(
                is_jal_or_jalr_writes_rd.expect_variable(),
                &is_jal_or_jalr.and(&not_rd_zero),
            );
            placer.assign_mask(
                is_slt_writes_rd.expect_variable(),
                &is_slt_m.and(&not_rd_zero),
            );
            let any_f2 = is_jal_m.or(&is_jalr_m).or(&is_slt_m).or(&is_branch_m);
            placer.assign_mask(
                gate_fam2_rd_zero.expect_variable(),
                &any_f2.and(&rd_is_zero_m),
            );
        };
        cs.set_values(value_fn);
    }

    // Helper-Boolean setup (deg 2 each).
    // is_jal_or_jalr_writes_rd = (is_jal + is_jalr) * (1 - rd_is_zero)
    // Rearranged: is_jal_or_jalr_writes_rd + (is_jal + is_jalr)*rd_is_zero - is_jal - is_jalr = 0
    cs.add_constraint_expr(
        Expr::from(is_jal_or_jalr_writes_rd)
            + (Expr::from(is_jal) + Expr::from(is_jalr)) * Expr::from(rd_is_zero)
            - Expr::from(is_jal)
            - Expr::from(is_jalr),
    );
    cs.add_constraint_expr(
        Expr::from(is_slt_writes_rd) + Expr::from(is_slt) * Expr::from(rd_is_zero)
            - Expr::from(is_slt),
    );
    // gate_fam2_rd_zero = (is_jal + is_jalr + is_slt + is_branch) * rd_is_zero  (deg 2)
    cs.add_constraint_expr(
        Expr::from(gate_fam2_rd_zero)
            - (Expr::from(is_jal)
                + Expr::from(is_jalr)
                + Expr::from(is_slt)
                + Expr::from(is_branch))
                * Expr::from(rd_is_zero),
    );

    // Self-generating witness contract (`ASSUME_MEMORY_VALUES_ASSIGNED ==
    // false`): the oracle is trusted only for INPUTS (instruction, register /
    // memory READ values, timestamps). Every family DERIVES its outputs — the
    // shared rd/mem write-value columns — in its own value_fn, gated on that
    // family's activity mask. The generic access resolver assigns
    // the oracle's write value first only as a fallback; the family writers
    // below overwrite it on their rows. The contract is pinned by
    // `test_unified_witness_self_generates_write_values` (poisoned oracle).
    //
    // Family 2's derivation mirrors the constraints below: jal/jalr →
    // saved_pc, slt → slt result (high limb 0), rd == x0 (incl. branches:
    // B-type has no rd field, decode forces rd_index = 0) → (0, 0).
    if !CS::ASSUME_MEMORY_VALUES_ASSIGNED {
        let is_jal_var = is_jal.expect_variable();
        let is_jalr_var = is_jalr.expect_variable();
        let is_slt_var = is_slt.expect_variable();
        let is_branch_var = is_branch.expect_variable();
        let jj_writes_var = is_jal_or_jalr_writes_rd.expect_variable();
        let slt_writes_var = is_slt_writes_rd.expect_variable();
        let saved_pc_low_var = comparison_rel_or_jump_saved_pc_low;
        let saved_pc_high_var = comparison_rel_or_jump_saved_pc_high;
        let slt_value_var = should_jump_or_slt_value;
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let is_jal_m = placer.get_boolean(is_jal_var);
            let is_jalr_m = placer.get_boolean(is_jalr_var);
            let is_slt_m = placer.get_boolean(is_slt_var);
            let is_branch_m = placer.get_boolean(is_branch_var);
            let any_f2 = is_jal_m.or(&is_jalr_m).or(&is_slt_m).or(&is_branch_m);
            let jj_writes = placer.get_boolean(jj_writes_var);
            let slt_writes = placer.get_boolean(slt_writes_var);

            let saved_pc_low = placer.get_u16(saved_pc_low_var);
            let saved_pc_high = placer.get_u16(saved_pc_high_var);
            let slt_value = placer.get_u16(slt_value_var);

            let mut low = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(0u16);
            low.assign_masked(&jj_writes, &saved_pc_low);
            low.assign_masked(&slt_writes, &slt_value);
            let mut high = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(0u16);
            high.assign_masked(&jj_writes, &saved_pc_high);

            placer.conditionally_assign_u16(rd_write_limbs[0], &any_f2, &low);
            placer.conditionally_assign_u16(rd_write_limbs[1], &any_f2, &high);
        };
        cs.set_values(value_fn);
    }

    // Per-opcode rd-write constraints. Low limb: jal/jalr → saved_pc_low; slt → slt_value.
    cs.add_constraint_expr(
        Expr::from(is_jal_or_jalr_writes_rd) * Expr::var(comparison_rel_or_jump_saved_pc_low)
            + Expr::from(is_slt_writes_rd) * Expr::var(should_jump_or_slt_value)
            - (Expr::from(is_jal_or_jalr_writes_rd) + Expr::from(is_slt_writes_rd))
                * Expr::var(rd_write_limbs[0]),
    );
    // High limb: jal/jalr write saved_pc_high.
    cs.add_constraint_expr(
        Expr::from(is_jal_or_jalr_writes_rd)
            * (Expr::var(comparison_rel_or_jump_saved_pc_high) - Expr::var(rd_write_limbs[1])),
    );
    // Pin rd_write_limbs[1] = 0 when SLT writes rd (rd != 0). SLT's 0/1 result
    // fits in the low limb. The Family-2 rd-write rewrite from standalone's
    // `selected_rd_high = (is_jal+is_jalr)*saved_pc_high` pattern to per-opcode
    // `is_X_writes_rd` helpers lost the implicit `selected_rd_high = 0 for SLT`
    // zeroing; this explicit constraint restores it. Without it the high limb
    // is only bounded by the top-level 16-bit RC on rd_write_limbs[1], leaving
    // 16 bits attacker-controlled. The negative test
    // `slt_rd_write_high_limb_nonzero_rejected` pins this.
    cs.add_constraint_expr(Expr::from(is_slt_writes_rd) * Expr::var(rd_write_limbs[1]));

    // rd_is_zero case: Family 2 fires with rd=0 forces rd_write = 0.
    cs.add_constraint_expr(Expr::from(gate_fam2_rd_zero) * Expr::var(rd_write_limbs[0]));
    cs.add_constraint_expr(Expr::from(gate_fam2_rd_zero) * Expr::var(rd_write_limbs[1]));

    vec![
        regiszero_request,
        u16getsign_request,
        rs2_sign_request,
        cond_jmp_request,
        jump_cleanup_request,
    ]
}
