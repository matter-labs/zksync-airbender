use super::*;
use crate::constraint::{Constraint, Term};
use crate::cs::circuit_trait::*;
use crate::gkr_circuits::jump_branch_slt_family::JumpSltBranchFamilyCircuitMask;
use crate::gkr_circuits::utils::update_intermediate_carry_value;
use crate::types::*;
use crate::witness_placer::*;
use field::PrimeField;

/// Family 2 (jump/branch/slt) constraints for the unified circuit. Mirrors the
/// audited standalone inner with two unified-specific adaptations:
/// (1) the `JumpCleanupOffset` lookup is gated so non-Family-2 cycles route to
/// `ZeroEntry`, and (2) the rd-write constraints are gated on per-opcode
/// `is_X_writes_rd` Booleans so non-Family-2 cycles don't pin rd_write_limbs.
pub fn apply_unified_jump_branch_slt_inner<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    inputs: OpcodeFamilyCircuitState<F>,
    decoder: JumpSltBranchFamilyCircuitMask,
    rs1_limbs: [Variable; 4],
    rs2_limbs: [Variable; 4],
    rd_write_limbs: [Variable; 2],
) {
    if let Some(circuit_family_extra_mask) =
        cs.get_value(inputs.decoder_data.circuit_family_extra_mask)
    {
        println!(
            "circuit_family_extra_mask = 0b{:08b}",
            circuit_family_extra_mask.as_u32_reduced()
        );
    }

    // U16 views of rs1/rs2 reassembled from U8 bytes via free algebra.
    let byte_shift = F::from_u32_unchecked(1 << 8);
    let rs1_low_c: Constraint<F> =
        Constraint::from(rs1_limbs[0]) + Term::from((byte_shift, rs1_limbs[1]));
    let rs1_high_c: Constraint<F> =
        Constraint::from(rs1_limbs[2]) + Term::from((byte_shift, rs1_limbs[3]));
    let rs2_low_c: Constraint<F> =
        Constraint::from(rs2_limbs[0]) + Term::from((byte_shift, rs2_limbs[1]));
    let rs2_high_c: Constraint<F> =
        Constraint::from(rs2_limbs[2]) + Term::from((byte_shift, rs2_limbs[3]));

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

    let intermediate_reg = Register::new_named(cs, "Intermediate reg for comparisons");
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

    // and we need 4 intermediate booleans
    let intermediate_bools = std::array::from_fn(|i| {
        cs.add_named_boolean_variable(&format!("Intermedaite boolean {}", i))
    });

    let is_branch = decoder.perform_branch();
    let is_slt = decoder.perform_slt();
    let is_jal = decoder.perform_jal();
    let is_jalr = decoder.perform_jalr();
    let rd_is_zero = decoder.rd_is_zero();

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

    if is_branch.get_value(cs).unwrap_or(false) {
        println!("BRANCH");
    }
    if is_slt.get_value(cs).unwrap_or(false) {
        println!("SLT/SLTU");
    }
    if is_jal.get_value(cs).unwrap_or(false) {
        println!("JAL");
    }
    if is_jalr.get_value(cs).unwrap_or(false) {
        println!("JALR");
    }

    let [add_rel_0_intermediate_of, add_rel_0_final_of, add_rel_1_intermediate_of, add_rel_1_final_of] =
        intermediate_bools;

    let [comparison_rel_or_jump_saved_pc_low, comparison_rel_or_jump_saved_pc_high] =
        intermediate_reg.0.map(|el| el.get_variable());

    let add_rel_0_intermediate_of_var = add_rel_0_intermediate_of.get_variable().unwrap();
    let add_rel_0_final_of_var = add_rel_0_final_of.get_variable().unwrap();

    let add_rel_1_intermediate_of_var = add_rel_1_intermediate_of.get_variable().unwrap();
    let add_rel_1_final_of_var = add_rel_1_final_of.get_variable().unwrap();

    {
        let imm_vars = inputs.decoder_data.imm;
        let pc_in_vars = inputs.cycle_start_state.pc;
        let rs1_vars = rs1_limbs;
        let rs2_vars = rs2_limbs;

        let is_branch_var = is_branch.get_variable().unwrap();
        let is_slt_var = is_slt.get_variable().unwrap();
        let is_jal_var = is_jal.get_variable().unwrap();
        let is_jalr_var = is_jalr.get_variable().unwrap();

        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            // NOTE: it is UNCONDITIONAL assignment, even though we select across multiple variants

            let mut out_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0);
            let mut intermedaite_of_value =
                <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false);
            let mut of_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false);

            let imm_low = placer.get_u16(imm_vars[0]);
            let imm = placer.get_u32_from_u16_parts(imm_vars);
            let rs1_low = placer.get_u16_from_u8_parts([rs1_vars[0], rs1_vars[1]]);
            let rs1_u32 = placer.get_u32_from_u8_parts(rs1_vars);
            let rs2_low = placer.get_u16_from_u8_parts([rs2_vars[0], rs2_vars[1]]);
            let rs2_u32 = placer.get_u32_from_u8_parts(rs2_vars);
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
                    &&<CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(
                        core::mem::size_of::<u32>() as u16,
                    ),
                    None,
                );
            }

            placer.assign_u32_from_u16_parts(
                [
                    comparison_rel_or_jump_saved_pc_low,
                    comparison_rel_or_jump_saved_pc_high,
                ],
                &out_value,
            );
            placer.assign_mask(add_rel_0_intermediate_of_var, &intermedaite_of_value);
            placer.assign_mask(add_rel_0_final_of_var, &of_value);
        };
        cs.set_values(value_fn);
    }

    // now we can put the constraint for such addition
    {
        let mut add_like_low_constraint = Constraint::empty();
        // first addend
        add_like_low_constraint += Term::from(is_jal) * Term::from(inputs.cycle_start_state.pc[0]);
        add_like_low_constraint += Term::from(is_jalr) * Term::from(inputs.cycle_start_state.pc[0]);
        // for subtraction 2^16*of + a - b = c -> 2^16*of + a = b + c
        // so we use output for the first addend, and keep second addend unchanged
        add_like_low_constraint +=
            Term::from(is_branch) * Term::from(comparison_rel_or_jump_saved_pc_low);
        add_like_low_constraint +=
            Term::from(is_slt) * Term::from(comparison_rel_or_jump_saved_pc_low);
        // second addend
        // NOTE: for additions we blindly mix imm and rs2 as preprocessing ensures that if imm !=0 then rs2 = x0
        add_like_low_constraint += Term::from(is_jal) * Term::from(4u32);
        add_like_low_constraint += Term::from(is_jalr) * Term::from(4u32);
        add_like_low_constraint += Term::from(is_branch) * rs2_low_c.clone();
        add_like_low_constraint += Term::from(is_slt) * rs2_low_c.clone();
        add_like_low_constraint += Term::from(is_slt) * Term::from(inputs.decoder_data.imm[0]);
        // out-like var
        add_like_low_constraint -=
            Term::from(is_jal) * Term::from(comparison_rel_or_jump_saved_pc_low);
        add_like_low_constraint -=
            Term::from(is_jalr) * Term::from(comparison_rel_or_jump_saved_pc_low);
        add_like_low_constraint -= Term::from(is_branch) * rs1_low_c.clone();
        add_like_low_constraint -= Term::from(is_slt) * rs1_low_c.clone();

        // intermediate carry
        add_like_low_constraint -=
            Term::from(is_jal) * Term::from((carry_shift, add_rel_0_intermediate_of_var));
        add_like_low_constraint -=
            Term::from(is_jalr) * Term::from((carry_shift, add_rel_0_intermediate_of_var));
        add_like_low_constraint -=
            Term::from(is_branch) * Term::from((carry_shift, add_rel_0_intermediate_of_var));
        add_like_low_constraint -=
            Term::from(is_slt) * Term::from((carry_shift, add_rel_0_intermediate_of_var));
        cs.add_constraint(add_like_low_constraint);

        // high part
        let mut add_like_high_constraint = Constraint::empty();
        // intermediate carry
        add_like_high_constraint += Term::from(is_jal) * Term::from(add_rel_0_intermediate_of_var);
        add_like_high_constraint += Term::from(is_jalr) * Term::from(add_rel_0_intermediate_of_var);
        add_like_high_constraint +=
            Term::from(is_branch) * Term::from(add_rel_0_intermediate_of_var);
        add_like_high_constraint += Term::from(is_slt) * Term::from(add_rel_0_intermediate_of_var);
        // first addend
        add_like_high_constraint += Term::from(is_jal) * Term::from(inputs.cycle_start_state.pc[1]);
        add_like_high_constraint +=
            Term::from(is_jalr) * Term::from(inputs.cycle_start_state.pc[1]);
        add_like_high_constraint +=
            Term::from(is_branch) * Term::from(comparison_rel_or_jump_saved_pc_high);
        add_like_high_constraint +=
            Term::from(is_slt) * Term::from(comparison_rel_or_jump_saved_pc_high);
        // second addend
        // NOTE: for additions we blindly mix imm and rs2 as preprocessing ensures that if imm !=0 then rs2 = x0
        add_like_high_constraint += Term::from(is_branch) * rs2_high_c.clone();
        add_like_high_constraint += Term::from(is_slt) * rs2_high_c.clone();
        add_like_high_constraint += Term::from(is_slt) * Term::from(inputs.decoder_data.imm[1]);
        // out-like
        add_like_high_constraint -=
            Term::from(is_jal) * Term::from(comparison_rel_or_jump_saved_pc_high);
        add_like_high_constraint -=
            Term::from(is_jalr) * Term::from(comparison_rel_or_jump_saved_pc_high);
        add_like_high_constraint -= Term::from(is_branch) * rs1_high_c.clone();
        add_like_high_constraint -= Term::from(is_slt) * rs1_high_c.clone();
        // final carry
        add_like_high_constraint -=
            Term::from(is_jal) * Term::from((carry_shift, add_rel_0_final_of_var));
        add_like_high_constraint -=
            Term::from(is_jalr) * Term::from((carry_shift, add_rel_0_final_of_var));
        add_like_high_constraint -=
            Term::from(is_branch) * Term::from((carry_shift, add_rel_0_final_of_var));
        add_like_high_constraint -=
            Term::from(is_slt) * Term::from((carry_shift, add_rel_0_final_of_var));
        cs.add_constraint(add_like_high_constraint);
    }

    // now we should compare the output result to 0,
    // then resolve jump/slt condition

    let comparison_result_is_zero = cs.add_named_variable("Comparison result is zero out var");
    cs.set_variables_from_lookup_constrained(
        &[LookupInput::from(
            Constraint::empty()
                + Term::from(comparison_rel_or_jump_saved_pc_low)
                + Term::from(comparison_rel_or_jump_saved_pc_high),
        )],
        &[comparison_result_is_zero],
        cs::circuit::LookupQueryTableType::Constant(TableType::RegIsZero),
    );

    // we also need a sign of rs1 to resolve jumps. The sign of rs1's high U16 limb
    // is queried; we reassemble the U16 from the high two bytes via a degree-1
    // expression — U16GetSign accepts the full 16-bit value as a single lookup input.
    let rs1_sign = cs.add_named_variable("rs1 sign boolean");
    cs.set_variables_from_lookup_constrained(
        &[LookupInput::Expression {
            linear_terms: vec![
                (F::from_u32_unchecked(1), rs1_limbs[2]),
                (byte_shift, rs1_limbs[3]),
            ],
            constant_coeff: F::ZERO,
        }],
        &[rs1_sign],
        cs::circuit::LookupQueryTableType::Constant(TableType::U16GetSign),
    );

    // and now we can resolve jump. Note that SLT/SLTU use the same formal(!) funct3 as BLT/BLTU,
    // and for JAL/JALR we formally set funct3 to be such that jump resolution will be always
    // false, so in computing next PC below we can avoid thinking about overlapping
    // boolean conditions
    let should_jump_or_slt_value = cs.add_named_variable("jump resolution variable");
    cs.set_variables_from_lookup_constrained(
        &[LookupInput::from(
            Constraint::empty()
                + rs2_high_c.clone()
                + Term::from((F::from_u32(1 << 16).unwrap(), rs1_sign))
                + Term::from((F::from_u32(1 << 17).unwrap(), add_rel_0_final_of_var))
                + Term::from((F::from_u32(1 << 18).unwrap(), comparison_result_is_zero))
                + Term::from((
                    F::from_u32(1 << 19).unwrap(),
                    inputs.decoder_data.funct3.expect("must have funct3"),
                )),
        )],
        &[should_jump_or_slt_value],
        cs::circuit::LookupQueryTableType::Constant(TableType::ConditionalJmpBranchSlt),
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

        let is_slt_var = is_slt.get_variable().unwrap();
        let is_jal_var = is_jal.get_variable().unwrap();
        let is_jalr_var = is_jalr.get_variable().unwrap();
        let is_branch_var = is_branch.get_variable().unwrap();

        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            // NOTE: it is UNCONDITIONAL assignment, even though we select across multiple variants

            let imm_low = placer.get_u16(imm_vars[0]);
            let imm = placer.get_u32_from_u16_parts(imm_vars);
            let rs1_low = placer.get_u16_from_u8_parts([rs1_vars[0], rs1_vars[1]]);
            let rs1_u32 = placer.get_u32_from_u8_parts(rs1_vars);
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
                    &&<CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(
                        core::mem::size_of::<u32>() as u16,
                    ),
                    None,
                );
            }

            placer.assign_u32_from_u16_parts(pc_out_vars, &out_value);
            placer.assign_mask(add_rel_1_intermediate_of_var, &intermedaite_of_value);
            placer.assign_mask(add_rel_1_final_of_var, &of_value);
        };
        cs.set_values(value_fn);
    }

    // enforce the jump if branch value
    cs.add_constraint(
        Term::from(is_branch) * Term::from(should_jump_or_slt_value)
            - Term::from(should_jump_if_branch),
    );

    // and the corresponding constraint
    // NOTE: if we have branch opcode, then `should_jump_or_slt_value` will indicate whether to branch or not,
    // and if we have `should_jump_or_slt_value` it'll indicate the value,
    // but not the presence of jump. That's why we added extra variable above
    {
        let mut add_like_low_constraint = Constraint::empty();
        // first addend - default case
        add_like_low_constraint += Term::from(is_jal) * Term::from(inputs.cycle_start_state.pc[0]);
        add_like_low_constraint += Term::from(is_jalr) * rs1_low_c.clone();
        add_like_low_constraint +=
            Term::from(is_branch) * Term::from(inputs.cycle_start_state.pc[0]);
        add_like_low_constraint += Term::from(is_slt) * Term::from(inputs.cycle_start_state.pc[0]);
        // second addend
        add_like_low_constraint += Term::from(is_jal) * Term::from(inputs.decoder_data.imm[0]);
        add_like_low_constraint += Term::from(is_jalr) * Term::from(inputs.decoder_data.imm[0]);
        add_like_low_constraint += Term::from(is_branch) * Term::from(4u32);
        add_like_low_constraint += Term::from(should_jump_if_branch)
            * (Term::from(inputs.decoder_data.imm[0]) - Term::from(4u32));
        add_like_low_constraint += Term::from(is_slt) * Term::from(4u32);
        // out-like var
        add_like_low_constraint -=
            Term::from(is_jal) * Term::from(pc_intermediate_addition_tmp_low);
        add_like_low_constraint -=
            Term::from(is_jalr) * Term::from(pc_intermediate_addition_tmp_low);
        add_like_low_constraint -=
            Term::from(is_branch) * Term::from(pc_intermediate_addition_tmp_low);
        add_like_low_constraint -=
            Term::from(is_slt) * Term::from(pc_intermediate_addition_tmp_low);

        // intermediate carry
        add_like_low_constraint -=
            Term::from(is_jal) * Term::from((carry_shift, add_rel_1_intermediate_of_var));
        add_like_low_constraint -=
            Term::from(is_jalr) * Term::from((carry_shift, add_rel_1_intermediate_of_var));
        add_like_low_constraint -=
            Term::from(is_branch) * Term::from((carry_shift, add_rel_1_intermediate_of_var));
        add_like_low_constraint -=
            Term::from(is_slt) * Term::from((carry_shift, add_rel_1_intermediate_of_var));
        cs.add_constraint(add_like_low_constraint);

        // high part
        let mut add_like_high_constraint = Constraint::empty();
        // intermediate carry
        add_like_high_constraint += Term::from(is_jal) * Term::from(add_rel_1_intermediate_of_var);
        add_like_high_constraint += Term::from(is_jalr) * Term::from(add_rel_1_intermediate_of_var);
        add_like_high_constraint +=
            Term::from(is_branch) * Term::from(add_rel_1_intermediate_of_var);
        add_like_high_constraint += Term::from(is_slt) * Term::from(add_rel_1_intermediate_of_var);
        // first addend
        add_like_high_constraint += Term::from(is_jal) * Term::from(inputs.cycle_start_state.pc[1]);
        add_like_high_constraint += Term::from(is_jalr) * rs1_high_c.clone();
        add_like_high_constraint +=
            Term::from(is_branch) * Term::from(inputs.cycle_start_state.pc[1]);
        add_like_high_constraint += Term::from(is_slt) * Term::from(inputs.cycle_start_state.pc[1]);
        // second addend
        add_like_high_constraint += Term::from(is_jal) * Term::from(inputs.decoder_data.imm[1]);
        add_like_high_constraint += Term::from(is_jalr) * Term::from(inputs.decoder_data.imm[1]);
        add_like_high_constraint +=
            Term::from(should_jump_if_branch) * Term::from(inputs.decoder_data.imm[1]);
        // out-like
        add_like_high_constraint -= Term::from(is_jal) * Term::from(inputs.cycle_end_state.pc[1]);
        add_like_high_constraint -= Term::from(is_jalr) * Term::from(inputs.cycle_end_state.pc[1]);
        add_like_high_constraint -=
            Term::from(is_branch) * Term::from(inputs.cycle_end_state.pc[1]);
        add_like_high_constraint -= Term::from(is_slt) * Term::from(inputs.cycle_end_state.pc[1]);
        // final carry
        add_like_high_constraint -=
            Term::from(is_jal) * Term::from((carry_shift, add_rel_1_final_of_var));
        add_like_high_constraint -=
            Term::from(is_jalr) * Term::from((carry_shift, add_rel_1_final_of_var));
        add_like_high_constraint -=
            Term::from(is_branch) * Term::from((carry_shift, add_rel_1_final_of_var));
        add_like_high_constraint -=
            Term::from(is_slt) * Term::from((carry_shift, add_rel_1_final_of_var));
        cs.add_constraint(add_like_high_constraint);
    }

    // is_fam2 = is_jal + is_jalr + is_slt + is_branch (mutually exclusive ⇒ sum ∈ {0, 1}).
    // Used to gate the JumpCleanupOffset lookup and the rd-write helpers below so
    // non-Family-2 cycles route the lookup to ZeroEntry and don't pin rd_write_limbs.
    let is_fam2 = cs.add_named_boolean_variable("is_fam2");
    {
        let is_jal_var = is_jal.get_variable().unwrap();
        let is_jalr_var = is_jalr.get_variable().unwrap();
        let is_slt_var = is_slt.get_variable().unwrap();
        let is_branch_var = is_branch.get_variable().unwrap();
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let any = placer
                .get_boolean(is_jal_var)
                .or(&placer.get_boolean(is_jalr_var))
                .or(&placer.get_boolean(is_slt_var))
                .or(&placer.get_boolean(is_branch_var));
            placer.assign_mask(is_fam2.get_variable().unwrap(), &any);
        };
        cs.set_values(value_fn);
    }
    cs.add_constraint_allow_explicit_linear(
        Constraint::from(is_fam2)
            - Term::from(is_jal)
            - Term::from(is_jalr)
            - Term::from(is_slt)
            - Term::from(is_branch),
    );

    // next_pc_bit_1 = bit 1 of pc_intermediate_addition_tmp_low. The JumpCleanupOffset
    // lookup tuple is (input, bit_1, pc_out_low) and is enforced against a gated
    // table_id so non-Family-2 cycles match (0, 0, 0) under the ZeroEntry table.
    let next_pc_bit_1 = cs.add_named_boolean_variable("bit 1 for computed next PC");
    {
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let tmp_low = placer.get_u16(pc_intermediate_addition_tmp_low);
            let bit_1 = tmp_low.shr(1).get_lowest_bits(1).is_one();
            placer.assign_mask(next_pc_bit_1.get_variable().unwrap(), &bit_1);
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

    // Gated lookup tuple (is_fam2 * input, is_fam2 * bit_1, is_fam2 * pc_out_low)
    // against table_id = is_fam2 * JumpCleanupOffset.to_num(). Non-Family-2 cycles
    // produce (0, 0, 0) under table_id 0 (ZeroEntry).
    {
        let jump_cleanup_table_num = Term::from(TableType::JumpCleanupOffset.to_num());
        let gated_input = cs.add_intermediate_named_variable_from_constraint(
            Constraint::from(is_fam2) * Term::from(pc_intermediate_addition_tmp_low),
            "JumpCleanup gated input",
        );
        let gated_bit_1 = cs.add_intermediate_named_variable_from_constraint(
            Constraint::from(is_fam2) * Term::from(next_pc_bit_1),
            "JumpCleanup gated bit_1",
        );
        let gated_pc_out_low = cs.add_intermediate_named_variable_from_constraint(
            Constraint::from(is_fam2) * Term::from(inputs.cycle_end_state.pc[0]),
            "JumpCleanup gated pc_out_low",
        );
        let gated_table_id = cs.add_intermediate_named_variable_from_constraint(
            Constraint::from(is_fam2) * jump_cleanup_table_num,
            "JumpCleanup gated table_id",
        );
        let tuple = [
            LookupInput::from(gated_input),
            LookupInput::from(gated_bit_1),
            LookupInput::from(gated_pc_out_low),
        ];
        cs.enforce_lookup_tuple_for_variable_table(&tuple, gated_table_id);
    }

    // unaligned jump is unprovable, and we only need to check bit number 1, as jump offset is always 0 mod 2,
    // and PC is 0 mod 4
    cs.add_constraint(
        (Constraint::from(is_jal) + Term::from(is_jalr) + Term::from(should_jump_if_branch))
            * Term::from(next_pc_bit_1),
    );

    // Per-opcode rd-write helpers. is_X_writes_rd = is_X AND NOT rd_is_zero (X ∈
    // {jal, jalr, slt}); gate_fam2_rd_zero = (any Family-2 sub-opcode) AND rd_is_zero.
    // Non-Family-2 cycles: all four 0 ⇒ every rd-write constraint below trivially
    // holds, so other families own rd_write_limbs on their own cycles.
    let is_jal_writes_rd = cs.add_named_boolean_variable("is_jal_writes_rd");
    let is_jalr_writes_rd = cs.add_named_boolean_variable("is_jalr_writes_rd");
    let is_slt_writes_rd = cs.add_named_boolean_variable("is_slt_writes_rd");
    let gate_fam2_rd_zero = cs.add_named_boolean_variable("gate_fam2_rd_zero");

    {
        let is_jal_var = is_jal.get_variable().unwrap();
        let is_jalr_var = is_jalr.get_variable().unwrap();
        let is_slt_var = is_slt.get_variable().unwrap();
        let is_branch_var = is_branch.get_variable().unwrap();
        let rd_is_zero_var = rd_is_zero.get_variable().unwrap();
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let is_jal_m = placer.get_boolean(is_jal_var);
            let is_jalr_m = placer.get_boolean(is_jalr_var);
            let is_slt_m = placer.get_boolean(is_slt_var);
            let is_branch_m = placer.get_boolean(is_branch_var);
            let rd_is_zero_m = placer.get_boolean(rd_is_zero_var);
            let not_rd_zero = rd_is_zero_m.negate();
            placer.assign_mask(
                is_jal_writes_rd.get_variable().unwrap(),
                &is_jal_m.and(&not_rd_zero),
            );
            placer.assign_mask(
                is_jalr_writes_rd.get_variable().unwrap(),
                &is_jalr_m.and(&not_rd_zero),
            );
            placer.assign_mask(
                is_slt_writes_rd.get_variable().unwrap(),
                &is_slt_m.and(&not_rd_zero),
            );
            let any_f2 = is_jal_m.or(&is_jalr_m).or(&is_slt_m).or(&is_branch_m);
            placer.assign_mask(
                gate_fam2_rd_zero.get_variable().unwrap(),
                &any_f2.and(&rd_is_zero_m),
            );
        };
        cs.set_values(value_fn);
    }

    // Helper-Boolean setup (deg 2 each).
    // is_X_writes_rd = is_X * (1 - rd_is_zero)  for X ∈ {jal, jalr, slt}
    // Rearranged: is_X_writes_rd + is_X * rd_is_zero - is_X = 0
    cs.add_constraint(
        Constraint::from(is_jal_writes_rd) + Term::from(is_jal) * Term::from(rd_is_zero)
            - Term::from(is_jal),
    );
    cs.add_constraint(
        Constraint::from(is_jalr_writes_rd) + Term::from(is_jalr) * Term::from(rd_is_zero)
            - Term::from(is_jalr),
    );
    cs.add_constraint(
        Constraint::from(is_slt_writes_rd) + Term::from(is_slt) * Term::from(rd_is_zero)
            - Term::from(is_slt),
    );
    // gate_fam2_rd_zero = (is_jal + is_jalr + is_slt + is_branch) * rd_is_zero  (deg 2)
    cs.add_constraint(
        Constraint::from(gate_fam2_rd_zero)
            - (Constraint::from(is_jal)
                + Term::from(is_jalr)
                + Term::from(is_slt)
                + Term::from(is_branch))
                * Term::from(rd_is_zero),
    );

    assert!(
        CS::ASSUME_MEMORY_VALUES_ASSIGNED,
        "Family 2 rd-write witness path requires CS::ASSUME_MEMORY_VALUES_ASSIGNED = true; \
         the no-ASSUME path is not implemented"
    );

    // Per-opcode rd-write constraints. Low limb: jal/jalr → saved_pc_low; slt → slt_value.
    cs.add_constraint(
        Term::from(is_jal_writes_rd) * Term::from(comparison_rel_or_jump_saved_pc_low)
            + Term::from(is_jalr_writes_rd) * Term::from(comparison_rel_or_jump_saved_pc_low)
            + Term::from(is_slt_writes_rd) * Term::from(should_jump_or_slt_value)
            - (Constraint::from(is_jal_writes_rd)
                + Term::from(is_jalr_writes_rd)
                + Term::from(is_slt_writes_rd))
                * Term::from(rd_write_limbs[0]),
    );
    // High limb: jal/jalr write saved_pc_high.
    cs.add_constraint(
        (Constraint::from(is_jal_writes_rd) + Term::from(is_jalr_writes_rd))
            * (Constraint::from(comparison_rel_or_jump_saved_pc_high)
                - Term::from(rd_write_limbs[1])),
    );
    // Pin rd_write_limbs[1] = 0 when SLT writes rd (rd != 0). SLT's 0/1 result fits
    // in the low limb only; without this constraint the high limb is only bounded
    // by Family 1's range check at 2^16, leaving 16 bits attacker-controlled.
    cs.add_constraint(Term::from(is_slt_writes_rd) * Term::from(rd_write_limbs[1]));

    // rd_is_zero case: Family 2 fires with rd=0 forces rd_write = 0.
    cs.add_constraint(Term::from(gate_fam2_rd_zero) * Term::from(rd_write_limbs[0]));
    cs.add_constraint(Term::from(gate_fam2_rd_zero) * Term::from(rd_write_limbs[1]));
}
