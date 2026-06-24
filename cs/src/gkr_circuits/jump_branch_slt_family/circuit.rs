use super::*;
use crate::cs::circuit_trait::*;
use crate::gkr_circuits::utils::update_intermediate_carry_value;
use crate::oracle::Placeholder;
use crate::structured_expr::Expr;
use crate::tables::TableDriver;
use crate::types::*;
use crate::witness_placer::*;
use field::PrimeField;

const TABLES_TOTAL_WIDTH: usize = 3;

pub fn jump_branch_slt_tables() -> Vec<TableType> {
    vec![
        TableType::RegIsZero,
        TableType::U16GetSign,
        TableType::ConditionalJmpBranchSlt,
        TableType::JumpCleanupOffset,
    ]
}

pub fn jump_branch_slt_table_addition_fn<F: PrimeField, CS: Circuit<F>>(cs: &mut CS) {
    for el in jump_branch_slt_tables() {
        cs.materialize_table::<TABLES_TOTAL_WIDTH>(el);
    }
}

pub fn jump_branch_slt_table_driver_fn<F: PrimeField>(table_driver: &mut TableDriver<F>) {
    for el in jump_branch_slt_tables() {
        table_driver.materialize_table::<TABLES_TOTAL_WIDTH>(el);
    }
}

fn apply_jump_branch_slt_inner<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    inputs: OpcodeFamilyCircuitState<F>,
    decoder: JumpSltBranchFamilyCircuitMask,
) {
    if let Some(circuit_family_extra_mask) =
        cs.get_value(inputs.decoder_data.circuit_family_extra_mask)
    {
        println!(
            "circuit_family_extra_mask = 0b{:08b}",
            circuit_family_extra_mask.as_u32_reduced()
        );
    }

    // read inputs and prepare outputs
    let rs1_access = cs.request_mem_access(
        MemoryAccessRequest::RegisterRead {
            reg_idx: inputs.decoder_data.rs1_index,
            read_value_placeholder: Placeholder::ShuffleRamReadValue(0),
            split_as_u8: false,
        },
        "rs1",
        0,
    );

    let rs2_access = cs.request_mem_access(
        MemoryAccessRequest::RegisterRead {
            reg_idx: inputs.decoder_data.rs2_index,
            read_value_placeholder: Placeholder::ShuffleRamReadValue(1),
            split_as_u8: false,
        },
        "rs2",
        1,
    );

    let rd_access = cs.request_mem_access(
        MemoryAccessRequest::RegisterReadWrite {
            reg_idx: inputs.decoder_data.rd_index,
            read_value_placeholder: Placeholder::ShuffleRamReadValue(2),
            write_value_placeholder: Placeholder::ShuffleRamWriteValue(2),
            split_read_as_u8: false,
            split_write_as_u8: false,
        },
        "rd",
        2,
    );

    let MemoryAccess::RegisterOnly(rs1_access) = rs1_access else {
        unreachable!()
    };
    let MemoryAccess::RegisterOnly(rs2_access) = rs2_access else {
        unreachable!()
    };
    let MemoryAccess::RegisterOnly(rd_access) = rd_access else {
        unreachable!()
    };

    let WordRepresentation::U16Limbs(rs1_limbs) = rs1_access.read_value else {
        unreachable!()
    };
    let WordRepresentation::U16Limbs(rs2_limbs) = rs2_access.read_value else {
        unreachable!()
    };
    let WordRepresentation::U16Limbs(rd_write_limbs) = rd_access.write_value else {
        unreachable!()
    };

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
                // let (add_result, of1) = sub_result.overflowing_sub(&imm);
                // let of = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::or(&of0, &of1);
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
        let pc_low = Expr::<F>::var(inputs.cycle_start_state.pc[0]);
        let pc_high = Expr::<F>::var(inputs.cycle_start_state.pc[1]);
        let rs1_low = Expr::<F>::var(rs1_limbs[0]);
        let rs1_high = Expr::<F>::var(rs1_limbs[1]);
        let rs2_low = Expr::<F>::var(rs2_limbs[0]);
        let rs2_high = Expr::<F>::var(rs2_limbs[1]);
        let imm_low = Expr::<F>::var(inputs.decoder_data.imm[0]);
        let imm_high = Expr::<F>::var(inputs.decoder_data.imm[1]);
        let comparison_low = Expr::<F>::var(comparison_rel_or_jump_saved_pc_low);
        let comparison_high = Expr::<F>::var(comparison_rel_or_jump_saved_pc_high);
        let carry0_intermediate = Expr::<F>::var(add_rel_0_intermediate_of_var);
        let carry0_final = Expr::<F>::var(add_rel_0_final_of_var);

        // for subtraction 2^16*of + a - b = c -> 2^16*of + a = b + c
        // so we use the output as the first addend, and keep the second addend unchanged.
        // NOTE: for additions we blindly mix imm and rs2 as preprocessing ensures that if imm !=0 then rs2 = x0
        let carry0_intermediate_shifted = carry0_intermediate.clone() * carry_shift;
        let jump_saved_pc_low = pc_low.clone() + Expr::<F>::from(4u32)
            - comparison_low.clone()
            - carry0_intermediate_shifted.clone();
        let branch_comparison_low = comparison_low.clone() + rs2_low.clone()
            - rs1_low.clone()
            - carry0_intermediate_shifted.clone();
        let slt_comparison_low =
            comparison_low.clone() + rs2_low + imm_low - rs1_low - carry0_intermediate_shifted;

        let add_like_low_expr = jump_saved_pc_low.clone().mask(is_jal)
            + jump_saved_pc_low.mask(is_jalr)
            + branch_comparison_low.mask(is_branch)
            + slt_comparison_low.mask(is_slt);
        cs.add_constraint_expr(add_like_low_expr);

        let carry0_final_shifted = carry0_final * carry_shift;
        let jump_saved_pc_high = carry0_intermediate.clone() + pc_high.clone()
            - comparison_high.clone()
            - carry0_final_shifted.clone();
        let branch_comparison_high =
            carry0_intermediate.clone() + comparison_high.clone() + rs2_high.clone()
                - rs1_high.clone()
                - carry0_final_shifted.clone();
        let slt_comparison_high = carry0_intermediate + comparison_high + rs2_high + imm_high
            - rs1_high
            - carry0_final_shifted;

        let add_like_high_expr = jump_saved_pc_high.clone().mask(is_jal)
            + jump_saved_pc_high.mask(is_jalr)
            + branch_comparison_high.mask(is_branch)
            + slt_comparison_high.mask(is_slt);
        cs.add_constraint_expr(add_like_high_expr);
    }

    // now we should compare the output result to 0,
    // then resolve jump/slt condition

    let comparison_result_is_zero = cs.add_named_variable("Comparison result is zero out var");
    cs.set_variables_from_lookup_constrained(
        &[LookupInput::from(
            Expr::<F>::var(comparison_rel_or_jump_saved_pc_low)
                + Expr::var(comparison_rel_or_jump_saved_pc_high),
        )],
        &[comparison_result_is_zero],
        cs::circuit::LookupQueryTableType::Constant(TableType::RegIsZero),
    );

    // we also need a sign of rs1 to resolve jumps
    let rs1_sign = cs.add_named_variable("rs1 sign boolean");
    cs.set_variables_from_lookup_constrained(
        &[LookupInput::from(rs1_limbs[1])],
        &[rs1_sign],
        cs::circuit::LookupQueryTableType::Constant(TableType::U16GetSign),
    );

    // Second-operand sign source for the comparison table. The table reads the second
    // operand's sign from bit 15 of its low-16 input. For the immediate variant (SLT/SLTI:
    // the decoder forces rs2 = x0 and carries the operand in `imm`) that sign must come
    // from the immediate's high limb, not rs2's (which is 0) -- otherwise signed `slti`
    // with a negative immediate resolves to the wrong value. Gated by `is_slt` so BRANCH
    // keeps rs2's high limb (its `imm` is the jump offset, not a comparison operand).
    // Mutually exclusive by decode (`imm != 0 => rs2 = x0`), so the gated sum is a select
    // and stays within 16 bits. Mirrors `slt_branch_sign_source`. Needs its own committed
    // variable: the gated term is degree 2 and lookup inputs must be degree 1.
    let slt_sign_source = cs.add_named_variable("slt/branch second-operand sign source");
    {
        let rs2_high_var = rs2_limbs[1];
        let imm_high_var = inputs.decoder_data.imm[1];
        let is_slt_var = is_slt.get_variable().unwrap();
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let rs2_high = placer.get_u16(rs2_high_var);
            let imm_high = placer.get_u16(imm_high_var);
            let is_slt = placer.get_boolean(is_slt_var);
            let zero = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(0);
            let addend =
                <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::select(&is_slt, &imm_high, &zero);
            // No overflow: mutual exclusion keeps the sum <= 0xFFFF.
            let (sign_source, _of) = rs2_high.overflowing_add(&addend);
            placer.assign_u16(slt_sign_source, &sign_source);
        };
        cs.set_values(value_fn);
    }
    cs.add_constraint_expr(
        Expr::<F>::var(slt_sign_source)
            - Expr::<F>::var(rs2_limbs[1])
            - Expr::<F>::var(inputs.decoder_data.imm[1]).mask(is_slt),
    );

    // and now we can resolve jump. Note that SLT/SLTU use the same formal(!) funct3 as BLT/BLTU,
    // and for JAL/JALR we formally set funct3 to be such that jump resolution will be always
    // false, so in computing next PC below we can avoid thinking about overlapping
    // boolean conditions
    let should_jump_or_slt_value = cs.add_named_variable("jump resolution variable");
    cs.set_variables_from_lookup_constrained(
        &[LookupInput::from(
            Expr::<F>::var(slt_sign_source)
                + Expr::var(rs1_sign) * F::from_u32(1 << 16).unwrap()
                + Expr::var(add_rel_0_final_of_var) * F::from_u32(1 << 17).unwrap()
                + Expr::var(comparison_result_is_zero) * F::from_u32(1 << 18).unwrap()
                + Expr::var(inputs.decoder_data.funct3.expect("must have funct3"))
                    * F::from_u32(1 << 19).unwrap(),
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
    cs.add_constraint_expr(
        Expr::<F>::from(is_branch) * Expr::var(should_jump_or_slt_value)
            - Expr::var(should_jump_if_branch),
    );

    // and the corresponding constraint
    // NOTE: if we have branch opcode, then `should_jump_or_slt_value` will indicate whether to branch or not,
    // and if we have `should_jump_or_slt_value` it'll indicate the value,
    // but not the presence of jump. That's why we added extra variable above
    {
        let pc_low = Expr::<F>::var(inputs.cycle_start_state.pc[0]);
        let pc_high = Expr::<F>::var(inputs.cycle_start_state.pc[1]);
        let rs1_low = Expr::<F>::var(rs1_limbs[0]);
        let rs1_high = Expr::<F>::var(rs1_limbs[1]);
        let imm_low = Expr::<F>::var(inputs.decoder_data.imm[0]);
        let imm_high = Expr::<F>::var(inputs.decoder_data.imm[1]);
        let pc_tmp_low = Expr::<F>::var(pc_intermediate_addition_tmp_low);
        let pc_out_high = Expr::<F>::var(inputs.cycle_end_state.pc[1]);
        let should_jump = Expr::<F>::var(should_jump_if_branch);
        let carry1_intermediate = Expr::<F>::var(add_rel_1_intermediate_of_var);
        let carry1_final = Expr::<F>::var(add_rel_1_final_of_var);

        let carry1_intermediate_shifted = carry1_intermediate.clone() * carry_shift;
        let jump_target_low = pc_low.clone() + imm_low.clone()
            - pc_tmp_low.clone()
            - carry1_intermediate_shifted.clone();
        let jalr_target_low =
            rs1_low + imm_low.clone() - pc_tmp_low.clone() - carry1_intermediate_shifted.clone();
        let pc_plus_four_low =
            pc_low + Expr::<F>::from(4u32) - pc_tmp_low - carry1_intermediate_shifted;
        let branch_taken_adjustment = should_jump.clone() * (imm_low - Expr::<F>::from(4u32));

        let add_like_low_expr = jump_target_low.mask(is_jal)
            + jalr_target_low.mask(is_jalr)
            + pc_plus_four_low.clone().mask(is_branch)
            + branch_taken_adjustment
            + pc_plus_four_low.mask(is_slt);
        cs.add_constraint_expr(add_like_low_expr);

        let carry1_final_shifted = carry1_final * carry_shift;
        let jump_target_high = carry1_intermediate.clone() + pc_high.clone() + imm_high.clone()
            - pc_out_high.clone()
            - carry1_final_shifted.clone();
        let jalr_target_high = carry1_intermediate.clone() + rs1_high + imm_high.clone()
            - pc_out_high.clone()
            - carry1_final_shifted.clone();
        let pc_plus_four_high = carry1_intermediate + pc_high - pc_out_high - carry1_final_shifted;
        let branch_taken_high_adjustment = should_jump * imm_high;

        let add_like_high_expr = jump_target_high.mask(is_jal)
            + jalr_target_high.mask(is_jalr)
            + pc_plus_four_high.clone().mask(is_branch)
            + branch_taken_high_adjustment
            + pc_plus_four_high.mask(is_slt);
        cs.add_constraint_expr(add_like_high_expr);
    }

    // cleanup lowest bit for jump address, and ensure that it's aligned
    let next_pc_bit_1 = cs.add_named_variable("bit 1 for computed next PC");
    cs.set_variables_from_lookup_constrained(
        &[LookupInput::from(pc_intermediate_addition_tmp_low)],
        &[next_pc_bit_1, inputs.cycle_end_state.pc[0]],
        cs::circuit::LookupQueryTableType::Constant(TableType::JumpCleanupOffset),
    );

    // unaligned jump is unprovable, and we only need to check bit number 1, as jump offset is always 0 mod 2,
    // and PC is 0 mod 4
    cs.add_constraint_expr(
        (Expr::<F>::from(is_jal) + Expr::<F>::from(is_jalr) + Expr::var(should_jump_if_branch))
            * Expr::var(next_pc_bit_1),
    );

    // our final touch is to write into RD. We should select and constraint.
    // NOTE: under preprocessing SLT with rd == x0 is preprocessed into NOP, but we write constraint explicitly
    // for clarity

    let selected_rd_low = cs.add_named_variable("selected rd[0]");
    let selected_rd_high = cs.add_named_variable("selected rd[1]");

    {
        let is_slt_var = is_slt.get_variable().unwrap();
        let is_jal_var = is_jal.get_variable().unwrap();
        let is_jalr_var = is_jalr.get_variable().unwrap();

        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            // NOTE: it is UNCONDITIONAL assignment, even though we select across multiple variants

            let jal_jalr_value = placer.get_u32_from_u16_parts([
                comparison_rel_or_jump_saved_pc_low,
                comparison_rel_or_jump_saved_pc_high,
            ]);
            let slt_value = placer.get_u16(should_jump_or_slt_value).widen();

            let mut out_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0);

            {
                // JAL/JALR
                let is_jal = placer.get_boolean(is_jal_var);
                let is_jalr = placer.get_boolean(is_jalr_var);
                let is_jump = is_jal.or(&is_jalr);
                out_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                    &is_jump,
                    &jal_jalr_value,
                    &out_value,
                );
            }
            {
                // SLT
                let is_slt = placer.get_boolean(is_slt_var);
                out_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                    &is_slt, &slt_value, &out_value,
                );
            }

            placer.assign_u32_from_u16_parts([selected_rd_low, selected_rd_high], &out_value);
        };
        cs.set_values(value_fn);
    }

    cs.add_constraint_expr(
        Expr::<F>::from(is_slt) * Expr::var(should_jump_or_slt_value)
            + (Expr::<F>::from(is_jal) + Expr::<F>::from(is_jalr))
                * Expr::var(comparison_rel_or_jump_saved_pc_low)
            - Expr::var(selected_rd_low),
    );
    cs.add_constraint_expr(
        (Expr::<F>::from(is_jal) + Expr::<F>::from(is_jalr))
            * Expr::var(comparison_rel_or_jump_saved_pc_high)
            - Expr::var(selected_rd_high),
    );

    assert!(
        CS::ASSUME_MEMORY_VALUES_ASSIGNED,
        "TODO: add witness generation here"
    );

    cs.add_constraint_expr(
        (Expr::<F>::one() - Expr::from(rd_is_zero)) * Expr::var(selected_rd_low)
            - Expr::var(rd_write_limbs[0]),
    );
    cs.add_constraint_expr(
        (Expr::<F>::one() - Expr::from(rd_is_zero)) * Expr::var(selected_rd_high)
            - Expr::var(rd_write_limbs[1]),
    );
}

pub fn jump_branch_slt_circuit_with_preprocessed_bytecode_for_gkr<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
) {
    let (input, bitmask) = cs.allocate_machine_state(true, false, JUMP_SLT_BRANCH_FAMILY_NUM_BITS);
    let bitmask: [_; JUMP_SLT_BRANCH_FAMILY_NUM_BITS] = bitmask.try_into().unwrap();
    let bitmask = bitmask.map(|el| Boolean::Is(el));
    let decoder = JumpSltBranchFamilyCircuitMask::from_mask(bitmask);
    apply_jump_branch_slt_inner(cs, input, decoder);
}

#[cfg(test)]
mod test {
    use test_utils::skip_if_ci;

    use super::*;
    use crate::cs::circuit_impl::BasicAssembly;
    use crate::gkr_compiler::compile_unrolled_circuit_state_transition_into_gkr;
    use crate::gkr_compiler::compile_unrolled_circuit_state_transition_into_unrolled_gkr_without_caches;
    use crate::gkr_compiler::dump_ssa_witness_eval_form;
    use crate::structured_expr::StructuredStatement;
    use crate::utils::serialize_to_file;

    type F = ::field::Mersenne31Field;

    fn has_sum_factor(expr: &Expr<F>) -> bool {
        let Expr::Product(factors) = expr else {
            return false;
        };

        factors.iter().any(|factor| matches!(factor, Expr::Sum(_)))
    }

    fn grouped_selector_terms_count(expr: &Expr<F>) -> usize {
        let Expr::Sum(terms) = expr else {
            return 0;
        };

        terms.iter().filter(|term| has_sum_factor(term)).count()
    }

    #[test]
    fn jump_branch_slt_records_grouped_selector_constraints() {
        let mut cs = BasicAssembly::<F>::new();
        jump_branch_slt_circuit_with_preprocessed_bytecode_for_gkr(&mut cs);
        let (output, _) = cs.finalize();

        assert!(output
            .structured_statements
            .iter()
            .any(|statement| matches!(
                statement,
                StructuredStatement::AssertZero { expr, .. }
                    if grouped_selector_terms_count(expr) >= 4
            )));
    }

    #[test]
    fn conditional_table_resolves_signed_slti_from_immediate_sign() {
        // Executable spec for the signed-SLTI sign fix. The `ConditionalJmpBranchSlt` table
        // derives the second operand's sign from bit 15 of its low-16 input. For the
        // immediate variant (SLT/SLTI: the decoder forces rs2 = x0 and carries the operand
        // in `imm`) the circuit must feed the IMMEDIATE's high limb there. Feeding rs2's
        // high limb (= 0, the old behaviour) is exactly the bug.
        use ::field::baby_bear::base::BabyBearField;

        let table = crate::tables::create_conditional_op_resolution_table::<BabyBearField>(0);

        // Pack a key exactly as `create_conditional_op_resolution_table` decodes it:
        // bits 0..16 = second-operand sign source, bit 16 = rs1_sign, bit 17 = unsigned_lt,
        // bit 18 = eq, bits 19..22 = funct3.
        let resolve =
            |sign_source: u32, rs1_sign: bool, unsigned_lt: bool, eq: bool, funct3: u32| -> u32 {
                let k = (sign_source & 0xFFFF)
                    | ((rs1_sign as u32) << 16)
                    | ((unsigned_lt as u32) << 17)
                    | ((eq as u32) << 18)
                    | (funct3 << 19);
                table.lookup_value::<1>(&[BabyBearField::new(k)])[0].as_u32_reduced()
            };

        const SLT_FUNCT3: u32 = 0b010;

        // `slti rd, x0, -1`: rs1 = 0 (>= 0), rs2 = x0, imm = -1 (high limb 0xFFFF).
        // unsigned_lt = borrow(rs1 - imm) = 1. Signed `0 < -1` = false => correct result 0.
        // Old (buggy) sign source = rs2 high limb = 0 -> table takes the same-sign branch and
        // returns unsigned_lt = 1 (WRONG). Fixed sign source = imm high limb = 0xFFFF ->
        // table sees rs2 < 0, rs1 >= 0 and returns 0 (CORRECT).
        assert_eq!(
            resolve(0x0000, false, true, false, SLT_FUNCT3),
            1,
            "documents the bug: feeding rs2's high limb (0) resolves signed `slti _,x0,-1` to 1"
        );
        assert_eq!(
            resolve(0xFFFF, false, true, false, SLT_FUNCT3),
            0,
            "fix: feeding the immediate's high limb (0xFFFF) resolves signed `slti _,x0,-1` to 0"
        );
    }

    #[test]
    fn jump_branch_slt_binds_immediate_sign_source() {
        // Regression guard for the signed-SLTI sign fix. The comparison table's
        // second-operand sign must be fed from a dedicated, value-bound sign-source variable
        // (rs2 high limb gated-summed with is_slt * imm high limb), not from rs2's high limb
        // directly. Reverting the fix removes this variable and reddens the test.
        let mut cs = BasicAssembly::<F>::new();
        jump_branch_slt_circuit_with_preprocessed_bytecode_for_gkr(&mut cs);
        let (output, _) = cs.finalize();

        // Reverting the fix removes this variable. (That it is value-bound rather than
        // dangling is covered separately by the determinism sweep over the compiled layout.)
        assert!(
            output
                .variable_names
                .values()
                .any(|name| name.as_str() == "slt/branch second-operand sign source"),
            "the SLTI sign fix must introduce the sign-source variable"
        );
    }

    #[test]
    fn compile_jump_branch_slt_circuit_into_gkr() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let gkr_compiled = compile_unrolled_circuit_state_transition_into_gkr::<BabyBearField>(
            &|cs| jump_branch_slt_table_addition_fn(cs),
            &|cs| jump_branch_slt_circuit_with_preprocessed_bytecode_for_gkr(cs),
            common_constants::ROM_WORD_SIZE,
            24,
        );

        serialize_to_file(
            &gkr_compiled,
            "compiled_circuits/jump_branch_slt_layout_gkr.json",
        );
    }

    #[test]
    fn compile_jump_branch_slt_gkr_witness_graph() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let ssa_forms = dump_ssa_witness_eval_form::<BabyBearField>(
            &|cs| jump_branch_slt_table_addition_fn(cs),
            &|cs| jump_branch_slt_circuit_with_preprocessed_bytecode_for_gkr(cs),
        );
        serialize_to_file(&ssa_forms, "compiled_circuits/jump_branch_slt_ssa_gkr.json");
    }

    #[test]
    fn compile_jump_branch_slt_circuit_into_no_caches_gkr() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let gkr_compiled =
            compile_unrolled_circuit_state_transition_into_unrolled_gkr_without_caches::<
                BabyBearField,
            >(
                &|cs| jump_branch_slt_table_addition_fn(cs),
                &|cs| jump_branch_slt_circuit_with_preprocessed_bytecode_for_gkr(cs),
                common_constants::ROM_WORD_SIZE,
                24,
            );

        serialize_to_file(
            &gkr_compiled,
            "compiled_circuits/jump_branch_slt_layout_no_caches_gkr.json",
        );
    }
}
