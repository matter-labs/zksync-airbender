use super::*;

pub fn jump_branch_slt_tables() -> Vec<TableType> {
    vec![
        TableType::ConditionalJmpBranchSlt,
        TableType::JumpCleanupOffset,
    ]
}

pub fn jump_branch_slt_table_addition_fn<F: PrimeField, CS: Circuit<F>>(cs: &mut CS) {
    for el in jump_branch_slt_tables() {
        cs.materialize_table(el);
    }
}

pub fn jump_branch_slt_table_driver_fn<F: PrimeField>(table_driver: &mut TableDriver<F>) {
    for el in jump_branch_slt_tables() {
        table_driver.materialize_table(el);
    }
}

fn apply_jump_branch_slt<F: PrimeField, CS: Circuit<F>, const SUPPORT_SIGNED: bool>(
    cs: &mut CS,
    inputs: OpcodeFamilyCircuitState<F>,
) {
    assert!(SUPPORT_SIGNED);

    let mut opt_ctx = OptimizationContext::new();
    let decoder =
        <JumpSltBranchDecoder<SUPPORT_SIGNED> as OpcodeFamilyDecoder>::BitmaskCircuitParser::parse(
            cs,
            inputs.decoder_data.circuit_family_extra_mask,
        );

    let is_branches = decoder.perform_branch();
    let is_sltregisters = decoder.perform_slt();
    let is_sltimmediates = decoder.perform_slti();
    let is_jal = decoder.perform_jal();
    let is_jalr = decoder.perform_jalr();

    let four_as_reg = Register([
        Num::Constant(F::from_u64_unchecked(4)),
        Num::Constant(F::ZERO),
    ]);

    // GET OPERANDS
    let (rs1_reg, rs1_mem_query) =
        get_rs1_as_shuffle_ram(cs, Num::Var(inputs.decoder_data.rs1_index), true);
    cs.add_shuffle_ram_query(rs1_mem_query);
    let (rs2_reg, rs2_mem_query) =
        get_rs2_as_shuffle_ram(cs, Num::Var(inputs.decoder_data.rs2_index), true);
    cs.add_shuffle_ram_query(rs2_mem_query);

    let imm_as_reg = Register(inputs.decoder_data.imm.map(|el| Num::Var(el)));
    let pc_as_reg = Register(inputs.cycle_start_state.pc.map(|el| Num::Var(el)));
    let rd_is_zero = Boolean::Is(inputs.decoder_data.rd_is_zero);

    // 1) first we get rd
    // BRANCHES
    let (comparison_out_for_branch_or_slt, of) =
        opt_ctx.append_sub_relation(rs1_reg, rs2_reg, is_branches, cs);
    let indexers = opt_ctx.save_indexers();
    // SLTREGISTERS
    opt_ctx.reset_indexers();
    let (comparison_out_for_branch_or_slt_t, of_t) =
        opt_ctx.append_sub_relation(rs1_reg, rs2_reg, is_sltregisters, cs);
    assert_eq!(
        comparison_out_for_branch_or_slt_t.0[0].get_variable(),
        comparison_out_for_branch_or_slt.0[0].get_variable()
    );
    assert_eq!(
        comparison_out_for_branch_or_slt_t.0[1].get_variable(),
        comparison_out_for_branch_or_slt.0[1].get_variable()
    );
    assert_eq!(of.get_variable().unwrap(), of_t.get_variable().unwrap());
    let t = opt_ctx.save_indexers();
    assert_eq!(indexers, t);
    // SLTIMMEDIATES
    opt_ctx.reset_indexers();
    let (comparison_out_for_branch_or_slt_t, of_t) =
        opt_ctx.append_sub_relation(rs1_reg, imm_as_reg, is_sltimmediates, cs);
    assert_eq!(
        comparison_out_for_branch_or_slt_t.0[0].get_variable(),
        comparison_out_for_branch_or_slt.0[0].get_variable()
    );
    assert_eq!(
        comparison_out_for_branch_or_slt_t.0[1].get_variable(),
        comparison_out_for_branch_or_slt.0[1].get_variable()
    );
    assert_eq!(of.get_variable().unwrap(), of_t.get_variable().unwrap());
    let t = opt_ctx.save_indexers();
    assert_eq!(indexers, t);
    // JAL (no PC overflow)
    opt_ctx.reset_indexers();
    let (next_pc_into_rd, of_t) = opt_ctx.append_add_relation(pc_as_reg, four_as_reg, is_jal, cs);
    assert_eq!(
        next_pc_into_rd.0[0].get_variable(),
        comparison_out_for_branch_or_slt.0[0].get_variable()
    );
    assert_eq!(
        next_pc_into_rd.0[1].get_variable(),
        comparison_out_for_branch_or_slt.0[1].get_variable()
    );
    assert_eq!(of.get_variable().unwrap(), of_t.get_variable().unwrap());
    // cs.add_constraint(Constraint::from(is_jal) * Term::from(of)); // PC + 4 can overflow
    let t = opt_ctx.save_indexers();
    assert_eq!(indexers, t);
    // JALR (no PC overflow)
    opt_ctx.reset_indexers();
    let (next_pc_into_rd, of_t) = opt_ctx.append_add_relation(pc_as_reg, four_as_reg, is_jalr, cs);
    assert_eq!(
        next_pc_into_rd.0[0].get_variable(),
        comparison_out_for_branch_or_slt.0[0].get_variable()
    );
    assert_eq!(
        next_pc_into_rd.0[1].get_variable(),
        comparison_out_for_branch_or_slt.0[1].get_variable()
    );
    assert_eq!(of.get_variable().unwrap(), of_t.get_variable().unwrap());
    // cs.add_constraint(Constraint::from(is_jalr) * Term::from(of)); // PC + 4 can overflow
    let t = opt_ctx.save_indexers();
    assert_eq!(indexers, t);

    // get flag for signed/unsigned cases
    let oz = cs.is_zero_reg(comparison_out_for_branch_or_slt);
    let sign1 = {
        let rs1_reg_high = rs1_reg.0[1];
        let pc_high = pc_as_reg.0[1];
        get_sign_bit_from_orthogonal_terms(
            cs,
            [
                is_branches,
                is_sltregisters,
                is_sltimmediates,
                is_jal,
                is_jalr,
            ],
            [rs1_reg_high, rs1_reg_high, rs1_reg_high, pc_high, pc_high].map(|x| x.get_variable()),
        )
    };
    let sign2 = {
        let rs2_reg_high = rs2_reg.0[1];
        let imm_high = imm_as_reg.0[1];
        get_sign_bit_from_orthogonal_terms(
            cs,
            [is_branches, is_sltregisters, is_sltimmediates],
            [rs2_reg_high, rs2_reg_high, imm_high].map(|x| x.get_variable()),
        )
    };

    let Boolean::Not(not_sign1_var) = sign1 else {
        unreachable!()
    };

    let Boolean::Not(not_sign2_var) = sign2 else {
        unreachable!()
    };

    let lookup_inputs = [
        Constraint::from(of)
            + Term::from(1 << 1) * Term::from(oz)
            + Term::from(1 << 2) * (Term::from(1) - Term::from(not_sign1_var))
            + Term::from(1 << 3) * (Term::from(1) - Term::from(not_sign2_var)),
        Constraint::from(inputs.decoder_data.funct3),
    ]
    .map(|c| LookupInput::from(c));
    let [flag] = cs.get_variables_from_lookup_constrained::<2, 1>(
        &lookup_inputs,
        TableType::ConditionalJmpBranchSlt,
    );

    // write to RD
    let rd_reg = {
        let write_out = Boolean::Is(cs.add_variable_from_constraint(
            (Term::from(1) - Term::from(rd_is_zero.get_variable().unwrap()))
                * (Term::from(is_jal) + Term::from(is_jalr)),
        ));
        let write_flag = Boolean::Is(cs.add_variable_from_constraint(
            (Term::from(1) - Term::from(rd_is_zero.get_variable().unwrap()))
                * (Term::from(is_sltregisters) + Term::from(is_sltimmediates)),
        ));
        let flag_reg = Register([Num::Var(flag), Num::Constant(F::ZERO)]);

        // If we will do branch, then it is formally 0 value anyway
        Register::choose_from_orthogonal_variants(
            cs,
            &[write_out, write_flag],
            &[next_pc_into_rd, flag_reg],
        )
    };
    // NOTE: Decoder table always sets rd = 0 for branch opcode, so we will end up writing 0 to x0
    let rd_mem_query = set_rd_without_mask_as_shuffle_ram(
        cs,
        Num::Var(inputs.decoder_data.rd_index),
        rd_reg,
        true,
    );
    cs.add_shuffle_ram_query(rd_mem_query);

    // 2) then we use the same variable to get pc value for different opcodes
    // TODO: by extending opt_ctx we can integrate the cleanup operation for jalr
    // SLTREGISTERS (no PC overflow)
    opt_ctx.restore_indexers(indexers);
    let (next_pc_for_state, of) =
        opt_ctx.append_add_relation(pc_as_reg, four_as_reg, is_sltregisters, cs);
    // cs.add_constraint(Constraint::from(is_sltregisters) * Term::from(of)); // PC + 4 can overflow
    // SLTIMMEDIATES (no PC overflow)
    opt_ctx.restore_indexers(indexers);
    let (next_pc_for_state_t, of_t) =
        opt_ctx.append_add_relation(pc_as_reg, four_as_reg, is_sltimmediates, cs);
    // cs.add_constraint(Constraint::from(is_sltimmediates) * Term::from(of)); // PC + 4 can overflow
    assert_eq!(
        next_pc_for_state_t.0[0].get_variable(),
        next_pc_for_state.0[0].get_variable()
    );
    assert_eq!(
        next_pc_for_state_t.0[1].get_variable(),
        next_pc_for_state.0[1].get_variable()
    );
    assert_eq!(of.get_variable().unwrap(), of_t.get_variable().unwrap());
    // JAL
    opt_ctx.restore_indexers(indexers);
    let (next_pc_for_state_t, of_t) =
        opt_ctx.append_add_relation(pc_as_reg, imm_as_reg, is_jal, cs);
    // cs.add_constraint(Constraint::from(is_jal) * Term::from(of)); // PC  can overflow
    assert_eq!(
        next_pc_for_state_t.0[0].get_variable(),
        next_pc_for_state.0[0].get_variable()
    );
    assert_eq!(
        next_pc_for_state_t.0[1].get_variable(),
        next_pc_for_state.0[1].get_variable()
    );
    assert_eq!(of.get_variable().unwrap(), of_t.get_variable().unwrap());
    // JALR
    opt_ctx.restore_indexers(indexers);
    let (next_pc_for_state_t, of_t) = opt_ctx.append_add_relation(rs1_reg, imm_as_reg, is_jalr, cs);
    // cs.add_constraint(Constraint::from(is_jalr) * Term::from(of)); // PC  can overflow
    assert_eq!(
        next_pc_for_state_t.0[0].get_variable(),
        next_pc_for_state.0[0].get_variable()
    );
    assert_eq!(
        next_pc_for_state_t.0[1].get_variable(),
        next_pc_for_state.0[1].get_variable()
    );
    assert_eq!(of.get_variable().unwrap(), of_t.get_variable().unwrap());
    // BRANCHES (not taken, no PC overflow)
    opt_ctx.restore_indexers(indexers);
    let is_branches_skipped = Boolean::and(&is_branches, &Boolean::Is(flag).toggle(), cs);
    let (next_pc_for_state_t, of_t) =
        opt_ctx.append_add_relation(pc_as_reg, four_as_reg, is_branches_skipped, cs);
    // cs.add_constraint(Constraint::from(is_branches_skipped) * Term::from(of)); // PC + 4 can overflow
    assert_eq!(
        next_pc_for_state_t.0[0].get_variable(),
        next_pc_for_state.0[0].get_variable()
    );
    assert_eq!(
        next_pc_for_state_t.0[1].get_variable(),
        next_pc_for_state.0[1].get_variable()
    );
    assert_eq!(of.get_variable().unwrap(), of_t.get_variable().unwrap());
    // BRANCHES (taken)
    opt_ctx.restore_indexers(indexers);
    let is_branches_taken = Boolean::and(&is_branches, &Boolean::Is(flag), cs);
    let (next_pc_for_state_t, of_t) =
        opt_ctx.append_add_relation(pc_as_reg, imm_as_reg, is_branches_taken, cs);
    // cs.add_constraint(Constraint::from(is_branches_taken) * Term::from(of)); // PC can overflow
    assert_eq!(
        next_pc_for_state_t.0[0].get_variable(),
        next_pc_for_state.0[0].get_variable()
    );
    assert_eq!(
        next_pc_for_state_t.0[1].get_variable(),
        next_pc_for_state.0[1].get_variable()
    );
    assert_eq!(of.get_variable().unwrap(), of_t.get_variable().unwrap());

    // get cleanup bits
    let lookup_inputs = [Constraint::from(next_pc_for_state.0[0])].map(|x| LookupInput::from(x));
    let [bit_1, dst_low_for_jump] = cs.get_variables_from_lookup_constrained::<1, 2>(
        &lookup_inputs,
        TableType::JumpCleanupOffset,
    );

    // unaligned jump is unprovable, and we only need to check bit number 1, as jump offset is always 0 mod 2,
    // and PC is 0 mod 4
    cs.add_constraint(
        (Constraint::from(is_jal) + Term::from(is_jalr) + Term::from(is_branches_taken))
            * Term::from(bit_1),
    );

    cs.add_constraint(
        (Constraint::from(is_jal) + Term::from(is_jalr) + Term::from(is_branches_taken)) * Term::from(dst_low_for_jump) + // if it required cleanup and verification
        (Constraint::from(is_sltregisters) + Term::from(is_sltimmediates) + Term::from(is_branches_skipped)) * Term::from(next_pc_for_state.0[0]) // if branch not taken or if we to SLT/SLTI
        - Constraint::from(inputs.cycle_end_state.pc[0]),
    );

    // Here we should also pay attention to padding cases, when none of the opcodes is taken,
    // so we must make a long "mask"
    cs.add_constraint(
        (Constraint::from(is_jal)
            + Term::from(is_jalr)
            + Term::from(is_branches_taken)
            + Constraint::from(is_sltregisters)
            + Term::from(is_sltimmediates)
            + Term::from(is_branches_skipped))
            * Term::from(next_pc_for_state.0[1])
            - Constraint::from(inputs.cycle_end_state.pc[1]),
    );

    // add witness evals
    let is_jal_var = is_jal.get_variable().unwrap();
    let is_jalr_var = is_jalr.get_variable().unwrap();
    let is_branches_taken_var = is_branches_taken.get_variable().unwrap();
    let is_sltregisters_var = is_sltregisters.get_variable().unwrap();
    let is_sltimmediates_var = is_sltimmediates.get_variable().unwrap();
    let is_branches_skipped_var = is_branches_skipped.get_variable().unwrap();

    let default_next_pc_vars = next_pc_for_state.0.map(|el| el.get_variable());
    let next_pc_dst_vars = inputs.cycle_end_state.pc;

    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        use cs::witness_placer::*;
        let is_jal = placer.get_boolean(is_jal_var);
        let is_jalr = placer.get_boolean(is_jalr_var);
        let is_branches_taken = placer.get_boolean(is_branches_taken_var);
        let is_sltregisters = placer.get_boolean(is_sltregisters_var);
        let is_sltimmediates = placer.get_boolean(is_sltimmediates_var);
        let is_branches_skipped = placer.get_boolean(is_branches_skipped_var);

        let mut pc_result_low = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(0);
        let mut pc_result_high = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(0);

        let default_pc_low = placer.get_u16(default_next_pc_vars[0]);
        let default_pc_high = placer.get_u16(default_next_pc_vars[1]);
        let jump_result_pc_low = placer.get_u16(dst_low_for_jump);

        let use_default_pc = is_sltregisters
            .or(&is_sltimmediates)
            .or(&is_branches_skipped);
        let use_jump_result = is_jal.or(&is_jalr).or(&is_branches_taken);
        let use_any = use_default_pc.or(&use_jump_result);

        pc_result_low = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::select(
            &use_default_pc,
            &default_pc_low,
            &pc_result_low,
        );
        pc_result_low = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::select(
            &use_jump_result,
            &jump_result_pc_low,
            &pc_result_low,
        );

        pc_result_high = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::select(
            &use_any,
            &default_pc_high,
            &pc_result_high,
        );

        placer.assign_u16(next_pc_dst_vars[0], &pc_result_low);
        placer.assign_u16(next_pc_dst_vars[1], &pc_result_high);
    };
    cs.set_values(value_fn);
}

pub fn jump_branch_slt_circuit_with_preprocessed_bytecode<
    F: PrimeField,
    CS: Circuit<F>,
    const SUPPORT_SIGNED: bool,
>(
    cs: &mut CS,
) {
    let input = cs.allocate_execution_circuit_state::<true>();
    apply_jump_branch_slt::<F, CS, SUPPORT_SIGNED>(cs, input);
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::utils::serialize_to_file;

    #[test]
    fn compile_jump_branch_slt_circuit() {
        use ::field::Mersenne31Field;

        let compiled = compile_unrolled_circuit_state_transition::<Mersenne31Field>(
            &|cs| jump_branch_slt_table_addition_fn(cs),
            &|cs| jump_branch_slt_circuit_with_preprocessed_bytecode::<_, _, true>(cs),
            1 << 20,
            24,
        );

        serialize_to_file(&compiled, "jump_branch_slt_preprocessed_layout.json");
    }

    #[test]
    fn compile_jump_branch_slt_witness_graph() {
        use ::field::Mersenne31Field;

        let ssa_forms = dump_ssa_witness_eval_form_for_unrolled_circuit::<Mersenne31Field>(
            &|cs| jump_branch_slt_table_addition_fn(cs),
            &|cs| jump_branch_slt_circuit_with_preprocessed_bytecode::<_, _, true>(cs),
        );
        serialize_to_file(&ssa_forms, "jump_branch_slt_preprocessed_ssa.json");
    }
}
