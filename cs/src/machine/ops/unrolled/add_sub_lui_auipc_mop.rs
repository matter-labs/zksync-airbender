use crate::devices::optimization_context::AddSubRelation;

use super::decoder::AddSubLuiAuipcMopDecoder;
use super::*;

pub fn add_sub_lui_auipc_mop_table_addition_fn<F: PrimeField, CS: Circuit<F>>(cs: &mut CS) {
    // no table
    let _ = cs;
}

fn apply_add_sub_lui_auipc_mop<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    inputs: OpcodeFamilyCircuitState<F>,
) {
    let mut opt_ctx = OptimizationContext::new();
    let decoder = <AddSubLuiAuipcMopDecoder as OpcodeFamilyDecoder>::BitmaskCircuitParser::parse(
        cs,
        inputs.decoder_data.circuit_family_extra_mask,
    );

    // read inputs
    let (rs1_reg, rs1_mem_query) =
        get_rs1_as_shuffle_ram(cs, Num::Var(inputs.decoder_data.rs1_index), true);
    cs.add_shuffle_ram_query(rs1_mem_query);
    let (rs2_reg, rs2_mem_query) =
        get_rs2_as_shuffle_ram(cs, Num::Var(inputs.decoder_data.rs2_index), true);
    cs.add_shuffle_ram_query(rs2_mem_query);

    // do what's effectively inside of optimization context, but we will manually allocate the output
    let out = opt_ctx.get_register_output(cs);
    // we will also need to pay 2 more range checks
    let intermediate_tmp = opt_ctx.get_register_output(cs);

    let indexers = opt_ctx.save_indexers();

    assert!(F::CHARACTERISTICS < (1u64 << 32));
    let modulus_reg = Register([
        Num::Constant(F::from_u64_unchecked((F::CHARACTERISTICS as u16) as u64)),
        Num::Constant(F::from_u64_unchecked(
            ((F::CHARACTERISTICS >> 16) as u16) as u64,
        )),
    ]);

    let shift = Term::from(1u64 << 16);

    let Register([out_low, out_high]) = out;

    // IMPORTANT: we must NOT allocate any more registers
    let is_add = decoder.perform_add();
    let is_addi = decoder.perform_addi();
    let is_sub = decoder.perform_sub();
    let is_lui = decoder.perform_lui();
    let is_auipc = decoder.perform_auipc();
    let is_addmod = decoder.perform_addmod();
    let is_submod = decoder.perform_submod();
    let is_mulmod = decoder.perform_submod();

    // ADD
    let of_var = {
        opt_ctx.restore_indexers(indexers);
        let relation = AddSubRelation {
            exec_flag: is_add,
            a: rs1_reg,
            b: rs2_reg,
            c: out,
        };
        let of_var = opt_ctx
            .append_add_sub_relation_raw(cs, relation)
            .get_variable()
            .unwrap();

        of_var
    };
    // ADDI
    {
        opt_ctx.restore_indexers(indexers);
        let relation = AddSubRelation {
            exec_flag: is_addi,
            a: rs1_reg,
            b: Register(inputs.decoder_data.imm.map(|x| Num::Var(x))),
            c: out,
        };
        let t = opt_ctx.append_add_sub_relation_raw(cs, relation);
        // check that we indeed use the same boolean for all the cases
        assert_eq!(of_var, t.get_variable().unwrap());
    }

    // SUB
    {
        opt_ctx.restore_indexers(indexers);
        let relation = AddSubRelation {
            exec_flag: is_sub,
            a: out,
            b: rs2_reg,
            c: rs1_reg,
        };
        let t = opt_ctx.append_add_sub_relation_raw(cs, relation);
        // check that we indeed use the same boolean for all the cases
        assert_eq!(of_var, t.get_variable().unwrap());
    }
    // LUI
    {
        opt_ctx.restore_indexers(indexers);
        let relation = AddSubRelation {
            exec_flag: is_lui,
            a: Register(std::array::from_fn(|_| Num::Constant(F::ZERO))),
            b: Register(inputs.decoder_data.imm.map(|x| Num::Var(x))),
            c: out,
        };
        let t = opt_ctx.append_add_sub_relation_raw(cs, relation);
        // check that we indeed use the same boolean for all the cases
        assert_eq!(of_var, t.get_variable().unwrap());
    }

    // AUIPC
    {
        opt_ctx.restore_indexers(indexers);
        let relation = AddSubRelation {
            exec_flag: is_auipc,
            a: Register(inputs.cycle_start_state.pc.map(|x| Num::Var(x))),
            b: Register(inputs.decoder_data.imm.map(|x| Num::Var(x))),
            c: out,
        };
        let t = opt_ctx.append_add_sub_relation_raw(cs, relation);
        // check that we indeed use the same boolean for all the cases
        assert_eq!(of_var, t.get_variable().unwrap());
    }

    let [rs1_reg_low, rs1_reg_high] = rs1_reg.0;
    let [rs2_reg_low, rs2_reg_high] = rs2_reg.0;

    // ADDMOD
    {
        opt_ctx.restore_indexers(indexers);
        cs.add_constraint(
            Constraint::from(is_addmod)
                * ((Constraint::from(out_low) + shift * Term::from(out_high))
                    - (Constraint::from(rs1_reg_low)
                        + shift * Term::from(rs1_reg_high)
                        + Term::from(rs2_reg_low)
                        + shift * Term::from(rs2_reg_high))),
        );
        // of + out - modulus = tmp, and OF must be true
        let relation = AddSubRelation {
            exec_flag: is_addmod,
            a: intermediate_tmp,
            b: modulus_reg,
            c: out,
        };
        let addmod_borrow_bit = opt_ctx.append_add_sub_relation_raw(cs, relation);
        cs.add_constraint(
            Term::from(is_addmod) * (Term::from(1u64) - Term::from(addmod_borrow_bit)),
        );
        // check that we indeed use the same boolean for all the cases
        assert_eq!(of_var, addmod_borrow_bit.get_variable().unwrap());
    }

    // SUBMOD
    {
        opt_ctx.restore_indexers(indexers);
        cs.add_constraint(
            Constraint::from(is_submod)
                * ((Constraint::from(out_low) + shift * Term::from(out_high))
                    - (Constraint::from(rs1_reg_low) + shift * Term::from(rs1_reg_high)
                        - Term::from(rs2_reg_low)
                        - shift * Term::from(rs2_reg_high))),
        );
        let relation = AddSubRelation {
            exec_flag: is_submod,
            a: intermediate_tmp,
            b: modulus_reg,
            c: out,
        };
        let submod_borrow_bit = opt_ctx.append_add_sub_relation_raw(cs, relation);
        cs.add_constraint(
            Term::from(is_submod) * (Term::from(1u64) - Term::from(submod_borrow_bit)),
        );
        // check that we indeed use the same boolean for all the cases
        assert_eq!(of_var, submod_borrow_bit.get_variable().unwrap());
    }

    // MULMOD
    {
        opt_ctx.restore_indexers(indexers);
        // that will create a witness for us
        let tmp = cs.add_variable_from_constraint(
            (Constraint::from(rs1_reg_low) + shift * Term::from(rs1_reg_high))
                * (Constraint::from(rs2_reg_low) + shift * Term::from(rs2_reg_high)),
        );
        cs.add_constraint(
            Constraint::from(is_mulmod)
                * ((Constraint::from(out_low) + shift * Term::from(out_high)) - Term::from(tmp)),
        );
        let relation = AddSubRelation {
            exec_flag: is_mulmod,
            a: intermediate_tmp,
            b: modulus_reg,
            c: out,
        };
        let mulmod_borrow_bit = opt_ctx.append_add_sub_relation_raw(cs, relation);
        cs.add_constraint(
            Term::from(is_mulmod) * (Term::from(1u64) - Term::from(mulmod_borrow_bit)),
        );
        // check that we indeed use the same boolean for all the cases
        assert_eq!(of_var, mulmod_borrow_bit.get_variable().unwrap());
    }

    // Witness function
    let out_vars = out.0.map(|el| el.get_variable());
    let intemediate_vars = intermediate_tmp.0.map(|el| el.get_variable());
    let imm_vars = inputs.decoder_data.imm;
    let pc_vars = inputs.cycle_start_state.pc;
    let rs1_vars = rs1_reg.0.map(|el| el.get_variable());
    let rs2_vars = rs2_reg.0.map(|el| el.get_variable());

    let is_add_var = is_add.get_variable().unwrap();
    let is_addi_var = is_addi.get_variable().unwrap();
    let is_sub_var = is_sub.get_variable().unwrap();
    let is_lui_var = is_lui.get_variable().unwrap();
    let is_auipc_var = is_auipc.get_variable().unwrap();
    let is_addmod_var = is_addmod.get_variable().unwrap();
    let is_submod_var = is_submod.get_variable().unwrap();
    let is_mulmod_var = is_mulmod.get_variable().unwrap();

    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        // NOTE: it is UNCONDITIONAL assignment, even though we select across multiple variants

        let mut out_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0);
        let mut intermediate_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0);
        let mut of_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false);

        use crate::cs::witness_placer::*;
        let imm = placer.get_u32_from_u16_parts(imm_vars);
        let rs1_u32 = placer.get_u32_from_u16_parts(rs1_vars);
        let rs2_u32 = placer.get_u32_from_u16_parts(rs2_vars);
        let pc_u32 = placer.get_u32_from_u16_parts(pc_vars);
        let boolean_false = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false);
        let modulus_constant =
            <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(F::CHARACTERISTICS as u32);
        {
            let is_add = placer.get_boolean(is_add_var);
            let (add_result, of) = rs1_u32.overflowing_add(&rs2_u32);
            out_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                &is_add,
                &add_result,
                &out_value,
            );
            of_value =
                <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(&is_add, &of, &of_value);
        }
        {
            let is_addi = placer.get_boolean(is_addi_var);
            let (addi_result, of) = rs1_u32.overflowing_add(&imm);
            out_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                &is_addi,
                &addi_result,
                &out_value,
            );
            of_value =
                <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(&is_addi, &of, &of_value);
        }
        {
            let is_sub = placer.get_boolean(is_sub_var);
            let (sub_result, of) = rs1_u32.overflowing_sub(&rs2_u32);
            out_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                &is_sub,
                &sub_result,
                &out_value,
            );
            of_value =
                <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(&is_sub, &of, &of_value);
        }
        {
            let is_lui = placer.get_boolean(is_lui_var);
            out_value =
                <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(&is_lui, &imm, &out_value);
            of_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                &is_lui,
                &boolean_false,
                &of_value,
            );
        }
        {
            let is_auipc = placer.get_boolean(is_auipc_var);
            let (auipc_result, of) = pc_u32.overflowing_add(&imm);
            out_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                &is_auipc,
                &auipc_result,
                &out_value,
            );
            of_value =
                <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(&is_auipc, &of, &of_value);
        }

        let rs1_f =
            <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::from_integer(rs1_u32);
        let rs2_f =
            <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::from_integer(rs2_u32);

        // addmod
        {
            let is_addmod = placer.get_boolean(is_addmod_var);
            let addmod_result = {
                let mut addmod_f = rs1_f.clone();
                addmod_f.add_assign(&rs2_f);
                addmod_f.as_integer()
            };
            out_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                &is_addmod,
                &addmod_result,
                &out_value,
            );
            // and also compute intermediate
            let (tmp, of) = addmod_result.overflowing_sub(&modulus_constant);
            intermediate_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                &is_addmod,
                &tmp,
                &intermediate_value,
            );
            of_value =
                <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(&is_addmod, &of, &of_value);
        }
        // submod
        {
            let is_submod = placer.get_boolean(is_submod_var);
            let submod_result = {
                let mut submod_f = rs1_f.clone();
                submod_f.sub_assign(&rs2_f);
                submod_f.as_integer()
            };
            out_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                &is_submod,
                &submod_result,
                &out_value,
            );
            let (tmp, of) = submod_result.overflowing_sub(&modulus_constant);
            intermediate_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                &is_submod,
                &tmp,
                &intermediate_value,
            );
            of_value =
                <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(&is_submod, &of, &of_value);
        }
        // mulmod - we do NOT need to assign intermediate variable
        {
            let is_mulmod = placer.get_boolean(is_mulmod_var);
            let mulmod_result = {
                let mut mulmod_f = rs1_f.clone();
                mulmod_f.mul_assign(&rs2_f);
                mulmod_f.as_integer()
            };
            out_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                &is_mulmod,
                &mulmod_result,
                &out_value,
            );
            let (tmp, of) = mulmod_result.overflowing_sub(&modulus_constant);
            intermediate_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                &is_mulmod,
                &tmp,
                &intermediate_value,
            );
            of_value =
                <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(&is_mulmod, &of, &of_value);
        }

        // actually assign
        placer.assign_u32_from_u16_parts(out_vars, &out_value);
        placer.assign_u32_from_u16_parts(intemediate_vars, &intermediate_value);
        placer.assign_mask(of_var, &of_value);
    };
    cs.set_values(value_fn);

    // write to RD
    let rd_reg = out;
    let is_rd_x0 = Boolean::Is(inputs.decoder_data.rd_is_zero);
    let rd_mem_query = set_rd_with_mask_as_shuffle_ram(
        cs,
        Num::Var(inputs.decoder_data.rd_index),
        rd_reg,
        is_rd_x0,
        true,
    );
    cs.add_shuffle_ram_query(rd_mem_query);

    // and we can increment PC without range checks

    // write to PC
    bump_pc_no_range_checks_explicit(
        cs,
        Register(inputs.cycle_start_state.pc.map(|x| Num::Var(x))),
        Register(inputs.cycle_end_state.pc.map(|x| Num::Var(x))),
    );

    opt_ctx.enforce_all(cs);
}

pub fn add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
) {
    let input = cs.allocate_execution_circuit_state::<true>();
    apply_add_sub_lui_auipc_mop(cs, input);
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::utils::serialize_to_file;

    #[test]
    fn compile_add_sub_lui_auipc_mop_circuit() {
        use ::field::Mersenne31Field;

        let compiled = compile_unrolled_circuit_state_transition::<Mersenne31Field>(
            &|cs| add_sub_lui_auipc_mop_table_addition_fn(cs),
            &|cs| add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode(cs),
            1 << 20,
            24,
        );

        serialize_to_file(&compiled, "add_sub_lui_auipc_mop_preprocessed_layout.json");
    }

    #[test]
    fn compile_add_sub_lui_auipc_mop_witness_graph() {
        use ::field::Mersenne31Field;

        let ssa_forms = dump_ssa_witness_eval_form_for_unrolled_circuit::<Mersenne31Field>(
            &|cs| add_sub_lui_auipc_mop_table_addition_fn(cs),
            &|cs| add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode(cs),
        );
        serialize_to_file(&ssa_forms, "add_sub_lui_auipc_mop_preprocessed_ssa.json");
    }
}
