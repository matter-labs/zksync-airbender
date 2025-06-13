use crate::cs::witness_placer::WitnessTypeSet;
use crate::cs::witness_placer::{
    cs_debug_evaluator::witness_early_branch_if_possible, WitnessPlacer,
};

use super::*;

pub const MOP_OP_KEY: DecoderMajorInstructionFamilyKey = DecoderMajorInstructionFamilyKey("MOP");
pub const ADDMOD_OP_KEY: DecoderInstructionVariantsKey = DecoderInstructionVariantsKey("ADDMOD");
pub const SUBMOD_OP_KEY: DecoderInstructionVariantsKey = DecoderInstructionVariantsKey("SUBMOD");
pub const MULMOD_OP_KEY: DecoderInstructionVariantsKey = DecoderInstructionVariantsKey("MULMOD");

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MopOp;

impl DecodableMachineOp for MopOp {
    fn define_decoder_subspace(
        &self,
        opcode: u8,
        func3: u8,
        func7: u8,
    ) -> Result<
        (
            InstructionType,
            DecoderMajorInstructionFamilyKey,
            &'static [DecoderInstructionVariantsKey],
        ),
        (),
    > {
        let params = match (opcode, func3, func7) {
            (OPERATION_SYSTEM, 0b100, 0b1000001) => {
                // ADD
                (InstructionType::RType, MOP_OP_KEY, &[ADDMOD_OP_KEY][..])
            }
            (OPERATION_SYSTEM, 0b100, 0b1000011) => {
                // Sub
                (InstructionType::RType, MOP_OP_KEY, &[SUBMOD_OP_KEY][..])
            }
            (OPERATION_SYSTEM, 0b100, 0b1000101) => {
                // MUL
                (InstructionType::RType, MOP_OP_KEY, &[MULMOD_OP_KEY][..])
            }
            _ => return Err(()),
        };

        Ok(params)
    }
}

impl<
        F: PrimeField,
        ST: BaseMachineState<F>,
        RS: RegisterValueSource<F>,
        DE: DecoderOutputSource<F, RS>,
        BS: IndexableBooleanSet,
    > MachineOp<F, ST, RS, DE, BS> for MopOp
{
    fn apply<
        CS: Circuit<F>,
        const ASSUME_TRUSTED_CODE: bool,
        const OUTPUT_EXACT_EXCEPTIONS: bool,
    >(
        cs: &mut CS,
        _machine_state: &ST,
        inputs: &DE,
        boolean_set: &BS,
        opt_ctx: &mut OptimizationContext<F, CS>,
    ) -> CommonDiffs<F> {
        opt_ctx.reset_indexers();
        let exec_flag = boolean_set.get_major_flag(MOP_OP_KEY);
        let addmod = boolean_set.get_minor_flag(MOP_OP_KEY, ADDMOD_OP_KEY);
        let submod = boolean_set.get_minor_flag(MOP_OP_KEY, SUBMOD_OP_KEY);
        let mulmod = boolean_set.get_minor_flag(MOP_OP_KEY, MULMOD_OP_KEY);

        let src1 = inputs.get_rs1_or_equivalent().get_register();
        let src2 = inputs.get_rs2_or_equivalent().get_register();

        let shift = F::from_u64_unchecked(1u64 << 16);

        let product_result = cs.add_variable_from_constraint(
            (Term::from(src1.0[0].get_variable()) + Term::from((shift, src1.0[1].get_variable())))
                * (Term::from(src2.0[0].get_variable())
                    + Term::from((shift, src2.0[1].get_variable()))),
        );

        // select orthogonal if we execute MOP, and do not care otherwise
        let result_register = opt_ctx.get_register_output(cs);
        // here we have to use intermediate variables and make a constraint like execute*(intermediate - output) == 0,
        // because value of `get_register_output` can be set by other branches

        // We do not need range checks here - if those values are not in the proper range, then constraint mentioned above will fail
        let [result_tmp_low, result_tmp_high] = std::array::from_fn(|_| cs.add_variable());
        cs.add_constraint(
            (Term::from(mulmod.get_variable().unwrap()) * Term::from(product_result))
                + (Term::from(addmod.get_variable().unwrap())
                    * (Term::from(src1.0[0].get_variable())
                        + Term::from((shift, src1.0[1].get_variable()))
                        + Term::from(src2.0[0].get_variable())
                        + Term::from((shift, src2.0[1].get_variable()))))
                + (Term::from(submod.get_variable().unwrap())
                    * (Term::from(src1.0[0].get_variable())
                        + Term::from((shift, src1.0[1].get_variable()))
                        - Term::from(src2.0[0].get_variable())
                        - Term::from((shift, src2.0[1].get_variable()))))
                - (Term::from(result_tmp_low) + Term::from((shift, result_tmp_high))),
        );

        let src_1_vars = [src1.0[0].get_variable(), src1.0[1].get_variable()];
        let src_2_vars = [src2.0[0].get_variable(), src2.0[1].get_variable()];

        let is_addmod = addmod.get_variable().unwrap();
        let is_submod = submod.get_variable().unwrap();
        let is_mulmod = mulmod.get_variable().unwrap();

        let outputs = [result_tmp_low, result_tmp_high];

        // assign witness to temporary result
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            use crate::cs::witness_placer::WitnessComputationalField;

            let a_reg = placer.get_u32_from_u16_parts(src_1_vars);
            let b_reg: <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32 =
                placer.get_u32_from_u16_parts(src_2_vars);

            let a_reg =
                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::from_integer(
                    a_reg,
                );
            let b_reg =
                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::from_integer(
                    b_reg,
                );

            let addmod_mask = placer.get_boolean(is_addmod);
            let submod_mask = placer.get_boolean(is_submod);
            let mulmod_mask = placer.get_boolean(is_mulmod);

            let mut result =
                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::constant(F::ZERO);
            // This logic reflects our constraint, even though looks ugly
            {
                let mut t = a_reg.clone();
                t.add_assign(&b_reg);
                result.add_assign_masked(&addmod_mask, &t);
            }
            {
                let mut t = a_reg.clone();
                t.sub_assign(&b_reg);
                result.add_assign_masked(&submod_mask, &t);
            }
            {
                result.add_assign_product_masked(&mulmod_mask, &a_reg, &b_reg);
            }

            let result = result.as_integer();
            placer.assign_u32_from_u16_parts(outputs, &result);
        };
        cs.set_values(value_fn);

        // add constraints and conditionally assign witness to final result

        cs.add_constraint(
            Term::from(exec_flag.get_variable().unwrap())
                * (Term::from(result_tmp_low) - Term::from(result_register.0[0].get_variable())),
        );
        cs.add_constraint(
            Term::from(exec_flag.get_variable().unwrap())
                * (Term::from(result_tmp_high) - Term::from(result_register.0[1].get_variable())),
        );

        let input_vars = [result_tmp_low, result_tmp_high];
        let output_vars = [
            result_register.0[0].get_variable(),
            result_register.0[1].get_variable(),
        ];
        let exec_flag_var = exec_flag.get_variable().unwrap();

        let inner_value_fn = move |placer: &mut CS::WitnessPlacer| {
            let mask = placer.get_boolean(exec_flag_var);
            let in_value = placer.get_u32_from_u16_parts(input_vars);
            placer.conditionally_assign_u32(output_vars, &mask, &in_value);
        };

        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let mask = placer.get_boolean(exec_flag_var);
            witness_early_branch_if_possible(mask, placer, &inner_value_fn);
        };

        cs.set_values(value_fn);
        // we want to return canonical result, so we will create subtraction relation and require underflow
        assert!(F::CHARACTERISTICS < u32::MAX as u64);
        let modulus = Register::new_from_constant(F::CHARACTERISTICS as u32);
        let (_res, uf_flag) = opt_ctx.append_sub_relation(result_register, modulus, exec_flag, cs);
        // if we execute, then UF must be true
        cs.add_constraint(
            (Term::from(1u64) - Term::from(uf_flag.get_variable().unwrap()))
                * Term::from(exec_flag.get_variable().unwrap()),
        );

        if exec_flag.get_value(cs).unwrap_or(false) {
            println!("MOP");
            if addmod.get_value(cs).unwrap() {
                println!("ADDMOD");
            }
            if submod.get_value(cs).unwrap() {
                println!("SUBMOD");
            }
            if mulmod.get_value(cs).unwrap() {
                println!("MULMOD");
            }
            dbg!(src1.get_value_unsigned(cs));
            dbg!(src2.get_value_unsigned(cs));
            dbg!(cs.get_value(result_tmp_low));
            dbg!(cs.get_value(result_tmp_high));
            dbg!(result_register.get_value_unsigned(cs));
            dbg!(uf_flag.get_value(cs));
        }

        let returned_value = [
            Constraint::<F>::from(result_register.0[0].get_variable()),
            Constraint::<F>::from(result_register.0[1].get_variable()),
        ];

        CommonDiffs {
            exec_flag,
            trapped: None,
            trap_reason: None,
            rd_value: vec![(returned_value, exec_flag)],
            new_pc_value: NextPcValue::Default,
        }
    }
}
