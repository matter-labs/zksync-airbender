use super::*;

pub const ADD_OP_KEY: DecoderMajorInstructionFamilyKey =
    DecoderMajorInstructionFamilyKey("ADD/ADDI");
pub const SUB_OP_KEY: DecoderMajorInstructionFamilyKey =
    DecoderMajorInstructionFamilyKey("SUB/SUBI");

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AddOp;

impl DecodableMachineOp for AddOp {
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
            (OPERATION_OP, 0b000, 0b000_0000) => {
                // ADD
                (InstructionType::RType, ADD_OP_KEY, &[][..])
            }
            (OPERATION_OP_IMM, 0b000, _) => {
                // ADDI
                (InstructionType::IType, ADD_OP_KEY, &[][..])
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
    > MachineOp<F, ST, RS, DE, BS> for AddOp
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
        let exec_flag = boolean_set.get_major_flag(ADD_OP_KEY);

        // decoder will place immediate into SRC2 to account for ADD/ADDI and similar variations
        let src1 = inputs.get_rs1_or_equivalent().get_register();
        let src2 = inputs.get_rs2_or_equivalent().get_register();

        let (res, _of_flag) = opt_ctx.append_add_relation(src1, src2, exec_flag, cs);

        if exec_flag.get_value(cs).unwrap_or(false) {
            println!("ADD");
            dbg!(src1.get_value_signed(cs));
            dbg!(src2.get_value_signed(cs));
            dbg!(res.get_value_signed(cs));
        }

        let returned_value = [
            Constraint::<F>::from(res.0[0].get_variable()),
            Constraint::<F>::from(res.0[1].get_variable()),
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SubOp;

impl DecodableMachineOp for SubOp {
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
            (OPERATION_OP, 0b000, 0b010_0000) => {
                // SUB
                (InstructionType::RType, SUB_OP_KEY, &[][..])
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
    > MachineOp<F, ST, RS, DE, BS> for SubOp
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
        let exec_flag = boolean_set.get_major_flag(SUB_OP_KEY);

        let src1 = inputs.get_rs1_or_equivalent().get_register();
        let src2 = inputs.get_rs2_or_equivalent().get_register();

        let (res, _uf_flag) = opt_ctx.append_sub_relation(src1, src2, exec_flag, cs);

        if exec_flag.get_value(cs).unwrap_or(false) {
            println!("SUB");
            dbg!(src1.get_value_signed(cs));
            dbg!(src2.get_value_signed(cs));
            dbg!(res.get_value_signed(cs));
        }

        let returned_value = [
            Constraint::<F>::from(res.0[0].get_variable()),
            Constraint::<F>::from(res.0[1].get_variable()),
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
