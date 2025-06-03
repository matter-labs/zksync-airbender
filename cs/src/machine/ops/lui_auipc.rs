use super::*;

pub const LUI_OP_KEY: DecoderMajorInstructionFamilyKey = DecoderMajorInstructionFamilyKey("LUI");
pub const AUIPC_OP_KEY: DecoderMajorInstructionFamilyKey =
    DecoderMajorInstructionFamilyKey("AUIPC");

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LuiOp;

impl DecodableMachineOp for LuiOp {
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
            (OPERATION_LUI, _, _) => {
                // LUI
                (InstructionType::UType, LUI_OP_KEY, &[][..])
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
    > MachineOp<F, ST, RS, DE, BS> for LuiOp
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
        let exec_flag = boolean_set.get_major_flag(LUI_OP_KEY);

        // Write decoded immediate into RD
        let res = inputs.get_imm();

        if exec_flag.get_value(cs).unwrap_or(false) {
            println!("LUI");
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
pub struct AuiPc;

impl DecodableMachineOp for AuiPc {
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
            (OPERATION_AUIPC, _, _) => {
                // AUIPC
                (InstructionType::UType, AUIPC_OP_KEY, &[][..])
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
    > MachineOp<F, ST, RS, DE, BS> for AuiPc
{
    fn apply<
        CS: Circuit<F>,
        const ASSUME_TRUSTED_CODE: bool,
        const OUTPUT_EXACT_EXCEPTIONS: bool,
    >(
        cs: &mut CS,
        machine_state: &ST,
        inputs: &DE,
        boolean_set: &BS,
        opt_ctx: &mut OptimizationContext<F, CS>,
    ) -> CommonDiffs<F> {
        opt_ctx.reset_indexers();
        let exec_flag = boolean_set.get_major_flag(AUIPC_OP_KEY);

        // add immediate into PC
        let pc = *machine_state.get_pc();
        let imm = inputs.get_imm();

        // NOTE: there is no 0 mod 4 check here are immediate only affects upper bits
        let (res, _of_flag) = opt_ctx.append_add_relation(pc, imm, exec_flag, cs);

        if exec_flag.get_value(cs).unwrap_or(false) {
            println!("AUIPC");
            dbg!(pc.get_value_unsigned(cs));
            dbg!(imm.get_value_unsigned(cs));
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
