use super::*;

pub const JUMP_COMMON_OP_KEY: DecoderMajorInstructionFamilyKey =
    DecoderMajorInstructionFamilyKey("JUMP_COMMON_KEY");
pub const JAL_OP_KEY: DecoderInstructionVariantsKey = DecoderInstructionVariantsKey("JAL");

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct JumpOp;

impl DecodableMachineOp for JumpOp {
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
            (OPERATION_JAL, _, _) => {
                // JAL
                (
                    InstructionType::JType,
                    JUMP_COMMON_OP_KEY,
                    &[JAL_OP_KEY][..],
                )
            }
            (OPERATION_JALR, 0b000, _) => {
                // JALR
                (InstructionType::IType, JUMP_COMMON_OP_KEY, &[][..])
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
    > MachineOp<F, ST, RS, DE, BS> for JumpOp
{
    fn define_used_tables() -> Vec<TableType> {
        vec![TableType::JumpCleanupOffset]
    }

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
        let exec_flag = boolean_set.get_major_flag(JUMP_COMMON_OP_KEY);
        let pc_next = inputs.get_pc_next();

        // our decoder will already place into SRC1 the value for JALR
        let src1 = inputs.get_rs1_or_equivalent().get_register();
        let imm = inputs.get_imm();

        // JAL adds immediate (that encodes 2-byte offsets) to PC
        // JALR addrs immediate (normal one) to RS1

        let is_jal = boolean_set.get_minor_flag(JUMP_COMMON_OP_KEY, JAL_OP_KEY);
        let pc = *machine_state.get_pc();

        let src1 = Register::choose::<CS>(cs, &is_jal, &pc, &src1);
        let (x, _of_flag) = opt_ctx.append_add_relation(src1, imm, exec_flag, cs);

        if ASSUME_TRUSTED_CODE {
            // - if it's JALR then we should clean the lowest bit anyway, so we only need to check 2nd bit

            let [bit_1, dst_low] = opt_ctx.append_lookup_relation(
                cs,
                &[x.0[0].get_variable()],
                TableType::JumpCleanupOffset.to_num(),
                exec_flag,
            );
            let is_misaligned_addr = bit_1;

            // if we have misasigned jump then we should make it unprovable circuit
            cs.add_constraint(Term::from(is_misaligned_addr) * exec_flag.get_terms());

            let dst_low = Num::Var(dst_low);
            let dst_high = x.0[1];
            let dst = Register([dst_low, dst_high]);

            if exec_flag.get_value(cs).unwrap_or(false) {
                println!("JUMP");
                if is_jal.get_value(cs).unwrap() {
                    dbg!(pc.get_value_unsigned(cs));
                } else {
                    dbg!(src1.get_value_unsigned(cs));
                }
                dbg!(imm.get_value_unsigned(cs));
                dbg!(dst.get_value_unsigned(cs));
                dbg!(pc_next.get_value_unsigned(cs));
            }

            let returned_value = [
                Constraint::<F>::from(pc_next.0[0].get_variable()),
                Constraint::<F>::from(pc_next.0[1].get_variable()),
            ];

            CommonDiffs {
                exec_flag,
                trapped: None,
                trap_reason: None,
                rd_value: vec![(returned_value, exec_flag)],
                new_pc_value: NextPcValue::Custom(dst),
            }
        } else {
            // NOTE why we only check 2nd bit and completely ignore lowest one:
            // - if it's JAL, then we add PC (0 mod 4) with immediate, that encodes 2-byte offset, so it's 0 mod 2 anyway
            // - if it's JALR then we should clean the lowest bit anyway, so we only need to check 2nd bit

            let [bit_1, dst_low] = opt_ctx.append_lookup_relation(
                cs,
                &[x.0[0].get_variable()],
                TableType::JumpCleanupOffset.to_num(),
                exec_flag,
            );
            let bit_1 = Boolean::Is(bit_1);
            let is_misaligned_addr = bit_1;

            let dst_low = Num::Var(dst_low);
            let dst_high = x.0[1];
            let dst = Register([dst_low, dst_high]);
            let trapped = is_misaligned_addr;
            let trap_reason = Num::Constant(F::from_u64_unchecked(
                TrapReason::InstructionAddressMisaligned as u64,
            ));

            if exec_flag.get_value(cs).unwrap_or(false) {
                println!("JUMP");
                if is_jal.get_value(cs).unwrap() {
                    dbg!(pc.get_value_unsigned(cs));
                } else {
                    dbg!(src1.get_value_unsigned(cs));
                }
                dbg!(imm.get_value_unsigned(cs));
                if trapped.get_value(cs).unwrap() {
                    dbg!(trap_reason.get_value(cs));
                } else {
                    dbg!(dst.get_value_unsigned(cs));
                }
            }

            let returned_value = [
                Constraint::<F>::from(pc_next.0[0].get_variable()),
                Constraint::<F>::from(pc_next.0[1].get_variable()),
            ];

            CommonDiffs {
                exec_flag,
                trapped: Some(trapped),
                trap_reason: Some(trap_reason),
                rd_value: vec![(returned_value, exec_flag)],
                new_pc_value: NextPcValue::Custom(dst),
            }
        }
    }
}
