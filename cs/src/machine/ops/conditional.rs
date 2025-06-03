use super::*;

pub const CONDITIONAL_COMMON_OP_KEY: DecoderMajorInstructionFamilyKey =
    DecoderMajorInstructionFamilyKey("CONDITIONAL_COMMON_KEY");

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ConditionalOp<const SUPPORT_SIGNED: bool>;

impl<const SUPPORT_SIGNED: bool> DecodableMachineOp for ConditionalOp<SUPPORT_SIGNED> {
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
            (OPERATION_OP_IMM, 0b010, _) if SUPPORT_SIGNED => {
                // SLTI
                (InstructionType::IType, CONDITIONAL_COMMON_OP_KEY, &[][..])
            }
            (OPERATION_OP_IMM, 0b011, _) => {
                // SLTIU
                (InstructionType::IType, CONDITIONAL_COMMON_OP_KEY, &[][..])
            }
            (OPERATION_OP, 0b010, 0) if SUPPORT_SIGNED => {
                // SLT
                (InstructionType::RType, CONDITIONAL_COMMON_OP_KEY, &[][..])
            }
            (OPERATION_OP, 0b011, 0) => {
                // SLTU
                (InstructionType::RType, CONDITIONAL_COMMON_OP_KEY, &[][..])
            }
            (OPERATION_BRANCH, 0b000, _) => {
                // BEQ
                (InstructionType::BType, CONDITIONAL_COMMON_OP_KEY, &[][..])
            }
            (OPERATION_BRANCH, 0b001, _) => {
                // BNE
                (InstructionType::BType, CONDITIONAL_COMMON_OP_KEY, &[][..])
            }
            (OPERATION_BRANCH, 0b100, _) if SUPPORT_SIGNED => {
                // BLT
                (InstructionType::BType, CONDITIONAL_COMMON_OP_KEY, &[][..])
            }
            (OPERATION_BRANCH, 0b101, _) if SUPPORT_SIGNED => {
                // BGE
                (InstructionType::BType, CONDITIONAL_COMMON_OP_KEY, &[][..])
            }
            (OPERATION_BRANCH, 0b110, _) => {
                // BLTU
                (InstructionType::BType, CONDITIONAL_COMMON_OP_KEY, &[][..])
            }
            (OPERATION_BRANCH, 0b111, _) => {
                // BGEU
                (InstructionType::BType, CONDITIONAL_COMMON_OP_KEY, &[][..])
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
        const SUPPORT_SIGNED: bool,
    > MachineOp<F, ST, RS, DE, BS> for ConditionalOp<SUPPORT_SIGNED>
{
    fn define_used_tables() -> Vec<TableType> {
        if SUPPORT_SIGNED {
            vec![
                TableType::JumpCleanupOffset,
                TableType::ConditionalOpAllConditionsResolver,
            ]
        } else {
            vec![
                TableType::JumpCleanupOffset,
                TableType::ConditionalOpUnsignedConditionsResolver,
            ]
        }
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
        // We only need a single flag here, because jump condition can be resolved separately via lookup table
        let exec_flag = boolean_set.get_major_flag(CONDITIONAL_COMMON_OP_KEY);

        // all of the instructions need to resolve a condition first, so we can compute it once
        let src1 = inputs.get_rs1_or_equivalent();
        let src2 = inputs.get_rs2_or_equivalent();

        // this is comparison of representations
        let (diff, uf_flag) =
            opt_ctx.append_sub_relation(src1.get_register(), src2.get_register(), exec_flag, cs);

        // and EQ flag
        let eq_flag = opt_ctx.append_is_zero_relation(diff, exec_flag, cs);

        // BLTU is just unsigned LT flag
        let bltu_flag = uf_flag;

        let pc = *machine_state.get_pc();
        let jump_offset = inputs.get_imm();
        // we add PC (0 mod 4) with immediate, that encodes 2-byte offset, so it's 0 mod 2 for all the purposes below
        let (jmp_addr, _of_flag) = opt_ctx.append_add_relation(pc, jump_offset, exec_flag, cs);
        let true_jmp_address = jmp_addr;

        // now we can assemble a condition, and then resolve a combination of
        // funct3 || lt flag || eq flag -> (should jump, should store)

        let pc_next = inputs.get_pc_next();
        let funct3 = inputs.funct3();

        let key_constraint = if SUPPORT_SIGNED == false {
            Term::from(funct3.get_variable())
                + Term::from((
                    F::from_u64_unchecked(1u64 << 3),
                    bltu_flag.get_variable().unwrap(),
                ))
                + Term::from((
                    F::from_u64_unchecked(1u64 << (3 + 1)),
                    eq_flag.get_variable().unwrap(),
                ))
        } else {
            // now more complex for signed cases
            let src1_sign_bit = src1.get_sign_bit().unwrap();
            let src2_sign_bit = src2.get_sign_bit().unwrap();

            // signed_comp_flag: (1-src_2_sign) * (sr1_1_sign ^ of) + src_1_sign * of

            // This deserves the comment here
            // - if LT is signed then:
            // - if signs are the same and are 0, then we should use uf_flag (example: 0b0..001 - 0b0..010 < 0)
            // - if signs are the same and are 1, then we should use uf_flag (example: 0b100... (i32::MIN) - 0b111... (-1) < 0)
            // - if signs are different then src1 > src2 if sign of src1 is 0, and src1 < src2 if sign of src1 is 1
            // so we use XOR to get "different signs", and form BLT(signed less-than):
            // if "same sign" then underflow from unsigned comparison, otherwise src1 sign

            // all that is implemented via single lookup relation

            Term::from(funct3.get_variable())
                + Term::from((
                    F::from_u64_unchecked(1u64 << 3),
                    bltu_flag.get_variable().unwrap(),
                ))
                + Term::from((
                    F::from_u64_unchecked(1u64 << (3 + 1)),
                    eq_flag.get_variable().unwrap(),
                ))
                + Term::from((
                    F::from_u64_unchecked(1u64 << (3 + 1 + 1)),
                    src1_sign_bit.get_variable().unwrap(),
                ))
                + Term::from((
                    F::from_u64_unchecked(1u64 << (3 + 1 + 1 + 1)),
                    src2_sign_bit.get_variable().unwrap(),
                ))
        };

        // NOTE: below lookups are conditional, so we do NOT use Booleans

        if ASSUME_TRUSTED_CODE == false {
            todo!();
        } else {
            // jump destination is always 0 mod 2 as explained above
            let [bit_1, _] = opt_ctx.append_lookup_relation(
                cs,
                &[jmp_addr.0[0].get_variable()],
                TableType::JumpCleanupOffset.to_num(),
                exec_flag,
            );
            let is_misaligned_addr = bit_1;

            let table_id = if SUPPORT_SIGNED {
                TableType::ConditionalOpAllConditionsResolver
            } else {
                TableType::ConditionalOpUnsignedConditionsResolver
            };

            let [should_jump, comparison_value] = opt_ctx
                .append_lookup_relation_from_linear_terms::<1, 2>(
                    cs,
                    &[key_constraint],
                    table_id.to_num(),
                    exec_flag,
                );

            let exec_jump = should_jump;
            let trapped = cs.add_variable_from_constraint(
                Term::from(should_jump) * Term::from(is_misaligned_addr),
            );

            // if we do jump, then it must be unprovable
            cs.add_constraint(Term::from(trapped) * exec_flag.get_terms());

            let new_pc_low = cs.add_variable_from_constraint(
                Term::from(exec_jump) * Term::from(true_jmp_address.0[0].get_variable())
                    + (Term::from(1) - Term::from(exec_jump))
                        * Term::from(pc_next.0[0].get_variable()),
            );
            let new_pc_high = cs.add_variable_from_constraint(
                Term::from(exec_jump) * Term::from(true_jmp_address.0[1].get_variable())
                    + (Term::from(1) - Term::from(exec_jump))
                        * Term::from(pc_next.0[1].get_variable()),
            );

            let pc = Register([Num::Var(new_pc_low), Num::Var(new_pc_high)]);

            let returned_value = [
                Constraint::<F>::from(comparison_value),
                Constraint::<F>::empty(),
            ];

            if exec_flag.get_value(cs).unwrap_or(false) {
                println!("CONDITIONAL");
                dbg!(src1.get_register().get_value_unsigned(cs));
                dbg!(src2.get_register().get_value_unsigned(cs));
                dbg!(pc.get_value_unsigned(cs));
                dbg!(jump_offset.get_value_unsigned(cs));
                dbg!(pc_next.get_value_unsigned(cs));
                dbg!(cs.get_value(should_jump));
                dbg!(cs.get_value(comparison_value));
                dbg!(true_jmp_address.get_value_unsigned(cs));
            }

            CommonDiffs {
                exec_flag: exec_flag,
                trapped: None,
                trap_reason: None,
                rd_value: vec![(returned_value, exec_flag)],
                new_pc_value: NextPcValue::Custom(pc),
            }
        }
    }
}
