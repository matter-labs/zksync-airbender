use super::*;

pub const SHIFT_COMMON_OP_KEY: DecoderMajorInstructionFamilyKey =
    DecoderMajorInstructionFamilyKey("SHIFT_COMMON_KEY");
// by default - all shifts are left shifts
// pub const SHIFT_LEFT_KEY: DecoderInstructionVariantsKey = DecoderInstructionVariantsKey("SLL/SLLI/ROL");
pub const SHIFT_RIGHT_KEY: DecoderInstructionVariantsKey =
    DecoderInstructionVariantsKey("SRL/SRLI/ROR/RORI");
pub const SHIFT_CYCLIC_KEY: DecoderInstructionVariantsKey =
    DecoderInstructionVariantsKey("ROR/RORI/ROL");
pub const SHIFT_RIGHT_ALGEBRAIC_KEY: DecoderInstructionVariantsKey =
    DecoderInstructionVariantsKey("SRA");

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ShiftOp<const SUPPORT_SRA: bool, const SUPPORT_ROT: bool>;

impl<const SUPPORT_SRA: bool, const SUPPORT_ROT: bool> DecodableMachineOp
    for ShiftOp<SUPPORT_SRA, SUPPORT_ROT>
{
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
            (OPERATION_OP_IMM, 0b001, 0) => {
                // SLLI
                (InstructionType::IType, SHIFT_COMMON_OP_KEY, &[][..])
            }
            (OPERATION_OP_IMM, 0b101, 0) => {
                // SRLI
                (
                    InstructionType::IType,
                    SHIFT_COMMON_OP_KEY,
                    &[SHIFT_RIGHT_KEY][..],
                )
            }
            (OPERATION_OP_IMM, 0b101, 0b010_0000) if SUPPORT_SRA => {
                // SRAI
                (
                    InstructionType::IType,
                    SHIFT_COMMON_OP_KEY,
                    &[SHIFT_RIGHT_KEY, SHIFT_RIGHT_ALGEBRAIC_KEY][..],
                )
            }
            (OPERATION_OP_IMM, 0b101, 0b011_0000) if SUPPORT_ROT => {
                // RORI
                (
                    InstructionType::IType,
                    SHIFT_COMMON_OP_KEY,
                    &[SHIFT_RIGHT_KEY, SHIFT_CYCLIC_KEY][..],
                )
            }
            (OPERATION_OP, 0b001, 0) => {
                // SLL
                (InstructionType::RType, SHIFT_COMMON_OP_KEY, &[][..])
            }
            (OPERATION_OP, 0b101, 0) => {
                // SRL
                (
                    InstructionType::RType,
                    SHIFT_COMMON_OP_KEY,
                    &[SHIFT_RIGHT_KEY][..],
                )
            }
            (OPERATION_OP, 0b101, 0b010_0000) if SUPPORT_SRA => {
                // SRA
                (
                    InstructionType::RType,
                    SHIFT_COMMON_OP_KEY,
                    &[SHIFT_RIGHT_KEY, SHIFT_RIGHT_ALGEBRAIC_KEY][..],
                )
            }
            (OPERATION_OP, 0b001, 0b011_0000) if SUPPORT_ROT => {
                // ROL
                (
                    InstructionType::RType,
                    SHIFT_COMMON_OP_KEY,
                    &[SHIFT_CYCLIC_KEY][..],
                )
            }
            (OPERATION_OP, 0b101, 0b011_0000) if SUPPORT_ROT => {
                // ROR
                (
                    InstructionType::RType,
                    SHIFT_COMMON_OP_KEY,
                    &[SHIFT_RIGHT_KEY, SHIFT_CYCLIC_KEY][..],
                )
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
        const SUPPORT_SRA: bool,
        const SUPPORT_ROT: bool,
    > MachineOp<F, ST, RS, DE, BS> for ShiftOp<SUPPORT_SRA, SUPPORT_ROT>
{
    fn define_used_tables() -> Vec<TableType> {
        if SUPPORT_SRA {
            vec![TableType::ShiftImplementation, TableType::SRASignFiller]
        } else {
            vec![TableType::ShiftImplementation]
        }
    }

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
        // this is common for FAMILY of shift instructions
        opt_ctx.reset_indexers();
        let exec_flag = boolean_set.get_major_flag(SHIFT_COMMON_OP_KEY);
        let is_right_shift = boolean_set.get_minor_flag(SHIFT_COMMON_OP_KEY, SHIFT_RIGHT_KEY);

        let src1 = inputs.get_rs1_or_equivalent();
        let src2 = inputs.get_rs2_or_equivalent();

        // truncate shift amount to 5 bits

        let input = src1.get_register();
        let input_sign = src1
            .get_register_with_decomposition_and_sign()
            .unwrap()
            .sign_bit;
        // This will be constrained by lookup
        let shift_amount_low_byte = src2
            .get_register_with_decomposition_and_sign()
            .unwrap()
            .low_word_unconstrained_decomposition
            .0;

        // This will truncate the shift
        let [shift_amount_to_use] = opt_ctx.append_lookup_relation_from_linear_terms::<2, 1>(
            cs,
            &[
                Constraint::from(shift_amount_low_byte),
                Constraint::from(0b1_1111), // truncate to 5 bits
            ],
            TableType::And.to_num(),
            exec_flag,
        );

        // we will do a little of brute force and ask a table for contributions

        if exec_flag.get_value(cs).unwrap_or(false) {
            println!("SHIFT OPCODE");
            dbg!(src1.get_register().get_value_unsigned(cs));
            dbg!(src2.get_register().get_value_unsigned(cs));
            dbg!(cs.get_value(shift_amount_low_byte));
            dbg!(cs.get_value(shift_amount_to_use));
            if is_right_shift.get_value(cs).unwrap() {
                if SUPPORT_SRA {
                    if boolean_set
                        .get_minor_flag(SHIFT_COMMON_OP_KEY, SHIFT_RIGHT_ALGEBRAIC_KEY)
                        .get_value(cs)
                        .unwrap()
                    {
                        println!("SRA");
                    } else {
                        println!("SRL");
                    }
                } else {
                    println!("SRL");
                }
            } else {
                println!("SLL");
            }
        }

        use crate::tables::*;

        if SUPPORT_ROT == false {
            // these shifts are quite trivial - they do a shift
            let [low_in_place, shifted_from_low_place] = opt_ctx
                .append_lookup_relation_from_linear_terms::<1, 2>(
                    cs,
                    &[Constraint::from(input.0[0])
                        + (Term::from(1 << 16) * Term::from(shift_amount_to_use))
                        + (Term::from(1 << 21) * Term::from(is_right_shift))],
                    TableType::ShiftImplementation.to_num(),
                    exec_flag,
                );

            let [high_in_place, shifted_from_high_place] = opt_ctx
                .append_lookup_relation_from_linear_terms::<1, 2>(
                    cs,
                    &[Constraint::from(input.0[1])
                        + (Term::from(1 << 16) * Term::from(shift_amount_to_use))
                        + (Term::from(1 << 21) * Term::from(is_right_shift))],
                    TableType::ShiftImplementation.to_num(),
                    exec_flag,
                );

            // now we just need to assemble the result

            // We modeled everything as RIGHT logical shift (and adjusted the shift value for SLL),
            // so our contribtuions are (we only need to get ones from logical shifts, and can unconditionally add from SRA as it's 0 if shift is logical)
            let selected_low = cs.add_variable_from_constraint(
                Term::from(is_right_shift) * (Term::from(low_in_place) + Term::from(shifted_from_high_place)) + // SRL
                (Term::from(1) - Term::from(is_right_shift)) * Term::from(low_in_place), // SLL
            );

            let selected_high = cs.add_variable_from_constraint(
                Term::from(is_right_shift) * (Term::from(high_in_place)) + // SRL
                (Term::from(1) - Term::from(is_right_shift)) * (Term::from(high_in_place) + Term::from(shifted_from_low_place)), // SLL
            );

            let mut returned_value = [
                Constraint::from(selected_low),
                Constraint::from(selected_high),
            ];

            if SUPPORT_SRA {
                let is_sra =
                    boolean_set.get_minor_flag(SHIFT_COMMON_OP_KEY, SHIFT_RIGHT_ALGEBRAIC_KEY);
                let [sra_filler_low, sra_filler_high] = opt_ctx
                    .append_lookup_relation_from_linear_terms::<1, 2>(
                        cs,
                        &[Constraint::from(input_sign)
                            + (Term::from(1 << 1) * Term::from(is_sra))
                            + (Term::from(1 << 2) * Term::from(shift_amount_to_use))],
                        TableType::SRASignFiller.to_num(),
                        exec_flag,
                    );

                returned_value[0] = returned_value[0].clone() + Term::from(sra_filler_low);
                returned_value[1] = returned_value[1].clone() + Term::from(sra_filler_high);
            }

            // now merge all the contributions

            CommonDiffs {
                exec_flag,
                trapped: None,
                trap_reason: None,
                rd_value: vec![(returned_value, exec_flag)],
                new_pc_value: NextPcValue::Default,
            }
        } else {
            todo!();
        }
    }
}
