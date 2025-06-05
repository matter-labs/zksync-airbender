use super::*;

pub const BINOP_COMMON_OP_KEY: DecoderMajorInstructionFamilyKey =
    DecoderMajorInstructionFamilyKey("BINOP_COMMON_KEY");
// NOTE: We do not need these as we are using funct3 instead

// pub const AND_OP_KEY: DecoderInstructionVariantsKey = DecoderInstructionVariantsKey("AND/ANDI");
// pub const OR_OP_KEY: DecoderInstructionVariantsKey = DecoderInstructionVariantsKey("OR/ORI");
// pub const XOR_OP_KEY: DecoderInstructionVariantsKey = DecoderInstructionVariantsKey("XOR/XORI");

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BinaryOp;

impl DecodableMachineOp for BinaryOp {
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
            (OPERATION_OP, 0b111, 0b000_0000) => {
                // AND
                (
                    InstructionType::RType,
                    BINOP_COMMON_OP_KEY,
                    &[][..],
                    // &[AND_OP_KEY][..],
                )
            }
            (OPERATION_OP_IMM, 0b111, _) => {
                // ANDI
                (
                    InstructionType::IType,
                    BINOP_COMMON_OP_KEY,
                    &[][..],
                    // &[AND_OP_KEY][..],
                )
            }
            (OPERATION_OP, 0b110, 0b000_0000) => {
                // OR
                (
                    InstructionType::RType,
                    BINOP_COMMON_OP_KEY,
                    &[][..],
                    // &[OR_OP_KEY][..],
                )
            }
            (OPERATION_OP_IMM, 0b110, _) => {
                // ORI
                (
                    InstructionType::IType,
                    BINOP_COMMON_OP_KEY,
                    &[][..],
                    // &[OR_OP_KEY][..],
                )
            }
            (OPERATION_OP, 0b100, 0b000_0000) => {
                // XOR
                (
                    InstructionType::RType,
                    BINOP_COMMON_OP_KEY,
                    &[][..],
                    // &[XOR_OP_KEY][..],
                )
            }
            (OPERATION_OP_IMM, 0b100, _) => {
                // XORI
                (
                    InstructionType::IType,
                    BINOP_COMMON_OP_KEY,
                    &[][..],
                    // &[XOR_OP_KEY][..],
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
    > MachineOp<F, ST, RS, DE, BS> for BinaryOp
{
    fn define_used_tables() -> Vec<TableType> {
        vec![TableType::Xor, TableType::Or, TableType::And]
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
        opt_ctx.reset_indexers();
        let exec_flag = boolean_set.get_major_flag(BINOP_COMMON_OP_KEY);

        // decoder will place immediate into SRC2 to account for ADD/ADDI and similar variations
        let src1 = inputs.get_rs1_or_equivalent();
        let src2 = inputs.get_rs2_or_equivalent();

        let funct3 = inputs.funct3();

        let src1_byte0 = Constraint::<F>::from(
            src1.get_register_with_decomposition_and_sign()
                .unwrap()
                .low_word_unconstrained_decomposition
                .0,
        );
        let src2_byte0 = Constraint::<F>::from(
            src2.get_register_with_decomposition_and_sign()
                .unwrap()
                .low_word_unconstrained_decomposition
                .0,
        );

        let src1_byte1 = src1
            .get_register_with_decomposition_and_sign()
            .unwrap()
            .low_word_unconstrained_decomposition
            .1
            .clone();
        let src2_byte1 = src2
            .get_register_with_decomposition_and_sign()
            .unwrap()
            .low_word_unconstrained_decomposition
            .1
            .clone();

        let src1_byte2 = src1
            .get_register_with_decomposition_and_sign()
            .unwrap()
            .high_word_decomposition
            .0
            .clone();
        let src2_byte2 = src2
            .get_register_with_decomposition_and_sign()
            .unwrap()
            .high_word_decomposition
            .0
            .clone();

        let src1_byte3 = Constraint::<F>::from(
            src1.get_register_with_decomposition_and_sign()
                .unwrap()
                .high_word_decomposition
                .1,
        );
        let src2_byte3 = Constraint::<F>::from(
            src2.get_register_with_decomposition_and_sign()
                .unwrap()
                .high_word_decomposition
                .1,
        );

        let src1_decomposition = [src1_byte0, src1_byte1, src1_byte2, src1_byte3];

        let src2_decomposition = [src2_byte0, src2_byte1, src2_byte2, src2_byte3];

        // NB: we don't need explicit range checks here: the correctness will be enforced by the call
        // to binary table - first and second tables are costrainted to be 8-bits long
        let mut res_chunks = vec![];
        let iter = itertools::multizip((src1_decomposition.iter(), src2_decomposition.iter()));

        for (left_in, right_in) in iter {
            let [out] = opt_ctx.append_lookup_relation_from_linear_terms::<2, 1>(
                cs,
                &[left_in.clone(), right_in.clone()],
                funct3,
                exec_flag,
            );
            res_chunks.push(out);
        }

        if exec_flag.get_value(cs).unwrap_or(false) {
            println!("BINOP");
            dbg!(src1.get_register().get_value_unsigned(cs));
            dbg!(src2.get_register().get_value_unsigned(cs));
            dbg!(cs.get_value(funct3.get_variable()));
            // dbg!(rd.get_value_unsigned(cs));
        }

        let returned_value = [
            Constraint::<F>::from(
                Term::from(res_chunks[0])
                    + Term::from((F::from_u64_unchecked(1 << 8), res_chunks[1])),
            ),
            Constraint::<F>::from(
                Term::from(res_chunks[2])
                    + Term::from((F::from_u64_unchecked(1 << 8), res_chunks[3])),
            ),
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
