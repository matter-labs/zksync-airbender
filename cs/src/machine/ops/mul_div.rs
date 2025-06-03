use crate::cs::witness_placer::{
    cs_debug_evaluator::witness_early_branch_if_possible, WitnessPlacer,
};

use super::*;

pub const MUL_COMMON_OP_KEY: DecoderMajorInstructionFamilyKey =
    DecoderMajorInstructionFamilyKey("MUL_COMMON_KEY");
pub const DIVREM_COMMON_OP_KEY: DecoderMajorInstructionFamilyKey =
    DecoderMajorInstructionFamilyKey("DIVREM_COMMON_KEY");
pub const MUL_OP_KEY: DecoderInstructionVariantsKey = DecoderInstructionVariantsKey("MUL");
// pub const MULHU_OP_KEY: DecoderInstructionVariantsKey = DecoderInstructionVariantsKey("MULHU");
pub const MULH_OP_KEY: DecoderInstructionVariantsKey = DecoderInstructionVariantsKey("MULH");
pub const MULHSU_OP_KEY: DecoderInstructionVariantsKey = DecoderInstructionVariantsKey("MULHSU");
pub const DIV_OP_KEY: DecoderInstructionVariantsKey = DecoderInstructionVariantsKey("DIV");
pub const DIVU_OP_KEY: DecoderInstructionVariantsKey = DecoderInstructionVariantsKey("DIVU");
pub const REM_OP_KEY: DecoderInstructionVariantsKey = DecoderInstructionVariantsKey("REM");
// pub const REMU_OP_KEY: DecoderInstructionVariantsKey = DecoderInstructionVariantsKey("REMU");

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MulOp<const SUPPORT_SIGNED: bool>;

impl<const SUPPORT_SIGNED: bool> DecodableMachineOp for MulOp<SUPPORT_SIGNED> {
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
            (OPERATION_OP, 0b000, M_EXT_FUNCT7) => {
                // MUL
                (InstructionType::RType, MUL_COMMON_OP_KEY, &[MUL_OP_KEY][..])
            }
            (OPERATION_OP, 0b001, M_EXT_FUNCT7) if SUPPORT_SIGNED => {
                // MULH
                (
                    InstructionType::RType,
                    MUL_COMMON_OP_KEY,
                    &[MULH_OP_KEY][..],
                )
            }
            (OPERATION_OP, 0b010, M_EXT_FUNCT7) if SUPPORT_SIGNED => {
                // MULHSU
                (
                    InstructionType::RType,
                    MUL_COMMON_OP_KEY,
                    &[MULHSU_OP_KEY][..],
                )
            }
            (OPERATION_OP, 0b011, M_EXT_FUNCT7) => {
                // MULHU
                // we only need MUL_OP_KEY to indicate that we take low value, and some other flags to indicated that
                // we use signed ops
                (InstructionType::RType, MUL_COMMON_OP_KEY, &[][..])
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
    > MachineOp<F, ST, RS, DE, BS> for MulOp<SUPPORT_SIGNED>
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
        let exec_flag = boolean_set.get_major_flag(MUL_COMMON_OP_KEY);

        let src1 = inputs.get_rs1_or_equivalent();
        let src2 = inputs.get_rs2_or_equivalent();

        if SUPPORT_SIGNED == false {
            let mul_flag = boolean_set.get_minor_flag(MUL_COMMON_OP_KEY, MUL_OP_KEY);

            let (mul_low, mul_high) = opt_ctx.append_mul_relation_unsigned(
                src1.get_register(),
                src2.get_register(),
                exec_flag,
                cs,
            );

            let use_low = mul_flag;
            let rd = Register::choose(cs, &use_low, &mul_low, &mul_high);

            if exec_flag.get_value(cs).unwrap_or(false) {
                println!("MUL");
                dbg!(src1.get_register().get_value_unsigned(cs));
                dbg!(src2.get_register().get_value_unsigned(cs));
                dbg!(rd.get_value_unsigned(cs));
            }

            let returned_value = [
                Constraint::<F>::from(rd.0[0].get_variable()),
                Constraint::<F>::from(rd.0[1].get_variable()),
            ];

            CommonDiffs {
                exec_flag,
                trapped: None,
                trap_reason: None,
                rd_value: vec![(returned_value, exec_flag)],
                new_pc_value: NextPcValue::Default,
            }
        } else {
            let mul_flag = boolean_set.get_minor_flag(MUL_COMMON_OP_KEY, MUL_OP_KEY);
            let mulh_flag = boolean_set.get_minor_flag(MUL_COMMON_OP_KEY, MULH_OP_KEY);
            let mulhsu_flag = boolean_set.get_minor_flag(MUL_COMMON_OP_KEY, MULHSU_OP_KEY);
            // high mul signed, or half mul signed by unsigned
            let op_1_is_signed = Boolean::or(&mulh_flag, &mulhsu_flag, cs);

            let op_2_is_signed = mulh_flag;

            let src1_sign = src1.get_sign_bit().unwrap();
            let src2_sign = src2.get_sign_bit().unwrap();

            let op_1_sign =
                Boolean::choose(cs, &op_1_is_signed, &src1_sign, &Boolean::Constant(false));
            let op_2_sign =
                Boolean::choose(cs, &op_2_is_signed, &src2_sign, &Boolean::Constant(false));

            let (mul_low, mul_high) = opt_ctx.append_mul_relation_raw(
                src1.get_register(),
                Num::from_boolean_is(op_1_sign),
                src2.get_register(),
                Num::from_boolean_is(op_2_sign),
                exec_flag,
                cs,
            );

            let use_low = mul_flag;
            let rd = Register::choose(cs, &use_low, &mul_low, &mul_high);

            if exec_flag.get_value(cs).unwrap_or(false) {
                if mul_flag.get_value(cs).unwrap_or(false) {
                    println!("MUL");
                } else if mulh_flag.get_value(cs).unwrap_or(false) {
                    println!("MULH");
                } else if mulhsu_flag.get_value(cs).unwrap_or(false) {
                    println!("MUL");
                } else {
                    println!("MULHU");
                }

                dbg!(src1.get_register().get_value_unsigned(cs));
                dbg!(src2.get_register().get_value_unsigned(cs));
                dbg!(mul_low.get_value_unsigned(cs));
                dbg!(mul_high.get_value_unsigned(cs));
                dbg!(rd.get_value_unsigned(cs));
            }

            let returned_value = [
                Constraint::<F>::from(rd.0[0].get_variable()),
                Constraint::<F>::from(rd.0[1].get_variable()),
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
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DivRemOp<const SUPPORT_SIGNED: bool>;

impl<const SUPPORT_SIGNED: bool> DecodableMachineOp for DivRemOp<SUPPORT_SIGNED> {
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
            (OPERATION_OP, 0b100, M_EXT_FUNCT7) if SUPPORT_SIGNED => {
                // DIV
                (
                    InstructionType::RType,
                    DIVREM_COMMON_OP_KEY,
                    &[DIV_OP_KEY][..],
                )
            }
            (OPERATION_OP, 0b101, M_EXT_FUNCT7) => {
                // DIVU
                (
                    InstructionType::RType,
                    DIVREM_COMMON_OP_KEY,
                    &[DIVU_OP_KEY][..],
                )
            }
            (OPERATION_OP, 0b110, M_EXT_FUNCT7) if SUPPORT_SIGNED => {
                // REM
                (
                    InstructionType::RType,
                    DIVREM_COMMON_OP_KEY,
                    &[REM_OP_KEY][..],
                )
            }
            (OPERATION_OP, 0b111, M_EXT_FUNCT7) => {
                // REMU
                // same as for MUL, we are fine to only use DIVU_OP_KEY
                (InstructionType::RType, DIVREM_COMMON_OP_KEY, &[][..])
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
    > MachineOp<F, ST, RS, DE, BS> for DivRemOp<SUPPORT_SIGNED>
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
        let exec_flag = boolean_set.get_major_flag(DIVREM_COMMON_OP_KEY);

        let src1 = inputs.get_rs1_or_equivalent();
        let src2 = inputs.get_rs2_or_equivalent();

        if SUPPORT_SIGNED == false {
            let divident = src1.get_register();
            let divisor = src2.get_register();

            let unsigned_div_flag = boolean_set.get_minor_flag(DIVREM_COMMON_OP_KEY, DIVU_OP_KEY);
            // resolve all the signs here instead of optimization context

            // Allocate range-checked variables
            let quotient = opt_ctx.get_register_output(cs);
            let remainder = opt_ctx.get_register_output(cs);

            // quite painful witness resolution, but there is no other option. We know an opcode to execute,
            // and we know if it's signed or unsigned

            let divident_vars = [divident.0[0].get_variable(), divident.0[1].get_variable()];

            let divisor_vars = [divisor.0[0].get_variable(), divisor.0[1].get_variable()];

            let quotient_vars = [quotient.0[0].get_variable(), quotient.0[1].get_variable()];

            let remainder_vars = [remainder.0[0].get_variable(), remainder.0[1].get_variable()];

            let exec_flag_var = exec_flag.get_variable().unwrap();

            let evaluation_fn_inner = move |placer: &mut CS::WitnessPlacer| {
                use crate::cs::witness_placer::*;

                let mask = placer.get_boolean(exec_flag_var);

                let divident_unsigned = placer.get_u32_from_u16_parts(divident_vars);
                let divisor_unsigned = placer.get_u32_from_u16_parts(divisor_vars);

                let divisor_is_non_zero = divisor_unsigned.is_zero().negate();

                // default value is as-is it was divisor == 0

                let quotient = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(u32::MAX);
                let remainder = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0);

                let masked_divisor = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                    &divisor_is_non_zero,
                    &divisor_unsigned,
                    &quotient,
                );
                let (maybe_quotient, maybe_remainder) =
                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::div_rem_assume_nonzero_divisor(
                        &divident_unsigned,
                        &masked_divisor,
                    );
                let quotient = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                    &divisor_is_non_zero,
                    &maybe_quotient,
                    &quotient,
                );
                let remainder = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                    &divisor_is_non_zero,
                    &maybe_remainder,
                    &remainder,
                );

                placer.conditionally_assign_u32(quotient_vars, &mask, &quotient);
                placer.conditionally_assign_u32(remainder_vars, &mask, &remainder);
            };

            let value_fn = move |placer: &mut CS::WitnessPlacer| {
                let mask = placer.get_boolean(exec_flag_var);
                witness_early_branch_if_possible(mask, placer, &evaluation_fn_inner);
            };

            cs.set_values(value_fn);

            use crate::devices::optimization_context::MulDivRelation;

            // manually append multiplication(!) relation
            let relation = MulDivRelation {
                exec_flag,
                op_1: divisor,
                op_1_sign: Num::Constant(F::ZERO),
                op_2: quotient,
                op_2_sign: Num::Constant(F::ZERO),
                additive_term: remainder,
                additive_term_sign: Num::Constant(F::ZERO),
                mul_low: divident,
                mul_high: Register([Num::Constant(F::ZERO); 2]),
            };
            opt_ctx.append_mul_relation_inner(relation);

            // now we must enforce sign of the remainder. Actually for all cases it's a sign of the divident,
            // and we already taken care of unsigned cases above

            // // check that modulus of remainder is less than modulus of divisor
            // // (only in case if divisor is not zero)
            let divisor_is_zero = opt_ctx.append_is_zero_relation(divisor, exec_flag, cs);

            // Logic below is fine for unsigned cases too

            let (_diff, bf) = opt_ctx.append_sub_relation(remainder, divisor, exec_flag, cs);

            // If divisor is not 0 then remainder < divisor if we execute
            // (1 - divisor_is_zero) * (1 - bf) * exec_flag = 0
            let t = Boolean::and(&divisor_is_zero.toggle(), &bf.toggle(), cs);
            cs.add_constraint(Term::from(t) * Term::from(exec_flag));

            // DIV-BY-0 MASK
            // when dividing by 0, our MulDivRelation leaves quotient undefined
            // so we need to explicitly define it
            // but we don't need an explicit mask for div-by-0 case
            // we can just enforce with constant constraints
            // (saves 2 variables)
            {
                let should_enforce = Boolean::and(&divisor_is_zero, &exec_flag, cs);
                let (quotient_low, quotient_high) = (quotient.0[0], quotient.0[1]);
                let (constant_low, constant_high) = (0xffff, 0xffff); // -1 is quotient value when div-by-0
                cs.add_constraint(
                    Constraint::from(should_enforce)
                        * (Term::from(quotient_low) - Term::from(constant_low)),
                );
                cs.add_constraint(
                    Constraint::from(should_enforce)
                        * (Term::from(quotient_high) - Term::from(constant_high)),
                );
            }

            let output_quotient = unsigned_div_flag;
            let rd = Register::choose(cs, &output_quotient, &quotient, &remainder);

            if exec_flag.get_value(cs).unwrap_or(false) {
                println!("DIV/REM");
                dbg!(src1.get_register().get_value_unsigned(cs));
                dbg!(src2.get_register().get_value_unsigned(cs));
                dbg!(rd.get_value_unsigned(cs));
            }

            let returned_value = [
                Constraint::<F>::from(rd.0[0].get_variable()),
                Constraint::<F>::from(rd.0[1].get_variable()),
            ];

            CommonDiffs {
                exec_flag,
                trapped: None,
                trap_reason: None,
                rd_value: vec![(returned_value, exec_flag)],
                new_pc_value: NextPcValue::Default,
            }
        } else {
            let divident = src1.get_register_with_decomposition_and_sign().unwrap();
            let divisor = src2.get_register_with_decomposition_and_sign().unwrap();

            let signed_div_flag = boolean_set.get_minor_flag(DIVREM_COMMON_OP_KEY, DIV_OP_KEY);
            let signed_rem_flag = boolean_set.get_minor_flag(DIVREM_COMMON_OP_KEY, REM_OP_KEY);

            let unsigned_div_flag = boolean_set.get_minor_flag(DIVREM_COMMON_OP_KEY, DIVU_OP_KEY);

            let is_signed_division = Boolean::or(&signed_div_flag, &signed_rem_flag, cs);

            let divisor = divisor.into_register_with_sign();

            // Allocate range-checked variables
            let quotient = opt_ctx.get_register_output(cs);
            let remainder = opt_ctx.get_register_output(cs);

            // decide on signs of divisor and divident. If it's signed then it's a sign, otherwise it'k always false
            let divisor_sign = Boolean::and(&is_signed_division, &divisor.sign_bit, cs);
            let divident_sign = Boolean::and(&is_signed_division, &divident.sign_bit, cs);

            // quite painful witness resolution, but there is no other option. We know an opcode to execute,
            // and we know if it's signed or unsigned

            let divident_vars = [
                divident.u16_limbs[0].get_variable(),
                divident.u16_limbs[1].get_variable(),
            ];

            let divisor_vars = [
                divisor.u16_limbs[0].get_variable(),
                divisor.u16_limbs[1].get_variable(),
            ];

            let quotient_vars = [quotient.0[0].get_variable(), quotient.0[1].get_variable()];
            let remainder_vars = [remainder.0[0].get_variable(), remainder.0[1].get_variable()];

            let exec_flag_var = exec_flag.get_variable().unwrap();
            let is_signed_division_var = is_signed_division.get_variable().unwrap();

            let evaluation_fn_inner = move |placer: &mut CS::WitnessPlacer| {
                use crate::cs::witness_placer::*;

                let mask = placer.get_boolean(exec_flag_var);

                let divident_unsigned = placer.get_u32_from_u16_parts(divident_vars);
                let divisor_unsigned = placer.get_u32_from_u16_parts(divisor_vars);

                let is_signed_division = placer.get_boolean(is_signed_division_var);
                // signed and unsigned representations are the same
                let divisor_is_non_zero = divisor_unsigned.is_zero().negate();

                // default value is as-is it was divisor == 0

                let quotient_if_unsigned_by_zero =
                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(u32::MAX);
                let remainder_if_unsigned_by_zero = divident_unsigned.clone();

                let one_u32 = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(1);

                // unsigned division by non-zero
                let masked_unsigned_divisor = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                    &divisor_is_non_zero,
                    &divisor_unsigned,
                    &one_u32, // this will never produce overflows even in signed case
                );
                let (maybe_unsigned_quotient, maybe_unsigned_remainder) =
                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::div_rem_assume_nonzero_divisor(
                        &divident_unsigned,
                        &masked_unsigned_divisor,
                    );
                let unsigned_quotient = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                    &divisor_is_non_zero,
                    &maybe_unsigned_quotient,
                    &quotient_if_unsigned_by_zero,
                );
                let unsigned_remainder = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                    &divisor_is_non_zero,
                    &maybe_unsigned_remainder,
                    &remainder_if_unsigned_by_zero,
                );

                // now signed case

                let quotient_if_signed_by_zero =
                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(u32::MAX);
                let remainder_if_signed_by_zero = divident_unsigned.clone();

                let quotient_if_signed_overflow =
                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(i32::MIN as u32);
                let remainder_if_signed_overflow =
                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0);

                let t0 = divident_unsigned.equal_to_constant(i32::MIN as u32);
                let t1 = divisor_unsigned.equal_to_constant(-1i32 as u32);
                let overflowing_division = t0.and(&t1);

                // if we have the case of overflowing division we can again divide by 1 instead
                let masked_signed_divisor_repr =
                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                        &overflowing_division,
                        &one_u32,
                        &masked_unsigned_divisor,
                    );

                // now it's safe to divide and select results later on

                let signed_divident =
                    <CS::WitnessPlacer as WitnessTypeSet<F>>::I32::from_unsigned(divident_unsigned);
                let masked_signed_divisor =
                    <CS::WitnessPlacer as WitnessTypeSet<F>>::I32::from_unsigned(
                        masked_signed_divisor_repr,
                    );
                let (maybe_signed_quotient, maybe_signed_remainder) = <CS::WitnessPlacer as WitnessTypeSet<F>>::I32::div_rem_assume_nonzero_divisor_no_overflow(&signed_divident, &masked_signed_divisor);

                let maybe_signed_quotient = maybe_signed_quotient.as_unsigned();
                let maybe_signed_remainder = maybe_signed_remainder.as_unsigned();

                // first select over signed case
                let signed_quotient = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                    &overflowing_division,
                    &quotient_if_signed_overflow,
                    &maybe_signed_quotient,
                );
                let signed_remainder = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                    &overflowing_division,
                    &remainder_if_signed_overflow,
                    &maybe_signed_remainder,
                );
                let signed_quotient = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                    &divisor_is_non_zero,
                    &signed_quotient,
                    &quotient_if_signed_by_zero,
                );
                let signed_remainder = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                    &divisor_is_non_zero,
                    &signed_remainder,
                    &remainder_if_signed_by_zero,
                );

                // now select over signed vs unsigned
                let quotient = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                    &is_signed_division,
                    &signed_quotient,
                    &unsigned_quotient,
                );
                let remainder = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                    &is_signed_division,
                    &signed_remainder,
                    &unsigned_remainder,
                );

                placer.conditionally_assign_u32(quotient_vars, &mask, &quotient);
                placer.conditionally_assign_u32(remainder_vars, &mask, &remainder);
            };

            let value_fn = move |placer: &mut CS::WitnessPlacer| {
                let mask = placer.get_boolean(exec_flag_var);
                witness_early_branch_if_possible(mask, placer, &evaluation_fn_inner);
            };

            cs.set_values(value_fn);

            // NB: this sign computation is formally proven correct via a z3 formal verifier
            //     script in ./z3/div_optim_signextension.z3
            //     to check it just install z3 and run `z3 div_optim_signextension.z3`
            //     and check that it outputs the word `unsat`to show that the reduction is correct
            let (quotient_sign, remainder_sign) = {
                // the quotient sign is always dependent on combination of dividend/divisor signs
                // unless quotient is zero of course
                // quotient_sign == (dividend_sign ^ divisor_sign)  * (1 - quotient_is_zero)
                let quotient_sign = {
                    let xor = Boolean::xor(&divident_sign, &divisor_sign, cs);
                    let qnz = opt_ctx
                        .append_is_zero_relation(quotient, exec_flag, cs)
                        .toggle();
                    Boolean::and(&xor, &qnz, cs)
                };

                // the remainder sign is always the same as the dividend's sign
                // unless remainder is zero of course
                // remainder_sign == dividend_sign * (1 - remainder_is_zero)
                let remainder_sign = {
                    let rnz = opt_ctx
                        .append_is_zero_relation(remainder, exec_flag, cs)
                        .toggle();
                    Boolean::and(&divident_sign, &rnz, cs)
                };

                (quotient_sign, remainder_sign)
            };

            let divident_sign_extension =
                Num::Var(cs.add_variable_from_constraint_allow_explicit_linear(
                    Term::from(divident_sign) * Term::from(0xffff),
                ));

            use crate::devices::optimization_context::MulDivRelation;

            // manually append multiplication(!) relation
            let relation = MulDivRelation {
                exec_flag,
                op_1: divisor.into_register(),
                op_1_sign: Num::from_boolean_is(divisor_sign),
                op_2: quotient,
                op_2_sign: Num::Var(quotient_sign.get_variable().unwrap()),
                additive_term: remainder,
                additive_term_sign: Num::Var(remainder_sign.get_variable().unwrap()),
                mul_low: divident.into_register(),
                mul_high: Register([divident_sign_extension, divident_sign_extension]),
            };
            opt_ctx.append_mul_relation_inner(relation);

            // INVARIANT:     |REM|<|DIVISOR| if DIVISOR != 0
            // check that modulus of remainder is less than modulus of divisor
            // we simply mask one add_sub relation based on which case we're in
            // this only applies if the divisor is not zero!!! otherwise of course remainder will be larger
            //
            //     remainder_sign divisor_sign
            //     0              0            -->  r <  d --> (r-d) < 0    --> condition: underflow
            //     1              1            --> -r < -d --> (r-d) > 0    --> !condition * !eq0
            //     0              1            -->  r < -d --> (r+d) < 2^32 --> condition: !overflow
            //     1              0            --> -r <  d --> (r+d) > 2^32 --> !condition * !eq0
            //
            // so just first determine condition, then determine if it's an inverse scenario
            // condition: !xor * of + xor * !of (which is just a xor)
            let divisor_is_zero =
                opt_ctx.append_is_zero_relation(divisor.into_register(), exec_flag, cs);
            let is_division_and_divisor_zero = Boolean::and(&divisor_is_zero, &exec_flag, cs);
            let is_modular_inequality = {
                let xor = Boolean::xor(&remainder_sign, &divisor_sign, cs);
                // different sign: ADD
                let indexers = opt_ctx.save_indexers();
                let exec_add = Boolean::and(&exec_flag, &xor, cs);
                let (out, of) =
                    opt_ctx.append_add_relation(remainder, divisor.into_register(), exec_add, cs);
                // same sign: SUB
                opt_ctx.restore_indexers(indexers);
                let exec_sub = Boolean::and(&exec_flag, &xor.toggle(), cs);
                let (out_, of_) =
                    opt_ctx.append_sub_relation(remainder, divisor.into_register(), exec_sub, cs);
                assert!(out == out_ && of == of_);
                let condition = Boolean::xor(&xor, &of, cs);
                let eq0 = cs.is_zero_reg(out);
                let condition_variant = Boolean::and(&condition.toggle(), &eq0.toggle(), cs);
                Boolean::choose(cs, &remainder_sign, &condition_variant, &condition)
            };
            let is_division_and_divisor_not_zero = {
                // EXEC * (DIVISOR!=0) == EXEC * (1 - DIVISOR==0) = EXEC - EXEC * (DIVISOR==0)
                Constraint::from(exec_flag) - Term::from(is_division_and_divisor_zero)
            };
            cs.add_constraint(
                is_division_and_divisor_not_zero
                    * (Term::from(1) - Term::from(is_modular_inequality)),
            );

            // DIV-BY-0 MASK
            // when dividing by 0, our MulDivRelation leaves quotient undefined
            // so we need to explicitly define it
            // but we don't need an explicit mask for div-by-0 case
            // we can just enforce with constant constraints
            // (saves 2 variables)
            {
                let should_enforce = is_division_and_divisor_zero;
                let (quotient_low, quotient_high) = (quotient.0[0], quotient.0[1]);
                let (constant_low, constant_high) = (0xffff, 0xffff); // -1 is quotient value when div-by-0
                cs.add_constraint(
                    Constraint::from(should_enforce)
                        * (Term::from(quotient_low) - Term::from(constant_low)),
                );
                cs.add_constraint(
                    Constraint::from(should_enforce)
                        * (Term::from(quotient_high) - Term::from(constant_high)),
                );
            }

            let output_quotient = Boolean::or(&signed_div_flag, &unsigned_div_flag, cs);
            let rd = Register::choose(cs, &output_quotient, &quotient, &remainder);

            if exec_flag.get_value(cs).unwrap_or(false) {
                println!("DIV/REM");
                dbg!(src1.get_register().get_value_unsigned(cs));
                dbg!(src2.get_register().get_value_unsigned(cs));
                dbg!(rd.get_value_unsigned(cs));
            }

            let returned_value = [
                Constraint::<F>::from(rd.0[0].get_variable()),
                Constraint::<F>::from(rd.0[1].get_variable()),
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
}
