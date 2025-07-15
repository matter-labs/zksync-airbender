use super::*;

pub fn mul_div_tables() -> Vec<TableType> {
    // no tables
    vec![
        TableType::RangeCheckSmall, // for 8-bit decompositions
    ]
}

pub fn mul_div_table_addition_fn<F: PrimeField, CS: Circuit<F>>(cs: &mut CS) {
    for el in mul_div_tables() {
        cs.materialize_table(el);
    }
}

pub fn mul_div_table_driver_fn<F: PrimeField>(table_driver: &mut TableDriver<F>) {
    for el in mul_div_tables() {
        table_driver.materialize_table(el);
    }
}

fn apply_mul_div<F: PrimeField, CS: Circuit<F>, const SUPPORT_SIGNED: bool>(
    cs: &mut CS,
    inputs: OpcodeFamilyCircuitState<F>,
) {
    // GET EXEC FLAGS
    // NB: we set division to 1 s.t. default padding-mask goes to 0 and our division-exclusive traps pass quietly
    let decoder =
        <DivMulDecoder<SUPPORT_SIGNED> as OpcodeFamilyDecoder>::BitmaskCircuitParser::parse(
            cs,
            inputs.decoder_data.circuit_family_extra_mask,
        );
    let is_division = decoder.perform_division_group();
    let is_multiplication = is_division.toggle();

    // GET OPERANDS
    let is_rd_x0 = Boolean::Is(inputs.decoder_data.rd_is_zero);
    let (rs1_reg, rs1_mem_query) =
        get_rs1_as_shuffle_ram(cs, Num::Var(inputs.decoder_data.rs1_index), true);
    cs.add_shuffle_ram_query(rs1_mem_query);
    let (rs2_reg, rs2_mem_query) =
        get_rs2_as_shuffle_ram(cs, Num::Var(inputs.decoder_data.rs2_index), true);
    cs.add_shuffle_ram_query(rs2_mem_query);

    // 1) first we allocate the right MulDiv operation
    //    TODO: test that the PADDING / default case (circuit_family_extra_mask == 0) always works
    //    TODO: possibly we could build a big table to take care of all the weird bit cases across the entire circuit
    let rs1_sign = if SUPPORT_SIGNED {
        let is_rs1_signed = decoder.perform_rs1_signed();
        let rs1_reg_high = rs1_reg.0[1];
        get_sign_bit_masked(cs, rs1_reg_high.get_variable(), is_rs1_signed)
    } else {
        Boolean::Constant(false)
    };
    let rs2_sign = if SUPPORT_SIGNED {
        let is_rs2_signed = decoder.perform_rs2_signed();
        let rs2_reg_high = rs2_reg.0[1];
        get_sign_bit_masked(cs, rs2_reg_high.get_variable(), is_rs2_signed)
    } else {
        Boolean::Constant(false)
    };
    let [[product_low, product_high], [quotient, remainder]] = {
        let new1 = Register::new(cs);
        let new2 = Register::new(cs);

        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            use crate::cs::witness_placer::*;
            let rs1_value = placer.get_u32_from_u16_parts(rs1_reg.0.map(|x| x.get_variable()));
            let rs2_value = placer.get_u32_from_u16_parts(rs2_reg.0.map(|x| x.get_variable()));
            let rs1_signed_value =
                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::I32::from_unsigned(
                    rs1_value.clone(),
                );
            let is_rs2_zero_value = rs2_value.is_zero();
            let quasi_divisor =
                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0x7fff_fff); // no overflows/underflows, and it's not 0
            let rs2_masked_non_zero_value = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<
                F,
            >>::U32::select(
                &is_rs2_zero_value, &quasi_divisor, &rs2_value
            );
            let rs2_signed_value =
                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::I32::from_unsigned(
                    rs2_value.clone(),
                );
            let rs2_masked_non_zero_signed_value =
                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::I32::from_unsigned(
                    rs2_masked_non_zero_value.clone(),
                );
            let is_rs1_signed_value = if SUPPORT_SIGNED {
                let is_rs1_signed_var = decoder.perform_rs1_signed().get_variable().unwrap();
                placer.get_boolean(is_rs1_signed_var)
            } else {
                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false)
            };
            let is_rs2_signed_value = if SUPPORT_SIGNED {
                let is_rs2_signed_var = decoder.perform_rs2_signed().get_variable().unwrap();
                placer.get_boolean(is_rs2_signed_var)
            } else {
                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false)
            };
            let (product_low_value_masked, product_high_value_masked) = {
                let is_both_signed_value = is_rs1_signed_value.and(&is_rs2_signed_value);
                let is_one_signed_value = is_rs1_signed_value.or(&is_rs2_signed_value);
                let (both_product_low_value, both_product_high_value) =
                    rs1_signed_value.widening_product_bits(&rs2_signed_value);
                let (one_product_low_value, one_product_high_value) =
                    rs1_signed_value.mixed_widening_product_bits(&rs2_value);
                let (none_product_low_value, none_product_high_value) =
                    rs1_value.split_widening_product(&rs2_value);
                let product_low_value_masked =
                    <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                        &is_both_signed_value,
                        &both_product_low_value,
                        &<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                            &is_one_signed_value,
                            &one_product_low_value,
                            &none_product_low_value,
                        ),
                    );
                let product_high_value_masked =
                    <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                        &is_both_signed_value,
                        &both_product_high_value,
                        &<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                            &is_one_signed_value,
                            &one_product_high_value,
                            &none_product_high_value,
                        ),
                    );
                (product_low_value_masked, product_high_value_masked)
            };
            let (quotient_value_masked, remainder_value_masked) = {
                let is_both_signed_value = is_rs1_signed_value.and(&is_rs2_signed_value);
                let (both_quotient_value, both_remainder_value) = {
                    let (quot, rem) = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::I32::div_rem_assume_nonzero_divisor_no_overflow(&rs1_signed_value, &rs2_masked_non_zero_signed_value);

                    (quot.as_unsigned(), rem.as_unsigned())
                };
                let (none_quotient_value, none_remainder_value) = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32::div_rem_assume_nonzero_divisor(&rs1_value, &rs2_masked_non_zero_value);
                let minus_one =
                    <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(
                        0xffff_ffff,
                    );
                let quotient_value_masked =
                    <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                        &is_rs2_zero_value,
                        &minus_one,
                        &<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                            &is_both_signed_value,
                            &both_quotient_value,
                            &none_quotient_value,
                        ),
                    );
                let remainder_value_masked =
                    <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                        &is_rs2_zero_value,
                        &rs1_value,
                        &<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                            &is_both_signed_value,
                            &both_remainder_value,
                            &none_remainder_value,
                        ),
                    );
                (quotient_value_masked, remainder_value_masked)
            };
            let is_multiplication_value = match is_multiplication {
                Boolean::Is(var) => placer.get_boolean(var),
                Boolean::Not(var) => placer.get_boolean(var).negate(),
                Boolean::Constant(c) => {
                    <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(c)
                }
            };
            let new1_value = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                &is_multiplication_value,
                &product_low_value_masked,
                &quotient_value_masked,
            );
            let new2_value = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                &is_multiplication_value,
                &product_high_value_masked,
                &remainder_value_masked,
            );
            placer.assign_u32_from_u16_parts(new1.0.map(|x| x.get_variable()), &new1_value);
            placer.assign_u32_from_u16_parts(new2.0.map(|x| x.get_variable()), &new2_value);
        };
        cs.set_values(value_fn);

        [[new1, new2]; 2]
    };
    let quotient_sign = if SUPPORT_SIGNED {
        // THIS WAS INDEPENDENTLY PROVEN CORRECT
        // will always depend on signs of dividend x divisor, unless the quotient is 0
        let xor = Boolean::xor(&rs1_sign, &rs2_sign, cs);
        let not_quotient_zero = cs.is_zero_reg(quotient).toggle();
        Boolean::and(&xor, &not_quotient_zero, cs)
    } else {
        Boolean::Constant(false)
    };
    let remainder_sign = if SUPPORT_SIGNED {
        // THIS WAS INDEPENDENTLY PROVEN CORRECT
        // will always be sign of dividend, unless the remainder is 0
        let not_remainder_zero = cs.is_zero_reg(remainder).toggle();
        Boolean::and(&rs1_sign, &not_remainder_zero, cs)
    } else {
        Boolean::Constant(false)
    };
    let rd_reg = {
        // MUL/DIV RELATION
        let op1 = Register::choose(cs, &is_multiplication, &rs1_reg, &quotient);
        let op1_sign = if SUPPORT_SIGNED {
            Num::Var(
                Boolean::choose(cs, &is_multiplication, &rs1_sign, &quotient_sign)
                    .get_variable()
                    .unwrap(),
            )
        } else {
            Num::Constant(F::ZERO)
        };
        let op2 = rs2_reg;
        let op2_sign = if SUPPORT_SIGNED {
            Num::Var(rs2_sign.get_variable().unwrap())
        } else {
            Num::Constant(F::ZERO)
        };
        let additive_term = Register::mask(&remainder, cs, is_division);
        let additive_term_sign = if SUPPORT_SIGNED {
            Num::Var(
                Boolean::and(&remainder_sign, &is_division, cs)
                    .get_variable()
                    .unwrap(),
            )
        } else {
            Num::Constant(F::ZERO)
        };
        let mul_low = Register::choose(cs, &is_multiplication, &product_low, &rs1_reg);
        let mul_high = {
            let rs1_reg_extension = {
                let ext = if SUPPORT_SIGNED {
                    Num::Var(cs.add_variable_from_constraint_allow_explicit_linear(
                        Constraint::from(rs1_sign) * Term::from(0xffff),
                    ))
                } else {
                    Num::Constant(F::ZERO)
                };
                Register([ext; 2])
            };
            Register::choose(cs, &is_multiplication, &product_high, &rs1_reg_extension)
        };
        OptimizationContext::enforce_mul_relation(
            cs,
            op1,
            op1_sign,
            op2,
            op2_sign,
            additive_term,
            additive_term_sign,
            mul_low,
            mul_high,
        );

        assert!(product_low == quotient && product_high == remainder);
        if SUPPORT_SIGNED {
            let is_mul_div_divu = decoder.perform_mul_div_divu();
            Register::choose(cs, &is_mul_div_divu, &product_low, &product_high)
        } else {
            let is_mul_divu = decoder.perform_mul_divu();
            Register::choose(cs, &is_mul_divu, &product_low, &product_high)
        }
    };

    // 2) then we take care of special division traps
    //    TODO: it's possible the second invariant would benefit from lookup table
    //          it's also possible it would simply benefit from smarter arithmetisation instead

    // INVARIANT 1:     QUOT==-1        if DIVISOR == 0
    let is_division_and_rs2_zero = {
        let is_rs2_zero = cs.is_zero_reg(rs2_reg);
        Constraint::from(Boolean::and(&is_division, &is_rs2_zero, cs))
    };
    let quotient_low = quotient.0[0];
    let quotient_high = quotient.0[1];
    cs.add_constraint(
        is_division_and_rs2_zero.clone() * (Term::from(quotient_low) - Term::from(0xffff)),
    );
    cs.add_constraint(
        is_division_and_rs2_zero.clone() * (Term::from(quotient_high) - Term::from(0xffff)),
    );
    // INVARIANT 2:     |REM|<|DIVISOR| if DIVISOR != 0
    let is_modular_inequality = if SUPPORT_SIGNED {
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
        let xor = Boolean::xor(&remainder_sign, &rs2_sign, cs);
        let (out, of) = choose_reg_add_sub_and_overflow(cs, xor, remainder, rs2_reg);
        let condition = Boolean::xor(&xor, &of, cs);
        let eq0 = cs.is_zero_reg(out);
        let condition_variant = Boolean::and(&condition.toggle(), &eq0.toggle(), cs);
        Boolean::choose(cs, &remainder_sign, &condition_variant, &condition)
    } else {
        let (_out, uf) = get_reg_sub_and_underflow(cs, remainder, rs2_reg);
        uf
    };
    let is_division_and_rs2_not_zero = {
        // DIVISION * (RS2!=0) == DIVISION * (1 - RS2==0) = DIVISION - DIVISION * (RS2==0)
        Constraint::from(is_division) - is_division_and_rs2_zero
    };
    cs.add_constraint(
        is_division_and_rs2_not_zero * (Term::from(1) - Term::from(is_modular_inequality)),
    );

    // write to RD
    let rd_mem_query = set_rd_with_mask_as_shuffle_ram(
        cs,
        Num::Var(inputs.decoder_data.rd_index),
        rd_reg,
        is_rd_x0,
        OPCODES_ARE_IN_ROM,
    );
    cs.add_shuffle_ram_query(rd_mem_query);

    // and we can increment PC without range checks
    // write to PC
    bump_pc_no_range_checks_explicit(
        cs,
        Register(inputs.cycle_start_state.pc.map(|x| Num::Var(x))),
        Register(inputs.cycle_end_state.pc.map(|x| Num::Var(x))),
    );
}

pub fn mul_div_circuit_with_preprocessed_bytecode<
    F: PrimeField,
    CS: Circuit<F>,
    const SUPPORT_SIGNED: bool,
>(
    cs: &mut CS,
) {
    let input = cs.allocate_execution_circuit_state::<true>();
    apply_mul_div::<_, _, SUPPORT_SIGNED>(cs, input);
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::utils::serialize_to_file;

    #[test]
    fn compile_mul_div_circuit() {
        use ::field::Mersenne31Field;

        let compiled = compile_unrolled_circuit_state_transition::<Mersenne31Field>(
            &|cs| mul_div_table_addition_fn(cs),
            &|cs| mul_div_circuit_with_preprocessed_bytecode::<_, _, true>(cs),
            1 << 20,
            24,
        );

        serialize_to_file(&compiled, "mul_div_preprocessed_layout.json");
    }

    #[test]
    fn compile_mul_div_witness_graph() {
        use ::field::Mersenne31Field;

        let ssa_forms = dump_ssa_witness_eval_form_for_unrolled_circuit::<Mersenne31Field>(
            &|cs| mul_div_table_addition_fn(cs),
            &|cs| mul_div_circuit_with_preprocessed_bytecode::<_, _, true>(cs),
        );
        serialize_to_file(&ssa_forms, "mul_div_preprocessed_ssa.json");
    }

    #[test]
    fn compile_mul_div_unsigned_circuit() {
        use ::field::Mersenne31Field;

        let compiled = compile_unrolled_circuit_state_transition::<Mersenne31Field>(
            &|cs| mul_div_table_addition_fn(cs),
            &|cs| mul_div_circuit_with_preprocessed_bytecode::<_, _, false>(cs),
            1 << 20,
            24,
        );

        serialize_to_file(&compiled, "mul_div_unsigned_preprocessed_layout.json");
    }

    #[test]
    fn compile_mul_div_unsigned_witness_graph() {
        use ::field::Mersenne31Field;

        let ssa_forms = dump_ssa_witness_eval_form_for_unrolled_circuit::<Mersenne31Field>(
            &|cs| mul_div_table_addition_fn(cs),
            &|cs| mul_div_circuit_with_preprocessed_bytecode::<_, _, false>(cs),
        );
        serialize_to_file(&ssa_forms, "mul_div_unsigned_preprocessed_ssa.json");
    }
}
