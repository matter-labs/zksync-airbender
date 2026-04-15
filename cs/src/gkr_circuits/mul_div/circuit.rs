use super::decoder::DivMulDecoder;
use super::*;
use crate::constraint::Constraint;
use crate::constraint::Term;
use crate::cs::circuit_trait::*;
use crate::gkr_circuits::utils::update_intermediate_carry_value;
use crate::oracle::Placeholder;
use crate::tables::TableDriver;
use crate::types::*;
use crate::witness_placer::*;
use field::PrimeField;

const TABLES_TOTAL_WIDTH: usize = 8;

// NOTE: this circuit should specify non-dummy CSR table in proving/setup. while compilation in tests
// takes case of properly computing offsets by using dummy table

pub fn mul_div_tables<const SUPPORT_SIGNED: bool>() -> Vec<TableType> {
    vec![
        TableType::ZeroEntry, // we need it, as we use conditional lookup enforcements
        TableType::RegIsZero,
        TableType::RangeCheck8x8,
    ]
}

pub fn mul_div_table_addition_fn<F: PrimeField, CS: Circuit<F>, const SUPPORT_SIGNED: bool>(
    cs: &mut CS,
) {
    for el in mul_div_tables::<SUPPORT_SIGNED>() {
        cs.materialize_table::<TABLES_TOTAL_WIDTH>(el);
    }
}

pub fn mul_div_table_driver_fn<F: PrimeField, const SUPPORT_SIGNED: bool>(
    table_driver: &mut TableDriver<F>,
) {
    for el in mul_div_tables::<SUPPORT_SIGNED>() {
        table_driver.materialize_table::<TABLES_TOTAL_WIDTH>(el);
    }
}

fn apply_mul_div_inner<F: PrimeField, CS: Circuit<F>, const SUPPORT_SIGNED: bool>(
    cs: &mut CS,
    inputs: OpcodeFamilyCircuitState<F>,
    decoder: <DivMulDecoder<SUPPORT_SIGNED> as OpcodeFamilyDecoder>::BitmaskCircuitParser,
) {
    // TODO: skip IMM from decoder completely

    if let Some(circuit_family_extra_mask) =
        cs.get_value(inputs.decoder_data.circuit_family_extra_mask)
    {
        println!(
            "circuit_family_extra_mask = 0b{:08b}",
            circuit_family_extra_mask.as_u32_reduced()
        );
    }

    // read inputs and prepare outputs
    let rs1_access = cs.request_mem_access(
        MemoryAccessRequest::RegisterRead {
            reg_idx: inputs.decoder_data.rs1_index,
            read_value_placeholder: Placeholder::ShuffleRamReadValue(0),
            split_as_u8: false,
        },
        "rs1",
        0,
    );

    let rs2_access = cs.request_mem_access(
        MemoryAccessRequest::RegisterRead {
            reg_idx: inputs.decoder_data.rs2_index,
            read_value_placeholder: Placeholder::ShuffleRamReadValue(1),
            split_as_u8: false,
        },
        "rs2",
        1,
    );

    let rd_access = cs.request_mem_access(
        MemoryAccessRequest::RegisterReadWrite {
            reg_idx: inputs.decoder_data.rd_index,
            read_value_placeholder: Placeholder::ShuffleRamReadValue(2),
            write_value_placeholder: Placeholder::ShuffleRamWriteValue(2),
            split_read_as_u8: false,
            split_write_as_u8: false,
        },
        "rd",
        2,
    );

    let MemoryAccess::RegisterOnly(rs1_access) = rs1_access else {
        unreachable!()
    };
    let MemoryAccess::RegisterOnly(rs2_access) = rs2_access else {
        unreachable!()
    };
    let MemoryAccess::RegisterOnly(rd_access) = rd_access else {
        unreachable!()
    };

    let WordRepresentation::U16Limbs(rs1_limbs) = rs1_access.read_value else {
        unreachable!()
    };
    let WordRepresentation::U16Limbs(rs2_limbs) = rs2_access.read_value else {
        unreachable!()
    };
    let WordRepresentation::U16Limbs(rd_write_limbs) = rd_access.write_value else {
        unreachable!()
    };

    let shift_left_16_bits = F::from_u32_with_reduction(1 << 16);
    let shift_right_8_bits = F::from_u32_with_reduction(1 << 8).inverse().unwrap();
    let shift_right_8_bits_term = Term::from_field(shift_right_8_bits);

    // we need range checks on the output to ensure proper addition
    let [out_low, out_high] = rd_write_limbs;
    cs.require_invariant(out_low, Invariant::RangeChecked { width: 16 });
    cs.require_invariant(out_high, Invariant::RangeChecked { width: 16 });

    if let Some(rs1_reg) = Register(rs1_limbs.map(|el| Num::Var(el))).get_value_unsigned(cs) {
        println!("RS1 value = 0x{:08x}", rs1_reg);
    }

    if let Some(rs2_reg) = Register(rs2_limbs.map(|el| Num::Var(el))).get_value_unsigned(cs) {
        println!("RS2 value = 0x{:08x}", rs2_reg);
    }

    if SUPPORT_SIGNED == false {
        let is_mul = decoder.is_mul();
        let is_mulhu = decoder.is_mulhu();
        let is_divu = decoder.is_divu();
        let is_remu = decoder.is_remu();

        // as usual we enforce division via witness and multiplication,
        // and should analyze exceptional cases. For unsigned ops only there is just divu/remu
        // with divisor being 0
        // - for DIVU quotient is u32::MAX
        // - for REMU remainder is dividend

        // it works well in our multiplication enforcement case: we enforce dividend = q * divisor + remainder,
        // and can set quotient witness to u32::MAX and remainder to dividend

        // for all other cases we check that remainder < divisor

        // we do not need any sign information, but we still need to break everything into u8 chunks (do via lookup that outputs exact lowest 8 bits),
        // and test if divisor is 0 (via lookup of the sum of limbs)

        if is_mul.get_value(cs).unwrap_or(false) {
            println!("MUL");
        }
        if is_mulhu.get_value(cs).unwrap_or(false) {
            println!("MULHI");
        }
        if is_divu.get_value(cs).unwrap_or(false) {
            println!("DIVU");
        }
        if is_remu.get_value(cs).unwrap_or(false) {
            println!("REMU");
        }

        let is_division_group_constraint = Term::<F>::from(is_divu) + Term::from(is_remu);
        let is_multiplication_group_constraint = Term::<F>::from(is_mul) + Term::from(is_mulhu);

        // Generic strategy:
        // - choose variables for (high, low) = q * divisor + remainder pattern
        // - split `q` and `divisor` equivalents into u8 limbs
        // - allocate witness variables for carries
        // - perform schoolbook multiplication + enforcement

        let rs2_is_zero = cs.add_named_variable("RS2 is zero out var");
        cs.set_variables_from_lookup_constrained(
            &[LookupInput::from(
                Constraint::empty() + Term::from(rs2_limbs[0]) + Term::from(rs2_limbs[1]),
            )],
            &[rs2_is_zero],
            cs::circuit::LookupQueryTableType::Constant(TableType::RegIsZero),
        );

        // divisor is always rs2, and quotient is either rs1 for multiplication, or extra witness for REMU,
        // or RD for DIVU

        // allocate splitting of future `q` and `divisor` and allocate witness for them
        let divisor_byte_0 = cs.add_named_variable("Divisor byte 0");
        cs.set_variables_from_lookup_constrained(
            &[LookupInput::from(
                Constraint::empty() + Term::from(rs2_limbs[0]),
            )],
            &[divisor_byte_0],
            cs::circuit::LookupQueryTableType::Constant(TableType::U16GetLowByte),
        );

        let divisor_byte_2 = cs.add_named_variable("Divisor byte 2");
        cs.set_variables_from_lookup_constrained(
            &[LookupInput::from(
                Constraint::empty() + Term::from(rs2_limbs[1]),
            )],
            &[divisor_byte_2],
            cs::circuit::LookupQueryTableType::Constant(TableType::U16GetLowByte),
        );

        // for quotient we can only allocate it, and copy to the next layer
        let quotient_byte_0 = cs.add_named_variable("Quotient byte 0");
        let quotient_byte_2 = cs.add_named_variable("Quotient byte 2");

        // we also need 2 variables of extra witness
        let extra_u16_witness_low = cs.add_named_variable("Extra U16 witness low");
        let extra_u16_witness_high = cs.add_named_variable("Extra U16 witness high");
        cs.require_invariant(extra_u16_witness_low, Invariant::RangeChecked { width: 16 });
        cs.require_invariant(
            extra_u16_witness_high,
            Invariant::RangeChecked { width: 16 },
        );
        let extra_witness = [extra_u16_witness_low, extra_u16_witness_high];

        let remainder_comparison_u16_witness_low =
            cs.add_named_variable("Remainder comparison U16 witness low");
        let remainder_comparison_u16_witness_high =
            cs.add_named_variable("Remainder comparison U16 witness high");
        cs.require_invariant(
            remainder_comparison_u16_witness_low,
            Invariant::RangeChecked { width: 16 },
        );
        cs.require_invariant(
            remainder_comparison_u16_witness_high,
            Invariant::RangeChecked { width: 16 },
        );

        // we do not need exact ranges for carry witnesses, just some range checks that fit
        // worst case option, and do NOT overflow the field
        assert!(F::CHAR_BITS > 16 + 13);
        let intermedaite_carry_witness: [Variable; 3] = std::array::from_fn(|i| {
            let var = cs.add_named_variable(&format!("Intermediate carry witness[{}]", i));
            cs.enforce_lookup_tuple_for_fixed_table(
                &[LookupInput::from(Constraint::empty() + Term::from(var))],
                TableType::RangeCheck13,
                false,
            );

            var
        });

        // set witness for all those variables
        {}

        // now we push everything to the intermediate layer
        let divisor_is_zero_if_division_layer_1 = cs
            .add_intermediate_named_variable_from_constraint(
                is_division_group_constraint.clone() * Term::from(rs2_is_zero),
                "divisor is zero if division at layer 1",
            );

        // select all variables and push them to layer 1
        let low_at_layer_1: [Variable; 2] = std::array::from_fn(|i| {
            cs.add_intermediate_named_variable_from_constraint(
                Term::from(is_mul) * Term::from(rd_write_limbs[i])
                    + Term::from(is_mulhu) * Term::from(extra_witness[i])
                    + Term::from(is_divu) * Term::from(rs1_limbs[i])
                    + Term::from(is_remu) * Term::from(rs1_limbs[i]),
                &format!("low[{}] at layer 1", i),
            )
        });
        let high_at_layer_1: [Variable; 2] = std::array::from_fn(|i| {
            cs.add_intermediate_named_variable_from_constraint(
                Term::from(is_mulhu) * Term::from(rd_write_limbs[i])
                    + Term::from(is_mul) * Term::from(extra_witness[i]),
                // 0 if any division group
                &format!("high[{}] at layer 1", i),
            )
        });
        let quotient_at_layer_1: [Variable; 2] = std::array::from_fn(|i| {
            cs.add_intermediate_named_variable_from_constraint(
                Term::from(is_mul) * Term::from(rs1_limbs[i])
                    + Term::from(is_mulhu) * Term::from(rs1_limbs[i])
                    + Term::from(is_divu) * Term::from(rd_write_limbs[i])
                    + Term::from(is_remu) * Term::from(extra_witness[i]),
                &format!("quotient[{}] at layer 1", i),
            )
        });
        let remainder_at_layer_1: [Variable; 2] = std::array::from_fn(|i| {
            cs.add_intermediate_named_variable_from_constraint(
                // 0 for any mul
                Term::from(is_divu) * Term::from(extra_witness[i])
                    + Term::from(is_remu) * Term::from(rd_write_limbs[i]),
                &format!("remainder[{}] at layer 1", i),
            )
        });
        // it'll select 0, so padding rows are fine
        let divisor_at_layer_1: [Variable; 2] = std::array::from_fn(|i| {
            cs.add_intermediate_named_variable_from_constraint(
                Term::from(is_mul) * Term::from(rs2_limbs[i])
                    + Term::from(is_mulhu) * Term::from(rs2_limbs[i])
                    + Term::from(is_divu) * Term::from(rs2_limbs[i])
                    + Term::from(is_remu) * Term::from(rs2_limbs[i]),
                &format!("divisor[{}] at layer 1", i),
            )
        });

        let remainder_comparison_u16_witness_low_at_layer_1 = cs
            .add_intermediate_named_variable_from_constraint(
                Constraint::from(remainder_comparison_u16_witness_low),
                "Remainder comparison U16 witness low at layer 1",
            );
        let remainder_comparison_u16_witness_high_at_layer_1 = cs
            .add_intermediate_named_variable_from_constraint(
                Constraint::from(remainder_comparison_u16_witness_high),
                "Remainder comparison U16 witness high at layer 1",
            );

        let divisor_byte_0_at_layer_1 = cs.add_intermediate_named_variable_from_constraint(
            Constraint::from(divisor_byte_0),
            "divisor byte 0 at layer 1",
        );
        let divisor_byte_2_at_layer_1 = cs.add_intermediate_named_variable_from_constraint(
            Constraint::from(divisor_byte_2),
            "divisor byte 2 at layer 1",
        );
        let quotient_byte_0_at_layer_1 = cs.add_intermediate_named_variable_from_constraint(
            Constraint::from(quotient_byte_0),
            "quotient byte 0 at layer 1",
        );
        let quotient_byte_2_at_layer_1 = cs.add_intermediate_named_variable_from_constraint(
            Constraint::from(quotient_byte_2),
            "quotient byte 2 at layer 1",
        );
        let mut i = 0;
        let intermedaite_carry_witness_layer_1 = intermedaite_carry_witness.map(|el| {
            let t = cs.add_intermediate_named_variable_from_constraint(
                Constraint::from(el),
                &format!("intermediate carry witness[{}] at layer 1", i),
            );
            i += 1;

            t
        });

        // enforce decomposition on the layer 1 for bytes
        cs.enforce_lookup_tuple_for_fixed_table(
            &[
                LookupInput::from(quotient_at_layer_1[0]),
                LookupInput::from(quotient_byte_0_at_layer_1),
            ],
            TableType::U16GetLowByte,
            false,
        );
        cs.enforce_lookup_tuple_for_fixed_table(
            &[
                LookupInput::from(quotient_at_layer_1[1]),
                LookupInput::from(quotient_byte_2_at_layer_1),
            ],
            TableType::U16GetLowByte,
            false,
        );

        // simply enforce the schoolbook multiplication relation
        {
            // 0-16 bits
            {
                let mut constraint = Constraint::<F>::empty();
                constraint +=
                    Term::from(divisor_byte_0_at_layer_1) * Term::from(quotient_byte_0_at_layer_1);
                constraint += (Term::from(divisor_at_layer_1[0])
                    - Term::from(divisor_byte_0_at_layer_1))
                    * shift_right_8_bits_term
                    * Term::from(quotient_byte_0_at_layer_1);
                constraint += (Term::from(quotient_at_layer_1[0])
                    - Term::from(quotient_byte_0_at_layer_1))
                    * shift_right_8_bits_term
                    * Term::from(divisor_byte_0_at_layer_1);
                constraint += Term::from(remainder_at_layer_1[0]);
                constraint -= Term::from(low_at_layer_1[0]);
                constraint -= Term::from((shift_left_16_bits, intermedaite_carry_witness[0]));
                cs.add_constraint(constraint);
            }
            // 16-32 bits
            {}
            // 32-48 bits
            {}
            // 48-64 bits
        }

        // and the last thing to do is to check that remainder < divisor unless divisor is 0,
        // and if divisor is 0 - then quotient is u32::MAX

        // 2^16 * of + remainder - divisor = witness
        let mut t = Term::from(remainder_comparison_u16_witness_low)
            - Term::from(remainder_at_layer_1[0])
            + Term::from(divisor_at_layer_1[0]);
        t.scale(shift_left_16_bits.inverse().unwrap());
        cs.add_constraint(t.clone() * t.clone());

        // 2^16*(1 - divisor_is_zero) + remainder - divisor - carry = witness
        let mut c = Term::from(1u32) - Term::from(divisor_is_zero_if_division_layer_1);
        c.scale(shift_left_16_bits);
        c = c + Term::from(remainder_at_layer_1[1]);
        c = c - Term::from(divisor_at_layer_1[1]);
        c = c - t;
        c = c - Term::from(remainder_comparison_u16_witness_high);
        cs.add_constraint(c);

        cs.add_constraint(
            (Term::<F>::from(low_at_layer_1[0]) - Term::from(remainder_at_layer_1[0]))
                * Term::from(divisor_is_zero_if_division_layer_1),
        );
        cs.add_constraint(
            (Term::<F>::from(low_at_layer_1[1]) - Term::from(remainder_at_layer_1[1]))
                * Term::from(divisor_is_zero_if_division_layer_1),
        );

        cs.add_constraint(
            (Term::<F>::from(u16::MAX as u32) - Term::from(quotient_at_layer_1[0]))
                * Term::from(divisor_is_zero_if_division_layer_1),
        );
        cs.add_constraint(
            (Term::<F>::from(u16::MAX as u32) - Term::from(quotient_at_layer_1[1]))
                * Term::from(divisor_is_zero_if_division_layer_1),
        );

        // Witness function - added before any constraints, so we can use debug machinery
        {
            let of_var = carry.get_variable().unwrap();
            let intermediate_of_var = intermediate_carry.get_variable().unwrap();
            let out_vars = [out_low, out_high];
            let intermediate_vars = intermediate_tmp.0.map(|el| el.get_variable());
            let imm_vars = inputs.decoder_data.imm;
            let pc_vars = inputs.cycle_start_state.pc;
            let rs1_vars = rs1_limbs;
            let rs2_vars = rs2_limbs;

            let is_add_var = is_add.get_variable().unwrap();
            let is_sub_var = is_sub.get_variable().unwrap();
            let is_auipc_var = is_auipc.get_variable().unwrap();
            let is_addmod_var = is_addmod.get_variable().unwrap();
            let is_submod_var = is_submod.get_variable().unwrap();
            let is_mulmod_var = is_mulmod.get_variable().unwrap();
            let _is_delegation_call_var = is_delegation_call.get_variable().unwrap();
            let is_non_determinism_read_var = is_non_determinism_read.get_variable().unwrap();

            let value_fn = move |placer: &mut CS::WitnessPlacer| {
                // NOTE: it is UNCONDITIONAL assignment, even though we select across multiple variants

                let mut out_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0);
                let mut intermediate_value =
                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0);
                let mut of_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false);
                let mut u16_intermedaite_carry_value =
                    <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false);

                let imm_low = placer.get_u16(imm_vars[0]);
                let imm = placer.get_u32_from_u16_parts(imm_vars);
                let rs1_low = placer.get_u16(rs1_vars[0]);
                let rs1_u32 = placer.get_u32_from_u16_parts(rs1_vars);
                let rs2_low = placer.get_u16(rs2_vars[0]);
                let rs2_u32 = placer.get_u32_from_u16_parts(rs2_vars);
                let pc_low = placer.get_u16(pc_vars[0]);
                let pc_u32 = placer.get_u32_from_u16_parts(pc_vars);
                let boolean_false = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false);
                let modulus_low = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(
                    F::CHARACTERISTICS as u16,
                );
                let modulus_constant = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(
                    F::CHARACTERISTICS as u32,
                );
                {
                    let is_add = placer.get_boolean(is_add_var);
                    let (add_result, of0) = rs1_u32.overflowing_add(&rs2_u32);
                    let (add_result, of1) = add_result.overflowing_add(&imm);
                    let of = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::or(&of0, &of1);
                    out_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                        &is_add,
                        &add_result,
                        &out_value,
                    );
                    of_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                        &is_add, &of, &of_value,
                    );
                    update_intermediate_carry_value::<F, CS::WitnessPlacer, false>(
                        &mut u16_intermedaite_carry_value,
                        &is_add,
                        &rs1_low,
                        &rs2_low,
                        Some(&imm_low),
                    );
                }
                {
                    let is_sub = placer.get_boolean(is_sub_var);
                    let (sub_result, of) = rs1_u32.overflowing_sub(&rs2_u32);
                    out_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                        &is_sub,
                        &sub_result,
                        &out_value,
                    );
                    of_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                        &is_sub, &of, &of_value,
                    );
                    update_intermediate_carry_value::<F, CS::WitnessPlacer, true>(
                        &mut u16_intermedaite_carry_value,
                        &is_sub,
                        &rs1_low,
                        &rs2_low,
                        Some(&imm_low),
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
                    of_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                        &is_auipc, &of, &of_value,
                    );
                    update_intermediate_carry_value::<F, CS::WitnessPlacer, false>(
                        &mut u16_intermedaite_carry_value,
                        &is_auipc,
                        &pc_low,
                        &imm_low,
                        None,
                    );
                }

                let rs1_f =
                    <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::from_integer(
                        rs1_u32,
                    );
                let rs2_f =
                    <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::from_integer(
                        rs2_u32,
                    );

                // addmod
                {
                    let is_addmod = placer.get_boolean(is_addmod_var);
                    let addmod_result = {
                        let mut addmod_f = rs1_f.clone();
                        addmod_f.add_assign(&rs2_f);
                        addmod_f.as_integer()
                    };
                    let add_mod_low = addmod_result.truncate();
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
                    of_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                        &is_addmod, &of, &of_value,
                    );
                    update_intermediate_carry_value::<F, CS::WitnessPlacer, true>(
                        &mut u16_intermedaite_carry_value,
                        &is_addmod,
                        &add_mod_low,
                        &modulus_low,
                        None,
                    );
                }
                // submod
                {
                    let is_submod = placer.get_boolean(is_submod_var);
                    let submod_result = {
                        let mut submod_f = rs1_f.clone();
                        submod_f.sub_assign(&rs2_f);
                        submod_f.as_integer()
                    };
                    let sub_mod_low = submod_result.truncate();
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
                    of_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                        &is_submod, &of, &of_value,
                    );
                    update_intermediate_carry_value::<F, CS::WitnessPlacer, true>(
                        &mut u16_intermedaite_carry_value,
                        &is_submod,
                        &sub_mod_low,
                        &modulus_low,
                        None,
                    );
                }
                // mulmod - both final and intermediate var (unconditional)
                {
                    let is_mulmod = placer.get_boolean(is_mulmod_var);
                    let mulmod_field = {
                        let mut mulmod_f = rs1_f.clone();
                        mulmod_f.mul_assign(&rs2_f);
                        mulmod_f
                    };
                    placer.assign_field(mulmod_intermediate_var, &mulmod_field);
                    let mulmod_result = mulmod_field.clone().as_integer();
                    let mul_mod_low = mulmod_result.truncate();
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
                    of_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                        &is_mulmod, &of, &of_value,
                    );
                    update_intermediate_carry_value::<F, CS::WitnessPlacer, true>(
                        &mut u16_intermedaite_carry_value,
                        &is_mulmod,
                        &mul_mod_low,
                        &modulus_low,
                        None,
                    );
                }
                // non-determinism
                {
                    let is_non_determinism_read = placer.get_boolean(is_non_determinism_read_var);
                    let oracle_value = placer.get_oracle_u32(Placeholder::ExternalOracle);
                    out_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                        &is_non_determinism_read,
                        &oracle_value,
                        &out_value,
                    );
                    of_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                        &is_non_determinism_read,
                        &boolean_false,
                        &of_value,
                    );
                }

                // actually assign
                if CS::ASSUME_MEMORY_VALUES_ASSIGNED == false {
                    placer.assign_u32_from_u16_parts(out_vars, &out_value);
                }

                placer.assign_u32_from_u16_parts(intermediate_vars, &intermediate_value);
                placer.assign_mask(of_var, &of_value);
                placer.assign_mask(intermediate_of_var, &u16_intermedaite_carry_value);
            };
            cs.set_values(value_fn);
        }
    } else {
        todo!("support signed ops")
    }

    if let Some(rd_reg) = Register(rd_write_limbs.map(|el| Num::Var(el))).get_value_unsigned(cs) {
        println!("RD value = 0x{:08x}", rd_reg);
    }

    // bump PC
    use crate::gkr_circuits::utils::calculate_pc_next_no_overflows_with_range_checks;
    calculate_pc_next_no_overflows_with_range_checks(
        cs,
        inputs.cycle_start_state.pc,
        inputs.cycle_end_state.pc,
    );
}

pub fn mul_div_circuit_with_preprocessed_bytecode_for_gkr<
    F: PrimeField,
    CS: Circuit<F>,
    const SUPPORT_SIGNED: bool,
>(
    cs: &mut CS,
) {
    let num_flags = if SUPPORT_SIGNED {
        MUL_DIV_FAMILY_NUM_FLAGS
    } else {
        UNSIGNED_MUL_DIV_FAMILY_NUM_FLAGS
    };
    let (input, bitmask) = cs.allocate_machine_state(false, false, num_flags);
    let bitmask: Vec<_> = bitmask.into_iter().map(|el| Boolean::Is(el)).collect();
    let decoder = DivMulFamilyCircuitMask::<SUPPORT_SIGNED>::from_mask(&bitmask);
    apply_mul_div_inner::<F, CS, SUPPORT_SIGNED>(cs, input, decoder);
}

#[cfg(test)]
mod test {
    use test_utils::skip_if_ci;

    use super::*;
    use crate::gkr_compiler::compile_unrolled_circuit_state_transition_into_gkr;
    use crate::gkr_compiler::compile_unrolled_circuit_state_transition_into_unrolled_gkr_without_caches;
    use crate::gkr_compiler::dump_ssa_witness_eval_form;
    use crate::utils::serialize_to_file;

    #[test]
    fn compile_unsigned_mul_div_into_gkr() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let gkr_compiled = compile_unrolled_circuit_state_transition_into_gkr::<BabyBearField>(
            &|cs| mul_div_table_addition_fn::<_, _, false>(cs),
            &|cs| mul_div_circuit_with_preprocessed_bytecode_for_gkr::<_, _, false>(cs),
            common_constants::ROM_WORD_SIZE,
            24,
        );

        serialize_to_file(
            &gkr_compiled,
            "compiled_circuits/unsigned_mul_div_preprocessed_layout_gkr.json",
        );
    }

    #[test]
    fn compile_unsigned_mul_div_gkr_witness_graph() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let ssa_forms = dump_ssa_witness_eval_form::<BabyBearField>(
            &|cs| mul_div_table_addition_fn::<_, _, false>(cs),
            &|cs| mul_div_circuit_with_preprocessed_bytecode_for_gkr::<_, _, false>(cs),
        );
        serialize_to_file(
            &ssa_forms,
            "compiled_circuits/unsigned_mul_div_preprocessed_ssa_gkr.json",
        );
    }

    #[test]
    fn compile_unsigned_mul_div_into_no_caches_gkr() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let gkr_compiled =
            compile_unrolled_circuit_state_transition_into_unrolled_gkr_without_caches::<
                BabyBearField,
            >(
                &|cs| mul_div_table_addition_fn::<_, _, false>(cs),
                &|cs| mul_div_circuit_with_preprocessed_bytecode_for_gkr::<_, _, false>(cs),
                common_constants::ROM_WORD_SIZE,
                24,
            );

        serialize_to_file(
            &gkr_compiled,
            "compiled_circuits/unsigned_mul_div_preprocessed_layout_no_caches_gkr.json",
        );
    }
}
