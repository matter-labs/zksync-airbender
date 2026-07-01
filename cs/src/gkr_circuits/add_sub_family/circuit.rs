use super::decoder::AddSubLuiAuipcMopDecoder;
use super::*;
use crate::cs::circuit_trait::*;
use crate::gkr_circuits::utils::{montgomery_product_expr, update_intermediate_carry_value};
use crate::oracle::Placeholder;
use crate::structured_expr::Expr;
use crate::tables::TableDriver;
use crate::types::*;
use crate::witness_placer::*;
use field::PrimeField;

fn word_from_u16_limbs_expr<F: PrimeField>(limbs: [Variable; 2], limb_shift: F) -> Expr<F> {
    Expr::var(limbs[0]) + Expr::var(limbs[1]) * limb_shift
}

pub fn add_sub_lui_auipc_mop_table_addition_fn<F: PrimeField, CS: Circuit<F>>(cs: &mut CS) {
    // no tables
    let _ = cs;
}

pub fn add_sub_lui_auipc_mop_table_driver_fn<F: PrimeField>(table_driver: &mut TableDriver<F>) {
    // no tables
    let _ = table_driver;
}

fn apply_add_sub_lui_auipc_mop_inner<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    inputs: OpcodeFamilyCircuitState<F>,
    decoder: <AddSubLuiAuipcMopDecoder as OpcodeFamilyDecoder>::BitmaskCircuitParser,
) {
    // NOTE: by preprocessing if we have rd == 0 in any of the opcodes below, then
    // we have rs1 = x0, rs2 = x0 and imm = 0, and it's preprocessed into plain addition,
    // so we do NOT need to mask rd value

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
    let WordRepresentation::U16Limbs(rd_read_limbs) = rd_access.read_value else {
        unreachable!()
    };
    let WordRepresentation::U16Limbs(rd_write_limbs) = rd_access.write_value else {
        unreachable!()
    };

    // we will also need to pay 2 more range checks
    let intermediate_tmp = Register::new_named(cs, "Modular ops intermediate comparison reg");
    let modulus_low = F::from_u32_unchecked((F::CHARACTERISTICS_U32 as u16) as u32);
    let modulus_high = F::from_u32_unchecked(((F::CHARACTERISTICS_U32 >> 16) as u16) as u32);

    let carry_shift = F::from_u32_with_reduction(1 << 16);

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

    if let Some(imm) =
        Register::<F>(inputs.decoder_data.imm.map(|el| Num::Var(el))).get_value_unsigned(cs)
    {
        println!("IMM value = 0x{:08x}", imm);
    }

    // IMPORTANT: we must NOT allocate any more registers
    let is_add = decoder.perform_add_addi_lui();
    let is_sub = decoder.perform_sub();
    let is_auipc = decoder.perform_auipc();
    let is_addmod = decoder.perform_addmod();
    let is_submod = decoder.perform_submod();
    let is_mulmod = decoder.perform_mulmod();
    let is_fmamod = decoder.perform_fmamod();
    let is_delegation_call = decoder.perform_delegation_call();
    let is_non_determinism_read = decoder.perform_non_determinism_read();

    if is_add.get_value(cs).unwrap_or(false) {
        println!("ADD/ADDI/LUI");
    }
    if is_sub.get_value(cs).unwrap_or(false) {
        println!("SUB");
    }
    if is_auipc.get_value(cs).unwrap_or(false) {
        println!("AUIPC");
    }
    if is_addmod.get_value(cs).unwrap_or(false) {
        println!("MOP_ADD");
    }
    if is_submod.get_value(cs).unwrap_or(false) {
        println!("MOP_SUB");
    }
    if is_mulmod.get_value(cs).unwrap_or(false) {
        println!("MOP_MUL");
    }
    if is_fmamod.get_value(cs).unwrap_or(false) {
        println!("MOP_FMA");
    }
    if is_delegation_call.get_value(cs).unwrap_or(false) {
        println!("DELEGATION CALL");
    }
    if is_non_determinism_read.get_value(cs).unwrap_or(false) {
        println!("NON-DETERMINISM READ");
    }

    let intermediate_carry = cs.add_named_boolean_variable("intermediate carry for out");
    let carry = cs.add_named_boolean_variable("carry for out");
    let mulmod_intermediate_var = cs.add_named_variable("MULMOD intermediate value");

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
        let rd_read_vars = rd_read_limbs;

        let is_add_var = is_add.get_variable().unwrap();
        let is_sub_var = is_sub.get_variable().unwrap();
        let is_auipc_var = is_auipc.get_variable().unwrap();
        let is_addmod_var = is_addmod.get_variable().unwrap();
        let is_submod_var = is_submod.get_variable().unwrap();
        let is_mulmod_var = is_mulmod.get_variable().unwrap();
        let is_fmamod_var = is_fmamod.get_variable().unwrap();
        let _is_delegation_call_var = is_delegation_call.get_variable().unwrap();
        let is_non_determinism_read_var = is_non_determinism_read.get_variable().unwrap();

        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            // NOTE: it is UNCONDITIONAL assignment, even though we select across multiple variants

            let mut out_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0);
            let mut intermediate_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0);
            let mut of_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false);
            let mut u16_intermedaite_carry_value =
                <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false);

            let imm_low = placer.get_u16(imm_vars[0]);
            let imm = placer.get_u32_from_u16_parts(imm_vars);
            let rs1_low = placer.get_u16(rs1_vars[0]);
            let rs1_u32 = placer.get_u32_from_u16_parts(rs1_vars);
            let rs2_low = placer.get_u16(rs2_vars[0]);
            let rs2_u32 = placer.get_u32_from_u16_parts(rs2_vars);
            let rd_read_u32 = placer.get_u32_from_u16_parts(rd_read_vars);
            let pc_low = placer.get_u16(pc_vars[0]);
            let pc_u32 = placer.get_u32_from_u16_parts(pc_vars);
            let boolean_false = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false);
            let modulus_low =
                <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(F::CHARACTERISTICS_U32 as u16);
            let modulus_constant =
                <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(F::CHARACTERISTICS_U32 as u32);
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
                of_value =
                    <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(&is_add, &of, &of_value);
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
                of_value =
                    <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(&is_sub, &of, &of_value);
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
                    rs1_u32.clone(),
                );
            let rs2_f =
                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::from_integer(
                    rs2_u32.clone(),
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
            // mulmod - both final and intermediate var (unconditional), and fmamod via mixing addition term
            {
                let is_mulmod = placer.get_boolean(is_mulmod_var);
                let is_fmamod = placer.get_boolean(is_fmamod_var);
                let is_mul_like = is_mulmod.or(&is_fmamod);
                let op1 =
                    <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::from_raw_repr_with_reduction(
                        rs1_u32,
                    );
                let op2 =
                    <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::from_raw_repr_with_reduction(
                        rs2_u32,
                    );
                let rd_raw =
                    <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::from_raw_repr_with_reduction(
                        rd_read_u32,
                    );
                let mut mulmod_field = op1;
                mulmod_field.mul_assign(&op2);
                mulmod_field.add_assign_masked(&is_fmamod, &rd_raw);
                let mulmod_result = mulmod_field.into_raw_repr_reduced();
                placer.assign_field(
                    mulmod_intermediate_var,
                    &<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::from_integer(
                        mulmod_result.clone(),
                    ),
                );
                let mul_mod_low = mulmod_result.truncate();
                out_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                    &is_mul_like,
                    &mulmod_result,
                    &out_value,
                );
                let (tmp, of) = mulmod_result.overflowing_sub(&modulus_constant);
                intermediate_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                    &is_mul_like,
                    &tmp,
                    &intermediate_value,
                );
                of_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                    &is_mul_like,
                    &of,
                    &of_value,
                );
                update_intermediate_carry_value::<F, CS::WitnessPlacer, true>(
                    &mut u16_intermedaite_carry_value,
                    &is_mul_like,
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

    // separate constraint for addmod/submod/mulmod. We use intermediate range-checked register to check
    // field element normalization

    // it'll be useful later on. We have a guarantee that all opcode flags are disjoint, and so
    // we can just use addition
    let is_modular = Expr::<F>::Sum(vec![
        Expr::from(is_addmod),
        Expr::from(is_submod),
        Expr::from(is_mulmod),
        Expr::from(is_fmamod),
    ]);

    {
        let rs1 = word_from_u16_limbs_expr(rs1_limbs, carry_shift);
        let rs2 = word_from_u16_limbs_expr(rs2_limbs, carry_shift);
        let rd_read = word_from_u16_limbs_expr(rd_read_limbs, carry_shift);
        let out = word_from_u16_limbs_expr([out_low, out_high], carry_shift);

        // ADDMOD
        {
            // nothing extra
        }
        // SUBMOD
        {
            // nothing extra
        }
        // MULMOD
        {
            // use intermediate variable, and mix-in the addition part
            cs.add_constraint_expr(
                montgomery_product_expr(rs1.clone(), rs2.clone())
                    + rd_read * Expr::var(is_fmamod.get_variable().unwrap())
                    - Expr::var(mulmod_intermediate_var),
            );
        }

        // enforce field ops - all at once, as we know that flags are disjoint
        // TODO: maybe we want to restructure it, but it'll not make less multiplications anyway
        let is_mul_like = Expr::<F>::Sum(vec![Expr::from(is_mulmod), Expr::from(is_fmamod)]);
        cs.add_constraint_expr(
            (out.clone() - (rs1.clone() + rs2.clone())).mask(is_addmod)
                + (out.clone() - (rs1.clone() - rs2)).mask(is_submod)
                + (out - Expr::var(mulmod_intermediate_var)) * is_mul_like,
        );

        // check normalization
        cs.add_constraint_expr((Expr::<F>::one() - Expr::from(carry)) * is_modular.clone());

        // out < modulus, so
        // 2^32*of + out - modulus = tmp
        // and we checked that there is always a borrow in the branches above

        // one constraint to ensure canonical form, and we merge it below with normal addition-like constraint
    }

    // we have just 2 sets of constraints:
    // - one that links register/imm inputs and output
    // - another that enforces reduction for GKR

    // generic constraint for addition-like ops links to RD directly.
    // each opcode contributes one linear equation per limb; we mask by its family bit and sum.
    // addmod/submod/mulmod share an equation per limb, so we factor it once and multiply
    // it by the sum of their opcode masks.
    // NOTE: for additions we blindly mix imm and rs2 as preprocessing ensures that if imm != 0 then rs2 = x0
    {
        let intermediate_carry_var = intermediate_carry.get_variable().unwrap();
        let carry_var = carry.get_variable().unwrap();

        // low limb
        // ADD/ADDI/LUI: rs1 + rs2 + imm - rd - 2^16 * intermediate_carry
        let eq_add_low = Expr::var(rs1_limbs[0])
            + Expr::var(rs2_limbs[0])
            + Expr::var(inputs.decoder_data.imm[0])
            - Expr::var(out_low)
            - Expr::var(intermediate_carry_var) * carry_shift;
        // AUIPC: pc + imm (no rs1/rs2)
        let eq_auipc_low = Expr::var(inputs.cycle_start_state.pc[0])
            + Expr::var(inputs.decoder_data.imm[0])
            - Expr::var(out_low)
            - Expr::var(intermediate_carry_var) * carry_shift;
        // SUB rearranged: 2^16*of + out + rs2 - rs1
        let eq_sub_low = Expr::var(out_low) + Expr::var(rs2_limbs[0])
            - Expr::var(rs1_limbs[0])
            - Expr::var(intermediate_carry_var) * carry_shift;
        // modular ops: 2^16*of + out - modulus = intermediate_tmp
        let eq_modular_low = Expr::var(intermediate_tmp.0[0].get_variable())
            + Expr::<F>::constant(modulus_low)
            - Expr::var(out_low)
            - Expr::var(intermediate_carry_var) * carry_shift;

        cs.add_constraint_expr(Expr::Sum(vec![
            eq_add_low.mask(is_add),
            eq_auipc_low.mask(is_auipc),
            eq_sub_low.mask(is_sub),
            eq_modular_low * is_modular.clone(),
        ]));

        // high limb: same structure plus intermediate_carry (carry-in from low limb),
        // and final carry-out shifted by 2^16
        let eq_add_high = Expr::<F>::from(intermediate_carry)
            + Expr::var(rs1_limbs[1])
            + Expr::var(rs2_limbs[1])
            + Expr::var(inputs.decoder_data.imm[1])
            - Expr::var(out_high)
            - Expr::var(carry_var) * carry_shift;
        let eq_auipc_high = Expr::<F>::from(intermediate_carry)
            + Expr::var(inputs.cycle_start_state.pc[1])
            + Expr::var(inputs.decoder_data.imm[1])
            - Expr::var(out_high)
            - Expr::var(carry_var) * carry_shift;
        let eq_sub_high =
            Expr::<F>::from(intermediate_carry) + Expr::var(out_high) + Expr::var(rs2_limbs[1])
                - Expr::var(rs1_limbs[1])
                - Expr::var(carry_var) * carry_shift;
        let eq_modular_high = Expr::<F>::from(intermediate_carry)
            + Expr::var(intermediate_tmp.0[1].get_variable())
            + Expr::<F>::constant(modulus_high)
            - Expr::var(out_high)
            - Expr::var(carry_var) * carry_shift;

        cs.add_constraint_expr(Expr::Sum(vec![
            eq_add_high.mask(is_add),
            eq_auipc_high.mask(is_auipc),
            eq_sub_high.mask(is_sub),
            eq_modular_high * is_modular,
        ]));
    }

    // Delegation call
    // We perform formal READ from register with CSR index at rs2 (in preprocessing),
    // and to ensure that it's a permutation and not a memory argument, we do not have inits/teardowns for such
    // registers, and enforce that read timestamps are 0, and read values are 0
    // We also ensure that out value is 0 as from preprocessing rd = x0
    {
        // delegation register value
        cs.add_constraint_expr(Expr::var(rs2_limbs[0]).mask(is_delegation_call));
        cs.add_constraint_expr(Expr::var(rs2_limbs[1]).mask(is_delegation_call));
        // read timestamp
        cs.add_constraint_expr(Expr::var(rs2_access.read_timestamp[0]).mask(is_delegation_call));
        cs.add_constraint_expr(Expr::var(rs2_access.read_timestamp[1]).mask(is_delegation_call));
        // out value
        cs.add_constraint_expr(Expr::var(rd_write_limbs[0]).mask(is_delegation_call));
        cs.add_constraint_expr(Expr::var(rd_write_limbs[1]).mask(is_delegation_call));
    }

    // Non-determinism - actually we do not have ANY constraint on RD value, other than range checks
    // done above for generic consistency

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

pub fn add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode_for_gkr<
    F: PrimeField,
    CS: Circuit<F>,
>(
    cs: &mut CS,
) {
    let (input, bitmask) =
        cs.allocate_machine_state(false, false, ADD_SUB_LUI_AUIPC_MOP_FAMILY_NUM_FLAGS);
    let bitmask: [_; ADD_SUB_LUI_AUIPC_MOP_FAMILY_NUM_FLAGS] = bitmask.try_into().unwrap();
    let bitmask = bitmask.map(|el| Boolean::Is(el));
    let decoder = AddSubLuiAuipcMopFamilyCircuitMask::from_mask(bitmask);
    apply_add_sub_lui_auipc_mop_inner(cs, input, decoder);
}

#[cfg(test)]
mod test {
    use test_utils::skip_if_ci;

    use super::*;
    use crate::cs::circuit_impl::BasicAssembly;
    use crate::gkr_compiler::compile_unrolled_circuit_state_transition_into_gkr;
    use crate::gkr_compiler::compile_unrolled_circuit_state_transition_into_unrolled_gkr_without_caches;
    use crate::gkr_compiler::dump_ssa_witness_eval_form;
    use crate::structured_expr::StructuredStatement;
    use crate::utils::serialize_to_file;

    type F = ::field::Mersenne31Field;

    fn contains_variable(expr: &Expr<F>, variable: Variable) -> bool {
        match expr {
            Expr::Constant(_) => false,
            Expr::Var(candidate) => *candidate == variable,
            Expr::Sum(terms) | Expr::Product(terms) => {
                terms.iter().any(|term| contains_variable(term, variable))
            }
        }
    }

    fn is_scaled_variable(expr: &Expr<F>) -> bool {
        match expr {
            Expr::Product(factors) if factors.len() == 2 => {
                factors
                    .iter()
                    .any(|factor| matches!(factor, Expr::Constant(_)))
                    && factors.iter().any(|factor| matches!(factor, Expr::Var(_)))
            }
            _ => false,
        }
    }

    fn is_word_from_u16_limbs(expr: &Expr<F>) -> bool {
        match expr {
            Expr::Sum(terms) if terms.len() == 2 => {
                terms.iter().any(|term| matches!(term, Expr::Var(_)))
                    && terms.iter().any(is_scaled_variable)
            }
            _ => false,
        }
    }

    fn contains_product_of_word_exprs(expr: &Expr<F>) -> bool {
        match expr {
            Expr::Product(factors)
                if factors.len() == 2 && factors.iter().all(is_word_from_u16_limbs) =>
            {
                true
            }
            Expr::Sum(terms) | Expr::Product(terms) => {
                terms.iter().any(contains_product_of_word_exprs)
            }
            Expr::Constant(_) | Expr::Var(_) => false,
        }
    }

    #[test]
    fn add_sub_circuit_records_structured_mulmod_word_product() {
        let mut cs = BasicAssembly::<F>::new();
        add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode_for_gkr(&mut cs);
        let (output, _) = cs.finalize();
        let mulmod_intermediate = output
            .variable_names
            .iter()
            .find_map(|(variable, name)| (name == "MULMOD intermediate value").then_some(*variable))
            .expect("mulmod intermediate variable must be named");

        assert!(output
            .structured_statements
            .iter()
            .any(|statement| matches!(
                statement,
                StructuredStatement::AssertZero {
                    expr,
                    prevent_optimizations: false,
                } if contains_product_of_word_exprs(expr)
                    && contains_variable(expr, mulmod_intermediate)
            )));
    }

    #[test]
    fn compile_add_sub_lui_auipc_mop_into_gkr() {
        skip_if_ci!();
        use field::baby_bear::base::BabyBearField;

        let gkr_compiled = compile_unrolled_circuit_state_transition_into_gkr::<BabyBearField>(
            &|cs| add_sub_lui_auipc_mop_table_addition_fn(cs),
            &|cs| add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode_for_gkr(cs),
            common_constants::ROM_WORD_SIZE,
            24,
        );

        serialize_to_file(
            &gkr_compiled,
            "compiled_circuits/add_sub_lui_auipc_mop_layout_gkr.json",
        );
    }

    #[test]
    fn compile_add_sub_lui_auipc_mop_gkr_witness_graph() {
        skip_if_ci!();
        use field::baby_bear::base::BabyBearField;

        let ssa_forms = dump_ssa_witness_eval_form::<BabyBearField>(
            &|cs| add_sub_lui_auipc_mop_table_addition_fn(cs),
            &|cs| add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode_for_gkr(cs),
        );
        serialize_to_file(
            &ssa_forms,
            "compiled_circuits/add_sub_lui_auipc_mop_ssa_gkr.json",
        );
    }

    #[test]
    fn compile_add_sub_lui_auipc_mop_into_no_caches_gkr() {
        skip_if_ci!();
        use field::baby_bear::base::BabyBearField;

        let gkr_compiled =
            compile_unrolled_circuit_state_transition_into_unrolled_gkr_without_caches::<
                BabyBearField,
            >(
                &|cs| add_sub_lui_auipc_mop_table_addition_fn(cs),
                &|cs| add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode_for_gkr(cs),
                common_constants::ROM_WORD_SIZE,
                24,
            );

        serialize_to_file(
            &gkr_compiled,
            "compiled_circuits/add_sub_lui_auipc_mop_layout_no_caches_gkr.json",
        );
    }
}
