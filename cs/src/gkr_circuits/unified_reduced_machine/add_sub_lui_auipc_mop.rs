use super::*;
use crate::constraint::{Constraint, Term};
use crate::cs::circuit_trait::*;
use crate::gkr_circuits::add_sub_family::AddSubLuiAuipcMopFamilyCircuitMask;
use crate::gkr_circuits::utils::update_intermediate_carry_value;
use crate::oracle::Placeholder;
use crate::types::*;
use crate::witness_placer::*;
use field::PrimeField;

/// Family 1 (add_sub/lui/auipc/mop) constraints for the unified circuit.
/// Mirrors the standalone inner (`add_sub_family`), adapted to take
/// pre-allocated rs1/rs2 U8 byte limbs from the unified body instead of
/// requesting memory accesses internally. Non-Family-1 cycles have all
/// `decoder.perform_*()` Booleans = 0 so every constraint here is multiplied
/// by 0 and is trivially satisfied.
pub fn apply_unified_add_sub_lui_auipc_mop_inner<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    inputs: OpcodeFamilyCircuitState<F>,
    decoder: AddSubLuiAuipcMopFamilyCircuitMask,
    rs1_limbs: [Variable; 4],
    rs2_limbs: [Variable; 4],
    rd_write_limbs: [Variable; 2],
    rs2_read_timestamp: [Variable; common_constants::NUM_TIMESTAMP_COLUMNS_FOR_RAM],
) {
    // NOTE: by preprocessing if we have rd == 0 in any of the opcodes below, then
    // we have rs1 = x0, rs2 = x0 and imm = 0, and it's preprocessed into plain addition,
    // so we do NOT need to mask rd value

    // we will also need to pay 2 more range checks
    let intermediate_tmp = Register::new_named(cs, "Modular ops intermediate comparison reg");
    let modulus_low = F::from_u32_unchecked((F::CHARACTERISTICS as u16) as u32);
    let modulus_high = F::from_u32_unchecked(((F::CHARACTERISTICS >> 16) as u16) as u32);

    let carry_shift = F::from_u32_with_reduction(1 << 16);
    let shift_term = Term::from_field(carry_shift);

    // U16 views of rs1/rs2 reassembled from U8 bytes
    let byte_shift = F::from_u32_unchecked(1 << 8);
    let rs1_low_c: Constraint<F> =
        Constraint::from(rs1_limbs[0]) + Term::from((byte_shift, rs1_limbs[1]));
    let rs1_high_c: Constraint<F> =
        Constraint::from(rs1_limbs[2]) + Term::from((byte_shift, rs1_limbs[3]));
    let rs2_low_c: Constraint<F> =
        Constraint::from(rs2_limbs[0]) + Term::from((byte_shift, rs2_limbs[1]));
    let rs2_high_c: Constraint<F> =
        Constraint::from(rs2_limbs[2]) + Term::from((byte_shift, rs2_limbs[3]));

    // we need range checks on the output to ensure proper addition
    let [out_low, out_high] = rd_write_limbs;
    cs.require_invariant(out_low, Invariant::RangeChecked { width: 16 });
    cs.require_invariant(out_high, Invariant::RangeChecked { width: 16 });

    // IMPORTANT: we must NOT allocate any more registers
    let is_add = decoder.perform_add_addi_lui();
    let is_sub = decoder.perform_sub();
    let is_auipc = decoder.perform_auipc();
    let is_addmod = decoder.perform_addmod();
    let is_submod = decoder.perform_submod();
    let is_mulmod = decoder.perform_mulmod();
    let is_delegation_call = decoder.perform_delegation_call();
    let is_non_determinism_read = decoder.perform_non_determinism_read();

    let intermediate_carry = cs.add_named_boolean_variable("intermediate carry for out");
    let carry = cs.add_named_boolean_variable("carry for out");
    let mulmod_intermediate_var = cs.add_named_variable("MULMOD intermediate value");

    // Witness function - added before any constraints, so we can use debug machinery
    {
        let of_var = carry.expect_variable();
        let intermediate_of_var = intermediate_carry.expect_variable();
        let out_vars = [out_low, out_high];
        let intermediate_vars = intermediate_tmp.0.map(|el| el.get_variable());
        let imm_vars = inputs.decoder_data.imm;
        let pc_vars = inputs.cycle_start_state.pc;
        let rs1_vars = rs1_limbs;
        let rs2_vars = rs2_limbs;

        let is_add_var = is_add.expect_variable();
        let is_sub_var = is_sub.expect_variable();
        let is_auipc_var = is_auipc.expect_variable();
        let is_addmod_var = is_addmod.expect_variable();
        let is_submod_var = is_submod.expect_variable();
        let is_mulmod_var = is_mulmod.expect_variable();
        let is_non_determinism_read_var = is_non_determinism_read.expect_variable();

        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            // NOTE: it is UNCONDITIONAL assignment, even though we select across multiple variants

            let mut out_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0);
            let mut intermediate_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0);
            let mut of_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false);
            let mut u16_intermedaite_carry_value =
                <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false);

            let imm_low = placer.get_u16(imm_vars[0]);
            let imm = placer.get_u32_from_u16_parts(imm_vars);
            let rs1_low = placer.get_u16_from_u8_parts([rs1_vars[0], rs1_vars[1]]);
            let rs1_u32 = placer.get_u32_from_u8_parts(rs1_vars);
            let rs2_low = placer.get_u16_from_u8_parts([rs2_vars[0], rs2_vars[1]]);
            let rs2_u32 = placer.get_u32_from_u8_parts(rs2_vars);
            let pc_low = placer.get_u16(pc_vars[0]);
            let pc_u32 = placer.get_u32_from_u16_parts(pc_vars);
            let boolean_false = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false);
            let modulus_low =
                <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(F::CHARACTERISTICS as u16);
            let modulus_constant =
                <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(F::CHARACTERISTICS as u32);
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

    // separate constraint for addmod/submod/mulmod. We use intermediate range-checked register to check
    // field element normalization

    {
        // ADDMOD
        {
            cs.add_constraint(
                Constraint::from(is_addmod)
                    * ((Constraint::from(out_low) + shift_term * Term::from(out_high))
                        - (rs1_low_c.clone()
                            + shift_term * rs1_high_c.clone()
                            + rs2_low_c.clone()
                            + shift_term * rs2_high_c.clone())),
            );
            cs.add_constraint(Term::from(is_addmod) * (Term::from(1u32) - Term::from(carry)));
        };

        // SUBMOD
        {
            cs.add_constraint(
                Constraint::from(is_submod)
                    * ((Constraint::from(out_low) + shift_term * Term::from(out_high))
                        - (rs1_low_c.clone() + shift_term * rs1_high_c.clone()
                            - rs2_low_c.clone()
                            - shift_term * rs2_high_c.clone())),
            );
            cs.add_constraint(Term::from(is_submod) * (Term::from(1u32) - Term::from(carry)));
        }

        // MULMOD
        {
            cs.add_constraint(
                (rs1_low_c.clone() + shift_term * rs1_high_c.clone())
                    * (rs2_low_c.clone() + shift_term * rs2_high_c.clone())
                    - Term::from(mulmod_intermediate_var),
            );
            cs.add_constraint(
                Constraint::from(is_mulmod)
                    * ((Constraint::from(out_low) + shift_term * Term::from(out_high))
                        - Term::from(mulmod_intermediate_var)),
            );
            cs.add_constraint(Term::from(is_mulmod) * (Term::from(1u32) - Term::from(carry)));
        }

        // out < modulus, so
        // 2^32*of + out - modulus = tmp
        // and we checked that there is always a borrow in the branches above

        // one constraint to ensure canonical form, and we merge it below with normal addition-like constraint
    }

    // we have just 2 sets of constraints:
    // - one that links register/imm inputs and output
    // - another that enforces reduction for GKR

    // generic constraint for addition-like ops links to RD directly
    {
        let mut add_like_low_constraint = Constraint::empty();
        // rs1
        add_like_low_constraint += Term::from(is_add) * rs1_low_c.clone();
        add_like_low_constraint +=
            Term::from(is_auipc) * Term::from(inputs.cycle_start_state.pc[0]);
        // for subtraction 2^16*of + a - b = c -> 2^16*of + a = b + c
        add_like_low_constraint += Term::from(is_sub) * Term::from(out_low);
        // for modular ops we also do 2^16*of + out - modulus -> intermediate
        add_like_low_constraint +=
            Term::from(is_addmod) * Term::from(intermediate_tmp.0[0].get_variable());
        add_like_low_constraint +=
            Term::from(is_submod) * Term::from(intermediate_tmp.0[0].get_variable());
        add_like_low_constraint +=
            Term::from(is_mulmod) * Term::from(intermediate_tmp.0[0].get_variable());
        // rs2
        // NOTE: for additions we blindly mix imm and rs2 as preprocessing ensures that if imm !=0 then rs2 = x0
        add_like_low_constraint += Term::from(is_add) * rs2_low_c.clone();
        add_like_low_constraint += Term::from(is_add) * Term::from(inputs.decoder_data.imm[0]);
        add_like_low_constraint += Term::from(is_auipc) * Term::from(inputs.decoder_data.imm[0]);
        add_like_low_constraint += Term::from(is_sub) * rs2_low_c.clone();
        add_like_low_constraint += Term::from((modulus_low, is_addmod.expect_variable()));
        add_like_low_constraint += Term::from((modulus_low, is_submod.expect_variable()));
        add_like_low_constraint += Term::from((modulus_low, is_mulmod.expect_variable()));
        // rd
        add_like_low_constraint -= Term::from(is_add) * Term::from(out_low);
        add_like_low_constraint -= Term::from(is_auipc) * Term::from(out_low);
        add_like_low_constraint -= Term::from(is_sub) * rs1_low_c.clone();
        add_like_low_constraint -= Term::from(is_addmod) * Term::from(out_low);
        add_like_low_constraint -= Term::from(is_submod) * Term::from(out_low);
        add_like_low_constraint -= Term::from(is_mulmod) * Term::from(out_low);

        // intermediate carry
        let intermediate_carry_var = intermediate_carry.expect_variable();
        add_like_low_constraint -=
            Term::from(is_add) * Term::from((carry_shift, intermediate_carry_var));
        add_like_low_constraint -=
            Term::from(is_auipc) * Term::from((carry_shift, intermediate_carry_var));
        add_like_low_constraint -=
            Term::from(is_sub) * Term::from((carry_shift, intermediate_carry_var));
        add_like_low_constraint -=
            Term::from(is_addmod) * Term::from((carry_shift, intermediate_carry_var));
        add_like_low_constraint -=
            Term::from(is_submod) * Term::from((carry_shift, intermediate_carry_var));
        add_like_low_constraint -=
            Term::from(is_mulmod) * Term::from((carry_shift, intermediate_carry_var));
        cs.add_constraint(add_like_low_constraint);

        // high part
        let mut add_like_high_constraint = Constraint::empty();
        // intermediate carry
        add_like_high_constraint += Term::from(is_add) * Term::from(intermediate_carry);
        add_like_high_constraint += Term::from(is_auipc) * Term::from(intermediate_carry);
        add_like_high_constraint += Term::from(is_sub) * Term::from(intermediate_carry);
        add_like_high_constraint += Term::from(is_addmod) * Term::from(intermediate_carry);
        add_like_high_constraint += Term::from(is_submod) * Term::from(intermediate_carry);
        add_like_high_constraint += Term::from(is_mulmod) * Term::from(intermediate_carry);
        // rs1
        add_like_high_constraint += Term::from(is_add) * rs1_high_c.clone();
        add_like_high_constraint +=
            Term::from(is_auipc) * Term::from(inputs.cycle_start_state.pc[1]);
        add_like_high_constraint += Term::from(is_sub) * Term::from(out_high);
        add_like_high_constraint +=
            Term::from(is_addmod) * Term::from(intermediate_tmp.0[1].get_variable());
        add_like_high_constraint +=
            Term::from(is_submod) * Term::from(intermediate_tmp.0[1].get_variable());
        add_like_high_constraint +=
            Term::from(is_mulmod) * Term::from(intermediate_tmp.0[1].get_variable());
        // rs2
        // NOTE: for additions we blindly mix imm and rs2 as preprocessing ensures that if imm !=0 then rs2 = x0
        add_like_high_constraint += Term::from(is_add) * rs2_high_c.clone();
        add_like_high_constraint += Term::from(is_add) * Term::from(inputs.decoder_data.imm[1]);
        add_like_high_constraint += Term::from(is_auipc) * Term::from(inputs.decoder_data.imm[1]);
        add_like_high_constraint += Term::from(is_sub) * rs2_high_c.clone();
        add_like_high_constraint += Term::from((modulus_high, is_addmod.expect_variable()));
        add_like_high_constraint += Term::from((modulus_high, is_submod.expect_variable()));
        add_like_high_constraint += Term::from((modulus_high, is_mulmod.expect_variable()));
        // rd
        add_like_high_constraint -= Term::from(is_add) * Term::from(out_high);
        add_like_high_constraint -= Term::from(is_auipc) * Term::from(out_high);
        add_like_high_constraint -= Term::from(is_sub) * rs1_high_c.clone();
        add_like_high_constraint += Term::from(is_addmod) * Term::from(out_high);
        add_like_high_constraint += Term::from(is_submod) * Term::from(out_high);
        add_like_high_constraint += Term::from(is_mulmod) * Term::from(out_high);
        // final carry
        let carry_var = carry.expect_variable();
        add_like_high_constraint -= Term::from(is_add) * Term::from((carry_shift, carry_var));
        add_like_high_constraint -= Term::from(is_auipc) * Term::from((carry_shift, carry_var));
        add_like_high_constraint -= Term::from(is_sub) * Term::from((carry_shift, carry_var));
        add_like_high_constraint -= Term::from(is_addmod) * Term::from((carry_shift, carry_var));
        add_like_high_constraint -= Term::from(is_submod) * Term::from((carry_shift, carry_var));
        add_like_high_constraint -= Term::from(is_mulmod) * Term::from((carry_shift, carry_var));
        cs.add_constraint(add_like_high_constraint);
    }

    // Delegation call
    // We perform formal READ from register with CSR index at rs2 (in preprocessing),
    // and to ensure that it's a permutation and not a memory argument, we do not have inits/teardowns for such
    // registers, and enforce that read timestamps are 0, and read values are 0
    // We also ensure that out value is 0 as from preprocessing rd = x0
    {
        // delegation register value
        cs.add_constraint(Term::from(is_delegation_call) * rs2_low_c.clone());
        cs.add_constraint(Term::from(is_delegation_call) * rs2_high_c.clone());
        // read timestamp
        cs.add_constraint(Term::from(is_delegation_call) * Term::from(rs2_read_timestamp[0]));
        cs.add_constraint(Term::from(is_delegation_call) * Term::from(rs2_read_timestamp[1]));
        // out value
        cs.add_constraint(Term::from(is_delegation_call) * Term::from(rd_write_limbs[0]));
        cs.add_constraint(Term::from(is_delegation_call) * Term::from(rd_write_limbs[1]));
    }

    // Non-determinism - actually we do not have ANY constraint on RD value, other than range checks
    // done above for generic consistency
}
