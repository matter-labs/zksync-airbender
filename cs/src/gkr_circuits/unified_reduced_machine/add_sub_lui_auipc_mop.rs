use super::*;
use crate::cs::circuit_trait::*;
use crate::gkr_circuits::add_sub_family::AddSubLuiAuipcMopFamilyCircuitMask;
use crate::gkr_circuits::utils::{montgomery_product_expr, update_intermediate_carry_value};
use crate::oracle::Placeholder;
use crate::structured_expr::Expr;
use crate::types::*;
use crate::witness_placer::*;
use field::PrimeField;

use super::circuit::F1_SCRATCH_BOOLS;

fn word_from_u16_limbs_expr<F: PrimeField>(limbs: [Variable; 2], limb_shift: F) -> Expr<F> {
    Expr::var(limbs[0]) + Expr::var(limbs[1]) * limb_shift
}

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
    rd_read_limbs: [Variable; 2],
    rs2_read_timestamp: [Variable; common_constants::NUM_TIMESTAMP_COLUMNS_FOR_RAM],
    // Shared 16-bit-RC scratch Register for the modular-ops intermediate
    intermediate_tmp: Register<F>,
    // Shared scratch-Boolean pool slots [0],[1] = carry / intermediate_carry.
    of_slots: [Boolean; F1_SCRATCH_BOOLS],
) {
    // NOTE: by preprocessing if we have rd == 0 in any of the opcodes below, then
    // we have rs1 = x0, rs2 = x0 and imm = 0, and it's preprocessed into plain addition,
    // so we do NOT need to mask rd value

    let modulus_low = F::from_u32_unchecked((F::CHARACTERISTICS as u16) as u32);
    let modulus_high = F::from_u32_unchecked(((F::CHARACTERISTICS >> 16) as u16) as u32);

    let carry_shift = F::from_u32_with_reduction(1 << 16);

    // U16 low/high limb views of rs1/rs2, reassembled as `Expr` from the 4 committed U8 bytes
    let byte_shift = F::from_u32_unchecked(1 << 8);
    let rs1_low_e: Expr<F> = Expr::var(rs1_limbs[0]) + Expr::var(rs1_limbs[1]) * byte_shift;
    let rs1_high_e: Expr<F> = Expr::var(rs1_limbs[2]) + Expr::var(rs1_limbs[3]) * byte_shift;
    let rs2_low_e: Expr<F> = Expr::var(rs2_limbs[0]) + Expr::var(rs2_limbs[1]) * byte_shift;
    let rs2_high_e: Expr<F> = Expr::var(rs2_limbs[2]) + Expr::var(rs2_limbs[3]) * byte_shift;

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
    let is_fmamod = decoder.perform_fmamod();
    let is_delegation_call = decoder.perform_delegation_call();
    let is_non_determinism_read = decoder.perform_non_determinism_read();

    let carry = of_slots[0];
    let intermediate_carry = of_slots[1];
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
        let rd_read_vars = rd_read_limbs;

        let is_add_var = is_add.expect_variable();
        let is_sub_var = is_sub.expect_variable();
        let is_auipc_var = is_auipc.expect_variable();
        let is_addmod_var = is_addmod.expect_variable();
        let is_submod_var = is_submod.expect_variable();
        let is_mulmod_var = is_mulmod.expect_variable();
        let is_fmamod_var = is_fmamod.expect_variable();
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

            // rs1/rs2 are reused value-domain by addmod/submod below; clone the raw words so the
            // mop product (which needs them in raw-repr form) can still decode them.
            let rs1_f =
                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::from_integer(
                    rs1_u32.clone(),
                );
            let rs2_f =
                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::from_integer(
                    rs2_u32.clone(),
                );
            let rd_read_u32 = placer.get_u32_from_u16_parts(rd_read_vars);

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
            // mulmod / fmamod - both final and intermediate var (unconditional)
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

            let is_f1_active = {
                let mut m = placer.get_boolean(is_add_var);
                m = m.or(&placer.get_boolean(is_sub_var));
                m = m.or(&placer.get_boolean(is_auipc_var));
                m = m.or(&placer.get_boolean(is_addmod_var));
                m = m.or(&placer.get_boolean(is_submod_var));
                m = m.or(&placer.get_boolean(is_mulmod_var));
                m = m.or(&placer.get_boolean(is_fmamod_var));
                m
            };
            placer.conditionally_assign_u32(intermediate_vars, &is_f1_active, &intermediate_value);
            placer.conditionally_assign_mask(of_var, &is_f1_active, &of_value);
            placer.conditionally_assign_mask(
                intermediate_of_var,
                &is_f1_active,
                &u16_intermedaite_carry_value,
            );
        };
        cs.set_values(value_fn);
    }

    // separate constraints for addmod/submod/mulmod/fmamod, mirroring the standalone
    // `add_sub_family` inner. All opcode flags are disjoint, so we gate with simple sums.
    let is_modular = Expr::<F>::Sum(vec![
        Expr::from(is_addmod),
        Expr::from(is_submod),
        Expr::from(is_mulmod),
        Expr::from(is_fmamod),
    ]);

    {
        let rs1 = rs1_low_e.clone() + rs1_high_e.clone() * carry_shift;
        let rs2 = rs2_low_e.clone() + rs2_high_e.clone() * carry_shift;
        let rd_read = word_from_u16_limbs_expr(rd_read_limbs, carry_shift);
        let out = word_from_u16_limbs_expr([out_low, out_high], carry_shift);

        // MULMOD: use intermediate variable, and mix-in the FMA addend.
        // rs1*rs2*R⁻¹ + is_fmamod*rd_old = mulmod_intermediate.
        cs.add_constraint_expr(
            montgomery_product_expr(rs1.clone(), rs2.clone())
                + rd_read * Expr::var(is_fmamod.expect_variable())
                - Expr::var(mulmod_intermediate_var),
        );

        // enforce field ops - all at once, as we know that flags are disjoint
        let is_mul_like = Expr::<F>::Sum(vec![Expr::from(is_mulmod), Expr::from(is_fmamod)]);
        cs.add_constraint_expr(
            (out.clone() - (rs1.clone() + rs2.clone())).mask(is_addmod)
                + (out.clone() - (rs1.clone() - rs2)).mask(is_submod)
                + (out - Expr::var(mulmod_intermediate_var)) * is_mul_like,
        );

        // check normalization: borrow on (out - modulus) must be 1, i.e. out < modulus
        cs.add_constraint_expr((Expr::<F>::one() - Expr::from(carry)) * is_modular.clone());
    }

    // two linking constraints: register/imm inputs ↔ output, one linear equation per limb,
    // masked by each opcode's family bit and summed (flags are disjoint).
    {
        let intermediate_carry_var = intermediate_carry.expect_variable();
        let carry_var = carry.expect_variable();

        // low limb
        // ADD/ADDI/LUI: rs1 + rs2 + imm - rd - 2^16 * intermediate_carry
        let eq_add_low =
            rs1_low_e.clone() + rs2_low_e.clone() + Expr::var(inputs.decoder_data.imm[0])
                - Expr::var(out_low)
                - Expr::var(intermediate_carry_var) * carry_shift;
        // AUIPC: pc + imm (no rs1/rs2)
        let eq_auipc_low = Expr::var(inputs.cycle_start_state.pc[0])
            + Expr::var(inputs.decoder_data.imm[0])
            - Expr::var(out_low)
            - Expr::var(intermediate_carry_var) * carry_shift;
        // SUB rearranged: 2^16*of + out + rs2 - rs1
        let eq_sub_low = Expr::var(out_low) + rs2_low_e.clone()
            - rs1_low_e.clone()
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
            + rs1_high_e.clone()
            + rs2_high_e.clone()
            + Expr::var(inputs.decoder_data.imm[1])
            - Expr::var(out_high)
            - Expr::var(carry_var) * carry_shift;
        let eq_auipc_high = Expr::<F>::from(intermediate_carry)
            + Expr::var(inputs.cycle_start_state.pc[1])
            + Expr::var(inputs.decoder_data.imm[1])
            - Expr::var(out_high)
            - Expr::var(carry_var) * carry_shift;
        let eq_sub_high =
            Expr::<F>::from(intermediate_carry) + Expr::var(out_high) + rs2_high_e.clone()
                - rs1_high_e.clone()
                - Expr::var(carry_var) * carry_shift;
        // modular ops subtract out_high (the canonical reduction; the earlier `+ out_high` was a
        // latent sign bug, fixed in lockstep with the standalone `eq_modular_high`).
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
        // delegation register value (rs2) = 0
        cs.add_constraint_expr(rs2_low_e.clone().mask(is_delegation_call));
        cs.add_constraint_expr(rs2_high_e.clone().mask(is_delegation_call));
        // read timestamp = 0
        cs.add_constraint_expr(Expr::var(rs2_read_timestamp[0]).mask(is_delegation_call));
        cs.add_constraint_expr(Expr::var(rs2_read_timestamp[1]).mask(is_delegation_call));
        // out value = 0 (rd = x0 by preprocessing)
        cs.add_constraint_expr(Expr::var(rd_write_limbs[0]).mask(is_delegation_call));
        cs.add_constraint_expr(Expr::var(rd_write_limbs[1]).mask(is_delegation_call));
    }

    // Non-determinism - actually we do not have ANY constraint on RD value, other than range checks
    // done above for generic consistency
}
