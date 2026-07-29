use super::*;
use crate::cs::circuit_trait::*;
use crate::gkr_circuits::add_sub_family::AddSubLuiAuipcMopFamilyCircuitMask;
use crate::gkr_circuits::utils::{
    montgomery_product_expr, mop_two_field_decompose, update_intermediate_carry_value,
};
use crate::oracle::Placeholder;
use crate::structured_expr::Expr;
use crate::types::*;
use crate::witness_placer::*;
use field::PrimeField;

use super::circuit::{F1_SCRATCH_BOOLS, F1_SCRATCH_VARS};

fn word_from_u16_limbs_expr<F: PrimeField>(limbs: [Variable; 2], limb_shift: F) -> Expr<F> {
    Expr::var(limbs[0]) + Expr::var(limbs[1]) * limb_shift
}

/// Family 1 (add_sub/lui/auipc/mop) constraints for the unified circuit.
/// Mirrors the standalone inner (`add_sub_family`), adapted to take
/// pre-allocated rs1/rs2 U8 byte limbs from the unified body instead of
/// requesting memory accesses internally. Non-Family-1 cycles have all
/// `decoder.perform_*()` Booleans = 0 so every constraint here is multiplied
/// by 0 and is trivially satisfied.
///
/// `MopF` is the field the `mop.rr` family operates over. When `F != MopF`
/// (`two_field`) the mop.rr modulus is sourced from `MopF` and mulmod/fmamod are
/// enforced by the unconditional integer-decomposition relation
/// `x·y + is_fma·d·R̂ + Ĉp̂ − q̂·p̂ − m·R̂ = 0` (a spectator on non-mul rows, where
/// the fully `is_mul_like`-masked `q̂` collapses to 0 and pins `m` to a fixed field
/// value); when `F == MopF` the previous single-field native path is taken unchanged.
/// The discriminator is a `TypeId` comparison. Because `q̂` is masked in full, the
/// quotient limbs and q-top/k bits are committed as *shared scratch pool* slots
/// (0 dedicated columns) rather than dedicated columns
#[expect(clippy::too_many_arguments)]
pub fn apply_unified_add_sub_lui_auipc_mop_inner<
    F: PrimeField,
    MopF: PrimeField,
    CS: Circuit<F>,
>(
    cs: &mut CS,
    inputs: OpcodeFamilyCircuitState<F>,
    decoder: AddSubLuiAuipcMopFamilyCircuitMask,
    tri_add: Boolean,
    rs1_limbs: [Variable; 2],
    rs2_limbs: [Variable; 2],
    rd_write_limbs: [Variable; 2],
    rd_read_limbs: [Variable; 2],
    rs2_read_timestamp: [Variable; common_constants::NUM_TIMESTAMP_COLUMNS_FOR_RAM],
    // Shared 16-bit-RC scratch Register for the modular-ops intermediate
    intermediate_tmp: Register<F>,
    // Shared scratch-Boolean pool slots [0],[1] = carry / intermediate_carry.
    of_slots: [Boolean; F1_SCRATCH_BOOLS],
    var_slots: [Variable; F1_SCRATCH_VARS],
) {
    // NOTE: by preprocessing if we have rd == 0 in any of the opcodes below, then
    // we have rs1 = x0, rs2 = x0 and imm = 0, and it's preprocessed into plain addition,
    // so we do NOT need to mask rd value

    let two_field = std::any::TypeId::of::<F>() != std::any::TypeId::of::<MopF>();
    if two_field {
        assert!(
            F::CHAR_BITS >= 68,
            "circuit field too small for two-field mop"
        );
        assert!(
            MopF::IS_MONT_REPR,
            "mop.rr opcodes field must be in Montgomery representation"
        );
    }

    let modulus_low = F::from_u32_unchecked((MopF::CHARACTERISTICS_U32 as u16) as u32);
    let modulus_high = F::from_u32_unchecked(((MopF::CHARACTERISTICS_U32 >> 16) as u16) as u32);

    let carry_shift = F::from_u32_with_reduction(1 << 16);

    // U16 low/high limb views of rs1/rs2 — the committed read limbs directly.
    let rs1_low_e: Expr<F> = Expr::var(rs1_limbs[0]);
    let rs1_high_e: Expr<F> = Expr::var(rs1_limbs[1]);
    let rs2_low_e: Expr<F> = Expr::var(rs2_limbs[0]);
    let rs2_high_e: Expr<F> = Expr::var(rs2_limbs[1]);

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
    let is_tri_add = tri_add;
    let tri_clo_b = of_slots[2];
    let tri_chi_b = of_slots[3];
    let mulmod_intermediate_var = cs.add_named_variable("MULMOD intermediate value");

    let (q_lo16_var, q_hi16_var, t_bit_vars) = if two_field {
        let q_lo16 = var_slots[0];
        let q_hi16 = var_slots[1];
        cs.require_invariant(q_lo16, Invariant::RangeChecked { width: 16 });
        cs.require_invariant(q_hi16, Invariant::RangeChecked { width: 16 });
        // Booleanity already holds pool-wide (the pool allocates these as Booleans), so we
        // reuse the slots' variables directly rather than re-declaring Boolean columns.
        let t0 = of_slots[2].expect_variable();
        let t1 = of_slots[3].expect_variable();
        let t2 = of_slots[4].expect_variable();
        (Some(q_lo16), Some(q_hi16), Some([t0, t1, t2]))
    } else {
        (None, None, None)
    };

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
        let is_tri_add_var = is_tri_add.expect_variable();
        let tri_clo_b_var = tri_clo_b.expect_variable();
        let tri_chi_b_var = tri_chi_b.expect_variable();

        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            // NOTE: it is UNCONDITIONAL assignment, even though we select across multiple variants

            let mut out_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0);
            let mut intermediate_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0);
            let mut of_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false);
            let mut u16_intermedaite_carry_value =
                <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false);
            // tri-add second-Boolean carries (low/high limb); set only on tri-add rows.
            let mut tri_clo_b_value =
                <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false);
            let mut tri_chi_b_value =
                <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false);
            let mut mop_t_values = [
                <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false),
                <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false),
                <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false),
            ];
            let mut writes_q_k_mask =
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
                MopF::CHARACTERISTICS_U32 as u16,
            );
            let modulus_constant =
                <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(MopF::CHARACTERISTICS_U32);
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

            // Two-field mop.rr decomposition: computed ONCE per row when F ≠ MopF.
            // Feeds addmod (`out_add`/`k_add`), submod (`out_sub`/`k_sub`) and mulmod/fmamod
            // (`m_int`/`m_field`/`q`) below. `None` on the native path (all row classes disjoint).
            let two_field_dec = if two_field {
                let is_mulmod_m = placer.get_boolean(is_mulmod_var);
                let is_fmamod_m = placer.get_boolean(is_fmamod_var);
                let is_mul_like_m = is_mulmod_m.or(&is_fmamod_m);
                Some(mop_two_field_decompose::<F, MopF, CS::WitnessPlacer>(
                    &rs1_u32,
                    &rs2_u32,
                    &rd_read_u32,
                    &is_fmamod_m,
                    &is_mul_like_m,
                ))
            } else {
                None
            };

            // addmod
            {
                let is_addmod = placer.get_boolean(is_addmod_var);
                let addmod_result = if let Some(dec) = &two_field_dec {
                    dec.out_add.clone()
                } else {
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
                let submod_result = if let Some(dec) = &two_field_dec {
                    dec.out_sub.clone()
                } else {
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

                let mulmod_result = if let Some(dec) = &two_field_dec {
                    dec.m_int.clone()
                } else {
                    let op1 = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::from_raw_repr_with_reduction(
                        rs1_u32,
                    );
                    let op2 = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::from_raw_repr_with_reduction(
                        rs2_u32,
                    );
                    let rd_raw = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::from_raw_repr_with_reduction(
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
                    mulmod_result
                };
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
            if let Some(dec) = &two_field_dec {
                let is_addmod_m = placer.get_boolean(is_addmod_var);
                let is_submod_m = placer.get_boolean(is_submod_var);
                let is_mulmod_m = placer.get_boolean(is_mulmod_var);
                let is_fmamod_m = placer.get_boolean(is_fmamod_var);
                let is_mul_like_m = is_mulmod_m.or(&is_fmamod_m);
                let writes_q_k = is_mul_like_m.or(&is_addmod_m).or(&is_submod_m);

                placer.conditionally_assign_u16(q_lo16_var.unwrap(), &is_mul_like_m, &dec.q_lo16);
                placer.conditionally_assign_u16(q_hi16_var.unwrap(), &is_mul_like_m, &dec.q_hi16);

                #[expect(clippy::needless_range_loop)]
                for i in 0..3 {
                    let mut ti = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false);
                    ti = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                        &is_mul_like_m,
                        &dec.q_top_bits[i],
                        &ti,
                    );
                    ti = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                        &is_addmod_m,
                        &dec.k_add_bits[i],
                        &ti,
                    );
                    ti = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                        &is_submod_m,
                        &dec.k_sub_bits[i],
                        &ti,
                    );
                    mop_t_values[i] = ti;
                }
                writes_q_k_mask = writes_q_k;

                placer.assign_field(mulmod_intermediate_var, &dec.m_field);
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
            // tri-add (unified-only): rd = rs1 + rs2 + rd_old (wrapping u32)
            {
                let is_tri_add = placer.get_boolean(is_tri_add_var);
                let rs1_high = placer.get_u16(rs1_vars[1]);
                let rs2_high = placer.get_u16(rs2_vars[1]);
                let rd_old_low = placer.get_u16(rd_read_vars[0]);
                let rd_old_high = placer.get_u16(rd_read_vars[1]);
                // Re-fetch rs1/rs2 as u32: the earlier mulmod/fmamod block consumes the outer
                // `rs1_u32`/`rs2_u32` by value, so they're unavailable here.
                let rs1_u32 = placer.get_u32_from_u16_parts(rs1_vars);
                let rs2_u32 = placer.get_u32_from_u16_parts(rs2_vars);
                let rd_old_u32 = placer.get_u32_from_u16_parts(rd_read_vars);

                // output = rs1 + rs2 + rd_old (mod 2^32)
                let (sum01, _) = rs1_u32.overflowing_add(&rs2_u32);
                let (tri_out, _) = sum01.overflowing_add(&rd_old_u32);
                out_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                    &is_tri_add,
                    &tri_out,
                    &out_value,
                );

                // low-limb carry = clo_a + clo_b: two chained 16-bit add carries provably sum to
                // floor((rs1_low + rs2_low + rd_old_low) / 2^16) ∈ {0,1,2}.
                let (s1, clo_a) = rs1_low.overflowing_add(&rs2_low);
                let (_lo, clo_b) = s1.overflowing_add(&rd_old_low);

                // high-limb carry = chi_a + chi_b, folding the low carry-in (clo_a, clo_b) as two
                // 1-bit carries. The three high-limb carries j1,j2,j3 sum to the true high carry
                // ∈ {0,1,2} (cannot be 3), so encode chi_a = (carry≥1) = j1|j2|j3 and
                // chi_b = (carry≥2) = at-least-two-of(j1,j2,j3).
                let zero_u16 = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(0u16);
                let (u1, j1) = rs1_high.overflowing_add(&rs2_high);
                let (u2, j2) = u1.overflowing_add_with_carry(&rd_old_high, &clo_a);
                let (_hi, j3) = u2.overflowing_add_with_carry(&zero_u16, &clo_b);
                let chi_a = j1.or(&j2).or(&j3);
                let chi_b = j1.and(&j2).or(&j1.and(&j3)).or(&j2.and(&j3));

                of_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                    &is_tri_add,
                    &chi_a,
                    &of_value,
                );
                u16_intermedaite_carry_value =
                    <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                        &is_tri_add,
                        &clo_a,
                        &u16_intermedaite_carry_value,
                    );
                tri_clo_b_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                    &is_tri_add,
                    &clo_b,
                    &tri_clo_b_value,
                );
                tri_chi_b_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                    &is_tri_add,
                    &chi_b,
                    &tri_chi_b_value,
                );
            }

            let is_f1_active = {
                let mut m = placer.get_boolean(is_add_var);
                m = m.or(&placer.get_boolean(is_sub_var));
                m = m.or(&placer.get_boolean(is_auipc_var));
                m = m.or(&placer.get_boolean(is_addmod_var));
                m = m.or(&placer.get_boolean(is_submod_var));
                m = m.or(&placer.get_boolean(is_mulmod_var));
                m = m.or(&placer.get_boolean(is_fmamod_var));
                m = m.or(&placer.get_boolean(is_tri_add_var));
                m
            };
            // actually assign if we are in debug modes
            if !CS::ASSUME_MEMORY_VALUES_ASSIGNED {
                placer.conditionally_assign_u32(out_vars, &is_f1_active, &out_value);
            }
            placer.conditionally_assign_u32(intermediate_vars, &is_f1_active, &intermediate_value);
            placer.conditionally_assign_mask(of_var, &is_f1_active, &of_value);
            placer.conditionally_assign_mask(
                intermediate_of_var,
                &is_f1_active,
                &u16_intermedaite_carry_value,
            );
            let is_tri_add_m = placer.get_boolean(is_tri_add_var);
            if two_field {
                let merged_mask = is_tri_add_m.or(&writes_q_k_mask);
                let v_lo = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                    &is_tri_add_m,
                    &tri_clo_b_value,
                    &mop_t_values[0],
                );
                placer.conditionally_assign_mask(tri_clo_b_var, &merged_mask, &v_lo);
                let v_hi = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                    &is_tri_add_m,
                    &tri_chi_b_value,
                    &mop_t_values[1],
                );
                placer.conditionally_assign_mask(tri_chi_b_var, &merged_mask, &v_hi);
                // Slot [4] = t2: mop path only (no tri-add write), single write.
                let [_, _, t2_var] = t_bit_vars.unwrap();
                placer.conditionally_assign_mask(t2_var, &writes_q_k_mask, &mop_t_values[2]);
            } else {
                placer.conditionally_assign_mask(tri_clo_b_var, &is_tri_add_m, &tri_clo_b_value);
                placer.conditionally_assign_mask(tri_chi_b_var, &is_tri_add_m, &tri_chi_b_value);
            }
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
        if two_field {
            // Montgomery-aware two-field decomposition: ONE UNCONDITIONAL
            // degree-2 constraint over the circuit field F,
            //   x·y + is_fma·d·R + C·p − q·p − m·R = 0,
            // with x = rs1, y = rs2, d = rd_read (fma addend), m = mulmod_intermediate_var, and
            // C = R = 2^32.
            //
            // RANGE SOUNDNESS/COMPLETENESS with NON-CANONICAL operands. rs1, rs2 and (fma) rd_read
            // are register words that may be ANY u32 — mop.rr accepts non-reduced inputs (possibly
            // ≥ MopF::CHAR, but ≤ u32::MAX). The quotient is committed as
            //   q̂ = q_lo16 + q_hi16·2^16 + k·2^32,  q_lo16,q_hi16 ∈ [0,2^16) (16-bit RC),
            //   k = t0 + 2·t1 + 4·t2 ∈ [0,8) (3 Booleans),  ⇒ q̂ ∈ [0, 8·2^32).
            // From q̂·p = x·y + is_fma·d·R̂ + R̂·p̂ − m·R̂ with the reduced output m ∈ [0,p), q̂ is
            // maximized at m = 0, x = y = d = u32::MAX, is_fma = 1. That maximum MUST fit the
            // representable range, else an honest prover cannot commit the quotient and the mul/fma
            // row becomes unsatisfiable (completeness break). Assert it, so a smaller MopF or a
            // wider Montgomery R can never silently violate the 2×16-bit-limb + 3-bit-k budget.
            // (Soundness — no wraparound of the degree-2 relation mod F — is covered separately by
            // the `F::CHAR_BITS >= 68` assert above: the largest term q̂·p̂ is < 8·2^32·p < 2^66 < F.)
            {
                let r: u128 = 1u128 << 32;
                let p: u128 = MopF::CHARACTERISTICS_U32 as u128;
                let max_quotient_numerator =
                    (u32::MAX as u128) * (u32::MAX as u128) + (u32::MAX as u128) * r + r * p;
                assert!(
                    max_quotient_numerator < (8u128 << 32) * p,
                    "mulmod/fmamod quotient q̂ (2×16-bit limbs + 3-bit k, range [0, 8·2^32)) is too \
                     narrow to represent the max quotient for non-canonical u32 inputs"
                );
            }
            let r_hat = F::from_u128_with_reduction(1u128 << 32);
            let p_hat = F::from_u32_with_reduction(MopF::CHARACTERISTICS_U32);
            let cp_hat =
                F::from_u128_with_reduction((1u128 << 32) * (MopF::CHARACTERISTICS_U32 as u128));

            let q_lo16_var = q_lo16_var.unwrap();
            let q_hi16_var = q_hi16_var.unwrap();
            let [t0, t1, t2] = t_bit_vars.unwrap();

            let is_mul_like_e = Expr::from(is_mulmod) + Expr::from(is_fmamod);
            let k_expr = Expr::var(t0)
                + Expr::var(t1) * F::from_u32_with_reduction(2)
                + Expr::var(t2) * F::from_u32_with_reduction(4);
            let q_low_limbs = Expr::var(q_lo16_var) + Expr::var(q_hi16_var) * carry_shift;
            let q_expr = (q_low_limbs + k_expr * r_hat) * is_mul_like_e;

            cs.add_constraint_expr(
                rs1.clone() * rs2.clone()
                    + Expr::from(is_fmamod) * rd_read.clone() * r_hat
                    + Expr::constant(cp_hat)
                    - q_expr * p_hat
                    - Expr::var(mulmod_intermediate_var) * r_hat,
            );
        } else {
            cs.add_constraint_expr(
                montgomery_product_expr(rs1.clone(), rs2.clone())
                    + rd_read * Expr::var(is_fmamod.expect_variable())
                    - Expr::var(mulmod_intermediate_var),
            );
        }

        // enforce field ops - all at once, as we know that flags are disjoint
        let is_mul_like = Expr::<F>::Sum(vec![Expr::from(is_mulmod), Expr::from(is_fmamod)]);
        let mul_term = (out.clone() - Expr::var(mulmod_intermediate_var)) * is_mul_like;
        if two_field {
            // addmod/submod over the non-native field with NON-CANONICAL operands (rs1, rs2 any
            // u32, possibly ≥ MopF::CHAR). The reduction count `k = t0 + 2·t1 + 4·t2` shares the
            // same 3 Boolean slots as the mul quotient's top bits, so k ∈ [0,8), and the output is
            // pinned canonical (out is 2×16-bit range-checked AND the `carry == 1` normalization
            // forces out < p). For the honest witness to fit that 3-bit budget:
            //   * addmod: out = rs1 + rs2 − k·p, so k = (rs1+rs2−out)/p ≤ (rs1+rs2)/p. Worst case
            //     rs1 = rs2 = 2^32−1 ⇒ k ≤ ⌊2·(2^32−1)/p⌋; require 2·(2^32−1) < 7·p ⇒ k ≤ 4 < 8.
            //   * submod: out = rs1 − rs2 + 3p − k·p. The +3p keeps the value non-negative for the
            //     worst borrow rs1 = 0, rs2 = 2^32−1 (needs 3p > 2^32−1), and bounds
            //     k = (rs1−rs2+3p−out)/p ≤ (2^32−1)/p + 3 < 6 < 8 under the same u32::MAX < 3p.
            // Assert both so a smaller MopF can never overflow the shared 3-bit k / break canonicity.
            assert!(((1u64 << 32) - 1) * 2 < (MopF::CHARACTERISTICS_U32 as u64) * 7);
            assert!((u32::MAX as u64) < (MopF::CHARACTERISTICS_U32 as u64) * 3);

            let [t0, t1, t2] = t_bit_vars.unwrap();
            let k_expr = Expr::var(t0)
                + Expr::var(t1) * F::from_u32_with_reduction(2)
                + Expr::var(t2) * F::from_u32_with_reduction(4);
            let p_hat = F::from_u32_with_reduction(MopF::CHARACTERISTICS_U32);
            let three_p_hat =
                F::from_u128_with_reduction(3u128 * (MopF::CHARACTERISTICS_U32 as u128));
            let k_p = k_expr * p_hat;
            let addmod_term =
                (rs1.clone() + rs2.clone() - k_p.clone() - out.clone()).mask(is_addmod);
            let submod_term =
                (rs1.clone() - rs2.clone() + Expr::constant(three_p_hat) - k_p - out.clone())
                    .mask(is_submod);
            cs.add_constraint_expr(addmod_term + submod_term + mul_term);
        } else {
            cs.add_constraint_expr(
                (out.clone() - (rs1.clone() + rs2.clone())).mask(is_addmod)
                    + (out.clone() - (rs1.clone() - rs2.clone())).mask(is_submod)
                    + mul_term,
            );
        }

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

        // tri-add (unified-only): rd = rs1 + rs2 + rd_old (wrapping u32), per-16-bit-limb.
        // Each limb carry ∈ {0,1,2} is encoded as a sum of two Booleans (chained-Boolean
        // carries): low = intermediate_carry (of_slots[1]) + tri_clo_b (of_slots[2]),
        // high = carry (of_slots[0]) + tri_chi_b (of_slots[3]); out limbs are 16-bit
        // range-checked, so each limb equation uniquely determines (out, carry) and the
        // discarded top carry realises the mod-2^32 wrap. Folded into the family
        // select-then-sum below as a 5th masked branch; idle when is_tri_add = 0.
        // NOTE: unlike the former standalone is_tri_add-gated constraints, the folded
        // form is sound only if the F1 flags are mutually exclusive (a two-flag row could
        // satisfy the sum with eq_add = -eq_tri). Exclusivity is enforced by the global
        // family dispatch one-hot in circuit.rs (execute · Σ all family bits ∈ {0,1}, plus
        // padding zeroing) and by the decoder ROM binding the packed bitmask atomically per
        // instruction — the same invariants the F3 exclusivity deletion relies on.
        let rd_old_low_e = Expr::var(rd_read_limbs[0]);
        let rd_old_high_e = Expr::var(rd_read_limbs[1]);
        let tri_clo = Expr::<F>::from(intermediate_carry) + Expr::<F>::from(tri_clo_b);
        let tri_chi = Expr::<F>::from(carry) + Expr::<F>::from(tri_chi_b);
        let eq_tri_low = rs1_low_e.clone() + rs2_low_e.clone() + rd_old_low_e
            - Expr::var(out_low)
            - tri_clo.clone() * carry_shift;

        cs.add_constraint_expr(Expr::Sum(vec![
            eq_add_low.mask(is_add),
            eq_auipc_low.mask(is_auipc),
            eq_sub_low.mask(is_sub),
            eq_modular_low * is_modular.clone(),
            eq_tri_low.mask(is_tri_add),
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

        // tri-add high limb: carry-in = tri_clo (the low limb's 2-bit carry), carry-out = tri_chi.
        let eq_tri_high = tri_clo + rs1_high_e.clone() + rs2_high_e.clone() + rd_old_high_e
            - Expr::var(out_high)
            - tri_chi * carry_shift;

        cs.add_constraint_expr(Expr::Sum(vec![
            eq_add_high.mask(is_add),
            eq_auipc_high.mask(is_auipc),
            eq_sub_high.mask(is_sub),
            eq_modular_high * is_modular,
            eq_tri_high.mask(is_tri_add),
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
