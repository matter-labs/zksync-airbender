use super::*;
use crate::concrete::VERIFIER_COMPILED_LAYOUT;

pub(crate) unsafe fn precompute_for_consistency_checks(
    skeleton: &ProofSkeletonInstance,
    deep_poly_alpha: &Mersenne31Quartic,
    powers_of_deep_quotient_challenge: &mut [Mersenne31Quartic;
             NUM_OPENINGS_AT_Z + NUM_OPENINGS_AT_Z_OMEGA],
) -> (Mersenne31Quartic, Mersenne31Quartic) {
    let mut precompute_with_evals_at_z = Mersenne31Quartic::ZERO;
    let mut precompute_with_evals_at_z_omega = Mersenne31Quartic::ZERO;
    let mut current = Mersenne31Quartic::ONE;
    let mut i = 0;
    for eval_at_z in skeleton.openings_at_z.iter() {
        *powers_of_deep_quotient_challenge.get_unchecked_mut(i) = current;
        i += 1;
        let mut t = current;
        t.mul_assign(&eval_at_z);
        precompute_with_evals_at_z.add_assign(&t);
        current.mul_assign(&deep_poly_alpha);
    }
    for eval_at_z_omega in skeleton.openings_at_z_omega.iter() {
        *powers_of_deep_quotient_challenge.get_unchecked_mut(i) = current;
        i += 1;
        let mut t = current;
        t.mul_assign(&eval_at_z_omega);
        precompute_with_evals_at_z_omega.add_assign(&t);
        current.mul_assign(&deep_poly_alpha);
    }

    (precompute_with_evals_at_z, precompute_with_evals_at_z_omega)
}

pub(crate) unsafe fn precompute_for_consistency_checks_with_fma(
    skeleton: &ProofSkeletonInstance,
    deep_poly_alpha: &Mersenne31Quartic,
    extra_factor_for_accumulation_at_z_omega: &mut Mersenne31Quartic,
) -> (Mersenne31Quartic, Mersenne31Quartic) {
    // here we should inverse the Horner rule (walk backwards)
    let num_evals_at_z = skeleton.openings_at_z.len();

    // our FMA is a*b + c -> a, so our best strategy with least copies is to
    // start from the very end, keep current value in `a`, and then scale it by challenge and
    // add the new value. Last iteration will need to be placed out of the loop

    let mut i = num_evals_at_z;
    let mut precompute_with_evals_at_z = core::hint::black_box(Mersenne31Quartic::ZERO);
    while i > 0 {
        i -= 1;
        let eval_to_add = skeleton.openings_at_z.get_unchecked(i);
        Mersenne31Quartic::fused_mul_add_assign(
            &mut precompute_with_evals_at_z,
            deep_poly_alpha,
            eval_to_add,
        );
    }

    let mut i = skeleton.openings_at_z_omega.len();
    let mut precompute_with_evals_at_z_omega = core::hint::black_box(Mersenne31Quartic::ZERO);
    while i > 0 {
        i -= 1;
        let eval_to_add = skeleton.openings_at_z_omega.get_unchecked(i);
        Mersenne31Quartic::fused_mul_add_assign(
            &mut precompute_with_evals_at_z_omega,
            deep_poly_alpha,
            eval_to_add,
        );
    }

    // multiply by extra power
    *extra_factor_for_accumulation_at_z_omega = deep_poly_alpha.pow_with_fma(num_evals_at_z as u32);
    precompute_with_evals_at_z_omega
        .mul_assign_with_fma(&*extra_factor_for_accumulation_at_z_omega);

    (precompute_with_evals_at_z, precompute_with_evals_at_z_omega)
}

pub(crate) unsafe fn accumulate_over_row_for_consistency_check(
    precompute_with_evals_at_z: Mersenne31Quartic,
    precompute_with_evals_at_z_omega: Mersenne31Quartic,
    query: &QueryValuesInstance,
    powers_of_deep_quotient_challenge: &[Mersenne31Quartic;
         NUM_OPENINGS_AT_Z + NUM_OPENINGS_AT_Z_OMEGA],
    divisor_for_z: &Mersenne31Quartic,
    divisor_for_z_omega: &Mersenne31Quartic,
    tau_in_domain_by_half: &Mersenne31Complex,
    tau_in_domain_by_half_inversed: &Mersenne31Complex,
) -> Mersenne31Quartic {
    // now we can do consistency check
    let mut accumulated_at_z = Mersenne31Quartic::ZERO;

    // setup, then witness, then memory, then stage 2 base, then stage 2 ext, then quotient
    let mut i = 0;
    for leaf_el in query.setup_leaf.iter() {
        let mut t = *powers_of_deep_quotient_challenge.get_unchecked(i);
        i += 1;
        t.mul_assign_by_base(leaf_el);
        accumulated_at_z.add_assign(&t);
    }

    for leaf_el in query.witness_leaf.iter() {
        let mut t = *powers_of_deep_quotient_challenge.get_unchecked(i);
        i += 1;
        t.mul_assign_by_base(leaf_el);
        accumulated_at_z.add_assign(&t);
    }

    for leaf_el in query.memory_leaf.iter() {
        let mut t = *powers_of_deep_quotient_challenge.get_unchecked(i);
        i += 1;
        t.mul_assign_by_base(leaf_el);
        accumulated_at_z.add_assign(&t);
    }

    for leaf_el in query.stage_2_leaf[..VERIFIER_COMPILED_LAYOUT
        .stage_2_layout
        .num_base_field_polys()]
        .iter()
    {
        let mut t = *powers_of_deep_quotient_challenge.get_unchecked(i);
        i += 1;
        t.mul_assign_by_base(leaf_el);
        accumulated_at_z.add_assign(&t);
    }

    for leaf_el in query.stage_2_leaf[VERIFIER_COMPILED_LAYOUT.stage_2_layout.ext4_polys_offset..]
        .array_chunks::<4>()
    {
        let mut t = *powers_of_deep_quotient_challenge.get_unchecked(i);
        let leaf_el = Mersenne31Quartic::from_array_of_base(*leaf_el);
        i += 1;
        t.mul_assign(&leaf_el);
        accumulated_at_z.add_assign(&t);
    }

    // quotient is just a single value
    {
        let mut t = *powers_of_deep_quotient_challenge.get_unchecked(i);
        let leaf_el = Mersenne31Quartic::from_array_of_base(query.quotient_leaf);
        i += 1;
        t.mul_assign(&leaf_el);
        // NOTE: we compute quotient at non-main domain first, and then LDE, so we do NOT have adjustment
        // there, and we should cancel one below
        t.mul_assign_by_base(tau_in_domain_by_half_inversed);
        accumulated_at_z.add_assign(&t);
    }

    // all terms are linear over leaf values, so it's enough to scale once
    accumulated_at_z.mul_assign_by_base(tau_in_domain_by_half);

    let mut simulated_from_z = precompute_with_evals_at_z;
    simulated_from_z.sub_assign(&accumulated_at_z);
    simulated_from_z.mul_assign(&divisor_for_z);

    let mut accumulated_at_z_omega = Mersenne31Quartic::ZERO;

    for index in WITNESS_NEXT_ROW_OPENING_INDEXES.iter() {
        let mut t = *powers_of_deep_quotient_challenge.get_unchecked(i);
        let leaf_el = query.witness_leaf.get_unchecked(*index);
        i += 1;
        t.mul_assign_by_base(leaf_el);
        accumulated_at_z_omega.add_assign(&t);
    }
    for index in MEMORY_NEXT_ROW_OPENING_INDEXES.iter() {
        let mut t = *powers_of_deep_quotient_challenge.get_unchecked(i);
        let leaf_el = query.memory_leaf.get_unchecked(*index);
        i += 1;
        t.mul_assign_by_base(leaf_el);
        accumulated_at_z_omega.add_assign(&t);
    }
    // single element for stage 2
    {
        let mut t = *powers_of_deep_quotient_challenge.get_unchecked(i);
        let leaf_el =
            query.stage_2_leaf[VERIFIER_COMPILED_LAYOUT.stage_2_layout.ext4_polys_offset
                + (MEMORY_GRAND_PRODUCT_ACCUMULATOR_POLY_INDEX
                    - VERIFIER_COMPILED_LAYOUT
                        .stage_2_layout
                        .num_base_field_polys())
                    * 4..]
                .array_chunks::<4>()
                .next()
                .unwrap_unchecked();
        let leaf_el = Mersenne31Quartic::from_array_of_base(*leaf_el);
        t.mul_assign(&leaf_el);
        accumulated_at_z_omega.add_assign(&t);
    }

    // all terms are linear over leaf values, so it's enough to scale once
    accumulated_at_z_omega.mul_assign_by_base(tau_in_domain_by_half);

    let mut simulated_from_z_omega = precompute_with_evals_at_z_omega;
    simulated_from_z_omega.sub_assign(&accumulated_at_z_omega);
    simulated_from_z_omega.mul_assign(&divisor_for_z_omega);

    let mut expected_value = simulated_from_z;
    expected_value.add_assign(&simulated_from_z_omega);

    expected_value
}

pub(crate) unsafe fn accumulate_over_row_for_consistency_check_with_fma(
    precompute_with_evals_at_z: Mersenne31Quartic,
    precompute_with_evals_at_z_omega: Mersenne31Quartic,
    query: &QueryValuesInstance,
    deep_poly_alpha: &Mersenne31Quartic,
    extra_factor_for_accumulation_at_z_omega: &Mersenne31Quartic,
    divisor_for_z: &Mersenne31Quartic,
    divisor_for_z_omega: &Mersenne31Quartic,
    tau_in_domain_by_half: &Mersenne31Complex,
    tau_in_domain_by_half_inversed: &Mersenne31Complex,
) -> Mersenne31Quartic {
    assert!(Mersenne31Quartic::CAN_PROJECT_FROM_BASE);

    // now we can do consistency check
    let mut accumulated_at_z;

    // it's effectively a Horner rule as we walk backwards

    // setup, then witness, then memory, then stage 2 base, then stage 2 ext, then quotient,
    // but all backwards

    // quotient is just a single value
    {
        accumulated_at_z = Mersenne31Quartic::from_array_of_base(query.quotient_leaf);
        // NOTE: we compute quotient at non-main domain first, and then LDE, so we do NOT have adjustment
        // there, and we should cancel one below
        accumulated_at_z.mul_assign_by_base(tau_in_domain_by_half_inversed);
    }

    let src_ptr = query.stage_2_leaf[VERIFIER_COMPILED_LAYOUT.stage_2_layout.ext4_polys_offset..]
        .as_ptr()
        .cast::<[Mersenne31Field; 4]>();
    let mut i =
        query.stage_2_leaf[VERIFIER_COMPILED_LAYOUT.stage_2_layout.ext4_polys_offset..].len() / 4;
    while i > 0 {
        i -= 1;
        let leaf_el = Mersenne31Quartic::project_ref_from_array(src_ptr.add(i).as_ref_unchecked());
        accumulated_at_z.fused_mul_add_assign(deep_poly_alpha, leaf_el);
    }

    // all elements below are in "base field", so we will use an out of cycle value to copy those into for FMA

    let mut leaf_value = core::hint::black_box(Mersenne31Quartic::ZERO);

    let mut i = VERIFIER_COMPILED_LAYOUT
        .stage_2_layout
        .num_base_field_polys();
    while i > 0 {
        i -= 1;
        leaf_value.c0.c0 = *query.stage_2_leaf.get_unchecked(i);
        accumulated_at_z.fused_mul_add_assign(deep_poly_alpha, &leaf_value);
    }

    let mut i = VERIFIER_COMPILED_LAYOUT.memory_layout.total_width;
    while i > 0 {
        i -= 1;
        leaf_value.c0.c0 = *query.memory_leaf.get_unchecked(i);
        accumulated_at_z.fused_mul_add_assign(deep_poly_alpha, &leaf_value);
    }

    let mut i = VERIFIER_COMPILED_LAYOUT.witness_layout.total_width;
    while i > 0 {
        i -= 1;
        leaf_value.c0.c0 = *query.witness_leaf.get_unchecked(i);
        accumulated_at_z.fused_mul_add_assign(deep_poly_alpha, &leaf_value);
    }

    let mut i = VERIFIER_COMPILED_LAYOUT.setup_layout.total_width;
    while i > 0 {
        i -= 1;
        leaf_value.c0.c0 = *query.setup_leaf.get_unchecked(i);
        accumulated_at_z.fused_mul_add_assign(deep_poly_alpha, &leaf_value);
    }

    // all terms are linear over leaf values, so it's enough to scale once
    accumulated_at_z.mul_assign_by_base(tau_in_domain_by_half);

    let mut simulated_from_z = precompute_with_evals_at_z;
    simulated_from_z.sub_assign(&accumulated_at_z);
    simulated_from_z.mul_assign(&divisor_for_z);

    let mut accumulated_at_z_omega;
    // normal sequence is witness - memory - stage 2, so we should reverse for Horner rule

    // single element for stage 2
    {
        let leaf_el =
            query.stage_2_leaf[VERIFIER_COMPILED_LAYOUT.stage_2_layout.ext4_polys_offset
                + (MEMORY_GRAND_PRODUCT_ACCUMULATOR_POLY_INDEX
                    - VERIFIER_COMPILED_LAYOUT
                        .stage_2_layout
                        .num_base_field_polys())
                    * 4..]
                .array_chunks::<4>()
                .next()
                .unwrap_unchecked();
        accumulated_at_z_omega = Mersenne31Quartic::from_array_of_base(*leaf_el);
    }

    // memory
    let mut i = MEMORY_NEXT_ROW_OPENING_INDEXES.len();
    while i > 0 {
        i -= 1;
        let index = *MEMORY_NEXT_ROW_OPENING_INDEXES.get_unchecked(i);
        leaf_value.c0.c0 = *query.memory_leaf.get_unchecked(index);
        accumulated_at_z_omega.fused_mul_add_assign(deep_poly_alpha, &leaf_value);
    }

    // witness
    let mut i = WITNESS_NEXT_ROW_OPENING_INDEXES.len();
    while i > 0 {
        i -= 1;
        let index = *WITNESS_NEXT_ROW_OPENING_INDEXES.get_unchecked(i);
        leaf_value.c0.c0 = *query.witness_leaf.get_unchecked(index);
        accumulated_at_z_omega.fused_mul_add_assign(deep_poly_alpha, &leaf_value);
    }

    accumulated_at_z_omega.mul_assign_with_fma(extra_factor_for_accumulation_at_z_omega);

    // all terms are linear over leaf values, so it's enough to scale once
    accumulated_at_z_omega.mul_assign_by_base(tau_in_domain_by_half);

    let mut simulated_from_z_omega = precompute_with_evals_at_z_omega;
    simulated_from_z_omega.sub_assign(&accumulated_at_z_omega);
    simulated_from_z_omega.mul_assign(&divisor_for_z_omega);

    let mut expected_value = simulated_from_z;
    expected_value.add_assign(&simulated_from_z_omega);

    expected_value
}
