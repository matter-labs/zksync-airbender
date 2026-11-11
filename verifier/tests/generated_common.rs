use verifier::add_sub_lui_auipc_mop::pessimistic_conjecture::common::{
    compute_claim, eval_multilinear_with_monomial_tensor, fold_whir_accumulator,
    precompute_monomial_tensor, push_whir_base_pow_entry, push_whir_pow_entry,
};
use verifier::field::baby_bear::base::BabyBearField;
use verifier::field::baby_bear::ext4::BabyBearExt4;
use verifier::field::{Field, FieldExtension};
use verifier::verifier_common::lazy_vec::LazyVec;
use verifier::verifier_common::whir::WhirAccumulator;

fn ext(seed: u32) -> BabyBearExt4 {
    <BabyBearExt4 as FieldExtension<BabyBearField>>::from_coeffs(core::array::from_fn(|i| {
        BabyBearField::from_nonreduced_u32(seed.wrapping_mul(0x9e37_79b9) ^ (i as u32 * 7919))
    }))
}

#[test]
fn compute_claim_matches_naive_batching() {
    let claims: Vec<BabyBearExt4> = (0..6).map(|i| ext(10 + i)).collect();
    let batch_base = ext(1);
    // `(n, o0, o1)`: `n == 0` skips a power, otherwise the first `n` of `o0`, `o1` take the next ones.
    let descs = [
        (0, 0, 0),
        (1, 3, 0),
        (0, 0, 0),
        (2, 0, 5),
        (1, 1, 0),
        (0, 0, 0),
        (2, 4, 2),
        (0, 0, 0),
    ];

    let mut expected = BabyBearExt4::ZERO;
    let mut power = BabyBearExt4::ONE;
    for &(n, o0, o1) in descs.iter() {
        if n == 0 {
            power.mul_assign(&batch_base);
        }
        for o in [o0, o1].into_iter().take(n) {
            let mut term = claims[o];
            term.mul_assign(&power);
            expected.add_assign(&term);
            power.mul_assign(&batch_base);
        }
    }

    let combined = unsafe { compute_claim(&claims, &descs, batch_base) };
    assert_eq!(combined, expected);
}

fn minus_one() -> BabyBearField {
    let mut v = BabyBearField::ZERO;
    v.sub_assign(&BabyBearField::ONE);
    v
}

#[test]
fn whir_base_pow_entries_match_embedded_extension_entries() {
    let points = [
        BabyBearField::ZERO,
        BabyBearField::ONE,
        minus_one(),
        BabyBearField::from_nonreduced_u32(5),
        BabyBearField::from_nonreduced_u32(123_456_789),
    ];
    let z_initial: Vec<BabyBearExt4> = (0..3).map(|i| ext(30 + i)).collect();
    let mut base = WhirAccumulator::<BabyBearField, BabyBearExt4, 8, 8>::new(ext(3));
    let mut embedded = WhirAccumulator::<BabyBearField, BabyBearExt4, 8, 8>::new(ext(3));

    let ext_point = ext(4);
    let ext_coefficient = ext(5);
    push_whir_pow_entry(&mut base, ext_point, ext_coefficient);
    push_whir_pow_entry(&mut embedded, ext_point, ext_coefficient);

    // `(point, prefactor, coefficient)` per entry, the extension entry first.
    let mut reference = vec![(ext_point, BabyBearExt4::ONE, ext_coefficient)];
    for (round, new_points) in [&points[..2], &points[2..4], &points[4..]]
        .into_iter()
        .enumerate()
    {
        for (i, &s) in new_points.iter().enumerate() {
            let coefficient = ext(50 + 10 * round as u32 + i as u32);
            push_whir_base_pow_entry(&mut base, s, coefficient);
            push_whir_pow_entry(&mut embedded, BabyBearExt4::from_base(s), coefficient);
            reference.push((BabyBearExt4::from_base(s), BabyBearExt4::ONE, coefficient));
        }

        let alpha = ext(40 + round as u32);
        fold_whir_accumulator(&mut base, alpha, &z_initial);
        fold_whir_accumulator(&mut embedded, alpha, &z_initial);
        for (s, prefactor, _) in reference.iter_mut() {
            // eq(s, alpha) = (1 - s)(1 - alpha) + s alpha
            let mut eq = BabyBearExt4::ONE;
            eq.sub_assign(s);
            let mut one_minus_alpha = BabyBearExt4::ONE;
            one_minus_alpha.sub_assign(&alpha);
            eq.mul_assign(&one_minus_alpha);
            let mut s_alpha = *s;
            s_alpha.mul_assign(&alpha);
            eq.add_assign(&s_alpha);
            prefactor.mul_assign(&eq);
            s.square();
        }

        assert_eq!(base.z_initial_idx, round + 1);
        assert_eq!(base.z_initial_idx, embedded.z_initial_idx);
        assert_eq!(base.z_initial_prefactor, embedded.z_initial_prefactor);
        assert_eq!(base.pow_entries.len(), 1);
        assert_eq!(base.base_pow_entries.len() + 1, reference.len());
        assert_eq!(embedded.pow_entries.len(), reference.len());
        let base_entries = base
            .pow_entries
            .as_slice()
            .iter()
            .map(|e| (e.current_scalar, e.prefactor, e.coefficient));
        let base_entries = base_entries.chain(base.base_pow_entries.as_slice().iter().map(|e| {
            (
                BabyBearExt4::from_base(e.current_scalar),
                e.prefactor,
                e.coefficient,
            )
        }));
        let embedded_entries = embedded
            .pow_entries
            .as_slice()
            .iter()
            .map(|e| (e.current_scalar, e.prefactor, e.coefficient));
        for ((b, e), r) in base_entries.zip(embedded_entries).zip(reference.iter()) {
            assert_eq!(b, *r, "round {round}");
            assert_eq!(e, *r, "round {round}");
        }
    }
}

#[test]
fn fused_leaf_evaluation_matches_naive_monomial_sum() {
    let all_challenges = [
        ext(60),
        BabyBearExt4::ONE,
        BabyBearExt4::from_base(minus_one()),
        BabyBearExt4::ZERO,
        ext(61),
    ];
    for k in [0, 1, 2, 3, 5] {
        let challenges = &all_challenges[..k];
        let coeffs: Vec<BabyBearExt4> = (0..1u32 << k).map(|i| ext(70 + i)).collect();
        let mut weights = LazyVec::<BabyBearExt4, 32>::new();
        precompute_monomial_tensor(challenges, &mut weights);

        let mut expected = BabyBearExt4::ZERO;
        for (i, c) in coeffs.iter().enumerate() {
            let mut w = BabyBearExt4::ONE;
            for (j, alpha) in challenges.iter().enumerate() {
                if (i >> j) & 1 == 1 {
                    w.mul_assign(alpha);
                }
            }
            assert_eq!(weights.as_slice()[i], w, "k = {k}, weight {i}");
            let mut term = *c;
            term.mul_assign(&w);
            expected.add_assign(&term);
        }
        assert_eq!(
            eval_multilinear_with_monomial_tensor(&coeffs, weights.as_slice()),
            expected,
            "k = {k}"
        );
    }
}
