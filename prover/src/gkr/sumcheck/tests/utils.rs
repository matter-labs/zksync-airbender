use std::collections::BTreeMap;

use crate::gkr::sumcheck::{
    access_and_fold::{ExtensionFieldPoly, GKRLayerSource, GKRStorage},
    eq_poly::*,
    evaluate_eq_poly, evaluate_eq_poly_at_line, evaluate_small_univariate_poly,
    evaluation_kernels::BatchedGKRKernel,
    output_univariate_monomial_form_max_quadratic,
};
use cs::definitions::GKRAddress;
use field::{Field, FieldExtension, PrimeField};
use worker::Worker;

use rand::RngCore;

pub(super) fn random_poly_in_ext<F, E>(size: usize) -> Vec<E>
where
    F: PrimeField,
    E: FieldExtension<F> + Field,
    [(); E::DEGREE]: Sized,
{
    let mut rng = rand::rng();

    (0..size)
        .map(|_| {
            let coefs: Vec<F> = [rng.next_u32(); E::DEGREE]
                .into_iter()
                .map(|value| F::from_u32_with_reduction(value))
                .collect();
            E::from_coeffs_in_base(&coefs)
        })
        .collect()
}

pub(super) fn setup_storage<F: PrimeField, E: FieldExtension<F> + Field>(
    inputs: Vec<(GKRAddress, Vec<E>)>,
    outputs: Vec<(GKRAddress, Vec<E>)>,
) -> GKRStorage<F, E> {
    let mut storage = GKRStorage::<F, E>::default();

    let mut layer_0 = GKRLayerSource::default();
    layer_0.layer_idx = 0;
    for (addr, poly) in inputs {
        layer_0
            .extension_field_inputs
            .insert(addr, ExtensionFieldPoly::new(poly.into_boxed_slice()));
    }
    storage.layers.push(layer_0);

    let mut layer_1 = GKRLayerSource::default();
    layer_1.layer_idx = 1;
    for (addr, poly) in outputs {
        layer_1
            .extension_field_inputs
            .insert(addr, ExtensionFieldPoly::new(poly.into_boxed_slice()));
    }
    storage.layers.push(layer_1);

    storage
}

pub(super) fn setup_sumcheck_params<F, E>(
    storage: &GKRStorage<F, E>,
    output_addrs: &[GKRAddress],
    input_polys: &[(GKRAddress, &[E])],
    folding_steps: usize,
) -> (E, Vec<E>, Vec<E>, BTreeMap<GKRAddress, E>)
where
    F: PrimeField,
    E: FieldExtension<F> + Field,
    [(); E::DEGREE]: Sized,
{
    let previous_round_challenges = random_poly_in_ext(folding_steps);

    let eq_precomputed = make_eq_poly_in_full::<F, E>(&previous_round_challenges);
    let eq_last = eq_precomputed.last().unwrap();

    // Compute claim as sum over all outputs
    let mut claim = E::ZERO;
    for addr in output_addrs {
        let poly = &storage.layers[1]
            .extension_field_inputs
            .get(addr)
            .unwrap()
            .values[..];
        claim.add_assign(&evaluate_with_precomputed_eq_ext::<F, E>(poly, eq_last));
    }

    // Compute expected random evaluations
    let folding_challenges: Vec<E> = random_poly_in_ext(folding_steps);
    let eq_for_evals = make_eq_poly_in_full::<F, E>(&folding_challenges);

    let mut expected = BTreeMap::new();
    for (addr, poly) in input_polys {
        expected.insert(
            *addr,
            evaluate_with_precomputed_eq_ext::<F, E>(poly, eq_for_evals.last().unwrap()),
        );
    }

    (
        claim,
        previous_round_challenges,
        folding_challenges,
        expected,
    )
}

pub(super) fn compute_product<F: PrimeField, E: FieldExtension<F> + Field>(
    a: &[E],
    b: &[E],
) -> Vec<E> {
    a.iter()
        .zip(b.iter())
        .map(|(a, b)| {
            let mut t = *a;
            t.mul_assign(b);
            t
        })
        .collect()
}

pub(super) fn compute_mask_identity<F: PrimeField, E: FieldExtension<F> + Field>(
    a: &[E],
    m: &[E],
) -> Vec<E> {
    a.iter()
        .zip(m.iter())
        .map(|(a, m)| {
            let mut result = *a;
            result.mul_assign(m);
            let mut one_minus_m = E::ONE;
            one_minus_m.sub_assign(m);
            result.add_assign(&one_minus_m);
            result
        })
        .collect()
}

pub(super) fn compute_lookup_sub<F: PrimeField, E: FieldExtension<F> + Field>(
    a: &[E],
    b: &[E],
    c: &[E],
    d: &[E],
) -> (Vec<E>, Vec<E>) {
    let num: Vec<E> = (0..a.len())
        .map(|i| {
            let mut ad = a[i];
            ad.mul_assign(&d[i]);
            let mut cb = c[i];
            cb.mul_assign(&b[i]);
            ad.sub_assign(&cb);
            ad
        })
        .collect();
    let den: Vec<E> = (0..a.len())
        .map(|i| {
            let mut bd = b[i];
            bd.mul_assign(&d[i]);
            bd
        })
        .collect();
    (num, den)
}

pub(super) fn compute_lookup_add<F: PrimeField, E: FieldExtension<F> + Field>(
    a: &[E],
    b: &[E],
    c: &[E],
    d: &[E],
) -> (Vec<E>, Vec<E>) {
    let num: Vec<E> = (0..a.len())
        .map(|i| {
            let mut ad = a[i];
            ad.mul_assign(&d[i]);
            let mut cb = c[i];
            cb.mul_assign(&b[i]);
            ad.add_assign(&cb);
            ad
        })
        .collect();
    let den: Vec<E> = (0..a.len())
        .map(|i| {
            let mut bd = b[i];
            bd.mul_assign(&d[i]);
            bd
        })
        .collect();
    (num, den)
}

pub(super) fn create_alternating_mask<F: PrimeField, E: FieldExtension<F> + Field>(
    size: usize,
) -> Vec<E> {
    (0..size)
        .map(|el| E::from_base(F::from_u64_with_reduction((el % 2) as u64)))
        .collect()
}

pub(super) fn run_sumcheck_test<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    K: BatchedGKRKernel<F, E>,
>(
    storage: &mut GKRStorage<F, E>,
    kernel: &K,
    initial_claim: E,
    previous_round_challenges: &[E],
    folding_challenges_precomputed: &[E],
    expected_random_evals: &BTreeMap<GKRAddress, E>,
) {
    let worker = Worker::new_with_num_threads(1);
    let folding_steps = previous_round_challenges.len();
    assert_eq!(folding_steps, folding_challenges_precomputed.len());
    let mut claim = initial_claim;
    let batch_challenges = vec![E::from_base(F::ONE); kernel.num_challenges()];
    let mut folding_challenges = vec![];
    let eq_reduced_precomputed = make_eq_poly_reduced::<F, E>(previous_round_challenges);
    let eq_reduced_len = eq_reduced_precomputed.len();
    let mut last_evaluations = BTreeMap::new();
    let mut last_eq_poly_prefactor_contribution = E::ONE;

    for step in 0..folding_steps {
        assert_eq!(folding_challenges.len(), step);

        if step != folding_steps - 1 {
            let mut accumulator = vec![[E::ZERO; 2]; 1 << (folding_steps - step - 1)];
            kernel.evaluate_over_storage(
                storage,
                step,
                &batch_challenges,
                &folding_challenges,
                &mut accumulator[..],
                folding_steps,
                &mut last_evaluations,
                &worker,
            );
            let eq = &eq_reduced_precomputed[eq_reduced_len - 1 - step];

            let [c0, c2] = evaluate_constant_and_quadratic_coeffs_with_precomputed_eq::<F, E>(
                &accumulator,
                eq,
            );

            println!("Step {}: accumulator = {:?}", step, accumulator);
            println!("Step {}: eq = {:?}", step, eq);
            println!("Step {}: c0 = {:?}, c2 = {:?}", step, c0, c2);
            println!("Step {}: claim = {:?}", step, claim);

            let mut normalized_claim = claim;
            normalized_claim.mul_assign(
                &last_eq_poly_prefactor_contribution
                    .inverse()
                    .expect("not zero"),
            );
            let coeffs = output_univariate_monomial_form_max_quadratic::<F, E>(
                previous_round_challenges[step],
                normalized_claim,
                c0,
                c2,
            );

            // Verify sumcheck claim
            {
                let s0 = evaluate_small_univariate_poly::<F, E>(&coeffs, &E::ZERO);
                let s1 = evaluate_small_univariate_poly::<F, E>(&coeffs, &E::ONE);
                let mut v = s0;
                v.add_assign(&s1);
                v.mul_assign(&last_eq_poly_prefactor_contribution);
                assert_eq!(v, claim);
            }

            let folding_challenge = folding_challenges_precomputed[step];
            folding_challenges.push(folding_challenge);
            let next_claim = evaluate_small_univariate_poly::<F, E>(&coeffs, &folding_challenge);

            {
                let t =
                    evaluate_eq_poly::<F, E>(&folding_challenge, &previous_round_challenges[step]);
                last_eq_poly_prefactor_contribution = t;
            }

            claim = next_claim;
        } else {
            let mut accumulator = [[E::ZERO; 2]];
            kernel.evaluate_over_storage(
                storage,
                step,
                &batch_challenges,
                &folding_challenges,
                &mut accumulator[..],
                folding_steps,
                &mut last_evaluations,
                &worker,
            );

            assert!(last_evaluations.len() > 0);

            let previous_round_last_challenge =
                previous_round_challenges.last().expect("must be present");
            let [[f0, f1]] = accumulator;
            let [eq0, eq1] = evaluate_eq_poly_at_line::<F, E>(previous_round_last_challenge);

            let mut t0 = eq0;
            t0.mul_assign(&f0);
            let mut t1 = eq1;
            t1.mul_assign(&f1);
            let mut claim_inner = t0;
            claim_inner.add_assign(&t1);

            println!("Final step: accumulator = {:?}", accumulator);
            println!("Final step: f0 = {:?}, f1 = {:?}", f0, f1);
            println!("Final step: eq0 = {:?}, eq1 = {:?}", eq0, eq1);
            println!("Final step: claim_inner = {:?}", claim_inner);
            println!(
                "Final step: last_eq_poly_prefactor_contribution = {:?}",
                last_eq_poly_prefactor_contribution
            );
            println!("Final step: claim = {:?}", claim);

            let mut recomputed_claim = claim_inner;
            recomputed_claim.mul_assign(&last_eq_poly_prefactor_contribution);
            println!("Final step: recomputed_claim = {:?}", recomputed_claim);
            assert_eq!(claim, recomputed_claim);

            let folding_challenge = folding_challenges_precomputed[step];
            folding_challenges.push(folding_challenge);

            // Verify final evaluations
            for (poly, expected) in expected_random_evals.iter() {
                let [f0, f1] = last_evaluations.remove(poly).expect("must be present");
                let mut random_value = f1;
                random_value.sub_assign(&f0);
                random_value.mul_assign(&folding_challenge);
                random_value.add_assign(&f0);
                assert_eq!(&random_value, expected);
            }
        }
    }
}
