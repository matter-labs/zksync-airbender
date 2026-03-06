use std::collections::BTreeMap;

use cs::definitions::GKRAddress;
use field::{Field, FieldExtension, Mersenne31Field, Mersenne31Quartic};
use worker::Worker;

use crate::gkr::sumcheck::access_and_fold::BaseFieldPoly;
use crate::gkr::sumcheck::eq_poly::*;
use crate::gkr::sumcheck::{
    access_and_fold::{ExtensionFieldPoly, GKRLayerSource, GKRStorage},
    evaluation_kernels::{BatchedGKRKernel, LookupBaseMinusMultiplicityByBaseGKRRelation},
};

use super::*;

#[test]
fn test_base_minus_multiplicity_by_base() {
    type F = Mersenne31Field;
    type E = Mersenne31Quartic;

    const FOLDING_STEPS: usize = 4;
    const POLY_SIZE: usize = 1 << FOLDING_STEPS;
    let worker = Worker::new_with_num_threads(1);

    let a: Vec<F> = (10..(10 + POLY_SIZE))
        .map(|el| F::from_u64_with_reduction(el as u64))
        .collect();

    // let b: Vec<F> = (10..(10 + POLY_SIZE))
    //     .map(|el| F::from_u64_with_reduction(el as u64))
    //     .collect();

    let b: Vec<F> = vec![F::TWO; POLY_SIZE];

    let c: Vec<F> = (64..(64 + POLY_SIZE))
        .map(|el| F::from_u64_with_reduction(el as u64))
        .collect();

    let gamma = E::from_base(F::from_u64_with_reduction(2 as u64));

    let mut nums = vec![];
    let mut dens = vec![];

    for ((a, b), c) in a.iter().zip(b.iter()).zip(c.iter()) {
        // 1/a - b/c -> c - ab, ac

        let mut a_den = gamma;
        a_den.add_assign_base(a);

        let mut c_den = gamma;
        c_den.add_assign_base(c);

        let mut t = a_den;
        t.mul_assign_by_base(b);
        let mut num = c_den;
        num.sub_assign_base(&t);

        let mut den = a_den;
        den.mul_assign(&c_den);

        nums.push(num);
        dens.push(den);
    }

    dbg!(&nums);
    dbg!(&dens);

    let mut storage = GKRStorage::<F, E>::default();
    let mut layer_0 = GKRLayerSource::default();
    layer_0.layer_idx = 0;
    layer_0.base_field_inputs.insert(
        GKRAddress::InnerLayer {
            layer: 0,
            offset: 0,
        },
        BaseFieldPoly::new(a.into_boxed_slice()),
    );
    layer_0.base_field_inputs.insert(
        GKRAddress::InnerLayer {
            layer: 0,
            offset: 1,
        },
        BaseFieldPoly::new(b.into_boxed_slice()),
    );
    layer_0.base_field_inputs.insert(
        GKRAddress::InnerLayer {
            layer: 0,
            offset: 2,
        },
        BaseFieldPoly::new(c.into_boxed_slice()),
    );
    storage.layers.push(layer_0);

    let mut layer_1 = GKRLayerSource::default();
    layer_1.layer_idx = 1;
    layer_1.extension_field_inputs.insert(
        GKRAddress::InnerLayer {
            layer: 1,
            offset: 0,
        },
        ExtensionFieldPoly::new(nums.into_boxed_slice()),
    );
    layer_1.extension_field_inputs.insert(
        GKRAddress::InnerLayer {
            layer: 1,
            offset: 1,
        },
        ExtensionFieldPoly::new(dens.into_boxed_slice()),
    );
    storage.layers.push(layer_1);

    let kernel = LookupBaseMinusMultiplicityByBaseGKRRelation {
        input: GKRAddress::InnerLayer {
            layer: 0,
            offset: 0,
        },
        setup: [
            GKRAddress::InnerLayer {
                layer: 0,
                offset: 1,
            },
            GKRAddress::InnerLayer {
                layer: 0,
                offset: 2,
            },
        ],
        outputs: [
            GKRAddress::InnerLayer {
                layer: 1,
                offset: 0,
            },
            GKRAddress::InnerLayer {
                layer: 1,
                offset: 1,
            },
        ],
        lookup_additive_challenge: gamma,
        _marker: core::marker::PhantomData,
    };

    let previous_round_challenges: Vec<E> = (0..FOLDING_STEPS)
        .map(|el| E::from_base(F::from_u64_with_reduction(1u64 << (el + 1))))
        .collect();
    // dbg!(&previous_round_challenges);

    let eq_precomputed = make_eq_poly_in_full::<E>(&previous_round_challenges, &worker);
    // dbg!(&eq_precomputed);

    let batching_challenges = vec![E::ONE, E::from_base(F::from_nonreduced_u32(123))];

    let mut claim = E::ZERO;
    for i in 0..2 {
        let mut subclaim = evaluate_with_precomputed_eq_ext::<E>(
            &storage.layers[1]
                .extension_field_inputs
                .get(&GKRAddress::InnerLayer {
                    layer: 1,
                    offset: i,
                })
                .unwrap()
                .values[..],
            &eq_precomputed.last().unwrap()[..],
        );
        subclaim.mul_assign(&batching_challenges[i]);
        claim.add_assign(&subclaim);
    }

    dbg!(claim);

    dbg!(&batching_challenges);

    let mut folding_challenges = vec![];

    let eq_reduced_precomputed = make_eq_poly_reduced::<E>(&previous_round_challenges, &worker);
    // dbg!(&eq_reduced_precomputed);
    let eq_reduced_len = eq_reduced_precomputed.len();

    let mut last_evaluations = BTreeMap::new();
    let mut last_eq_poly_prefactor_contribution = E::ONE;

    for step in 0..FOLDING_STEPS {
        assert_eq!(folding_challenges.len(), step);
        dbg!(step);
        dbg!(&folding_challenges);

        if step != FOLDING_STEPS - 1 {
            let mut accumulator = vec![[E::ZERO; 2]; POLY_SIZE >> (step + 1)];
            kernel.evaluate_over_storage(
                &mut storage,
                step,
                &batching_challenges,
                &folding_challenges,
                &mut accumulator[..],
                FOLDING_STEPS,
                &mut last_evaluations,
                &worker,
            );
            let eq = &eq_reduced_precomputed[eq_reduced_len - 1 - step];

            dbg!(&accumulator);
            dbg!(&eq);

            let [c0, c2] = evaluate_constant_and_quadratic_coeffs_with_precomputed_eq::<F, E>(
                &accumulator,
                &eq,
                &worker,
            );

            dbg!([c0, c2]);

            let mut normalized_claim = claim;
            normalized_claim.mul_assign(
                &last_eq_poly_prefactor_contribution
                    .inverse()
                    .expect("not zero"),
            );
            dbg!(normalized_claim);
            let coeffs = output_univariate_monomial_form_max_quadratic::<F, E>(
                previous_round_challenges[step],
                normalized_claim,
                c0,
                c2,
            );

            // this will give us a sumcheck claim for the next round
            {
                let s0 = evaluate_small_univariate_poly::<F, E, 4>(&coeffs, &E::ZERO);
                let s1 = evaluate_small_univariate_poly::<F, E, 4>(&coeffs, &E::ONE);
                let mut v = s0;
                v.add_assign(&s1);
                v.mul_assign(&last_eq_poly_prefactor_contribution);
                assert_eq!(v, claim);
            }

            let folding_challenge = E::from_base(F::from_u64_with_reduction(2 * (step as u64) + 1));
            folding_challenges.push(folding_challenge);
            let next_claim = evaluate_small_univariate_poly::<F, E, 4>(&coeffs, &folding_challenge);

            dbg!(next_claim);

            {
                let t =
                    evaluate_eq_poly::<F, E>(&folding_challenge, &previous_round_challenges[step]);
                last_eq_poly_prefactor_contribution = t;
                // eq_poly_prefactor.mul_assign(&t);
            }

            claim = next_claim;
        } else {
            let mut accumulator = [[E::ZERO; 2]];
            // the last folding step is special - inputs are already polynomials of size 2,
            // and so we should output f(0) and f(1) explicitly,
            // and use them to verify the claim, and also then compute f(last folding challenge)

            // claim = \sum_{b = 0,1} eq(r, b) * kernel(X(b), Y(b)),
            // and we should also collect X(0/1), Y(0/1) (all unique ones)

            kernel.evaluate_over_storage(
                &mut storage,
                step,
                &batching_challenges,
                &folding_challenges,
                &mut accumulator[..],
                FOLDING_STEPS,
                &mut last_evaluations,
                &worker,
            );

            // we would commit those values
            assert!(last_evaluations.len() > 0);

            // in the accumulator we should have kernel(X(b), Y(b)) (batched), and now we can just multiply corresponding coordinates
            // over (1 - previous_round_challenges[last]) and previous_round_challenges[last], and add them up to verify that they match the claim

            dbg!(&accumulator);
            let previous_round_last_challenge =
                &previous_round_challenges.last().expect("must be present");
            dbg!(previous_round_last_challenge);

            // [eq(r_last, 0) * A(r'.., 0) * B(r'..., 0) + eq(r_last, 1) * A(r'..., 1) * B(r'..., 1)] of the example above
            let [[f0, f1]] = accumulator;
            let [eq0, eq1] = evaluate_eq_poly_at_line::<F, E>(&previous_round_last_challenge);

            dbg!([f0, f1]);
            dbg!([eq0, eq1]);

            let mut t0 = eq0;
            t0.mul_assign(&f0);
            let mut t1 = eq1;
            t1.mul_assign(&f1);
            let mut claim_inner = t0;
            claim_inner.add_assign(&t1);

            let folding_challenge = E::from_base(F::from_u64_with_reduction(2 * (step as u64) + 1));
            folding_challenges.push(folding_challenge);
            // derive new claims

            let eq_precomputed = make_eq_poly_in_full::<E>(&folding_challenges, &worker);
            for poly in [
                GKRAddress::InnerLayer {
                    layer: 0,
                    offset: 0,
                },
                GKRAddress::InnerLayer {
                    layer: 0,
                    offset: 1,
                },
                GKRAddress::InnerLayer {
                    layer: 0,
                    offset: 2,
                },
            ] {
                let evals = &storage.layers[0]
                    .base_field_inputs
                    .get(&poly)
                    .unwrap()
                    .values[..];
                let expected = evaluate_with_precomputed_eq::<F, E>(
                    evals,
                    &eq_precomputed.last().unwrap()[..],
                );

                let [f0, f1] = last_evaluations.remove(&poly).expect("must be present");
                dbg!([f0, f1]);
                let mut random_value = f1;
                random_value.sub_assign(&f0);
                random_value.mul_assign(&folding_challenge);
                random_value.add_assign(&f0);
                assert_eq!(random_value, expected, "failed for {:?}", poly);
            }

            let mut recomputed_claim = claim_inner;
            recomputed_claim.mul_assign(&last_eq_poly_prefactor_contribution);
            assert_eq!(claim, recomputed_claim);
        }
    }
}
