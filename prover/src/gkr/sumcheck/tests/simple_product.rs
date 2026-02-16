use std::collections::BTreeMap;
use std::sync::Arc;

use cs::definitions::GKRAddress;
use field::{Field, FieldExtension, Mersenne31Field, Mersenne31Quartic};
use worker::Worker;

use crate::gkr::sumcheck::eq_poly::*;
use crate::gkr::sumcheck::{
    access_and_fold::{ExtensionFieldPoly, GKRLayerSource, GKRStorage},
    evaluation_kernels::{BatchedGKRKernel, SameSizeProductGKRRelation},
};

// Generic logic - three step sumcheck
// s(X) = eq(r1, X) \sum_{Y, Z = {0,1}} eq(r2, r3, Y, Z) A(X, Y, Z) B(X, Y, Z)
// then we treat \sum_{Y, Z = {0,1}} eq(r2, r3, Y, Z) A(X, Y, Z) B(X, Y, Z) as quadratic over X
// f(r1, r2, r3) = \sum_{X, Y, Z} eq(r1, r2, r3, X, Y, Z) A(X, Y, Z) B(X, Y, Z) = s(0) + s(1)
// prover sends s(X) and gets a new claim s(r1')
// s(r1') = eq(r1, r1') \sum_{Y, Z = {0,1}} eq(r2, r3, Y, Z) A(r1', Y, Z) B(r1', Y, Z), and we break it further
// t(Y) = eq(r1, r1') eq(r2, Y) \sum_{Z} eq(r3, Z) A(r1', Y, Z) B(r1', Y, Z) (and here we actually strip eq(r1, r1') from monomial form)
// so again s(r1') = t(0) + t(1)
// prover sends t(Y) and get a new claim t(r2')
// t(r2') = eq(r1, r1') eq(r2, r2') \sum_{Z} eq(r3, Z) A(r1', r2', Z) B(r1', r2', Z)
// this one is easy to evaluate explicitly - prover sends A(r1', r2', Z) B(r1', r2', Z) in plain text,
// then verifier can evaluate the sum on it's own, and derive claims A(r1', r2', r3') and B(r1', r2', r3')

// For sumchecks with larger set of round we just have more intermediate steps

// NOTE: when we send univariate polys in intermediate rounds, we strip eq poly contributions
// of all the eq(r, r') that happened before this sumcheck round, so for the very last one we only need eq(r2, r2') factor,
// and not the full eq(r1, r1') * eq(r2, r2') product in front of \sum_{Z} eq(r3, Z) A(r1', r2', Z) B(r1', r2', Z)

use super::*;

#[test]
fn test_simple_product() {
    type F = Mersenne31Field;
    type E = Mersenne31Quartic;

    const FOLDING_STEPS: usize = 4;
    const POLY_SIZE: usize = 1 << FOLDING_STEPS;
    let worker = Worker::new_with_num_threads(1);

    let a: Vec<E> = (0..POLY_SIZE)
        .map(|el| E::from_base(F::from_u64_with_reduction(el as u64)))
        .collect();

    let b: Vec<E> = (0..POLY_SIZE)
        .map(|el| E::from_base(F::from_u64_with_reduction(el as u64)))
        .collect();

    let output: Vec<E> = a
        .iter()
        .zip(b.iter())
        .map(|(a, b)| {
            let mut t = *a;
            t.mul_assign(b);

            t
        })
        .collect();

    let mut storage = GKRStorage::<F, E>::default();
    let mut layer_0 = GKRLayerSource::default();
    layer_0.layer_idx = 0;
    layer_0.extension_field_inputs.insert(
        GKRAddress::InnerLayer {
            layer: 0,
            offset: 0,
        },
        ExtensionFieldPoly::new(a.into_boxed_slice()),
    );
    layer_0.extension_field_inputs.insert(
        GKRAddress::InnerLayer {
            layer: 0,
            offset: 1,
        },
        ExtensionFieldPoly::new(b.into_boxed_slice()),
    );

    storage.layers.push(layer_0);
    let mut layer_1 = GKRLayerSource::default();
    layer_1.layer_idx = 1;
    layer_1.extension_field_inputs.insert(
        GKRAddress::InnerLayer {
            layer: 1,
            offset: 0,
        },
        ExtensionFieldPoly::new(output.into_boxed_slice()),
    );

    storage.layers.push(layer_1);

    let kernel = SameSizeProductGKRRelation {
        inputs: [
            GKRAddress::InnerLayer {
                layer: 0,
                offset: 0,
            },
            GKRAddress::InnerLayer {
                layer: 0,
                offset: 1,
            },
        ],
        output: GKRAddress::InnerLayer {
            layer: 1,
            offset: 0,
        },
    };

    let previous_round_challenges: Vec<E> = (0..FOLDING_STEPS)
        .map(|el| E::from_base(F::from_u64_with_reduction(1u64 << (el + 1))))
        .collect();
    // dbg!(&previous_round_challenges);

    let eq_precomputed = make_eq_poly_in_full::<E>(&previous_round_challenges);
    // dbg!(&eq_precomputed);

    let mut claim = evaluate_with_precomputed_eq_ext::<E>(
        &storage.layers[1]
            .extension_field_inputs
            .get(&GKRAddress::InnerLayer {
                layer: 1,
                offset: 0,
            })
            .unwrap()
            .values[..],
        &eq_precomputed.last().unwrap()[..],
    );
    dbg!(claim);

    let mut expected_random_evals = BTreeMap::new();
    {
        let folding_challenges: Vec<E> = (0..FOLDING_STEPS)
            .map(|el| E::from_base(F::from_u64_with_reduction(2 * (el as u64) + 1)))
            .collect();
        let eq_precomputed = make_eq_poly_in_full::<E>(&folding_challenges);
        let a = &storage.layers[0]
            .extension_field_inputs
            .get(&GKRAddress::InnerLayer {
                layer: 0,
                offset: 0,
            })
            .unwrap()
            .values[..];
        let a_expected =
            evaluate_with_precomputed_eq_ext::<E>(a, &eq_precomputed.last().unwrap()[..]);
        expected_random_evals.insert(
            GKRAddress::InnerLayer {
                layer: 0,
                offset: 0,
            },
            a_expected,
        );
        let b = &storage.layers[0]
            .extension_field_inputs
            .get(&GKRAddress::InnerLayer {
                layer: 0,
                offset: 1,
            })
            .unwrap()
            .values[..];
        let b_expected =
            evaluate_with_precomputed_eq_ext::<E>(b, &eq_precomputed.last().unwrap()[..]);
        expected_random_evals.insert(
            GKRAddress::InnerLayer {
                layer: 0,
                offset: 1,
            },
            b_expected,
        );
    }

    let batch_challenge = E::from_base(F::ONE);
    let mut batch_challenges = vec![batch_challenge];

    let mut folding_challenges = vec![];

    let eq_reduced_precomputed = make_eq_poly_reduced::<E>(&previous_round_challenges);
    // dbg!(&eq_reduced_precomputed);
    let eq_reduced_len = eq_reduced_precomputed.len();

    {
        let a = &storage.layers[0]
            .extension_field_inputs
            .get(&GKRAddress::InnerLayer {
                layer: 0,
                offset: 0,
            })
            .unwrap()
            .values[..];
        let b = &storage.layers[0]
            .extension_field_inputs
            .get(&GKRAddress::InnerLayer {
                layer: 0,
                offset: 1,
            })
            .unwrap()
            .values[..];

        {
            // explicit sum
            let eq = eq_precomputed.last().unwrap();
            assert_eq!(eq.len(), POLY_SIZE);
            let mut result = E::ZERO;

            for i in 0..POLY_SIZE {
                let a0 = a[i];
                let b0 = b[i];
                let eq0 = eq[i];
                let mut t = a0;
                t.mul_assign(&b0);
                t.mul_assign(&eq0);
                result.add_assign(&t);
            }

            dbg!(result);
        }
    }

    let mut last_evaluations = BTreeMap::new();
    let mut last_eq_poly_prefactor_contribution = E::ONE;

    for step in 0..FOLDING_STEPS {
        assert_eq!(folding_challenges.len(), step);
        dbg!(step);

        if step != FOLDING_STEPS - 1 {
            let mut accumulator = vec![[E::ZERO; 2]; POLY_SIZE >> (step + 1)];
            kernel.evaluate_over_storage(
                &mut storage,
                step,
                &batch_challenges,
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
                &batch_challenges,
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

            let mut t0 = eq0;
            t0.mul_assign(&f0);
            let mut t1 = eq1;
            t1.mul_assign(&f1);
            let mut claim_inner = t0;
            claim_inner.add_assign(&t1);

            let mut recomputed_claim = claim_inner;
            recomputed_claim.mul_assign(&last_eq_poly_prefactor_contribution);
            assert_eq!(claim, recomputed_claim);

            let folding_challenge = E::from_base(F::from_u64_with_reduction(2 * (step as u64) + 1));
            folding_challenges.push(folding_challenge);
            // derive new claims
            for poly in [
                GKRAddress::InnerLayer {
                    layer: 0,
                    offset: 0,
                },
                GKRAddress::InnerLayer {
                    layer: 0,
                    offset: 1,
                },
            ] {
                let [f0, f1] = last_evaluations.remove(&poly).expect("must be present");
                let mut random_value = f1;
                random_value.sub_assign(&f0);
                random_value.mul_assign(&folding_challenge);
                random_value.add_assign(&f0);
                assert_eq!(&random_value, expected_random_evals.get(&poly).unwrap());
            }
        }
    }
}
