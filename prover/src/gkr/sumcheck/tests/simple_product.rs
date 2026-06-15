use std::collections::BTreeMap;
use std::sync::Arc;

use cs::definitions::GKRAddress;
use field::{Field, FieldExtension, Mersenne31Field, Mersenne31Quartic};
use worker::Worker;

use crate::gkr::prover::sumcheck_loop::windowed_mode::full_size_scratch::initial_round::evaluate_initial_with_full_sized_scratch;
use crate::gkr::sumcheck::access_and_fold::DisjointAccessQuasiSlice;
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

    let eq_precomputed = make_eq_poly_in_full::<E>(&previous_round_challenges, &worker);
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
        let eq_precomputed = make_eq_poly_in_full::<E>(&folding_challenges, &worker);
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
    let batch_challenges = vec![batch_challenge];

    let mut folding_challenges = vec![];

    let eq_reduced_precomputed = make_eq_poly_reduced::<E>(&previous_round_challenges, &worker);
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

            // dbg!(&accumulator);
            // dbg!(&eq);

            let [c0, c2] = evaluate_constant_and_quadratic_coeffs_with_precomputed_eq::<F, E>(
                &accumulator,
                &eq,
                &worker,
            );

            // dbg!([c0, c2]);

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
                dbg!(s0);
                let s1 = evaluate_small_univariate_poly::<F, E, 4>(&coeffs, &E::ONE);
                dbg!(s1);
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

#[test]
fn test_windowed_product() {
    type F = Mersenne31Field;
    type E = Mersenne31Quartic;

    fn var_repr(x: usize) -> &'static str {
        match x {
            0 => "0",
            1 => "1",
            2 => "inf",
            _ => unreachable!(),
        }
    }

    const FOLDING_STEPS: usize = 4;
    const POLY_SIZE: usize = 1 << FOLDING_STEPS;
    let worker = Worker::new_with_num_threads(8);

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

    let previous_round_challenges: Vec<E> = (0..FOLDING_STEPS)
        .map(|el| E::from_base(F::from_u64_with_reduction(1u64 << (el + 1))))
        .collect();
    // dbg!(&previous_round_challenges);
    let eq_precomputed = make_eq_poly_in_full::<E>(&previous_round_challenges, &worker);
    let eq_prefix_precomputed =
        make_eq_poly_in_full::<E>(&previous_round_challenges[..(FOLDING_STEPS - 1)], &worker);
    // dbg!(&eq_precomputed);

    // dbg!(make_eq_poly_in_full::<E>(&previous_round_challenges[..(FOLDING_STEPS-1)], &worker));

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

        let prev_eq_precomputed = make_eq_poly_in_full::<E>(&previous_round_challenges, &worker);
        let eq = prev_eq_precomputed.last().unwrap();
        let mut recomptued_claim = E::ZERO;
        for j in 0..POLY_SIZE / 2 {
            let i = j * 2;
            let eq_prefix = eq_prefix_precomputed.last().unwrap()[j];
            let eq_suffix = &eq_precomputed[1];

            let mut t_0 = a[i];
            t_0.mul_assign(&b[i]);
            let mut acc_0 = eq_prefix;
            acc_0.mul_assign(&eq_suffix[0]);
            let acc_0_copy = acc_0;
            assert_eq!(acc_0, eq[i]);
            acc_0.mul_assign(&t_0);

            let mut t_1 = a[i + 1];
            t_1.mul_assign(&b[i + 1]);
            let mut acc_1 = eq_prefix;
            acc_1.mul_assign(&eq_suffix[1]);
            let acc_1_copy = acc_1;
            assert_eq!(acc_1, eq[i + 1]);
            acc_1.mul_assign(&t_1);

            recomptued_claim.add_assign(&acc_0);
            recomptued_claim.add_assign(&acc_1);

            let x2 = (i / 2) % 2;
            let x1 = (i / 4) % 2;
            let x0 = (i / 8) % 2;
            // println!("{} : {} : {} = {} * ({} * {} + {} * {})", var_repr(x0), var_repr(x1), var_repr(x2), eq_prefix, eq_suffix[0], t_0, eq_suffix[1], t_1);
        }
        assert_eq!(recomptued_claim, claim);
    }

    let folding_challenges: Vec<E> = (0..FOLDING_STEPS)
        .map(|el| E::from_base(F::from_u64_with_reduction(2 * (el as u64) + 1)))
        .collect();

    let mut expected_random_evals = BTreeMap::new();
    {
        let eq_precomputed = make_eq_poly_in_full::<E>(&folding_challenges, &worker);
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

    // merged window of 3 variables at once

    let srcs = [
        storage
            .try_get_ext_poly(GKRAddress::InnerLayer {
                layer: 0,
                offset: 0,
            })
            .unwrap(),
        storage
            .try_get_ext_poly(GKRAddress::InnerLayer {
                layer: 0,
                offset: 0,
            })
            .unwrap(),
    ];
    let work_size = 1 << (FOLDING_STEPS - 3);
    let precomputed_eq = &eq_precomputed[FOLDING_STEPS - 3];
    // dbg!(&precomputed_eq);
    assert_eq!(work_size, precomputed_eq.len());

    fn interpolate_at_inf<F: Field>(a: F, b: F) -> F {
        let mut result = b;
        result.sub_assign(&a);
        result
    }

    // make prefactors table
    let mut eq_prefactors = [E::ZERO; 27]; // not important - we can multiply by it at the very end
    {
        // 1 - r at 0, r at 1

        let mut x0_factors = [E::ZERO; 2];
        x0_factors[0] = E::ONE;
        x0_factors[0].sub_assign(&previous_round_challenges[0]);
        x0_factors[1] = previous_round_challenges[0];

        let mut x1_factors = [E::ZERO; 2];
        x1_factors[0] = E::ONE;
        x1_factors[0].sub_assign(&previous_round_challenges[1]);
        x1_factors[1] = previous_round_challenges[1];

        let mut x2_factors = [E::ZERO; 2];
        x2_factors[0] = E::ONE;
        x2_factors[0].sub_assign(&previous_round_challenges[2]);
        x2_factors[1] = previous_round_challenges[2];

        // dbg!(x0_factors);
        // dbg!(x1_factors);
        // dbg!(x2_factors);

        for x0 in 0..2 {
            let x0_challenge = x0_factors[x0];
            let dst_offset = 9 * x0;
            for x1 in 0..2 {
                let x1_challenge = x1_factors[x1];
                let dst_offset = dst_offset + 3 * x1;
                let mut common_challenge = x1_challenge;
                common_challenge.mul_assign(&x0_challenge);
                {
                    eq_prefactors[dst_offset] = common_challenge;
                    eq_prefactors[dst_offset].mul_assign(&x2_factors[0]);
                    eq_prefactors[dst_offset + 1] = common_challenge;
                    eq_prefactors[dst_offset + 1].mul_assign(&x2_factors[1]);
                    eq_prefactors[dst_offset + 2] = interpolate_at_inf(
                        eq_prefactors[dst_offset],
                        eq_prefactors[dst_offset + 1],
                    );
                }
                // here we filled all options of (x0, x1, 0/1/inf)
            }

            // now extrapolate over x1
            for x2 in 0..3 {
                let src_0_idx = dst_offset + x2;
                let src_1_idx = dst_offset + 3 + x2;
                eq_prefactors[dst_offset + 3 * 2 + x2] =
                    interpolate_at_inf(eq_prefactors[src_0_idx], eq_prefactors[src_1_idx]);
            }
        }

        // and interpolate over x0
        for x1 in 0..3 {
            let dst_offset = 3 * x1;
            for x2 in 0..3 {
                let src_0_idx = 0 + dst_offset + x2;
                let src_1_idx = 9 + dst_offset + x2;
                eq_prefactors[18 + dst_offset + x2] =
                    interpolate_at_inf(eq_prefactors[src_0_idx], eq_prefactors[src_1_idx]);
            }
        }

        // for i in 0..27 {
        //     let x2 = i % 3;
        //     let x1 = (i / 3) % 3;
        //     let x0 = (i / 9) % 3;
        //     println!("Eq {} : {} : {} = {}", var_repr(x0), var_repr(x1), var_repr(x2), eq_prefactors[i]);
        // }
    }

    let mut accumulator = [E::ZERO; 27];

    {
        let mut a_values = [E::ZERO; 27];
        let mut b_values = [E::ZERO; 27];
        let x0_stride = 1 << (FOLDING_STEPS - 1);
        let x1_stride = x0_stride / 2;
        let x2_stride = x1_stride / 2;

        for row in 0..work_size {
            let absolute_row_idx = row;
            let eq_prefactor = &precomputed_eq[absolute_row_idx];

            for (dst, src) in [(&mut a_values, srcs[0]), (&mut b_values, srcs[1])] {
                // we need to extrapolate

                for x0 in 0..2 {
                    let stride = x0_stride * x0;
                    let dst_offset = 9 * x0;
                    for x1 in 0..2 {
                        let stride = stride + x1 * x1_stride;
                        let dst_offset = dst_offset + 3 * x1;
                        {
                            let src_0_idx = stride + absolute_row_idx;
                            let src_1_idx = src_0_idx + x2_stride;

                            dst[dst_offset] = src[src_0_idx];
                            dst[dst_offset + 1] = src[src_1_idx];
                            dst[dst_offset + 2] =
                                interpolate_at_inf(dst[dst_offset], dst[dst_offset + 1]);
                        }
                        // here we filled all options of (x0, x1, 0/1/inf)
                    }

                    // now extrapolate over x1
                    for x2 in 0..3 {
                        let src_0_idx = dst_offset + x2;
                        let src_1_idx = dst_offset + 3 + x2;
                        dst[dst_offset + 3 * 2 + x2] =
                            interpolate_at_inf(dst[src_0_idx], dst[src_1_idx]);
                    }
                }

                // and extrapolate over x0
                for x1 in 0..3 {
                    let dst_offset = 3 * x1;
                    for x2 in 0..3 {
                        let src_0_idx = 0 + dst_offset + x2;
                        let src_1_idx = 9 + dst_offset + x2;
                        dst[18 + dst_offset + x2] =
                            interpolate_at_inf(dst[src_0_idx], dst[src_1_idx]);
                    }
                }
            }

            // for x0 in 0..3 {
            //     let dst_offset = 9 * x0;
            //     for x1 in 0..3 {
            //         let dst_offset = dst_offset + 3 * x1;
            //         for x2 in 0..3 {
            //             let dst_offset = dst_offset + x2;
            //             let value = a_values[dst_offset];
            //             println!("{} : {} : {} = {}", var_repr(x0), var_repr(x1), var_repr(x2), value);
            //         }
            //     }
            // }

            // SIMD-y
            for i in 0..27 {
                let mut t = a_values[i];
                t.mul_assign(&b_values[i]);
                let mut acc = *eq_prefactor;
                let x2 = i % 3;
                let x1 = (i / 3) % 3;
                let x0 = (i / 9) % 3;
                // println!("Acc {} : {} : {} += {} * {}", var_repr(x0), var_repr(x1), var_repr(x2), acc, t);
                acc.mul_assign_by_base(&t);
                accumulator[i].add_assign(&acc);

                // let mut tt = *eq_prefactor;
                // tt.mul_assign(&eq_prefactors[i]);
                // println!("Eq {} : {} : {} = {}", var_repr(x0), var_repr(x1), var_repr(x2), tt);
            }
        }
    }

    {
        // self-check our batched description
        use crate::gkr::prover::sumcheck_loop::batch_evaluation::BatchedGKRDescription;
        use crate::gkr::prover::sumcheck_loop::windowed_mode::full_size_scratch::produce_descriptions_from_batched_description;
        let batched_description = BatchedGKRDescription {
            quadratic_part_base_by_base: Vec::new(),
            quadratic_part_base_by_ext: Vec::new(),
            quadratic_part_ext_by_ext: vec![(
                GKRAddress::InnerLayer {
                    layer: 0,
                    offset: 0,
                },
                vec![(
                    GKRAddress::InnerLayer {
                        layer: 0,
                        offset: 1,
                    },
                    E::ONE,
                )],
            )],
            linear_part_base_by_everything: Vec::new(),
            linear_part_ext_by_everything: Vec::new(),
            outputs_in_base: Vec::new(),
            outputs_in_ext: Vec::new(),
            constant_term: E::ZERO,
            _marker: core::marker::PhantomData::<F>,
        };
        dbg!(&batched_description);

        let (windowed_description, src_base, src_ext) =
            produce_descriptions_from_batched_description(&batched_description);
        let base_sources = vec![];
        let ext_sources: Vec<_> = src_ext
            .iter()
            .map(|el| {
                let slice = storage.try_get_ext_poly(*el).unwrap();
                DisjointAccessQuasiSlice::<_, false>::from_init_slice(slice)
            })
            .collect();

        let row_range = 0..2;
        let acc = evaluate_initial_with_full_sized_scratch(
            &base_sources,
            &ext_sources,
            &windowed_description,
            precomputed_eq,
            FOLDING_STEPS,
            row_range,
        );
        assert_eq!(acc, accumulator);
    }

    // for the first round we need to sum over x1 and x2

    let x1_and_x2_eq = make_eq_poly_in_full::<E>(&previous_round_challenges[1..][..2], &worker)
        .pop()
        .unwrap();
    assert_eq!(x1_and_x2_eq.len(), 4);

    let mut evals = [E::ZERO; 3];
    for x0 in 0..3 {
        let dst_offset = 9 * x0;
        for x1 in 0..2 {
            let eq_offset = x1 * 2;
            let dst_offset = dst_offset + 3 * x1;
            for x2 in 0..2 {
                let dst_offset = dst_offset + x2;
                let eq_offset = eq_offset + x2;
                let mut value = accumulator[dst_offset];
                value.mul_assign(&x1_and_x2_eq[eq_offset]);
                evals[x0].add_assign(&value);
            }
        }
    }

    let mut x0_eq_at_0 = E::ONE;
    x0_eq_at_0.sub_assign(&previous_round_challenges[0]);
    let mut eval_at_0 = evals[0];
    eval_at_0.mul_assign(&x0_eq_at_0);

    let x0_eq_at_1 = previous_round_challenges[0];
    let mut eval_at_1 = evals[1];
    eval_at_1.mul_assign(&x0_eq_at_1);

    let mut reconstructed_claim = eval_at_0;
    reconstructed_claim.add_assign(&eval_at_1);
    assert_eq!(reconstructed_claim, claim);

    // now we kind-of take challenge and re-evaluate
    let x0_eq_at_random =
        evaluate_eq_poly::<F, E>(&previous_round_challenges[0], &folding_challenges[0]);
    let mut c2 = evals[2];
    c2.mul_assign(&folding_challenges[0]);
    c2.mul_assign(&folding_challenges[0]);

    let mut c1 = evals[1];
    c1.sub_assign(&evals[2]);
    c1.sub_assign(&evals[0]);
    c1.mul_assign(&folding_challenges[0]);

    let c0 = evals[0];
    let mut new_claim = c0;
    new_claim.add_assign(&c1);
    new_claim.add_assign(&c2);
    new_claim.mul_assign(&x0_eq_at_random);

    dbg!(new_claim);

    claim = new_claim;
    let mut eq_prefactor = x0_eq_at_random;

    // now we bind and send again

    fn bind_univariate<F: Field>(c0: F, c1: F, c2: F, challenge: F) -> F {
        // The univariate is given by its values at {0, 1, inf}: c0 = P(0), c1 = P(1),
        // c2 = leading coefficient. So P(X) = c0 + (c1 - c2 - c0) * X + c2 * X^2.
        let mut c1 = c1;
        c1.sub_assign(&c2);
        c1.sub_assign(&c0);
        c1.mul_assign(&challenge);

        let mut c2 = c2;
        c2.mul_assign(&challenge);
        c2.mul_assign(&challenge);

        let mut binded = c0;
        binded.add_assign(&c1);
        binded.add_assign(&c2);

        binded
    }

    let mut next_accumulator = [E::ZERO; 9];
    for x1 in 0..3 {
        let src_offset = 3 * x1;
        let dst_offset = 3 * x1;
        for x2 in 0..3 {
            let src_offset = src_offset + x2;
            let dst_offset = dst_offset + x2;
            {
                let binded = bind_univariate(
                    accumulator[0 + src_offset],
                    accumulator[9 + src_offset],
                    accumulator[18 + src_offset],
                    folding_challenges[0],
                );
                next_accumulator[dst_offset] = binded;
            }
        }
    }

    let x2_eq = make_eq_poly_in_full::<E>(&previous_round_challenges[2..][..1], &worker)
        .pop()
        .unwrap();
    assert_eq!(x2_eq.len(), 2);
    let mut evals = [E::ZERO; 3];
    for x1 in 0..3 {
        let dst_offset = 3 * x1;
        for x2 in 0..2 {
            let dst_offset = dst_offset + x2;
            let eq_offset = x2;
            let mut value = next_accumulator[dst_offset];
            value.mul_assign(&x2_eq[eq_offset]);
            evals[x1].add_assign(&value);
        }
    }

    let mut x1_eq_at_0 = E::ONE;
    x1_eq_at_0.sub_assign(&previous_round_challenges[1]);
    let mut eval_at_0 = evals[0];
    eval_at_0.mul_assign(&x1_eq_at_0);

    let x1_eq_at_1 = previous_round_challenges[1];
    let mut eval_at_1 = evals[1];
    eval_at_1.mul_assign(&x1_eq_at_1);

    let mut reconstructed_claim = eval_at_0;
    reconstructed_claim.add_assign(&eval_at_1);
    reconstructed_claim.mul_assign(&eq_prefactor);
    assert_eq!(reconstructed_claim, claim);

    let x1_eq_at_random =
        evaluate_eq_poly::<F, E>(&previous_round_challenges[1], &folding_challenges[1]);
    let mut c2 = evals[2];
    c2.mul_assign(&folding_challenges[1]);
    c2.mul_assign(&folding_challenges[1]);

    let mut c1 = evals[1];
    c1.sub_assign(&evals[2]);
    c1.sub_assign(&evals[0]);
    c1.mul_assign(&folding_challenges[1]);

    let c0 = evals[0];
    let mut new_claim = c0;
    new_claim.add_assign(&c1);
    new_claim.add_assign(&c2);
    new_claim.mul_assign(&x1_eq_at_random);
    // `evals` carry no eq over the already-folded variables, so the claim must be scaled
    // by the eq prefactor accumulated over all prior rounds (here eq(c0, r0)), not only by
    // this round's factor x1_eq_at_random
    new_claim.mul_assign(&eq_prefactor);

    dbg!(new_claim);

    claim = new_claim;
    eq_prefactor.mul_assign(&x1_eq_at_random);

    // and the final one
    let accumulator = next_accumulator;
    let mut next_accumulator = [E::ZERO; 3];
    for x2 in 0..3 {
        let src_offset = x2;
        let dst_offset = x2;
        {
            let binded = bind_univariate(
                accumulator[0 + src_offset],
                accumulator[3 + src_offset],
                accumulator[6 + src_offset],
                folding_challenges[1],
            );
            next_accumulator[dst_offset] = binded;
        }
    }
    let evals = next_accumulator;

    let mut x2_eq_at_0 = E::ONE;
    x2_eq_at_0.sub_assign(&previous_round_challenges[2]);
    let mut eval_at_0 = evals[0];
    eval_at_0.mul_assign(&x2_eq_at_0);
    dbg!(eval_at_0);

    let x2_eq_at_1 = previous_round_challenges[2];
    let mut eval_at_1 = evals[1];
    eval_at_1.mul_assign(&x2_eq_at_1);
    dbg!(eval_at_1);

    let mut reconstructed_claim = eval_at_0;
    reconstructed_claim.add_assign(&eval_at_1);
    reconstructed_claim.mul_assign(&eq_prefactor);
    assert_eq!(reconstructed_claim, claim);

    // get next claim for explicit round
    let x2_eq_at_random =
        evaluate_eq_poly::<F, E>(&previous_round_challenges[2], &folding_challenges[2]);
    let mut c2 = evals[2];
    c2.mul_assign(&folding_challenges[2]);
    c2.mul_assign(&folding_challenges[2]);

    let mut c1 = evals[1];
    c1.sub_assign(&evals[2]);
    c1.sub_assign(&evals[0]);
    c1.mul_assign(&folding_challenges[2]);

    let c0 = evals[0];
    let mut new_claim = c0;
    new_claim.add_assign(&c1);
    new_claim.add_assign(&c2);
    new_claim.mul_assign(&x2_eq_at_random);
    new_claim.mul_assign(&eq_prefactor);

    dbg!(new_claim);

    claim = new_claim;
    eq_prefactor.mul_assign(&x2_eq_at_random);

    // and now we should fold/bind over the window

    let mut folded_polys = vec![];
    let binding_prefactor = make_eq_poly_in_full::<E>(&folding_challenges[..3], &worker)
        .pop()
        .unwrap();
    assert_eq!(binding_prefactor.len(), 8);
    // let mut values_scratch = [E::ZERO; 8];
    let x0_stride = 1 << (FOLDING_STEPS - 1);
    let x1_stride = x0_stride / 2;
    let x2_stride = x1_stride / 2;

    for poly in srcs.into_iter() {
        let mut result = Vec::with_capacity(2);
        // let dst = &mut values_scratch;

        for row in 0..work_size {
            let absolute_row_idx = row;
            let mut folded = E::ZERO;
            for x0 in 0..2 {
                let prefactor_idx = x0 * 4;
                let stride = x0_stride * x0;
                for x1 in 0..2 {
                    let prefactor_idx = prefactor_idx + x1 * 2;
                    let stride = stride + x1 * x1_stride;
                    for x2 in 0..2 {
                        let prefactor_idx = prefactor_idx + x2;
                        let stride = stride + x2 * x2_stride;
                        let src_idx = stride + absolute_row_idx;

                        let mut t = binding_prefactor[prefactor_idx];
                        t.mul_assign_by_base(&poly[src_idx]);
                        folded.add_assign(&t);
                    }
                    // here we filled all options of (x0, x1, 0/1/inf)
                }
            }

            result.push(folded);
        }
        assert_eq!(result.len(), work_size);

        folded_polys.push(result);
    }

    // and now we have explicit sumcheck
    let mut x3_eq_at_0 = E::ONE;
    x3_eq_at_0.sub_assign(&previous_round_challenges[3]);
    let mut eval_at_0 = folded_polys[0][0];
    eval_at_0.mul_assign(&folded_polys[1][0]);
    eval_at_0.mul_assign(&x3_eq_at_0);

    let x3_eq_at_1 = &previous_round_challenges[3];
    let mut eval_at_1 = folded_polys[0][1];
    eval_at_1.mul_assign(&folded_polys[1][1]);
    eval_at_1.mul_assign(&x3_eq_at_1);

    let mut reconstructed_claim = eval_at_0;
    reconstructed_claim.add_assign(&eval_at_1);
    reconstructed_claim.mul_assign(&eq_prefactor);
    assert_eq!(reconstructed_claim, claim);
}
