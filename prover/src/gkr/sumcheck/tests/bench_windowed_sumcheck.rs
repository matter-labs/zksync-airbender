use std::collections::BTreeMap;
use std::sync::Arc;

use cs::definitions::GKRAddress;
use fft::bitreverse_enumeration_inplace;
use field::{Field, FieldExtension, Mersenne31Field, Mersenne31Quartic};
use worker::Worker;

use crate::gkr::sumcheck::access_and_fold::BaseFieldPoly;
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
fn bench_simple_product() {
    type F = Mersenne31Field;
    type E = Mersenne31Quartic;

    const FOLDING_STEPS: usize = 24;
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
    let eq_reduced_len = eq_reduced_precomputed.len();

    let mut last_evaluations: BTreeMap<GKRAddress, [Mersenne31Quartic; 2]> = BTreeMap::new();
    let mut last_eq_poly_prefactor_contribution = E::ONE;

    let now = std::time::Instant::now();
    for step in 0..FOLDING_STEPS {
        assert_eq!(folding_challenges.len(), step);

        if step == 3 {
            panic!("Took {:?}", now.elapsed());
        }

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

            let [c0, c2] = evaluate_constant_and_quadratic_coeffs_with_precomputed_eq::<F, E>(
                &accumulator,
                &eq,
                &worker,
            );

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

            {
                let t =
                    evaluate_eq_poly::<F, E>(&folding_challenge, &previous_round_challenges[step]);
                last_eq_poly_prefactor_contribution = t;
            }

            claim = next_claim;
        } else {
            unreachable!()
        }
    }
}

#[test]
fn bench_windowed_product() {
    type F = Mersenne31Field;
    type E = Mersenne31Quartic;

    const FOLDING_STEPS: usize = 24;
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
    // dbg!(&eq_precomputed);

    let eq_reduced_precomputed = make_eq_poly_reduced::<E>(&previous_round_challenges, &worker);

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
    assert_eq!(work_size, precomputed_eq.len());

    // make prefactors table
    let eq_prefactors = [E::ONE; 27]; // not important - we can multiply by it at the very end

    fn interpolate_at_inf<F: Field>(a: F, b: F) -> F {
        let mut result = b;
        result.sub_assign(&a);
        result
    }

    let now = std::time::Instant::now();
    worker.scope(work_size, |scope, geometry| {
        for thread_idx in 0..geometry.len() {
            let chunk_size = geometry.get_chunk_size(thread_idx);
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);

            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                let mut accumulator = [E::ZERO; 27];
                let mut a_values = [E::ZERO; 27];
                let mut b_values = [E::ZERO; 27];
                let x0_stride = 1 << (FOLDING_STEPS - 1);
                let x1_stride = x0_stride / 2;
                let x2_stride = x1_stride / 2;

                for i in 0..chunk_size {
                    let absolute_row_idx = chunk_start + i;
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
                                    let src_0_idx = absolute_row_idx + stride;
                                    let src_1_idx = absolute_row_idx + stride + x2_stride;

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

                        // and interpolate over x0
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

                    // SIMD-y
                    for i in 0..27 {
                        let mut t = a_values[i];
                        t.mul_assign(&b_values[i]);
                        let mut acc = *eq_prefactor;
                        acc.mul_assign_by_base(&t);
                        accumulator[i].add_assign(&acc);
                    }
                }
            });
        }
    });

    panic!("Took {:?}", now.elapsed());
}

#[test]
fn bench_windowed_base_product() {
    type F = Mersenne31Field;
    type E = Mersenne31Quartic;

    const FOLDING_STEPS: usize = 24;
    const POLY_SIZE: usize = 1 << FOLDING_STEPS;
    let worker = Worker::new_with_num_threads(8);

    let a: Vec<_> = (0..POLY_SIZE)
        .map(|el| F::from_u64_with_reduction(el as u64))
        .collect();

    let b: Vec<_> = (0..POLY_SIZE)
        .map(|el| F::from_u64_with_reduction(el as u64))
        .collect();

    let output: Vec<_> = a
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

    storage.layers.push(layer_0);
    let mut layer_1 = GKRLayerSource::default();
    layer_1.layer_idx = 1;
    layer_1.base_field_inputs.insert(
        GKRAddress::InnerLayer {
            layer: 1,
            offset: 0,
        },
        BaseFieldPoly::new(output.into_boxed_slice()),
    );

    storage.layers.push(layer_1);

    let previous_round_challenges: Vec<E> = (0..FOLDING_STEPS)
        .map(|el| E::from_base(F::from_u64_with_reduction(1u64 << (el + 1))))
        .collect();
    // dbg!(&previous_round_challenges);

    let eq_precomputed = make_eq_poly_in_full::<E>(&previous_round_challenges, &worker);
    // dbg!(&eq_precomputed);

    let eq_reduced_precomputed = make_eq_poly_reduced::<E>(&previous_round_challenges, &worker);

    // merged window of 3 variables at once

    let srcs = [
        storage
            .try_get_base_poly(GKRAddress::InnerLayer {
                layer: 0,
                offset: 0,
            })
            .unwrap(),
        storage
            .try_get_base_poly(GKRAddress::InnerLayer {
                layer: 0,
                offset: 0,
            })
            .unwrap(),
    ];
    let work_size = 1 << (FOLDING_STEPS - 3);
    let precomputed_eq = &eq_precomputed[FOLDING_STEPS - 3];
    assert_eq!(work_size, precomputed_eq.len());

    // make prefactors table
    let eq_prefactors = [E::ONE; 27]; // not important - we can multiply by it at the very end

    fn interpolate_at_inf<F: Field>(a: F, b: F) -> F {
        let mut result = b;
        result.sub_assign(&a);
        result
    }

    let now = std::time::Instant::now();
    worker.scope(work_size, |scope, geometry| {
        for thread_idx in 0..geometry.len() {
            let chunk_size = geometry.get_chunk_size(thread_idx);
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);

            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                let mut accumulator = [E::ZERO; 27];
                let mut a_values = [F::ZERO; 27];
                let mut b_values = [F::ZERO; 27];
                let x0_stride = 1 << (FOLDING_STEPS - 1);
                let x1_stride = x0_stride / 2;
                let x2_stride = x1_stride / 2;

                for i in 0..chunk_size {
                    let absolute_row_idx = chunk_start + i;
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
                                    let src_0_idx = absolute_row_idx + stride;
                                    let src_1_idx = absolute_row_idx + stride + x2_stride;

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

                        // and interpolate over x0
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

                    // SIMD-y
                    for i in 0..27 {
                        let mut t = a_values[i];
                        t.mul_assign(&b_values[i]);
                        let mut acc = *eq_prefactor;
                        acc.mul_assign_by_base(&t);
                        accumulator[i].add_assign(&acc);
                    }
                }
            });
        }
    });

    panic!("Took {:?}", now.elapsed());
}
