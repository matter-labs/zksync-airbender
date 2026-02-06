use std::collections::BTreeMap;

use cs::definitions::GKRAddress;
use field::{Field, FieldExtension, Mersenne31Field, Mersenne31Quartic, PrimeField};
use worker::Worker;

use crate::gkr::sumcheck::{
    eq_poly::*,
    evaluate_eq_poly, evaluate_eq_poly_at_line, evaluate_small_univariate_poly,
    evaluation_kernels::{
        BatchedGKRKernel, ExtensionCopyGKRRelation, LookupBaseMinusMultiplicityByBaseGKRRelation,
        LookupPairGKRRelation, MaskIntoIdentityProductGKRRelation, SameSizeProductGKRRelation,
    },
    output_univariate_monomial_form_max_quadratic,
};

use super::utils::*;

type F = Mersenne31Field;
type E = Mersenne31Quartic;

#[test]
fn test_same_size_product_basic() {
    const FOLDING_STEPS: usize = 4;
    const POLY_SIZE: usize = 1 << FOLDING_STEPS;

    let addr_a = GKRAddress::BaseLayerMemory(0);
    let addr_b = GKRAddress::BaseLayerMemory(1);
    let addr_out = GKRAddress::InnerLayer {
        layer: 1,
        offset: 0,
    };

    let a = random_poly_in_ext::<F, E>(POLY_SIZE);
    let b = random_poly_in_ext::<F, E>(POLY_SIZE);
    let output = compute_product::<F, E>(&a, &b);

    let mut storage = setup_storage::<F, E>(
        vec![(addr_a, a.clone()), (addr_b, b.clone())],
        vec![(addr_out, output)],
    );

    let kernel = SameSizeProductGKRRelation {
        inputs: [addr_a, addr_b],
        output: addr_out,
    };

    let (claim, prev_challenges, folding_challenges, expected_evals) = setup_sumcheck_params(
        &storage,
        &[addr_out],
        &[(addr_a, &a), (addr_b, &b)],
        FOLDING_STEPS,
    );

    run_sumcheck_test(
        &mut storage,
        &kernel,
        claim,
        &prev_challenges,
        &folding_challenges,
        &expected_evals,
    );
}

#[test]
fn test_same_size_product_inner_layer() {
    const FOLDING_STEPS: usize = 4;
    const POLY_SIZE: usize = 1 << FOLDING_STEPS;

    // SameSizeProductGKRRelation with InnerLayer addresses
    let addr_a = GKRAddress::InnerLayer {
        layer: 0,
        offset: 0,
    };
    let addr_b = GKRAddress::InnerLayer {
        layer: 0,
        offset: 1,
    };
    let addr_out = GKRAddress::InnerLayer {
        layer: 1,
        offset: 0,
    };

    let a = random_poly_in_ext::<F, E>(POLY_SIZE);
    let b = random_poly_in_ext::<F, E>(POLY_SIZE);
    let output = compute_product::<F, E>(&a, &b);

    let mut storage = setup_storage::<F, E>(
        vec![(addr_a, a.clone()), (addr_b, b.clone())],
        vec![(addr_out, output)],
    );

    let kernel = SameSizeProductGKRRelation {
        inputs: [addr_a, addr_b],
        output: addr_out,
    };

    let (claim, prev_challenges, folding_challenges, expected_evals) = setup_sumcheck_params(
        &storage,
        &[addr_out],
        &[(addr_a, &a), (addr_b, &b)],
        FOLDING_STEPS,
    );

    run_sumcheck_test(
        &mut storage,
        &kernel,
        claim,
        &prev_challenges,
        &folding_challenges,
        &expected_evals,
    );
}

#[test]
fn test_lookup_pair() {
    const FOLDING_STEPS: usize = 4;
    const POLY_SIZE: usize = 1 << FOLDING_STEPS;

    // a/b + c/d = (a*d + c*b) / (b*d)
    let a = random_poly_in_ext::<F, E>(POLY_SIZE);
    let b = random_poly_in_ext::<F, E>(POLY_SIZE);
    let c = random_poly_in_ext::<F, E>(POLY_SIZE);
    let d = random_poly_in_ext::<F, E>(POLY_SIZE);

    // Output: [a*d + c*b, b*d]
    let (output_num, output_den) = compute_lookup_add::<F, E>(&a, &b, &c, &d);

    let mut storage = setup_storage::<F, E>(
        vec![
            (GKRAddress::BaseLayerMemory(0), a.clone()),
            (GKRAddress::BaseLayerMemory(1), b.clone()),
            (GKRAddress::BaseLayerMemory(2), c.clone()),
            (GKRAddress::BaseLayerMemory(3), d.clone()),
        ],
        vec![
            (
                GKRAddress::InnerLayer {
                    layer: 1,
                    offset: 0,
                },
                output_num,
            ),
            (
                GKRAddress::InnerLayer {
                    layer: 1,
                    offset: 1,
                },
                output_den,
            ),
        ],
    );

    let kernel = LookupPairGKRRelation {
        inputs: [
            [
                GKRAddress::BaseLayerMemory(0),
                GKRAddress::BaseLayerMemory(1),
            ],
            [
                GKRAddress::BaseLayerMemory(2),
                GKRAddress::BaseLayerMemory(3),
            ],
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
    };

    let (claim, prev_challenges, folding_challenges, expected_evals) = setup_sumcheck_params(
        &storage,
        &[
            GKRAddress::InnerLayer {
                layer: 1,
                offset: 0,
            },
            GKRAddress::InnerLayer {
                layer: 1,
                offset: 1,
            },
        ],
        &[
            (GKRAddress::BaseLayerMemory(0), &a),
            (GKRAddress::BaseLayerMemory(1), &b),
            (GKRAddress::BaseLayerMemory(2), &c),
            (GKRAddress::BaseLayerMemory(3), &d),
        ],
        FOLDING_STEPS,
    );

    run_sumcheck_test(
        &mut storage,
        &kernel,
        claim,
        &prev_challenges,
        &folding_challenges,
        &expected_evals,
    );
}

#[test]
fn test_extension_copy() {
    const FOLDING_STEPS: usize = 4;
    const POLY_SIZE: usize = 1 << FOLDING_STEPS;

    let a = random_poly_in_ext::<F, E>(POLY_SIZE);

    // Copy: output = input (same polynomial)
    let output = a.clone();

    let mut storage = setup_storage::<F, E>(
        vec![(GKRAddress::BaseLayerMemory(0), a.clone())],
        vec![(
            GKRAddress::InnerLayer {
                layer: 1,
                offset: 0,
            },
            output,
        )],
    );

    let kernel = ExtensionCopyGKRRelation {
        input: GKRAddress::BaseLayerMemory(0),
        output: GKRAddress::InnerLayer {
            layer: 1,
            offset: 0,
        },
    };

    let (claim, prev_challenges, folding_challenges, expected_evals) = setup_sumcheck_params(
        &storage,
        &[GKRAddress::InnerLayer {
            layer: 1,
            offset: 0,
        }],
        &[(GKRAddress::BaseLayerMemory(0), &a)],
        FOLDING_STEPS,
    );

    run_sumcheck_test(
        &mut storage,
        &kernel,
        claim,
        &prev_challenges,
        &folding_challenges,
        &expected_evals,
    );
}

#[test]
#[ignore = "base field access in get_for_sumcheck_round_1 incomplete"]
fn test_mask_into_identity_product() {
    const FOLDING_STEPS: usize = 4;
    const POLY_SIZE: usize = 1 << FOLDING_STEPS;

    let worker = Worker::new_with_num_threads(1);

    let addr_input = GKRAddress::BaseLayerMemory(0);
    let addr_mask = GKRAddress::BaseLayerMemory(1);
    let addr_out = GKRAddress::InnerLayer {
        layer: 1,
        offset: 0,
    };

    let input: Vec<E> = random_poly_in_ext::<F, E>(POLY_SIZE);
    let mask: Vec<F> = create_alternating_mask_base::<F>(POLY_SIZE);

    // Compute expected output: input * mask + (1 - mask)
    let output = compute_mask_identity_mixed::<F, E>(&input, &mask);

    // Set up storage with mixed inputs
    let mut storage = setup_mixed_storage::<F, E>(
        vec![(addr_mask, mask.clone())],   // base field inputs
        vec![(addr_input, input.clone())], // extension field inputs
        vec![(addr_out, output.clone())],
    );

    let kernel = MaskIntoIdentityProductGKRRelation {
        input: addr_input,
        mask: addr_mask,
        output: addr_out,
    };

    let prev_challenges: Vec<E> = random_poly_in_ext::<F, E>(FOLDING_STEPS);
    let folding_challenges_precomputed: Vec<E> = random_poly_in_ext::<F, E>(FOLDING_STEPS);
    let eq_precomputed = make_eq_poly_in_full::<F, E>(&prev_challenges);
    let eq_last = eq_precomputed.last().unwrap();

    let claim = evaluate_with_precomputed_eq_ext::<F, E>(&output, eq_last);

    let batch_challenges =
        vec![E::from_base(F::ONE); BatchedGKRKernel::<F, E>::num_challenges(&kernel)];
    let mut folding_challenges = vec![];
    let eq_reduced = make_eq_poly_reduced::<F, E>(&prev_challenges);
    let mut last_evaluations = BTreeMap::new();
    let mut eq_prefactor = E::ONE;
    let mut current_claim = claim;

    for step in 0..FOLDING_STEPS {
        let is_final = step + 1 == FOLDING_STEPS;
        let acc_size = if is_final {
            1
        } else {
            1 << (FOLDING_STEPS - step - 1)
        };
        let mut accumulator = vec![[E::ZERO; 2]; acc_size];

        kernel.evaluate_over_storage(
            &mut storage,
            step,
            &batch_challenges,
            &folding_challenges,
            &mut accumulator,
            FOLDING_STEPS,
            &mut last_evaluations,
            &worker,
        );

        let folding_challenge = folding_challenges_precomputed[step];

        if !is_final {
            let eq = &eq_reduced[eq_reduced.len() - 1 - step];
            let [c0, c2] = evaluate_constant_and_quadratic_coeffs_with_precomputed_eq::<F, E>(
                &accumulator,
                eq,
            );

            let mut normalized = current_claim;
            normalized.mul_assign(&eq_prefactor.inverse().unwrap());
            let coeffs = output_univariate_monomial_form_max_quadratic::<F, E>(
                prev_challenges[step],
                normalized,
                c0,
                c2,
            );

            let s0 = evaluate_small_univariate_poly::<F, E>(&coeffs, &E::ZERO);
            let s1 = evaluate_small_univariate_poly::<F, E>(&coeffs, &E::ONE);
            let mut v = s0;
            v.add_assign(&s1);
            v.mul_assign(&eq_prefactor);
            assert_eq!(v, current_claim, "Sumcheck failed at step {}", step);

            current_claim = evaluate_small_univariate_poly::<F, E>(&coeffs, &folding_challenge);
            eq_prefactor = evaluate_eq_poly::<F, E>(&folding_challenge, &prev_challenges[step]);
        } else {
            let [[f0, f1]] = accumulator.try_into().unwrap();
            let [eq0, eq1] = evaluate_eq_poly_at_line::<F, E>(prev_challenges.last().unwrap());
            let mut t0 = eq0;
            t0.mul_assign(&f0);
            let mut t1 = eq1;
            t1.mul_assign(&f1);
            let mut claim_inner = t0;
            claim_inner.add_assign(&t1);
            let mut recomputed = claim_inner;
            recomputed.mul_assign(&eq_prefactor);
            assert_eq!(current_claim, recomputed, "Final claim verification failed");

            // Verify final evaluations
            let eq_for_evals = make_eq_poly_in_full::<F, E>(
                &[&folding_challenges[..], &[folding_challenge]].concat(),
            );
            let eq_eval_last = eq_for_evals.last().unwrap();

            // Check extension field input
            let expected_input = evaluate_with_precomputed_eq_ext::<F, E>(&input, eq_eval_last);
            let [f0, f1] = last_evaluations.remove(&addr_input).unwrap();
            let mut actual = f1;
            actual.sub_assign(&f0);
            actual.mul_assign(&folding_challenge);
            actual.add_assign(&f0);
            assert_eq!(actual, expected_input, "Eval mismatch for input");

            // Check base field mask
            let expected_mask = evaluate_base_with_precomputed_eq::<F, E>(&mask, eq_eval_last);
            let [f0, f1] = last_evaluations.remove(&addr_mask).unwrap();
            let mut actual = f1;
            actual.sub_assign(&f0);
            actual.mul_assign(&folding_challenge);
            actual.add_assign(&f0);
            assert_eq!(actual, expected_mask, "Eval mismatch for mask");
        }
        folding_challenges.push(folding_challenge);
    }
}
