use std::collections::BTreeMap;

use cs::definitions::GKRAddress;
use field::{Field, FieldExtension, Mersenne31Field, Mersenne31Quartic, PrimeField};
use worker::Worker;

use super::utils::*;
use crate::gkr::sumcheck::{
    eq_poly::*,
    evaluate_eq_poly, evaluate_eq_poly_at_line, evaluate_small_univariate_poly,
    evaluation_kernels::{
        BatchedGKRKernel, ExtensionCopyGKRRelation, LookupPairGKRRelation,
        SameSizeProductGKRRelation,
    },
    output_univariate_monomial_form_max_quadratic,
};

type F = Mersenne31Field;
type E = Mersenne31Quartic;

#[test]
fn test_batched_kernels() {
    const FOLDING_STEPS: usize = 4;
    const POLY_SIZE: usize = 1 << FOLDING_STEPS;

    // Create input polynomials
    let copy_input = random_poly_in_ext::<F, E>(POLY_SIZE);
    let product_a = random_poly_in_ext::<F, E>(POLY_SIZE);
    let product_b = random_poly_in_ext::<F, E>(POLY_SIZE);
    let lookup_a = random_poly_in_ext::<F, E>(POLY_SIZE);
    let lookup_b = random_poly_in_ext::<F, E>(POLY_SIZE);
    let lookup_c = random_poly_in_ext::<F, E>(POLY_SIZE);
    let lookup_d = random_poly_in_ext::<F, E>(POLY_SIZE);

    // Compute outputs
    let copy_output = copy_input.clone();
    let product_output = compute_product::<F, E>(&product_a, &product_b);
    let (lookup_num, lookup_den) =
        compute_lookup_add::<F, E>(&lookup_a, &lookup_b, &lookup_c, &lookup_d);

    // Input addresses
    let addr_copy_in = GKRAddress::BaseLayerMemory(0);
    let addr_product_a = GKRAddress::BaseLayerMemory(1);
    let addr_product_b = GKRAddress::BaseLayerMemory(2);
    let addr_lookup_a = GKRAddress::BaseLayerMemory(3);
    let addr_lookup_b = GKRAddress::BaseLayerMemory(4);
    let addr_lookup_c = GKRAddress::BaseLayerMemory(5);
    let addr_lookup_d = GKRAddress::BaseLayerMemory(6);

    // Output addresses
    let addr_copy_out = GKRAddress::InnerLayer {
        layer: 1,
        offset: 0,
    };
    let addr_product_out = GKRAddress::InnerLayer {
        layer: 1,
        offset: 1,
    };
    let addr_lookup_num = GKRAddress::InnerLayer {
        layer: 1,
        offset: 2,
    };
    let addr_lookup_den = GKRAddress::InnerLayer {
        layer: 1,
        offset: 3,
    };

    // Build storage
    let inputs = vec![
        (addr_copy_in, copy_input.clone()),
        (addr_product_a, product_a.clone()),
        (addr_product_b, product_b.clone()),
        (addr_lookup_a, lookup_a.clone()),
        (addr_lookup_b, lookup_b.clone()),
        (addr_lookup_c, lookup_c.clone()),
        (addr_lookup_d, lookup_d.clone()),
    ];
    let outputs = vec![
        (addr_copy_out, copy_output.clone()),
        (addr_product_out, product_output.clone()),
        (addr_lookup_num, lookup_num.clone()),
        (addr_lookup_den, lookup_den.clone()),
    ];
    let mut storage = setup_storage::<F, E>(inputs, outputs);

    // Define kernels
    let copy_kernel = ExtensionCopyGKRRelation {
        input: addr_copy_in,
        output: addr_copy_out,
    };
    let product_kernel = SameSizeProductGKRRelation {
        inputs: [addr_product_a, addr_product_b],
        output: addr_product_out,
    };
    let lookup_kernel = LookupPairGKRRelation {
        inputs: [
            [addr_lookup_a, addr_lookup_b],
            [addr_lookup_c, addr_lookup_d],
        ],
        outputs: [addr_lookup_num, addr_lookup_den],
    };

    // Batch challenges
    let copy_bc = E::from_base(F::from_u64_with_reduction(3));
    let product_bc = E::from_base(F::from_u64_with_reduction(5));
    let lookup_bc = [
        E::from_base(F::from_u64_with_reduction(11)),
        E::from_base(F::from_u64_with_reduction(13)),
    ];

    // Compute combined claim
    let prev_challenges: Vec<E> = random_poly_in_ext::<F, E>(FOLDING_STEPS);
    let folding_challenges_precomputed: Vec<E> = random_poly_in_ext::<F, E>(FOLDING_STEPS);
    let eq_precomputed = make_eq_poly_in_full::<F, E>(&prev_challenges);
    let eq_last = eq_precomputed.last().unwrap();

    let output_polys = [&copy_output, &product_output, &lookup_num, &lookup_den];
    let batch_challenges = [copy_bc, product_bc, lookup_bc[0], lookup_bc[1]];

    let mut combined_claim = E::ZERO;
    for (poly, bc) in output_polys.iter().zip(batch_challenges.iter()) {
        let mut t = *bc;
        t.mul_assign(&evaluate_with_precomputed_eq_ext::<F, E>(poly, eq_last));
        combined_claim.add_assign(&t);
    }

    // Run batched sumcheck
    let worker = Worker::new_with_num_threads(1);
    let mut claim = combined_claim;
    let mut folding_challenges = vec![];
    let eq_reduced = make_eq_poly_reduced::<F, E>(&prev_challenges);
    let mut last_evaluations = BTreeMap::new();
    let mut eq_prefactor = E::ONE;

    for step in 0..FOLDING_STEPS {
        let is_final = step + 1 == FOLDING_STEPS;
        let acc_size = if is_final {
            1
        } else {
            1 << (FOLDING_STEPS - step - 1)
        };
        let mut accumulator = vec![[E::ZERO; 2]; acc_size];

        // Evaluate all kernels into the same accumulator
        copy_kernel.evaluate_over_storage(
            &mut storage,
            step,
            &[copy_bc],
            &folding_challenges,
            &mut accumulator,
            FOLDING_STEPS,
            &mut last_evaluations,
            &worker,
        );
        product_kernel.evaluate_over_storage(
            &mut storage,
            step,
            &[product_bc],
            &folding_challenges,
            &mut accumulator,
            FOLDING_STEPS,
            &mut last_evaluations,
            &worker,
        );
        lookup_kernel.evaluate_over_storage(
            &mut storage,
            step,
            &lookup_bc,
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

            let mut normalized = claim;
            normalized.mul_assign(&eq_prefactor.inverse().unwrap());
            let coeffs = output_univariate_monomial_form_max_quadratic::<F, E>(
                prev_challenges[step],
                normalized,
                c0,
                c2,
            );

            // Verify s(0) + s(1) == claim / prefactor
            let s0 = evaluate_small_univariate_poly::<F, E>(&coeffs, &E::ZERO);
            let s1 = evaluate_small_univariate_poly::<F, E>(&coeffs, &E::ONE);
            let mut v = s0;
            v.add_assign(&s1);
            v.mul_assign(&eq_prefactor);
            assert_eq!(v, claim, "Sumcheck failed at step {}", step);

            claim = evaluate_small_univariate_poly::<F, E>(&coeffs, &folding_challenge);
            eq_prefactor = evaluate_eq_poly::<F, E>(&folding_challenge, &prev_challenges[step]);
        } else {
            // Final step verification
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
            assert_eq!(claim, recomputed, "Final claim verification failed");

            // Verify final evaluations
            let eq_for_evals = make_eq_poly_in_full::<F, E>(
                &[&folding_challenges[..], &[folding_challenge]].concat(),
            );
            let eq_eval_last = eq_for_evals.last().unwrap();
            let input_polys: Vec<(GKRAddress, &[E])> = vec![
                (addr_copy_in, &copy_input),
                (addr_product_a, &product_a),
                (addr_product_b, &product_b),
                (addr_lookup_a, &lookup_a),
                (addr_lookup_b, &lookup_b),
                (addr_lookup_c, &lookup_c),
                (addr_lookup_d, &lookup_d),
            ];
            for (addr, poly) in input_polys {
                let expected = evaluate_with_precomputed_eq_ext::<F, E>(poly, eq_eval_last);
                let [f0, f1] = last_evaluations.remove(&addr).unwrap();
                let mut actual = f1;
                actual.sub_assign(&f0);
                actual.mul_assign(&folding_challenge);
                actual.add_assign(&f0);
                assert_eq!(actual, expected, "Eval mismatch for {:?}", addr);
            }
        }
        folding_challenges.push(folding_challenge);
    }
}
