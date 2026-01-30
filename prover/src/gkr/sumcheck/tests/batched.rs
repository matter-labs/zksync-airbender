use std::collections::BTreeMap;

use cs::definitions::GKRAddress;
use field::{Field, FieldExtension, Mersenne31Field, Mersenne31Quartic, PrimeField};
use worker::Worker;

use super::utils::*;
use crate::gkr::sumcheck::{
    eq_poly::*, evaluate_eq_poly, evaluate_eq_poly_at_line, evaluate_small_univariate_poly,
    evaluation_kernels::*, output_univariate_monomial_form_max_quadratic,
};

type F = Mersenne31Field;
type E = Mersenne31Quartic;

/// Test batching all 6 implemented kernels in a single sumcheck.
#[test]
fn test_batched_kernels() {
    const FOLDING_STEPS: usize = 3;
    const POLY_SIZE: usize = 1 << FOLDING_STEPS;

    // Create input polynomials using helpers
    let copy_input = random_poly_in_ext::<F, E>(POLY_SIZE);
    let initial_b = random_poly_in_ext::<F, E>(POLY_SIZE);
    let initial_c = random_poly_in_ext::<F, E>(POLY_SIZE);
    let unbalanced_d = random_poly_in_ext::<F, E>(POLY_SIZE);
    let unbalanced_e = random_poly_in_ext::<F, E>(POLY_SIZE);
    let mask_f = random_poly_in_ext::<F, E>(POLY_SIZE);
    let mask_m = create_alternating_mask::<F, E>(POLY_SIZE);
    let lookup_sub_g = random_poly_in_ext::<F, E>(POLY_SIZE);
    let lookup_sub_h = random_poly_in_ext::<F, E>(POLY_SIZE);
    let lookup_sub_i = random_poly_in_ext::<F, E>(POLY_SIZE);
    let lookup_sub_j = random_poly_in_ext::<F, E>(POLY_SIZE);
    let lookup_add_k = random_poly_in_ext::<F, E>(POLY_SIZE);
    let lookup_add_l = random_poly_in_ext::<F, E>(POLY_SIZE);
    let lookup_add_m = random_poly_in_ext::<F, E>(POLY_SIZE);
    let lookup_add_n = random_poly_in_ext::<F, E>(POLY_SIZE);

    // Compute outputs using helpers
    let copy_output = copy_input.clone();
    let initial_output = compute_product::<F, E>(&initial_b, &initial_c);
    let unbalanced_output = compute_product::<F, E>(&unbalanced_d, &unbalanced_e);
    let mask_output = compute_mask_identity::<F, E>(&mask_f, &mask_m);
    let (lookup_sub_num, lookup_sub_den) =
        compute_lookup_sub::<F, E>(&lookup_sub_g, &lookup_sub_h, &lookup_sub_i, &lookup_sub_j);
    let (lookup_add_num, lookup_add_den) =
        compute_lookup_add::<F, E>(&lookup_add_k, &lookup_add_l, &lookup_add_m, &lookup_add_n);

    // Define input addresses with correct types for validation:
    // - Copy: non-cached
    // - InitialGrandProduct: both Cached
    // - UnbalancedGrandProduct: one Cached, one non-cached
    // - LookupWithCachedDensAndSetup: inputs[1] (denominator) must be Cached
    // - Others: non-cached
    let addr_copy = GKRAddress::BaseLayerMemory(0);
    let addr_initial_b = GKRAddress::Cached {
        layer: 0,
        offset: 0,
    };
    let addr_initial_c = GKRAddress::Cached {
        layer: 0,
        offset: 1,
    };
    let addr_unbalanced_cached = GKRAddress::Cached {
        layer: 0,
        offset: 2,
    };
    let addr_unbalanced_scalar = GKRAddress::BaseLayerMemory(1);
    let addr_mask_f = GKRAddress::BaseLayerMemory(2);
    let addr_mask_m = GKRAddress::BaseLayerMemory(3);
    let addr_lookup_sub_g = GKRAddress::BaseLayerMemory(4);
    let addr_lookup_sub_h = GKRAddress::Cached {
        layer: 0,
        offset: 3,
    }; // denominator - must be Cached
    let addr_lookup_sub_i = GKRAddress::BaseLayerMemory(5);
    let addr_lookup_sub_j = GKRAddress::BaseLayerMemory(6);
    let addr_lookup_add_k = GKRAddress::BaseLayerMemory(7);
    let addr_lookup_add_l = GKRAddress::BaseLayerMemory(8);
    let addr_lookup_add_m = GKRAddress::BaseLayerMemory(9);
    let addr_lookup_add_n = GKRAddress::BaseLayerMemory(10);

    // Build storage
    let inputs = vec![
        (addr_copy, copy_input.clone()),
        (addr_initial_b, initial_b.clone()),
        (addr_initial_c, initial_c.clone()),
        (addr_unbalanced_cached, unbalanced_d.clone()),
        (addr_unbalanced_scalar, unbalanced_e.clone()),
        (addr_mask_f, mask_f.clone()),
        (addr_mask_m, mask_m.clone()),
        (addr_lookup_sub_g, lookup_sub_g.clone()),
        (addr_lookup_sub_h, lookup_sub_h.clone()),
        (addr_lookup_sub_i, lookup_sub_i.clone()),
        (addr_lookup_sub_j, lookup_sub_j.clone()),
        (addr_lookup_add_k, lookup_add_k.clone()),
        (addr_lookup_add_l, lookup_add_l.clone()),
        (addr_lookup_add_m, lookup_add_m.clone()),
        (addr_lookup_add_n, lookup_add_n.clone()),
    ];
    // Output addresses
    let addr_out_copy = GKRAddress::InnerLayer {
        layer: 1,
        offset: 0,
    };
    let addr_out_initial = GKRAddress::InnerLayer {
        layer: 1,
        offset: 1,
    };
    let addr_out_unbalanced = GKRAddress::InnerLayer {
        layer: 1,
        offset: 2,
    };
    let addr_out_mask = GKRAddress::InnerLayer {
        layer: 1,
        offset: 3,
    };
    let addr_out_lookup_sub_num = GKRAddress::InnerLayer {
        layer: 1,
        offset: 4,
    };
    let addr_out_lookup_sub_den = GKRAddress::InnerLayer {
        layer: 1,
        offset: 5,
    };
    let addr_out_lookup_add_num = GKRAddress::InnerLayer {
        layer: 1,
        offset: 6,
    };
    let addr_out_lookup_add_den = GKRAddress::InnerLayer {
        layer: 1,
        offset: 7,
    };

    let outputs = vec![
        (addr_out_copy, copy_output.clone()),
        (addr_out_initial, initial_output.clone()),
        (addr_out_unbalanced, unbalanced_output.clone()),
        (addr_out_mask, mask_output.clone()),
        (addr_out_lookup_sub_num, lookup_sub_num.clone()),
        (addr_out_lookup_sub_den, lookup_sub_den.clone()),
        (addr_out_lookup_add_num, lookup_add_num.clone()),
        (addr_out_lookup_add_den, lookup_add_den.clone()),
    ];
    let mut storage = setup_storage::<F, E>(inputs, outputs);

    // Define kernels with correct address types
    let copy_kernel = CopyGKRRelation {
        input: addr_copy,
        output: addr_out_copy,
    };
    let initial_kernel = InitialGrandProductFromCachesGKRRelation {
        inputs: [addr_initial_b, addr_initial_c],
        output: addr_out_initial,
    };
    let unbalanced_kernel = UnbalancedGrandProductWithCacheGKRRelation {
        inputs: [addr_unbalanced_cached, addr_unbalanced_scalar],
        output: addr_out_unbalanced,
    };
    let mask_kernel = MaskIntoIdentityProductGKRRelation {
        input: addr_mask_f,
        mask: addr_mask_m,
        output: addr_out_mask,
    };
    let lookup_sub_kernel = LookupWithCachedDensAndSetupGKRRelation {
        input: [addr_lookup_sub_g, addr_lookup_sub_h],
        setup: [addr_lookup_sub_i, addr_lookup_sub_j],
        output: [addr_out_lookup_sub_num, addr_out_lookup_sub_den],
    };
    let lookup_add_kernel = LookupPairGKRRelation {
        inputs: [
            [addr_lookup_add_k, addr_lookup_add_l],
            [addr_lookup_add_m, addr_lookup_add_n],
        ],
        outputs: [addr_out_lookup_add_num, addr_out_lookup_add_den],
    };

    // Batch challenges
    let copy_bc = E::from_base(F::from_u64_with_reduction(3));
    let initial_bc = E::from_base(F::from_u64_with_reduction(5));
    let unbalanced_bc = E::from_base(F::from_u64_with_reduction(7));
    let mask_bc = E::from_base(F::from_u64_with_reduction(11));
    let lookup_sub_bc = [
        E::from_base(F::from_u64_with_reduction(13)),
        E::from_base(F::from_u64_with_reduction(17)),
    ];
    let lookup_add_bc = [
        E::from_base(F::from_u64_with_reduction(19)),
        E::from_base(F::from_u64_with_reduction(23)),
    ];

    // Compute combined claim
    let prev_challenges: Vec<E> = random_poly_in_ext::<F, E>(FOLDING_STEPS);
    let folding_challenges_precomputed: Vec<E> = random_poly_in_ext::<F, E>(FOLDING_STEPS);
    let eq_precomputed = make_eq_poly_in_full::<F, E>(&prev_challenges);
    let eq_last = eq_precomputed.last().unwrap();

    let output_polys = [
        &copy_output,
        &initial_output,
        &unbalanced_output,
        &mask_output,
        &lookup_sub_num,
        &lookup_sub_den,
        &lookup_add_num,
        &lookup_add_den,
    ];
    let batch_challenges = [
        copy_bc,
        initial_bc,
        unbalanced_bc,
        mask_bc,
        lookup_sub_bc[0],
        lookup_sub_bc[1],
        lookup_add_bc[0],
        lookup_add_bc[1],
    ];

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
        initial_kernel.evaluate_over_storage(
            &mut storage,
            step,
            &[initial_bc],
            &folding_challenges,
            &mut accumulator,
            FOLDING_STEPS,
            &mut last_evaluations,
            &worker,
        );
        unbalanced_kernel.evaluate_over_storage(
            &mut storage,
            step,
            &[unbalanced_bc],
            &folding_challenges,
            &mut accumulator,
            FOLDING_STEPS,
            &mut last_evaluations,
            &worker,
        );
        mask_kernel.evaluate_over_storage(
            &mut storage,
            step,
            &[mask_bc],
            &folding_challenges,
            &mut accumulator,
            FOLDING_STEPS,
            &mut last_evaluations,
            &worker,
        );
        lookup_sub_kernel.evaluate_over_storage(
            &mut storage,
            step,
            &lookup_sub_bc,
            &folding_challenges,
            &mut accumulator,
            FOLDING_STEPS,
            &mut last_evaluations,
            &worker,
        );
        lookup_add_kernel.evaluate_over_storage(
            &mut storage,
            step,
            &lookup_add_bc,
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
                (addr_copy, &copy_input),
                (addr_initial_b, &initial_b),
                (addr_initial_c, &initial_c),
                (addr_unbalanced_cached, &unbalanced_d),
                (addr_unbalanced_scalar, &unbalanced_e),
                (addr_mask_f, &mask_f),
                (addr_mask_m, &mask_m),
                (addr_lookup_sub_g, &lookup_sub_g),
                (addr_lookup_sub_h, &lookup_sub_h),
                (addr_lookup_sub_i, &lookup_sub_i),
                (addr_lookup_sub_j, &lookup_sub_j),
                (addr_lookup_add_k, &lookup_add_k),
                (addr_lookup_add_l, &lookup_add_l),
                (addr_lookup_add_m, &lookup_add_m),
                (addr_lookup_add_n, &lookup_add_n),
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
