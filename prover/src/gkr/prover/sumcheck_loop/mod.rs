use crate::gkr::prover::SumcheckIntermediateProofValues;
use std::collections::BTreeMap;

use crate::gkr::{
    prover::dimension_reduction::forward::DimensionReducingInputOutput,
    sumcheck::{
        access_and_fold::GKRStorage,
        eq_poly::{
            evaluate_constant_and_quadratic_coeffs_with_precomputed_eq,
            evaluate_with_precomputed_eq, evaluate_with_precomputed_eq_ext, make_eq_poly_in_full,
        },
        evaluate_eq_poly, evaluate_small_univariate_poly,
        output_univariate_monomial_form_max_quadratic,
    },
};
use crate::worker::Worker;
use field::{Field, FieldExtension, PrimeField};

use crate::gkr::prover::transcript_utils::{commit_field_els, draw_random_field_els};
use cs::gkr_compiler::GKRLayerDescription;
use cs::{definitions::GKRAddress, gkr_compiler::OutputType};
use kernel_collector::KernelCollector;
use transcript::Seed;

mod kernel_collector;

/// # Panics
/// Panics if claims or challenge points for the output layer are missing from storage.
pub fn evaluate_dimension_reducing_sumcheck_for_layer<F: PrimeField, E: FieldExtension<F> + Field>(
    layer_idx: usize,
    layer: &BTreeMap<OutputType, DimensionReducingInputOutput>,
    claim_points: &mut BTreeMap<usize, Vec<E>>,
    claims_storage: &mut BTreeMap<usize, BTreeMap<GKRAddress, E>>,
    gkr_storage: &mut GKRStorage<F, E>,
    batching_challenge: &mut E,
    seed: &mut Seed,
    trace_len_after_reduction: usize,
    worker: &Worker,
) -> SumcheckIntermediateProofValues<F, E>
where
    [(); E::DEGREE]: Sized,
{
    println!("Evaluating layer {layer_idx} (dimension reducing) in sumcheck direction");
    println!("Trace length of reduced poly is {trace_len_after_reduction}");
    let output_layer_idx = layer_idx + 1;

    let output_claims = claims_storage
        .get(&output_layer_idx)
        .expect("claims for output layer must exist");
    let prev_challenges = claim_points
        .get(&output_layer_idx)
        .expect("claim points for output layer must exist");

    assert!(trace_len_after_reduction.is_power_of_two());
    let folding_steps = trace_len_after_reduction.trailing_zeros() as usize;
    assert!(folding_steps >= 2, "need at least 2 folding steps");

    // Precompute eq polynomial evaluations over the boolean hypercube
    let eq_polys = make_eq_poly_in_full::<E>(prev_challenges, &worker);

    let batch_challenge_base = *batching_challenge;

    let collector =
        KernelCollector::from_dimension_reducing_relations(layer, layer_idx, batch_challenge_base);
    debug_assert!(!collector.is_empty());

    let claim = collector.compute_combined_claim(output_claims);

    let (mut folding_challenges, internal_round_coefficients, last_evaluations, final_accumulator) =
        run_sumcheck_loop::<F, E, 4>(
            &collector,
            claim,
            prev_challenges,
            &eq_polys,
            gkr_storage,
            folding_steps,
            worker,
            seed,
        );

    #[cfg(feature = "gkr_self_checks")]
    {
        let recomputed = collector.compute_last_step_accumulator_from_evals(&last_evaluations);
        assert_eq!(
            recomputed, final_accumulator,
            "last_evaluations inconsistent with final accumulator"
        );
    }

    let transcript_inputs: Vec<E> = last_evaluations
        .iter()
        .map(|el| el.1.iter())
        .flatten()
        .copied()
        .collect();
    commit_field_els(seed, &transcript_inputs);

    let challenges = draw_random_field_els::<F, E>(seed, 3);
    let [r_before_last, r_last, next_batching_challenge] = challenges.try_into().unwrap();
    folding_challenges.push(r_before_last);
    folding_challenges.push(r_last);

    assert_eq!(
        trace_len_after_reduction.trailing_zeros() as usize,
        folding_challenges.len() - 1
    );

    // After sumcheck completes, extract claims for the input layer

    // we have evaluations of some poly f(r1, r2, ...., 0/1, 0/1) - in total of 4 values;

    let eq_polys = make_eq_poly_in_full(&[r_before_last, r_last], &worker);

    let new_claims: BTreeMap<_, _> = last_evaluations
        .iter()
        .map(|(addr, evals)| {
            let eval = evaluate_with_precomputed_eq_ext(evals, &eq_polys.last().unwrap()[..]);

            (*addr, eval)
        })
        .collect();

    #[cfg(feature = "gkr_self_checks")]
    {
        let eq_polys = make_eq_poly_in_full::<E>(&folding_challenges, worker);
        for (k, v) in new_claims.iter() {
            if let Some(poly) = gkr_storage.try_get_base_poly(*k) {
                let eval = evaluate_with_precomputed_eq(poly, &eq_polys.last().unwrap()[..]);
                assert_eq!(eval, *v, "claim diverged for poly {k:?}");
            } else if let Some(poly) = gkr_storage.try_get_ext_poly(*k) {
                let eval = evaluate_with_precomputed_eq_ext(poly, &eq_polys.last().unwrap()[..]);
                assert_eq!(eval, *v, "claim diverged for poly {k:?}");
            } else {
                unreachable!()
            }
        }
    }

    claims_storage.insert(layer_idx, new_claims);
    claim_points.insert(layer_idx, folding_challenges);

    // and we can purge the storage
    gkr_storage.purge_up_to_layer(layer_idx);

    *batching_challenge = next_batching_challenge;

    SumcheckIntermediateProofValues {
        sumcheck_num_rounds: folding_steps,
        internal_round_coefficients,
        final_step_evaluations: last_evaluations
            .into_iter()
            .map(|(k, v)| (k, v.to_vec()))
            .collect(),
        _marker: core::marker::PhantomData,
    }
}

/// # Panics
/// Panics if claims or challenge points for the output layer are missing from storage.
pub fn evaluate_sumcheck_for_layer<F: PrimeField, E: FieldExtension<F> + Field>(
    layer_idx: usize,
    layer: &GKRLayerDescription,
    claim_points: &mut BTreeMap<usize, Vec<E>>,
    claims_storage: &mut BTreeMap<usize, BTreeMap<GKRAddress, E>>,
    gkr_storage: &mut GKRStorage<F, E>,
    batching_challenge: &mut E,
    compiled_circuit: &cs::gkr_compiler::GKRCircuitArtifact<F>,
    trace_len: usize,
    lookup_challenges_additive_part: E,
    constraints_batch_challenge: E,
    seed: &mut Seed,
    worker: &Worker,
) -> SumcheckIntermediateProofValues<F, E>
where
    [(); E::DEGREE]: Sized,
{
    println!("Evaluating layer {layer_idx} in sumcheck direction");

    let output_layer_idx = layer_idx + 1;

    let output_claims = claims_storage
        .get(&output_layer_idx)
        .expect("claims for output layer must exist");
    let prev_challenges = claim_points
        .get(&output_layer_idx)
        .expect("claim points for output layer must exist");

    assert!(trace_len.is_power_of_two());
    let folding_steps = trace_len.trailing_zeros() as usize;
    assert!(folding_steps >= 4, "need at least 4 folding steps");

    let eq_polys = make_eq_poly_in_full::<E>(prev_challenges, worker);

    let batch_challenge_base = *batching_challenge;

    let collector = KernelCollector::from_layer(
        layer,
        layer_idx,
        batch_challenge_base,
        gkr_storage,
        lookup_challenges_additive_part,
        constraints_batch_challenge,
        compiled_circuit.memory_layout.total_width,
        compiled_circuit.witness_layout.total_width,
    );

    debug_assert!(!collector.is_empty());

    let claim = collector.compute_combined_claim(output_claims);

    let (mut folding_challenges, internal_round_coefficients, last_evaluations, final_accumulator) =
        run_sumcheck_loop::<F, E, 2>(
            &collector,
            claim,
            prev_challenges,
            &eq_polys,
            gkr_storage,
            folding_steps,
            worker,
            seed,
        );

    #[cfg(feature = "gkr_self_checks")]
    {
        let recomputed = collector.compute_last_step_accumulator_from_evals(&last_evaluations);
        assert_eq!(
            recomputed, final_accumulator,
            "last_evaluations inconsistent with final accumulator"
        );
    }

    // After sumcheck completes, extract claims for the input layer
    let transcript_inputs: Vec<E> = last_evaluations
        .iter()
        .map(|el| el.1.iter())
        .flatten()
        .copied()
        .collect();
    commit_field_els(seed, &transcript_inputs);

    let challenges = draw_random_field_els::<F, E>(seed, 2);
    let [last_r, next_batching_challenge] = challenges.try_into().unwrap();
    folding_challenges.push(last_r);
    assert_eq!(
        folding_challenges.len(),
        trace_len.trailing_zeros() as usize
    );

    let new_claims: BTreeMap<_, _> = last_evaluations
        .iter()
        .map(|(addr, &[f0, f1])| (*addr, interpolate_linear::<F, E>(f0, f1, &last_r)))
        .collect();

    // self-check
    #[cfg(feature = "gkr_self_checks")]
    {
        let eq_polys = make_eq_poly_in_full::<E>(&folding_challenges, worker);
        for (k, v) in new_claims.iter() {
            if let Some(poly) = gkr_storage.try_get_base_poly(*k) {
                let eval = evaluate_with_precomputed_eq(poly, &eq_polys.last().unwrap()[..]);
                assert_eq!(eval, *v, "claim diverged for poly {k:?}");
            } else if let Some(poly) = gkr_storage.try_get_ext_poly(*k) {
                let eval = evaluate_with_precomputed_eq_ext(poly, &eq_polys.last().unwrap()[..]);
                assert_eq!(eval, *v, "claim diverged for poly {k:?}");
            } else {
                unreachable!()
            }
        }
    }

    claims_storage.insert(layer_idx, new_claims);
    claim_points.insert(layer_idx, folding_challenges);

    // and we can purge the storage
    gkr_storage.purge_up_to_layer(layer_idx);

    *batching_challenge = next_batching_challenge;

    SumcheckIntermediateProofValues {
        sumcheck_num_rounds: folding_steps,
        internal_round_coefficients,
        final_step_evaluations: last_evaluations
            .into_iter()
            .map(|(k, v)| (k, v.to_vec()))
            .collect(),
        _marker: core::marker::PhantomData,
    }
}

fn run_sumcheck_loop<F: PrimeField, E: FieldExtension<F> + Field, const N: usize>(
    collector: &KernelCollector<F, E>,
    initial_claim: E,
    prev_challenges: &[E],
    eq_poly: &[Box<[E]>],
    gkr_storage: &mut GKRStorage<F, E>,
    folding_steps: usize,
    worker: &Worker,
    seed: &mut Seed,
) -> (Vec<E>, Vec<[E; 4]>, BTreeMap<GKRAddress, [E; N]>, [E; 2])
where
    [(); E::DEGREE]: Sized,
{
    let mut claim = initial_claim;
    let mut folding_challenges = Vec::with_capacity(folding_steps);
    let mut last_evaluations: BTreeMap<GKRAddress, [E; N]> = BTreeMap::new();

    let mut eq_prefactor = E::ONE;

    let max_acc_size = 1 << (folding_steps - 1);
    let mut accumulator_buffer = vec![[E::ZERO; 2]; max_acc_size];
    let mut intermediate_coeffs = Vec::with_capacity(folding_steps);

    for step in 0..folding_steps - 1 {
        let acc_size = 1 << (folding_steps - step - 1);
        let accumulator = &mut accumulator_buffer[..acc_size];
        if step > 0 {
            accumulator.fill([E::ZERO; 2]);
        }

        collector.evaluate_kernels_over_storage(
            gkr_storage,
            step,
            &folding_challenges,
            accumulator,
            folding_steps,
            &mut last_evaluations,
            worker,
        );

        let eq = &eq_poly[folding_steps - step - 1];

        assert_eq!(eq.len(), acc_size);

        let [c0, c2] = evaluate_constant_and_quadratic_coeffs_with_precomputed_eq::<F, E>(
            &accumulator,
            eq,
            worker,
        );

        let mut normalized_claim = claim;
        normalized_claim.mul_assign(&eq_prefactor.inverse().expect("eq prefactor non-zero"));

        let coeffs = output_univariate_monomial_form_max_quadratic::<F, E>(
            prev_challenges[step],
            normalized_claim,
            c0,
            c2,
        );

        #[cfg(feature = "gkr_self_checks")]
        {
            let s0 = evaluate_small_univariate_poly::<F, E, _>(&coeffs, &E::ZERO);
            let s1 = evaluate_small_univariate_poly::<F, E, _>(&coeffs, &E::ONE);
            let mut sum = s0;
            sum.add_assign(&s1);
            sum.mul_assign(&eq_prefactor);
            assert_eq!(sum, claim, "s(0) + s(1) != claim / eq_prefactor");
        }

        commit_field_els(seed, &coeffs);
        intermediate_coeffs.push(coeffs);
        let folding_challenge = draw_random_field_els(seed, 1)[0];

        let new_claim = evaluate_small_univariate_poly::<F, E, _>(&coeffs, &folding_challenge);

        claim = new_claim;
        eq_prefactor = evaluate_eq_poly::<F, E>(&folding_challenge, &prev_challenges[step]);

        folding_challenges.push(folding_challenge);
    }

    // Final step
    {
        let step = folding_steps - 1;
        let accumulator = &mut accumulator_buffer[..1];
        accumulator.fill([E::ZERO; 2]);

        collector.evaluate_kernels_over_storage(
            gkr_storage,
            step,
            &folding_challenges,
            accumulator,
            folding_steps,
            &mut last_evaluations,
            worker,
        );

        #[cfg(feature = "gkr_self_checks")]
        {
            let [f0, f1] = accumulator[0];
            let [eq0, eq1]: [E; 2] = eq_poly[1].to_vec().try_into().unwrap();

            let mut t0 = eq0;
            t0.mul_assign(&f0);
            let mut t1 = eq1;
            t1.mul_assign(&f1);
            let mut claim_inner = t0;
            claim_inner.add_assign(&t1);

            let mut recomputed_claim = claim_inner;
            recomputed_claim.mul_assign(&eq_prefactor);

            assert_eq!(
                recomputed_claim, claim,
                "s(0) + s(1) != claim / eq_prefactor"
            );
        }
    }

    (
        folding_challenges,
        intermediate_coeffs,
        last_evaluations,
        accumulator_buffer[0],
    )
}

#[inline(always)]
fn interpolate_linear<F: PrimeField, E: FieldExtension<F> + Field>(f0: E, f1: E, r: &E) -> E {
    let mut result = f1;
    result.sub_assign(&f0);
    result.mul_assign(r);
    result.add_assign(&f0);
    result
}
