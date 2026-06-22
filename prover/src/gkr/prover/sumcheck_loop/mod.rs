use crate::gkr::prover::SumcheckIntermediateProofValues;
use std::collections::BTreeMap;

use crate::gkr::prover::GKRExternalChallenges;
use crate::gkr::sumcheck::evaluation_kernels::*;
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

mod batch_evaluation;
mod distribution_analysis;
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
        run_sumcheck_loop::<F, E, 4, false>(
            &collector,
            claim,
            prev_challenges,
            &eq_polys,
            gkr_storage,
            &BatchedGKRTermDescriptionConstants::<F, E>::default(),
            folding_steps,
            worker,
            seed,
        );

    #[cfg(feature = "gkr_self_checks")]
    {
        // As in the same-size case, the last round emits a univariate monomial, so
        // `final_accumulator` is now `[G(0), G2]` rather than the explicit endpoints
        // `[G(0), G(1)]`. Both share the constant term `G(0)`, which we check; the per-round
        // and per-poly checks cover the rest.
        let recomputed = collector.compute_last_step_accumulator_from_evals(
            &BatchedGKRTermDescriptionConstants::<F, E>::default(),
            &last_evaluations,
        );
        assert_eq!(
            recomputed[0], final_accumulator[0],
            "last_evaluations inconsistent with final accumulator constant term G(0)"
        );
    }

    // The last folding challenge drawn inside the loop is the challenge for the last *output*
    // coordinate (`r_before_last`). It fixes that coordinate of the `[E;4]` bilinear
    // `last_evaluations` (over (last output coord) x (pairwise/LSB coord)), reducing it to a
    // `[E;2]` line in the remaining LSB coordinate. That line is what we send in the proof and
    // commit to the transcript; we then draw the LSB challenge `r_last` to fix it and obtain
    // the next-layer at-point claims.
    assert_eq!(
        trace_len_after_reduction.trailing_zeros() as usize,
        folding_challenges.len()
    );
    let r_before_last = *folding_challenges.last().expect("at least one folding round");

    // `[E;4]` layout: [v0, v1, v2, v3] split as (x_last=0: v0,v1 | x_last=1: v2,v3), so the
    // LSB=0 component is (v0 @ x_last=0, v2 @ x_last=1) and LSB=1 is (v1, v3). Interpolating
    // over x_last at `r_before_last` yields the `[E;2]` LSB line [lsb0, lsb1].
    let lsb_lines: BTreeMap<GKRAddress, [E; 2]> = last_evaluations
        .iter()
        .map(|(addr, evals)| {
            let lsb0 = interpolate_linear::<F, E>(evals[0], evals[2], &r_before_last);
            let lsb1 = interpolate_linear::<F, E>(evals[1], evals[3], &r_before_last);
            (*addr, [lsb0, lsb1])
        })
        .collect();

    // Send the LSB lines in the proof and commit them before drawing the LSB challenge.
    let final_step_evaluations: BTreeMap<GKRAddress, Vec<E>> = lsb_lines
        .iter()
        .map(|(k, v)| (*k, v.to_vec()))
        .collect();

    let transcript_inputs: Vec<E> = lsb_lines.values().flatten().copied().collect();
    commit_field_els(seed, &transcript_inputs);

    let challenges = draw_random_field_els::<F, E>(seed, 2);
    let [r_last, next_batching_challenge] = challenges.try_into().unwrap();
    folding_challenges.push(r_last);

    assert_eq!(
        trace_len_after_reduction.trailing_zeros() as usize,
        folding_challenges.len() - 1
    );

    // After sumcheck completes, extract claims for the input layer by fixing the LSB
    // coordinate at `r_last`.
    let new_claims: BTreeMap<_, _> = lsb_lines
        .iter()
        .map(|(addr, [lsb0, lsb1])| {
            (*addr, interpolate_linear::<F, E>(*lsb0, *lsb1, &r_last))
        })
        .collect();

    #[cfg(feature = "gkr_self_checks")]
    {
        println!("Self-checking explicit at-point evaluations");
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
        final_step_evaluations,
        extra_evaluations_from_caching_relations: BTreeMap::new(), // none are possible here
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
    _compiled_circuit: &cs::gkr_compiler::GKRCircuitArtifact<F>,
    trace_len: usize,
    lookup_challenges_multiplicative_part: E,
    lookup_challenges_additive_part: E,
    inits_and_teardowns_top_bits: &[u32],
    address_high_bits_shift: u32,
    external_challenges: &GKRExternalChallenges<F, E>,
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
        lookup_challenges_multiplicative_part,
        lookup_challenges_additive_part,
        inits_and_teardowns_top_bits,
        address_high_bits_shift,
    );

    debug_assert!(!collector.is_empty());

    let claim = collector.compute_combined_claim(output_claims);

    let challenge_constants = BatchedGKRTermDescriptionConstants::<F, E> {
        external_challenges: *external_challenges,
        lookup_challenges_multiplicative_part: lookup_challenges_multiplicative_part,
        lookup_challenges_additive_part: lookup_challenges_additive_part,
        _marker: core::marker::PhantomData,
    };

    let (mut folding_challenges, internal_round_coefficients, last_evaluations, final_accumulator) =
        run_sumcheck_loop::<F, E, 2, true>(
            &collector,
            claim,
            prev_challenges,
            &eq_polys,
            gkr_storage,
            &challenge_constants,
            folding_steps,
            worker,
            seed,
        );

    #[cfg(feature = "gkr_self_checks")]
    {
        // The last round now emits a univariate monomial, so `final_accumulator` holds the
        // monomial form `[G(0), G2]` (constant + quadratic/at-infinity coeff) rather than the
        // old explicit endpoints `[G(0), G(1)]`. `compute_last_step_accumulator_from_evals`
        // still reconstructs the endpoints from `last_evaluations`; both forms share the
        // constant term `G(0)`, which we check here. The per-round `s(0) + s(1) == claim`
        // check (inside `run_sumcheck_loop`) and the per-poly at-point checks below cover the
        // rest of the consistency.
        let recomputed = collector
            .compute_last_step_accumulator_from_evals(&challenge_constants, &last_evaluations);
        assert_eq!(
            recomputed[0], final_accumulator[0],
            "last_evaluations inconsistent with final accumulator constant term G(0)"
        );
    }

    // After sumcheck completes, the last folding challenge (drawn inside the loop together
    // with the final univariate monomial) fixes the final coordinate. We reduce each input
    // poly's line `[f0, f1]` to a single at-point evaluation, which is both the next-layer
    // claim and the value sent in the proof. These at-point evaluations are committed to the
    // transcript before the next batching challenge is drawn.
    assert_eq!(
        folding_challenges.len(),
        trace_len.trailing_zeros() as usize
    );
    let last_r = *folding_challenges.last().expect("at least one folding round");

    let mut new_claims: BTreeMap<_, _> = last_evaluations
        .iter()
        .map(|(addr, &[f0, f1])| (*addr, interpolate_linear::<F, E>(f0, f1, &last_r)))
        .collect();

    // Snapshot the at-point evaluations to send in the proof before the cached-relation
    // handling extends `new_claims` with extra explicitly-computed dependencies.
    let final_step_evaluations: BTreeMap<GKRAddress, Vec<E>> =
        new_claims.iter().map(|(k, v)| (*k, vec![*v])).collect();

    let transcript_inputs: Vec<E> = new_claims.values().copied().collect();
    commit_field_els(seed, &transcript_inputs);

    let next_batching_challenge = draw_random_field_els::<F, E>(seed, 1)[0];

    // self-check
    #[cfg(feature = "gkr_self_checks")]
    {
        println!("Self-checking explicit at-point evaluations");
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

    let mut extra_evaluations_from_caching_relations = BTreeMap::new();
    if layer.cached_relations.is_empty() == false {
        use crate::gkr::sumcheck::eq_poly::*;
        let mut eq_poly = None;

        for (cached_addr, relation) in layer.cached_relations.iter() {
            assert!(
                new_claims.contains_key(cached_addr),
                "Missing claim for cached address {:?}",
                cached_addr
            );

            #[cfg(feature = "gkr_self_checks")]
            {
                println!("Self-checking explicit at-point evaluations for cache relations");
                let claim = new_claims[cached_addr];
                if eq_poly.is_none() {
                    let mut eq_precomputed = make_eq_poly_in_full(&folding_challenges, worker);
                    let eq_at_z = eq_precomputed.pop().unwrap();
                    eq_poly = Some(eq_at_z);
                }
                if let Some(poly) = gkr_storage.try_get_base_poly(*cached_addr) {
                    let eval = evaluate_with_precomputed_eq(poly, &eq_poly.as_ref().unwrap()[..]);
                    // if claim != eval {
                    //     println!(
                    //         "claim diverged for poly {cached_addr:?} from relation {:?}",
                    //         relation
                    //     );
                    // }
                    assert_eq!(
                        eval, claim,
                        "claim diverged for poly {cached_addr:?} from relation {:?}",
                        relation
                    );
                } else if let Some(poly) = gkr_storage.try_get_ext_poly(*cached_addr) {
                    let eval =
                        evaluate_with_precomputed_eq_ext(poly, &eq_poly.as_ref().unwrap()[..]);
                    // if claim != eval {
                    //     println!(
                    //         "claim diverged for poly {cached_addr:?} from relation {:?}",
                    //         relation
                    //     );
                    // }
                    assert_eq!(
                        eval, claim,
                        "claim diverged for poly {cached_addr:?} from relation {:?}",
                        relation
                    );
                } else {
                    unreachable!()
                }
            }

            for dep in relation.dependencies() {
                if new_claims.contains_key(&dep) {
                    continue;
                }
                match dep {
                    GKRAddress::BaseLayerWitness(_)
                    | GKRAddress::BaseLayerMemory(_)
                    | GKRAddress::Setup(_)
                    | GKRAddress::InnerLayer { .. } => {
                        println!("Explicitly computing value for {:?}", dep);
                        if eq_poly.is_none() {
                            let mut eq_precomputed =
                                make_eq_poly_in_full(&folding_challenges, worker);
                            let eq_at_z = eq_precomputed.pop().unwrap();
                            eq_poly = Some(eq_at_z);
                        }
                        let evaluation = if let Some(values) = gkr_storage.try_get_base_poly(dep) {
                            evaluate_with_precomputed_eq::<F, E>(
                                values,
                                &eq_poly.as_ref().unwrap()[..],
                            )
                        } else if let Some(values) = gkr_storage.try_get_ext_poly(dep) {
                            evaluate_with_precomputed_eq_ext::<E>(
                                values,
                                &eq_poly.as_ref().unwrap()[..],
                            )
                        } else {
                            panic!("Unknown poly at address {:?}", dep);
                        };

                        new_claims.insert(dep, evaluation);
                        extra_evaluations_from_caching_relations.insert(dep, evaluation);
                    }
                    _ => {
                        panic!(
                            "Unexpected dependency address {:?} for cached relation {:?}",
                            dep, cached_addr
                        );
                    }
                }
            }
        }

        if !extra_evaluations_from_caching_relations.is_empty() {
            let transcript_input = extra_evaluations_from_caching_relations
                .values()
                .copied()
                .collect::<Vec<_>>();
            commit_field_els(seed, &transcript_input);
        }

        #[cfg(feature = "gkr_self_checks")]
        assert!(crate::gkr::prover::debug_utils::verify_cache_relations(
            layer,
            &new_claims,
            external_challenges,
            lookup_challenges_multiplicative_part,
        ));
    }

    claims_storage.insert(layer_idx, new_claims);
    claim_points.insert(layer_idx, folding_challenges);

    // and we can purge the storage
    gkr_storage.purge_up_to_layer(layer_idx);

    *batching_challenge = next_batching_challenge;

    SumcheckIntermediateProofValues {
        sumcheck_num_rounds: folding_steps,
        internal_round_coefficients,
        final_step_evaluations,
        extra_evaluations_from_caching_relations,
        _marker: core::marker::PhantomData,
    }
}

fn run_sumcheck_loop<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const N: usize,
    const USE_BATCHING: bool,
>(
    collector: &KernelCollector<F, E>,
    initial_claim: E,
    prev_challenges: &[E],
    eq_poly: &[Box<[E]>],
    gkr_storage: &mut GKRStorage<F, E>,
    challenge_constants: &BatchedGKRTermDescriptionConstants<F, E>,
    folding_steps: usize,
    worker: &Worker,
    seed: &mut Seed,
) -> (Vec<E>, Vec<[E; 4]>, BTreeMap<GKRAddress, [E; N]>, [E; 2])
where
    [(); E::DEGREE]: Sized,
{
    if USE_BATCHING {
        println!("Running sumcheck loop in batched mode");
    } else {
        println!("Running sumcheck loop in individual kernel mode");
    };

    let mut claim = initial_claim;
    let mut folding_challenges = Vec::with_capacity(folding_steps);
    let mut last_evaluations: BTreeMap<GKRAddress, [E; N]> = BTreeMap::new();

    let mut eq_prefactor = E::ONE;

    let max_acc_size = 1 << (folding_steps - 1);
    let mut accumulator_buffer = vec![[E::ZERO; 2]; max_acc_size];
    let mut intermediate_coeffs = Vec::with_capacity(folding_steps);

    let batched_description = if USE_BATCHING {
        collector.make_batched_description(challenge_constants, collector.layer)
    } else {
        Default::default()
    };

    // Every round - including the last one - now emits a univariate monomial and draws a
    // folding challenge. The last round's kernel evaluation produces the monomial form
    // `[G(0), G2]` (see `EXPLICIT_FORM == false` handling in the evaluators) while still
    // folding all input polys down to their line and recording `last_evaluations`, which the
    // callers use to fix the last coordinate at the freshly drawn challenge.
    for step in 0..folding_steps {
        let acc_size = 1 << (folding_steps - step - 1);
        let accumulator = &mut accumulator_buffer[..acc_size];
        if step > 0 {
            accumulator.fill([E::ZERO; 2]);
        }

        if USE_BATCHING {
            use crate::gkr::prover::sumcheck_loop::batch_evaluation::evaluate_batched_gkr_description;
            evaluate_batched_gkr_description(
                &batched_description,
                gkr_storage,
                step,
                &folding_challenges,
                accumulator,
                folding_steps,
                &mut last_evaluations,
                worker,
            );
        } else {
            collector.evaluate_kernels_over_storage(
                gkr_storage,
                step,
                &folding_challenges,
                accumulator,
                folding_steps,
                &mut last_evaluations,
                worker,
            );
        }

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
            assert_eq!(
                sum, claim,
                "s(0) + s(1) != claim / eq_prefactor at folding step {}",
                step
            );
        }

        commit_field_els(seed, &coeffs);
        intermediate_coeffs.push(coeffs);
        let folding_challenge = draw_random_field_els(seed, 1)[0];

        let new_claim = evaluate_small_univariate_poly::<F, E, _>(&coeffs, &folding_challenge);

        claim = new_claim;
        eq_prefactor = evaluate_eq_poly::<F, E>(&folding_challenge, &prev_challenges[step]);

        folding_challenges.push(folding_challenge);
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
