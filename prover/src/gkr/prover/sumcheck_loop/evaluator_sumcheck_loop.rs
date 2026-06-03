use fft::materialize_powers_serial_starting_with_elem;
use sumcheck_common::representation::PolyAccessor;

use super::*;
use crate::gkr::prover::*;

fn compute_combined_claim<F: PrimeField, E: FieldExtension<F> + Field>(
    layer: &GKRLayerDescription,
    output_claims: &BTreeMap<GKRAddress, E>,
    precomputed_challenges: &[E],
) -> E {
    let mut result = E::ZERO;
    let mut challenges_it = precomputed_challenges.iter();
    for gate in layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
        .take(15)
    {
        let num_challenges = gate.enforced_relation.num_challenges();
        let outputs = gate.enforced_relation.ordered_outputs_for_batching();
        if outputs.len() == 0 {
            assert_eq!(num_challenges, 1);
            let _ = *challenges_it.next().expect("next challenge");
        } else {
            assert_eq!(num_challenges, outputs.len());
            for output in outputs.into_iter() {
                let value = output_claims
                    .get(&output)
                    .expect(&format!("must have a claim for {:?}", output));
                let mut t = *challenges_it.next().expect("next challenge");
                t.mul_assign(value);
                result.add_assign(&t);
            }
        }
    }
    // assert!(challenges_it.next().is_none());

    result
}

pub(crate) fn run_sumcheck_loop_with_external_evaluator<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    EVAL: crate::gkr::sumcheck::SumcheckEvaluator<F, E>,
>(
    _evaluator: &EVAL,
    layer_idx: usize,
    layer: &GKRLayerDescription,
    output_claims: &BTreeMap<GKRAddress, E>,
    prev_challenges: &[E],
    eq_poly: &[Box<[E]>],
    gkr_storage: &mut GKRStorage<F, E>,
    compiled_circuit: &cs::gkr_compiler::GKRCircuitArtifact<F>,
    challenge_constants: &BatchedGKRTermDescriptionConstants<F, E>,
    batch_challenge_base: E,
    folding_steps: usize,
    worker: &Worker,
    seed: &mut Seed,
) -> (Vec<E>, Vec<[E; 4]>, BTreeMap<GKRAddress, [E; 2]>, [E; 2])
where
    [(); E::DEGREE]: Sized,
{
    use crate::gkr::sumcheck::access_and_fold::sumcheck_common_source::*;

    let mut all_base_field_inputs = BTreeSet::new();
    let mut all_ext_field_inputs = BTreeSet::new();
    let mut all_base_field_outputs = BTreeSet::new();
    let mut all_ext_field_outputs = BTreeSet::new();

    let mut total_required_challenges = 0usize;
    for gate in layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
    {
        total_required_challenges += gate.enforced_relation.num_challenges();
        gate.enforced_relation
            .dump_base_field_inputs(&mut all_base_field_inputs);
        gate.enforced_relation
            .dump_ext_field_inputs(&mut all_ext_field_inputs);
        gate.enforced_relation
            .dump_base_field_outputs(&mut all_base_field_outputs);
        gate.enforced_relation
            .dump_ext_field_outputs(&mut all_ext_field_outputs);
    }

    dbg!(&all_base_field_inputs);

    let mut folding_challenges: Vec<E> = Vec::with_capacity(folding_steps);
    let batching_challenges = materialize_powers_serial_starting_with_one::<_, Global>(
        batch_challenge_base,
        total_required_challenges,
    );
    let lookup_delinearization_challenges = if compiled_circuit.generic_lookup_tables_width > 1 {
        let num_to_compute = compiled_circuit.generic_lookup_tables_width - 1;
        materialize_powers_serial_starting_with_elem::<_, Global>(
            challenge_constants.lookup_challenges_multiplicative_part,
            num_to_compute,
        )
    } else {
        vec![]
    };

    let mut claim = compute_combined_claim::<F, E>(layer, output_claims, &batching_challenges);

    let max_acc_size = 1 << (folding_steps - 1);

    let mut acc_current_len = max_acc_size;
    let mut intermediate_coeffs: Vec<[E; 4]> = Vec::with_capacity(folding_steps);
    let mut eq_prefactor = E::ONE;

    // round 0
    {
        dbg!(claim);
        dbg!(eq_prefactor);
        dbg!(&folding_challenges);

        let step = 0;
        let mut source = SumcheckRound0Source {
            storage: gkr_storage,
        };
        let all_base_field_sources: Vec<_> = all_base_field_inputs
            .iter()
            .map(|el| source.get_source_for_base_poly(*el))
            .collect();
        let all_ext_field_sources: Vec<_> = all_ext_field_inputs
            .iter()
            .map(|el| source.get_source_for_ext_poly(*el))
            .collect();

        let all_base_field_output_sources: Vec<_> = all_base_field_outputs
            .iter()
            .map(|el| source.get_source_for_base_poly(*el))
            .collect();
        let all_ext_field_output_sources: Vec<_> = all_ext_field_outputs
            .iter()
            .map(|el| source.get_source_for_ext_poly(*el))
            .collect();

        let initial_round_fn =
            EVAL::get_layer_evaluator_for_initial_round::<SumcheckRound0Source<F, E>, _>(0);
        let base_field_input_ctx = source.base_field_input_ctx();
        let ext_field_input_ctx = source.ext_field_input_ctx();

        let eq = &eq_poly[folding_steps - step - 1];
        assert_eq!(acc_current_len, eq.len());
        let now = std::time::Instant::now();
        let partial_results =
            apply_reduce::<_>(acc_current_len, worker, |dst, chunk_start, chunk_size| {
                let range = chunk_start..chunk_start + chunk_size;
                *dst = (initial_round_fn)(
                    &all_base_field_sources,
                    &all_ext_field_sources,
                    &all_base_field_output_sources,
                    &all_ext_field_output_sources,
                    &batching_challenges,
                    &challenge_constants.external_challenges,
                    &lookup_delinearization_challenges,
                    &challenge_constants.lookup_challenges_additive_part,
                    &base_field_input_ctx,
                    &ext_field_input_ctx,
                    eq,
                    range,
                );
            });
        println!(
            "Evaluating initial round for layer {} took {:?}",
            layer_idx,
            now.elapsed()
        );

        interpolate_and_commit_values(
            partial_results,
            prev_challenges,
            seed,
            &mut folding_challenges,
            &mut claim,
            &mut intermediate_coeffs,
            &mut eq_prefactor,
            step,
        );
    };

    // round 1
    {
        dbg!(claim);
        dbg!(eq_prefactor);
        dbg!(&folding_challenges);

        acc_current_len /= 2;
        let step = 1;
        let mut source = SumcheckRound1Source::new(gkr_storage, &folding_challenges);
        let all_base_field_sources: Vec<_> = all_base_field_inputs
            .iter()
            .map(|el| source.get_source_for_base_poly(*el))
            .collect();
        let all_ext_field_sources: Vec<_> = all_ext_field_inputs
            .iter()
            .map(|el| source.get_source_for_ext_poly(*el))
            .collect();

        let round_fn = EVAL::get_layer_evaluator::<SumcheckRound1Source<F, E>, _, false>(0);
        let base_field_input_ctx = source.base_field_input_ctx();
        let ext_field_input_ctx = source.ext_field_input_ctx();

        let eq = &eq_poly[folding_steps - step - 1];
        assert_eq!(acc_current_len, eq.len());
        let now = std::time::Instant::now();
        let partial_results =
            apply_reduce::<_>(acc_current_len, worker, |dst, chunk_start, chunk_size| {
                let range = chunk_start..chunk_start + chunk_size;
                *dst = (round_fn)(
                    &all_base_field_sources,
                    &all_ext_field_sources,
                    &batching_challenges,
                    &challenge_constants.external_challenges,
                    &lookup_delinearization_challenges,
                    &challenge_constants.lookup_challenges_additive_part,
                    &base_field_input_ctx,
                    &ext_field_input_ctx,
                    eq,
                    range,
                );
            });
        println!(
            "Evaluating round {} for layer {} took {:?}",
            step,
            layer_idx,
            now.elapsed()
        );

        interpolate_and_commit_values(
            partial_results,
            prev_challenges,
            seed,
            &mut folding_challenges,
            &mut claim,
            &mut intermediate_coeffs,
            &mut eq_prefactor,
            step,
        );
    }

    // round 2
    {
        acc_current_len /= 2;
        let step = 2;
        let mut source = SumcheckRound2Source::new(gkr_storage, &folding_challenges);
        let all_base_field_sources: Vec<_> = all_base_field_inputs
            .iter()
            .map(|el| source.get_source_for_base_poly(*el))
            .collect();
        let all_ext_field_sources: Vec<_> = all_ext_field_inputs
            .iter()
            .map(|el| source.get_source_for_ext_poly(*el))
            .collect();

        let round_fn = EVAL::get_layer_evaluator::<SumcheckRound2Source<F, E>, _, false>(0);
        let base_field_input_ctx = source.base_field_input_ctx();
        let ext_field_input_ctx = source.ext_field_input_ctx();

        let eq = &eq_poly[folding_steps - step - 1];
        assert_eq!(acc_current_len, eq.len());
        let now = std::time::Instant::now();
        let partial_results =
            apply_reduce::<_>(acc_current_len, worker, |dst, chunk_start, chunk_size| {
                let range = chunk_start..chunk_start + chunk_size;
                *dst = (round_fn)(
                    &all_base_field_sources,
                    &all_ext_field_sources,
                    &batching_challenges,
                    &challenge_constants.external_challenges,
                    &lookup_delinearization_challenges,
                    &challenge_constants.lookup_challenges_additive_part,
                    &base_field_input_ctx,
                    &ext_field_input_ctx,
                    eq,
                    range,
                );
            });
        println!(
            "Evaluating round {} for layer {} took {:?}",
            step,
            layer_idx,
            now.elapsed()
        );

        interpolate_and_commit_values(
            partial_results,
            prev_challenges,
            seed,
            &mut folding_challenges,
            &mut claim,
            &mut intermediate_coeffs,
            &mut eq_prefactor,
            step,
        );
    }

    // round 3+ except the last one
    for step in 3..folding_steps - 1 {
        acc_current_len /= 2;
        let mut source = SumcheckRound3AndBeyondSource::new(gkr_storage, &folding_challenges);
        let all_base_field_sources: Vec<_> = all_base_field_inputs
            .iter()
            .map(|el| source.get_source_for_base_poly(*el))
            .collect();
        let all_ext_field_sources: Vec<_> = all_ext_field_inputs
            .iter()
            .map(|el| source.get_source_for_ext_poly(*el))
            .collect();

        let round_fn =
            EVAL::get_layer_evaluator::<SumcheckRound3AndBeyondSource<F, E>, _, false>(0);
        let base_field_input_ctx = source.base_field_input_ctx();
        let ext_field_input_ctx = source.ext_field_input_ctx();

        let eq = &eq_poly[folding_steps - step - 1];
        assert_eq!(acc_current_len, eq.len());
        let now = std::time::Instant::now();
        let partial_results =
            apply_reduce::<_>(acc_current_len, worker, |dst, chunk_start, chunk_size| {
                let range = chunk_start..chunk_start + chunk_size;
                *dst = (round_fn)(
                    &all_base_field_sources,
                    &all_ext_field_sources,
                    &batching_challenges,
                    &challenge_constants.external_challenges,
                    &lookup_delinearization_challenges,
                    &challenge_constants.lookup_challenges_additive_part,
                    &base_field_input_ctx,
                    &ext_field_input_ctx,
                    eq,
                    range,
                );
            });
        println!(
            "Evaluating round {} for layer {} took {:?}",
            step,
            layer_idx,
            now.elapsed()
        );

        interpolate_and_commit_values(
            partial_results,
            prev_challenges,
            seed,
            &mut folding_challenges,
            &mut claim,
            &mut intermediate_coeffs,
            &mut eq_prefactor,
            step,
        );
    }

    // last round is different due to different commit and returned evaluation form

    // last round
    {
        acc_current_len /= 2;
        let step = folding_steps - 1;
        let mut source = SumcheckRound3AndBeyondSource::new(gkr_storage, &folding_challenges);
        let all_base_field_sources: Vec<_> = all_base_field_inputs
            .iter()
            .map(|el| source.get_source_for_base_poly(*el))
            .collect();
        let all_ext_field_sources: Vec<_> = all_ext_field_inputs
            .iter()
            .map(|el| source.get_source_for_ext_poly(*el))
            .collect();

        let round_fn = EVAL::get_layer_evaluator::<SumcheckRound3AndBeyondSource<F, E>, _, true>(0);
        let base_field_input_ctx = source.base_field_input_ctx();
        let ext_field_input_ctx = source.ext_field_input_ctx();

        let eq = &eq_poly[folding_steps - step - 1];
        assert_eq!(acc_current_len, eq.len());
        let now = std::time::Instant::now();
        let partial_results =
            apply_reduce::<_>(acc_current_len, worker, |dst, chunk_start, chunk_size| {
                let range = chunk_start..chunk_start + chunk_size;
                *dst = (round_fn)(
                    &all_base_field_sources,
                    &all_ext_field_sources,
                    &batching_challenges,
                    &challenge_constants.external_challenges,
                    &lookup_delinearization_challenges,
                    &challenge_constants.lookup_challenges_additive_part,
                    &base_field_input_ctx,
                    &ext_field_input_ctx,
                    eq,
                    range,
                );
            });
        println!(
            "Evaluating round {} for layer {} took {:?}",
            step,
            layer_idx,
            now.elapsed()
        );

        let [mut f0, mut f1] = partial_results[0];
        for [a, b] in partial_results[1..].iter() {
            f0.add_assign(a);
            f1.add_assign(b);
        }

        let final_accumulator = [f0, f1];

        #[cfg(feature = "gkr_self_checks")]
        {
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
                "s(0) + s(1) != claim / eq_prefactor at explicit sumcheck verification"
            );
        }

        // read last values from sources
        let mut final_values = BTreeMap::new();
        for (poly, src) in all_base_field_inputs
            .iter()
            .zip(all_base_field_sources.iter())
        {
            let evals = *src
                .current_values()
                .as_array::<2>()
                .expect("length must match");
            final_values.insert(*poly, evals);
        }
        for (poly, src) in all_ext_field_inputs
            .iter()
            .zip(all_ext_field_sources.iter())
        {
            let evals = *src
                .current_values()
                .as_array::<2>()
                .expect("length must match");
            final_values.insert(*poly, evals);
        }

        (
            folding_challenges,
            intermediate_coeffs,
            final_values,
            final_accumulator,
        )
    }
}

fn interpolate_and_commit_values<F: PrimeField, E: FieldExtension<F> + Field>(
    partial_results: Vec<[E; 2]>,
    prev_challenges: &[E],
    seed: &mut Seed,
    folding_challenges: &mut Vec<E>,
    claim: &mut E,
    intermediate_coeffs: &mut Vec<[E; 4]>,
    eq_prefactor: &mut E,
    step: usize,
) where
    [(); E::DEGREE]: Sized,
{
    let [mut c0, mut c2] = partial_results[0];
    for [a, b] in partial_results[1..].iter() {
        c0.add_assign(a);
        c2.add_assign(b);
    }

    dbg!((c0, c2));

    let mut normalized_claim = *claim;
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
            sum, *claim,
            "s(0) + s(1) != claim / eq_prefactor at folding step {}",
            step
        );
    }

    commit_field_els(seed, &coeffs);
    intermediate_coeffs.push(coeffs);
    let folding_challenge = draw_random_field_els(seed, 1)[0];

    let new_claim = evaluate_small_univariate_poly::<F, E, _>(&coeffs, &folding_challenge);

    *claim = new_claim;
    *eq_prefactor = evaluate_eq_poly::<F, E>(&folding_challenge, &prev_challenges[step]);

    folding_challenges.push(folding_challenge);
}
