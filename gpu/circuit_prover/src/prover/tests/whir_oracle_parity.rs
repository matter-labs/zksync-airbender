use super::*;

use crate::prover::proof_layout::{
    BackwardLayerDims, ProofLayoutInputs, WhirBaseLayerDims, WhirDims, WhirIntermediateDims,
};

/// Build a minimal `ProofLayoutInputs` tailored to the parity test's WHIR-only
/// data flow. The test exercises only `schedule_gpu_whir_fold_with_sources`,
/// so the layout's `output_evaluations` and `backward_layers` are empty —
/// the slab only carries the WHIR proof fields the test compares against the
/// CPU reference.
fn build_whir_only_proof_layout_inputs(
    whir_schedule: &WhirSchedule,
    initial_trace_size_log_2: usize,
    memory_holder: &TraceHolder<BF>,
    witness_holder: &TraceHolder<BF>,
    setup_holder: &TraceHolder<BF>,
) -> ProofLayoutInputs {
    assert_eq!(
        whir_schedule.whir_steps_schedule.len(),
        whir_schedule.whir_queries_schedule.len(),
    );
    assert_eq!(
        whir_schedule.whir_steps_schedule.len(),
        whir_schedule.whir_pow_schedule.len(),
    );
    assert_eq!(
        whir_schedule.whir_steps_schedule.len(),
        whir_schedule.whir_steps_lde_factors.len() + 1,
    );
    let initial_values_per_leaf = 1usize << whir_schedule.whir_steps_schedule[0];
    let tree_cap_size = whir_schedule.cap_size;
    let tree_cap_log2 = tree_cap_size.trailing_zeros() as usize;
    let initial_query_count = whir_schedule.whir_queries_schedule[0];

    let base_layer_dims = |holder: &TraceHolder<BF>| -> WhirBaseLayerDims {
        let cap_digest_count = 1usize << holder.log_tree_cap_size;
        let leaf_values_len = holder.columns_count * initial_values_per_leaf;
        let path_len = if holder.columns_count == 0 {
            0
        } else {
            (holder.log_domain_size
                - holder.log_rows_per_leaf
                - (holder.log_tree_cap_size - holder.log_lde_factor)) as usize
        };
        WhirBaseLayerDims {
            num_columns: holder.columns_count,
            cap_digest_count,
            query_count: initial_query_count,
            leaf_values_len,
            path_len,
        }
    };

    let mut folded_trace_len_log2 = initial_trace_size_log_2;
    let mut intermediate = Vec::with_capacity(whir_schedule.whir_steps_lde_factors.len());
    for (oracle_idx, &lde_factor) in whir_schedule.whir_steps_lde_factors.iter().enumerate() {
        folded_trace_len_log2 -= whir_schedule.whir_steps_schedule[oracle_idx];
        let values_per_leaf_log2 = whir_schedule.whir_steps_schedule[oracle_idx + 1];
        let path_len = folded_trace_len_log2 + lde_factor.trailing_zeros() as usize
            - values_per_leaf_log2
            - tree_cap_log2;
        intermediate.push(WhirIntermediateDims {
            cap_digest_count: tree_cap_size,
            query_count: whir_schedule.whir_queries_schedule[oracle_idx + 1],
            leaf_values_len: 1usize << values_per_leaf_log2,
            path_len,
        });
    }

    let total_folding_steps = whir_schedule.whir_steps_schedule.iter().sum::<usize>();
    let final_monomials_len = 1usize << (initial_trace_size_log_2 - total_folding_steps);
    let whir = WhirDims {
        setup: base_layer_dims(setup_holder),
        memory: base_layer_dims(memory_holder),
        witness: base_layer_dims(witness_holder),
        intermediate,
        num_ood_samples: whir_schedule.whir_steps_lde_factors.len(),
        total_sumcheck_polys: total_folding_steps,
        pow_rounds: whir_schedule.whir_pow_schedule.len(),
        final_monomials_len,
    };

    ProofLayoutInputs {
        output_evaluations: std::collections::BTreeMap::new(),
        backward_layers: Vec::<BackwardLayerDims>::new(),
        whir,
    }
}

pub(super) fn assert_recursive_whir_oracle_parity_for_supported_path(
    mem_oracle: &ColumnMajorBaseOracleForLDE<BF, DefaultTreeConstructor>,
    mem_polys_claims: &[E4],
    gpu_mem_trace_holder: &mut TraceHolder<BF>,
    wit_oracle: &ColumnMajorBaseOracleForLDE<BF, DefaultTreeConstructor>,
    wit_polys_claims: &[E4],
    gpu_wit_trace_holder: &mut TraceHolder<BF>,
    setup_oracle: &ColumnMajorBaseOracleForLDE<BF, DefaultTreeConstructor>,
    setup_polys_claims: &[E4],
    gpu_setup_trace_holder: &mut TraceHolder<BF>,
    original_evaluation_point: &[E4],
    original_lde_factor: usize,
    batching_challenge: E4,
    whir_schedule: &WhirSchedule,
    twiddles: &Twiddles<BF, Global>,
    mut transcript_seed: Seed,
    trace_len_log2: usize,
    worker: &Worker,
    context: &ProverContext,
) -> WhirPolyCommitProof<BF, E4, DefaultTreeConstructor> {
    let two_inv = BF::from_u32_unchecked(2).inverse().unwrap();
    let scheduled_transcript_seed = transcript_seed;
    let oracle_refs = [mem_oracle, wit_oracle, setup_oracle];
    let evals_refs = [mem_polys_claims, wit_polys_claims, setup_polys_claims];
    let total_base_oracles = oracle_refs.iter().map(|oracle| oracle.num_columns()).sum();
    let challenge_powers = materialize_powers_serial_starting_with_one::<E4, Global>(
        batching_challenge,
        total_base_oracles,
    );
    let (base_mem_powers, rest) = challenge_powers.split_at(evals_refs[0].len());
    let (base_wit_powers, base_setup_powers) = rest.split_at(evals_refs[1].len());

    let mut batched_poly_on_main_domain = vec![E4::ZERO; 1 << trace_len_log2];
    for (challenges_set, values_set) in [
        (
            base_mem_powers,
            &oracle_refs[0].cosets[0].original_values_normal_order,
        ),
        (
            base_wit_powers,
            &oracle_refs[1].cosets[0].original_values_normal_order,
        ),
        (
            base_setup_powers,
            &oracle_refs[2].cosets[0].original_values_normal_order,
        ),
    ] {
        for (batch_challenge, base_value) in challenges_set.iter().zip(values_set.iter()) {
            for (dst, src) in batched_poly_on_main_domain
                .iter_mut()
                .zip(base_value.column.iter())
            {
                let mut term = *batch_challenge;
                term.mul_assign_by_base(src);
                dst.add_assign(&term);
            }
        }
    }

    let use_hypercube_evals_for_batching = true;
    // CPU initially creates batched evals from coset 0 evaluations rather than
    // hypercube evaluations, so we only compare if the GPU also does the former.
    // (Later on, we'll compare the monomial forms unconditionally,
    // because they should always match.)
    if !use_hypercube_evals_for_batching {
        let gpu_batched_poly_on_main_domain = debug_build_initial_batched_evals_for_test(
            gpu_mem_trace_holder,
            mem_polys_claims,
            gpu_wit_trace_holder,
            wit_polys_claims,
            gpu_setup_trace_holder,
            setup_polys_claims,
            batching_challenge,
            use_hypercube_evals_for_batching,
            context,
        )
        .unwrap();
        assert_eq!(gpu_batched_poly_on_main_domain, batched_poly_on_main_domain);
    }
    let mut sumchecked_poly_monomial_form =
        compute_column_major_monomial_form_from_main_domain_owned_for_test(
            batched_poly_on_main_domain,
            twiddles,
        );
    let mut sumchecked_poly_evaluation_form = sumchecked_poly_monomial_form.clone();
    let eval_log2 = sumchecked_poly_evaluation_form.len().trailing_zeros();
    prover::gkr::whir::hypercube_to_monomial::multivariate_coeffs_into_hypercube_evals(
        &mut sumchecked_poly_evaluation_form,
        eval_log2,
    );
    bitreverse_enumeration_inplace(&mut sumchecked_poly_evaluation_form);

    let mut claim = E4::ZERO;
    for (challenges_set, values_set) in [base_mem_powers, base_wit_powers, base_setup_powers]
        .into_iter()
        .zip(evals_refs.into_iter())
    {
        for (challenge, value) in challenges_set.iter().zip(values_set.iter()) {
            let mut term = *value;
            term.mul_assign(challenge);
            claim.add_assign(&term);
        }
    }

    let mut eq_poly = make_eq_poly_in_full::<E4>(original_evaluation_point, worker)
        .pop()
        .unwrap()
        .into_vec();
    let (gpu_pre_eq_evaluation_form, gpu_post_eq_evaluation_form) =
        debug_build_initial_state_snapshots_for_test(
            gpu_mem_trace_holder,
            mem_polys_claims,
            gpu_wit_trace_holder,
            wit_polys_claims,
            gpu_setup_trace_holder,
            setup_polys_claims,
            original_evaluation_point,
            batching_challenge,
            use_hypercube_evals_for_batching,
            context,
        )
        .unwrap();
    assert_eq!(gpu_pre_eq_evaluation_form, sumchecked_poly_evaluation_form);
    assert_eq!(gpu_post_eq_evaluation_form, sumchecked_poly_evaluation_form);
    let (gpu_batch_challenges, gpu_claim, gpu_monomial_form, gpu_evaluation_form, gpu_eq_poly) =
        debug_build_initial_state_for_test(
            gpu_mem_trace_holder,
            mem_polys_claims,
            gpu_wit_trace_holder,
            wit_polys_claims,
            gpu_setup_trace_holder,
            setup_polys_claims,
            original_evaluation_point,
            batching_challenge,
            use_hypercube_evals_for_batching,
            context,
        )
        .unwrap();
    assert_eq!(
        gpu_batch_challenges,
        [
            base_mem_powers.to_vec(),
            base_wit_powers.to_vec(),
            base_setup_powers.to_vec(),
        ]
    );
    assert_eq!(gpu_claim, claim);
    assert_eq!(gpu_monomial_form, sumchecked_poly_monomial_form);
    assert_eq!(gpu_evaluation_form, sumchecked_poly_evaluation_form);
    assert_eq!(gpu_eq_poly, eq_poly);
    let mut poly_size_log2 = trace_len_log2;

    let mut whir_steps_schedule = whir_schedule.whir_steps_schedule.iter().copied().peekable();
    let mut whir_queries_schedule = whir_schedule.whir_queries_schedule.iter().copied();
    let mut whir_steps_lde_factors = whir_schedule.whir_steps_lde_factors.iter().copied();
    let mut whir_pow_schedule = whir_schedule.whir_pow_schedule.iter().copied();
    let mut cpu_pre_pow_seeds = Vec::with_capacity(whir_schedule.whir_pow_schedule.len());
    let mut cpu_pow_nonces = Vec::with_capacity(whir_schedule.whir_pow_schedule.len());
    let mut cpu_sumcheck_polys =
        Vec::with_capacity(whir_schedule.whir_steps_schedule.iter().sum::<usize>());
    let mut cpu_recursive_caps = Vec::with_capacity(whir_schedule.whir_steps_lde_factors.len());
    let mut cpu_ood_samples = Vec::with_capacity(whir_schedule.whir_steps_lde_factors.len());
    let mut cpu_recursive_query_indexes =
        Vec::with_capacity(whir_schedule.whir_steps_lde_factors.len());
    let transcript_seed_before_initial_rounds = transcript_seed.clone();

    let num_initial_folding_rounds = whir_steps_schedule.next().unwrap();
    let initial_queries = whir_queries_schedule.next().unwrap();
    let initial_pow_bits = whir_pow_schedule.next().unwrap();
    let mut gpu_initial_fold_state = debug_build_initial_fold_state_for_test(
        gpu_mem_trace_holder,
        mem_polys_claims,
        gpu_wit_trace_holder,
        wit_polys_claims,
        gpu_setup_trace_holder,
        setup_polys_claims,
        original_evaluation_point,
        batching_challenge,
        use_hypercube_evals_for_batching,
        context,
    )
    .unwrap();
    let mut gpu_monomial_after_initial_rounds = Vec::new();
    let mut folding_challenges_in_round = Vec::with_capacity(num_initial_folding_rounds);
    let mut initial_round_sumcheck_polys = Vec::with_capacity(num_initial_folding_rounds);
    for folding_round in 0..num_initial_folding_rounds {
        let (f0, f1, f_half) =
            special_three_point_eval_for_test(&sumchecked_poly_evaluation_form, &eq_poly);
        let coeffs = special_lagrange_interpolate_for_test(f0, f1, f_half, E4::from_base(two_inv));
        initial_round_sumcheck_polys.push(coeffs);
        cpu_sumcheck_polys.push(coeffs);
        commit_field_els::<BF, E4>(&mut transcript_seed, &coeffs);
        let folding_challenge = draw_random_field_els::<BF, E4>(&mut transcript_seed, 1)[0];
        folding_challenges_in_round.push(folding_challenge);
        claim = evaluate_small_univariate_poly::<BF, E4, 3>(&coeffs, &folding_challenge);
        fold_monomial_form_for_test(&mut sumchecked_poly_monomial_form, folding_challenge);
        fold_evaluation_form_for_test(&mut sumchecked_poly_evaluation_form, folding_challenge);
        fold_eq_poly_for_test(&mut eq_poly, folding_challenge);
        let gpu_monomial_after_round = debug_apply_initial_fold_challenge_for_test(
            &mut gpu_initial_fold_state,
            folding_challenge,
            context,
        )
        .unwrap();
        gpu_monomial_after_initial_rounds = gpu_monomial_after_round.clone();
        if gpu_monomial_after_round != sumchecked_poly_monomial_form {
            let first_mismatch = gpu_monomial_after_round
                .iter()
                .zip(sumchecked_poly_monomial_form.iter())
                .enumerate()
                .find(|(_, (gpu, cpu))| gpu != cpu)
                .map(|(idx, (gpu, cpu))| (idx, *gpu, *cpu));
            panic!(
                "initial WHIR monomial fold diverged at round {folding_round}; first_mismatch={first_mismatch:?}"
            );
        }
    }
    poly_size_log2 -= num_initial_folding_rounds;

    let first_lde_factor = whir_steps_lde_factors.next().unwrap();
    let next_folding_steps = *whir_steps_schedule.peek().unwrap();
    let mut cpu_rs_oracle = build_cpu_recursive_whir_oracle_for_test(
        &sumchecked_poly_monomial_form,
        twiddles,
        first_lde_factor,
        1 << next_folding_steps,
        whir_schedule.cap_size,
        worker,
    );
    let mut gpu_rs_oracle = GpuWhirExtensionOracle::from_monomial_coeffs(
        &sumchecked_poly_monomial_form,
        first_lde_factor,
        1 << next_folding_steps,
        whir_schedule.cap_size,
        false, // transform_leaves_to_multilinear_coeffs
        context,
    )
    .unwrap();
    assert_eq!(
        gpu_rs_oracle.get_tree_cap(&context).unwrap(),
        <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(
            &cpu_rs_oracle.tree,
        )
    );
    cpu_recursive_caps.push(
        <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(
            &cpu_rs_oracle.tree,
        ),
    );
    let gpu_initial_round_checkpoint = debug_initial_round_checkpoint_for_test(
        gpu_mem_trace_holder,
        mem_polys_claims,
        gpu_wit_trace_holder,
        wit_polys_claims,
        gpu_setup_trace_holder,
        setup_polys_claims,
        original_evaluation_point,
        original_lde_factor,
        batching_challenge,
        num_initial_folding_rounds,
        first_lde_factor,
        next_folding_steps,
        whir_schedule.cap_size,
        use_hypercube_evals_for_batching,
        transcript_seed_before_initial_rounds,
        context,
    )
    .unwrap();
    add_whir_commitment_to_transcript(
        &mut transcript_seed,
        &WhirCommitment::<BF, DefaultTreeConstructor> {
            cap: <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(
                &cpu_rs_oracle.tree,
            ),
            _marker: core::marker::PhantomData,
        },
    );

    let ood_point = draw_random_field_els::<BF, E4>(&mut transcript_seed, 1)[0];
    let ood_value = evaluate_monomial_form_for_test(&sumchecked_poly_monomial_form, ood_point);
    cpu_ood_samples.push(ood_value);
    commit_field_els::<BF, E4>(&mut transcript_seed, &[ood_value]);
    assert_eq!(
        gpu_initial_round_checkpoint.sumcheck_polys, initial_round_sumcheck_polys,
        "initial WHIR sumcheck polys diverged before PoW",
    );
    assert_eq!(
        gpu_initial_round_checkpoint.folding_challenges, folding_challenges_in_round,
        "initial WHIR folding challenges diverged before recursive commitment",
    );
    assert_eq!(
        gpu_initial_round_checkpoint.folded_monomial_form, gpu_monomial_after_initial_rounds,
        "all-in-one initial WHIR checkpoint diverged from the stepwise GPU fold path",
    );
    let gpu_materialized_initial_rs_oracle = GpuWhirExtensionOracle::from_monomial_coeffs(
        &gpu_initial_round_checkpoint.folded_monomial_form,
        first_lde_factor,
        1 << next_folding_steps,
        whir_schedule.cap_size,
        false, // transform_leaves_to_multilinear_coeffs
        context,
    )
    .unwrap();
    assert_eq!(
        gpu_initial_round_checkpoint.recursive_cap,
        gpu_materialized_initial_rs_oracle.get_tree_cap(&context).unwrap(),
        "initial recursive WHIR commitment does not match the cap rebuilt from the materialized folded monomial form",
    );
    if gpu_initial_round_checkpoint.folded_monomial_form != sumchecked_poly_monomial_form {
        let first_mismatch = gpu_initial_round_checkpoint
            .folded_monomial_form
            .iter()
            .zip(sumchecked_poly_monomial_form.iter())
            .enumerate()
            .find(|(_, (gpu, cpu))| gpu != cpu)
            .map(|(idx, (gpu, cpu))| (idx, *gpu, *cpu));
        panic!(
            "initial folded WHIR monomial form diverged before recursive commitment; first_mismatch={first_mismatch:?}"
        );
    }
    assert_eq!(
        gpu_initial_round_checkpoint.recursive_cap,
        <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(
            &cpu_rs_oracle.tree,
        ),
        "initial recursive WHIR commitment diverged before PoW",
    );
    assert_eq!(
        gpu_initial_round_checkpoint.ood_point, ood_point,
        "initial WHIR OOD point diverged before PoW",
    );
    assert_eq!(
        gpu_initial_round_checkpoint.ood_value, ood_value,
        "initial WHIR OOD value diverged before PoW",
    );
    assert_eq!(
        gpu_initial_round_checkpoint.transcript_seed, transcript_seed,
        "initial WHIR transcript seed diverged before PoW",
    );
    let rs_domain_log2 = trace_len_log2 + original_lde_factor.trailing_zeros() as usize;
    let query_domain_log2 = rs_domain_log2 - num_initial_folding_rounds;
    let query_domain_size = 1u64 << query_domain_log2;
    let query_domain_generator = domain_generator_for_size::<BF>(query_domain_size);
    let extended_generator = domain_generator_for_size::<BF>(1u64 << rs_domain_log2);
    let mut high_powers_offsets = materialize_powers_serial_starting_with_one::<BF, Global>(
        domain_generator_for_size::<BF>(1u64 << num_initial_folding_rounds)
            .inverse()
            .unwrap(),
        1 << (num_initial_folding_rounds - 1),
    );
    bitreverse_enumeration_inplace(&mut high_powers_offsets);
    let query_index_bits = query_domain_size.trailing_zeros() as usize;
    cpu_pre_pow_seeds.push(transcript_seed);
    let (initial_nonce, mut bit_source) = draw_query_bits(
        &mut transcript_seed,
        initial_queries * query_index_bits,
        initial_pow_bits,
        worker,
    );
    cpu_pow_nonces.push(initial_nonce);
    let delinearization_challenge = draw_random_field_els::<BF, E4>(&mut transcript_seed, 1)[0];
    let mut claim_correction = {
        let mut t = ood_value;
        t.mul_assign(&delinearization_challenge);
        t
    };
    // Matches upstream `prover/src/gkr/whir/mod.rs`: OOD contribution uses x, and the i-th
    // per-query contribution uses x^(i+2).
    let mut current_delinearization_challenge = delinearization_challenge;
    current_delinearization_challenge.square();
    let mut in_domain_samples = Vec::with_capacity(initial_queries);
    for _ in 0..initial_queries {
        let query_index = assemble_query_index(query_index_bits, &mut bit_source);
        let query_point = query_domain_generator.pow(query_index as u32);
        let base_root = extended_generator.pow(query_index as u32);
        let base_root_inv = base_root.inverse().unwrap();
        let mut batched_evals = vec![E4::ZERO; mem_oracle.values_per_leaf];
        for (oracle, batching_challenges) in oracle_refs
            .iter()
            .zip([base_mem_powers, base_wit_powers, base_setup_powers].iter())
        {
            let (_, leaf, _) = oracle.query_for_folded_index(query_index);
            for (dst, src) in batched_evals.iter_mut().zip(leaf.iter()) {
                for (a, b) in src.iter().zip(batching_challenges.iter()) {
                    let mut t = *b;
                    t.mul_assign_by_base(a);
                    dst.add_assign(&t);
                }
            }
        }
        let folded = fold_coset_for_test(
            batched_evals,
            num_initial_folding_rounds,
            &folding_challenges_in_round,
            &base_root_inv,
            &high_powers_offsets,
            &two_inv,
        );
        let mut t = folded;
        t.mul_assign(&current_delinearization_challenge);
        claim_correction.add_assign(&t);
        in_domain_samples.push((query_point, current_delinearization_challenge));
        current_delinearization_challenge.mul_assign(&delinearization_challenge);
    }
    update_eq_poly_for_test(
        &mut eq_poly,
        &[(ood_point, delinearization_challenge)],
        &in_domain_samples,
    );
    claim.add_assign(&claim_correction);

    let num_internal_rounds = whir_schedule.whir_steps_lde_factors.len() - 1;
    for _internal_round in 0..num_internal_rounds {
        let num_folding_steps = whir_steps_schedule.next().unwrap();
        let num_queries = whir_queries_schedule.next().unwrap();
        let pow_bits = whir_pow_schedule.next().unwrap();
        let rs_domain_log2 = poly_size_log2 + cpu_rs_oracle.cosets.len().trailing_zeros() as usize;
        let query_domain_log2 = rs_domain_log2 - num_folding_steps;
        let mut folding_challenges_in_round = Vec::with_capacity(num_folding_steps);
        for _ in 0..num_folding_steps {
            let (f0, f1, f_half) =
                special_three_point_eval_for_test(&sumchecked_poly_evaluation_form, &eq_poly);
            let coeffs =
                special_lagrange_interpolate_for_test(f0, f1, f_half, E4::from_base(two_inv));
            cpu_sumcheck_polys.push(coeffs);
            commit_field_els::<BF, E4>(&mut transcript_seed, &coeffs);
            let folding_challenge = draw_random_field_els::<BF, E4>(&mut transcript_seed, 1)[0];
            folding_challenges_in_round.push(folding_challenge);
            claim = evaluate_small_univariate_poly::<BF, E4, 3>(&coeffs, &folding_challenge);
            fold_monomial_form_for_test(&mut sumchecked_poly_monomial_form, folding_challenge);
            fold_evaluation_form_for_test(&mut sumchecked_poly_evaluation_form, folding_challenge);
            fold_eq_poly_for_test(&mut eq_poly, folding_challenge);
        }
        poly_size_log2 -= num_folding_steps;

        let lde_factor = whir_steps_lde_factors.next().unwrap();
        let next_folding_steps = *whir_steps_schedule.peek().unwrap();
        let next_cpu_oracle = build_cpu_recursive_whir_oracle_for_test(
            &sumchecked_poly_monomial_form,
            twiddles,
            lde_factor,
            1 << next_folding_steps,
            whir_schedule.cap_size,
            worker,
        );
        let next_gpu_oracle = GpuWhirExtensionOracle::from_monomial_coeffs(
            &sumchecked_poly_monomial_form,
            lde_factor,
            1 << next_folding_steps,
            whir_schedule.cap_size,
            false, // transform_leaves_to_multilinear_coeffs
            context,
        )
        .unwrap();
        assert_eq!(
            next_gpu_oracle.get_tree_cap(&context).unwrap(),
            <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(
                &next_cpu_oracle.tree,
            )
        );
        let next_cpu_oracle_cap = <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<
            BF,
        >>::get_cap(&next_cpu_oracle.tree);
        cpu_recursive_caps.push(next_cpu_oracle_cap.clone());
        // Upstream now folds the recursive oracle cap into the transcript before drawing
        // the next OOD point (see prover/src/gkr/whir/mod.rs ~line 1056).
        add_whir_commitment_to_transcript(
            &mut transcript_seed,
            &WhirCommitment::<BF, DefaultTreeConstructor> {
                cap: next_cpu_oracle_cap,
                _marker: core::marker::PhantomData,
            },
        );

        let ood_point = draw_random_field_els::<BF, E4>(&mut transcript_seed, 1)[0];
        let ood_value = evaluate_monomial_form_for_test(&sumchecked_poly_monomial_form, ood_point);
        cpu_ood_samples.push(ood_value);
        // Upstream also commits the OOD value to the transcript in the recursive round
        // (see prover/src/gkr/whir/mod.rs ~line 1067).
        commit_field_els::<BF, E4>(&mut transcript_seed, &[ood_value]);
        let query_domain_size = 1u64 << query_domain_log2;
        let query_domain_generator = domain_generator_for_size::<BF>(query_domain_size);
        let extended_generator = domain_generator_for_size::<BF>(1u64 << rs_domain_log2);
        let mut high_powers_offsets = materialize_powers_serial_starting_with_one::<BF, Global>(
            domain_generator_for_size::<BF>(1u64 << num_folding_steps)
                .inverse()
                .unwrap(),
            1 << (num_folding_steps - 1),
        );
        bitreverse_enumeration_inplace(&mut high_powers_offsets);
        let query_index_bits = query_domain_size.trailing_zeros() as usize;
        cpu_pre_pow_seeds.push(transcript_seed);
        let (nonce, mut bit_source) = draw_query_bits(
            &mut transcript_seed,
            num_queries * query_index_bits,
            pow_bits,
            worker,
        );
        cpu_pow_nonces.push(nonce);
        let delinearization_challenge = draw_random_field_els::<BF, E4>(&mut transcript_seed, 1)[0];
        let mut claim_correction = {
            let mut t = ood_value;
            t.mul_assign(&delinearization_challenge);
            t
        };
        // Running-powers weighting: OOD uses x, the i-th query uses x^(i+2).
        let mut current_delinearization_challenge = delinearization_challenge;
        current_delinearization_challenge.square();
        let mut in_domain_samples = Vec::with_capacity(num_queries);
        let mut recursive_round_query_indexes = Vec::with_capacity(num_queries);
        for _ in 0..num_queries {
            let query_index = assemble_query_index(query_index_bits, &mut bit_source);
            recursive_round_query_indexes.push(query_index);
            let (_, cpu_values, cpu_query) = cpu_rs_oracle.query_for_folded_index(query_index);
            let (_, gpu_values, gpu_query) = gpu_rs_oracle
                .query_for_folded_index(query_index, context)
                .unwrap();
            assert_eq!(gpu_values, cpu_values, "recursive query values diverged");
            assert_eq!(gpu_query.index, cpu_query.index);
            assert_eq!(
                gpu_query.leaf_values_concatenated,
                cpu_query.leaf_values_concatenated
            );
            assert_eq!(gpu_query.path, cpu_query.path);

            let query_point = query_domain_generator.pow(query_index as u32);
            let base_root = extended_generator.pow(query_index as u32);
            let base_root_inv = base_root.inverse().unwrap();
            let folded = fold_coset_for_test(
                cpu_values,
                num_folding_steps,
                &folding_challenges_in_round,
                &base_root_inv,
                &high_powers_offsets,
                &two_inv,
            );
            let mut t = folded;
            t.mul_assign(&current_delinearization_challenge);
            claim_correction.add_assign(&t);
            in_domain_samples.push((query_point, current_delinearization_challenge));
            current_delinearization_challenge.mul_assign(&delinearization_challenge);
        }
        update_eq_poly_for_test(
            &mut eq_poly,
            &[(ood_point, delinearization_challenge)],
            &in_domain_samples,
        );
        cpu_recursive_query_indexes.push(recursive_round_query_indexes);
        claim.add_assign(&claim_correction);

        cpu_rs_oracle = next_cpu_oracle;
        gpu_rs_oracle = next_gpu_oracle;
    }

    let final_folding_steps = whir_steps_schedule.next().unwrap();
    let final_queries = whir_queries_schedule.next().unwrap();
    let final_pow_bits = whir_pow_schedule.next().unwrap();
    let rs_domain_log2 = poly_size_log2 + cpu_rs_oracle.cosets.len().trailing_zeros() as usize;
    let query_domain_log2 = rs_domain_log2 - final_folding_steps;
    let mut folding_challenges_in_round = Vec::with_capacity(final_folding_steps);
    for _ in 0..final_folding_steps {
        let (f0, f1, f_half) =
            special_three_point_eval_for_test(&sumchecked_poly_evaluation_form, &eq_poly);
        let coeffs = special_lagrange_interpolate_for_test(f0, f1, f_half, E4::from_base(two_inv));
        cpu_sumcheck_polys.push(coeffs);
        commit_field_els::<BF, E4>(&mut transcript_seed, &coeffs);
        let folding_challenge = draw_random_field_els::<BF, E4>(&mut transcript_seed, 1)[0];
        folding_challenges_in_round.push(folding_challenge);
        claim = evaluate_small_univariate_poly::<BF, E4, 3>(&coeffs, &folding_challenge);
        fold_monomial_form_for_test(&mut sumchecked_poly_monomial_form, folding_challenge);
        fold_evaluation_form_for_test(&mut sumchecked_poly_evaluation_form, folding_challenge);
        fold_eq_poly_for_test(&mut eq_poly, folding_challenge);
    }
    // Upstream commits the final monomial-form coefficients into the transcript before
    // drawing the final query PoW (see prover/src/gkr/whir/mod.rs line ~1297).
    commit_field_els::<BF, E4>(&mut transcript_seed, &sumchecked_poly_monomial_form);
    let query_domain_size = 1u64 << query_domain_log2;
    let query_domain_generator = domain_generator_for_size::<BF>(query_domain_size);
    let extended_generator = domain_generator_for_size::<BF>(1u64 << rs_domain_log2);
    let mut high_powers_offsets = materialize_powers_serial_starting_with_one::<BF, Global>(
        domain_generator_for_size::<BF>(1u64 << final_folding_steps)
            .inverse()
            .unwrap(),
        1 << (final_folding_steps - 1),
    );
    bitreverse_enumeration_inplace(&mut high_powers_offsets);
    let query_index_bits = query_domain_size.trailing_zeros() as usize;
    cpu_pre_pow_seeds.push(transcript_seed);
    let (final_nonce, mut bit_source) = draw_query_bits(
        &mut transcript_seed,
        final_queries * query_index_bits,
        final_pow_bits,
        worker,
    );
    cpu_pow_nonces.push(final_nonce);
    let mut final_round_query_indexes = Vec::with_capacity(final_queries);
    for _ in 0..final_queries {
        let query_index = assemble_query_index(query_index_bits, &mut bit_source);
        final_round_query_indexes.push(query_index);
        let (_, cpu_values, cpu_query) = cpu_rs_oracle.query_for_folded_index(query_index);
        let (_, gpu_values, gpu_query) = gpu_rs_oracle
            .query_for_folded_index(query_index, context)
            .unwrap();
        assert_eq!(
            gpu_values, cpu_values,
            "final recursive query values diverged"
        );
        assert_eq!(gpu_query.index, cpu_query.index);
        assert_eq!(
            gpu_query.leaf_values_concatenated,
            cpu_query.leaf_values_concatenated
        );
        assert_eq!(gpu_query.path, cpu_query.path);

        let query_point = query_domain_generator.pow(query_index as u32);
        let base_root = extended_generator.pow(query_index as u32);
        let base_root_inv = base_root.inverse().unwrap();
        let folded = fold_coset_for_test(
            cpu_values,
            final_folding_steps,
            &folding_challenges_in_round,
            &base_root_inv,
            &high_powers_offsets,
            &two_inv,
        );
        assert_eq!(
            folded,
            evaluate_monomial_form_for_test(
                &sumchecked_poly_monomial_form,
                E4::from_base(query_point)
            )
        );
    }
    cpu_recursive_query_indexes.push(final_round_query_indexes);
    // pre_pow_seeds parity dropped: end-to-end byte equality covers seed correctness.
    let _ = cpu_pre_pow_seeds;
    let whir_proof_layout_inputs = build_whir_only_proof_layout_inputs(
        whir_schedule,
        trace_len_log2,
        gpu_mem_trace_holder,
        gpu_wit_trace_holder,
        gpu_setup_trace_holder,
    );
    let whir_proof_layout = ProofLayout::new(&whir_proof_layout_inputs);
    // Allocate a real proof slab so the schedule can route every WHIR proof
    // field through it; the test then D2Hs the slab and runs `parse_whir_proof`
    // to materialize a `WhirPolyCommitProof` mirror of what production
    // assembles in `schedule_terminal_proof_assembly`.
    assert!(
        whir_proof_layout.total_bytes > 0,
        "WHIR proof layout produced an empty slab; test misconfigured",
    );
    assert_eq!(
        whir_proof_layout.total_bytes % core::mem::size_of::<E4>(),
        0,
        "proof slab size must be E4-aligned",
    );
    let proof_slab: DeviceAllocation<E4> = context
        .alloc_with_extra_alignment::<E4, 4>(
            whir_proof_layout.total_bytes / core::mem::size_of::<E4>(),
            AllocationPlacement::BestFit,
        )
        .unwrap();
    let mut base_layer_point_device: DeviceAllocation<E4> = context
        .alloc(
            original_evaluation_point.len().max(1),
            AllocationPlacement::Top,
        )
        .unwrap();
    let mut base_layer_point_host =
        unsafe { context.alloc_host_uninit_slice::<E4>(original_evaluation_point.len()) };
    let mut base_layer_point_callbacks = crate::primitives::callbacks::Callbacks::new();
    let base_layer_point_host_accessor = base_layer_point_host.get_mut_accessor();
    let base_layer_point_for_h2d = original_evaluation_point.to_vec();
    base_layer_point_callbacks
        .schedule(
            move || unsafe {
                base_layer_point_host_accessor
                    .get_mut()
                    .copy_from_slice(&base_layer_point_for_h2d);
            },
            context.get_exec_stream(),
        )
        .unwrap();
    memory_copy_async(
        &mut base_layer_point_device[..original_evaluation_point.len()],
        &base_layer_point_host,
        context.get_exec_stream(),
    )
    .unwrap();
    // Test path: stage the witness/memory/setup unified caps into the slab
    // BEFORE invoking WHIR. Production prepares the same state in
    // `prepare_stage1_and_forward_setup` (witness via `commit_all_into`,
    // memory/setup via the pinned-host H2D into the slab). The test holders
    // already own committed caps in `unified_device_cap`, so a single D2D per
    // source seeds the slab cap ranges that WHIR (and the slab parser) now
    // expect.
    {
        use crate::prover::proof_layout::WhirBaseLayerKind;
        let slab_base = proof_slab.as_ptr() as *mut u8;
        for (holder, kind) in [
            (&*gpu_mem_trace_holder, WhirBaseLayerKind::Memory),
            (&*gpu_wit_trace_holder, WhirBaseLayerKind::Witness),
            (&*gpu_setup_trace_holder, WhirBaseLayerKind::Setup),
        ] {
            let (dst_ptr, dst_len_u32) =
                unsafe { whir_proof_layout.whir_base_cap_device_mut(slab_base, kind) };
            if dst_len_u32 == 0 {
                continue;
            }
            // SAFETY: `Digest = [u32; DIGEST_U32_WORDS]`; reinterpreting the
            // device cap as `[u32]` of equal byte length is layout-safe. The
            // dst range is a live, disjoint subrange of `proof_slab`.
            let src_u32 = unsafe { holder.unified_device_cap().transmute::<u32>() };
            assert_eq!(src_u32.len(), dst_len_u32);
            let dst =
                unsafe { era_cudart::slice::DeviceSlice::from_raw_parts_mut(dst_ptr, dst_len_u32) };
            era_cudart::memory::memory_copy_async(dst, src_u32, context.get_exec_stream()).unwrap();
        }
    }
    // Test path: stage the host-supplied transcript seed and batching challenge
    // into device buffers up front so `schedule_gpu_whir_fold_with_sources` can
    // run on device transcript ops just like prove() does in production.
    let mut device_seed: DeviceAllocation<u32> = context
        .alloc(
            crate::ops::blake2s::STATE_SIZE,
            AllocationPlacement::BestFit,
        )
        .unwrap();
    let mut device_seed_staging =
        unsafe { context.alloc_host_uninit_slice::<u32>(crate::ops::blake2s::STATE_SIZE) };
    let device_seed_staging_accessor = device_seed_staging.get_mut_accessor();
    unsafe {
        device_seed_staging_accessor
            .get_mut()
            .copy_from_slice(&scheduled_transcript_seed.0);
    }
    memory_copy_async(
        &mut device_seed,
        &device_seed_staging,
        context.get_exec_stream(),
    )
    .unwrap();
    let mut batching_challenge_device_test: DeviceAllocation<E4> =
        context.alloc(1, AllocationPlacement::BestFit).unwrap();
    let mut batching_challenge_host_test = unsafe { context.alloc_host_uninit_slice::<E4>(1) };
    let batching_challenge_host_test_accessor = batching_challenge_host_test.get_mut_accessor();
    unsafe {
        batching_challenge_host_test_accessor.get_mut()[0] = batching_challenge;
    }
    memory_copy_async(
        &mut batching_challenge_device_test,
        &batching_challenge_host_test,
        context.get_exec_stream(),
    )
    .unwrap();
    let scheduled_gpu_whir = schedule_gpu_whir_fold_with_sources(
        gpu_mem_trace_holder,
        gpu_wit_trace_holder,
        gpu_setup_trace_holder,
        &base_layer_point_device[..original_evaluation_point.len()],
        &mut device_seed[..],
        &batching_challenge_device_test[..],
        original_lde_factor,
        whir_schedule.whir_steps_schedule.clone(),
        whir_schedule.whir_queries_schedule.clone(),
        whir_schedule.whir_steps_lde_factors.clone(),
        whir_schedule.whir_pow_schedule.clone(),
        whir_schedule.cap_size,
        trace_len_log2,
        true, // use_hypercube_evals_for_batching
        &proof_slab,
        &whir_proof_layout,
        context,
    )
    .unwrap();
    // Test-side slab D2H + parse. This mirrors the production terminal
    // assembly path (`schedule_terminal_proof_assembly`) without going through
    // the orchestration helper, and replaces the prior cfg(test)-gated
    // host-mirror writebacks that populated `proof.*` directly via callbacks.
    let mut slab_mirror =
        unsafe { context.alloc_host_uninit_slice::<u8>(whir_proof_layout.total_bytes) };
    {
        let slab_u8 = unsafe {
            era_cudart::slice::DeviceSlice::from_raw_parts(
                proof_slab.as_ptr() as *const u8,
                whir_proof_layout.total_bytes,
            )
        };
        memory_copy_async(&mut slab_mirror, slab_u8, context.get_exec_stream()).unwrap();
    }
    context.get_exec_stream().synchronize().unwrap();
    let slab_mirror_accessor = slab_mirror.get_accessor();
    let mut scheduled_gpu_whir_proof =
        whir_proof_layout.parse_whir_proof(unsafe { slab_mirror_accessor.get() });
    drop(scheduled_gpu_whir);
    let scheduled_recursive_caps = scheduled_gpu_whir_proof
        .intermediate_whir_oracles
        .iter()
        .map(|oracle| oracle.commitment.cap.clone())
        .collect::<Vec<_>>();
    let _scheduled_recursive_query_indexes = scheduled_gpu_whir_proof
        .intermediate_whir_oracles
        .iter()
        .map(|oracle| {
            oracle
                .queries
                .iter()
                .map(|query| query.index)
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    // Per-round assertions in workflow order to find first divergence.
    // Sumcheck polys: one per folding step. whir_steps_schedule = [1, 4, 4, 4, 4, 4]
    // OOD samples: one per recursive round (rounds 1..N)
    // Recursive caps: one per recursive round
    {
        let mut step_offset = 0;
        for (round_idx, &num_steps) in whir_schedule.whir_steps_schedule.iter().enumerate() {
            for step in 0..num_steps {
                let idx = step_offset + step;
                assert_eq!(
                    scheduled_gpu_whir_proof.sumcheck_polys[idx], cpu_sumcheck_polys[idx],
                    "sumcheck poly diverged at round {round_idx} step {step} (global idx {idx})"
                );
            }
            step_offset += num_steps;
            // After each round's sumcheck: check OOD (except base round)
            if round_idx > 0 {
                let ood_idx = round_idx - 1;
                if ood_idx < cpu_ood_samples.len() {
                    assert_eq!(
                        scheduled_gpu_whir_proof.ood_samples[ood_idx], cpu_ood_samples[ood_idx],
                        "OOD sample diverged at round {round_idx} (ood_idx {ood_idx})"
                    );
                }
            }
            // Check recursive cap
            if round_idx > 0 {
                let cap_idx = round_idx - 1;
                if cap_idx < cpu_recursive_caps.len() {
                    assert_eq!(
                        scheduled_recursive_caps[cap_idx], cpu_recursive_caps[cap_idx],
                        "recursive cap diverged at round {round_idx} (cap_idx {cap_idx})"
                    );
                }
            }
            // Check PoW nonce
            if round_idx < scheduled_gpu_whir_proof.pow_nonces.len() {
                assert_eq!(
                    scheduled_gpu_whir_proof.pow_nonces[round_idx], cpu_pow_nonces[round_idx],
                    "PoW nonce diverged at round {round_idx}"
                );
            }
        }
    }
    let _ = claim;
    // The parity test returns a `WhirPolyCommitProof` shape compatible with the
    // upstream WHIR verifier path. `parse_whir_proof` populates every device-
    // produced field; the base-layer `evals` are sourced separately by the
    // caller in production (`base_layer_claims` writes them into the slab),
    // so here we splice in the host-supplied per-oracle claims directly.
    scheduled_gpu_whir_proof
        .memory_commitment
        .evals
        .copy_from_slice(mem_polys_claims);
    scheduled_gpu_whir_proof
        .witness_commitment
        .evals
        .copy_from_slice(wit_polys_claims);
    scheduled_gpu_whir_proof
        .setup_commitment
        .evals
        .copy_from_slice(setup_polys_claims);
    scheduled_gpu_whir_proof.whir_schedule = whir_schedule.clone();
    scheduled_gpu_whir_proof
}
