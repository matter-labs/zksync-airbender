use super::*;

mod fold_round;
mod round_phases;

use fold_round::schedule_fold_round;
use round_phases::{
    schedule_commit_next_oracle_phase, schedule_delinearization_running_powers_phase,
    schedule_ood_sample_phase, schedule_pow_and_query_indexes_phase,
};

pub(crate) fn schedule_gpu_whir_fold_with_sources(
    memory_trace_holder: &mut TraceHolder<BF>,
    memory_unified_device_cap: &DeviceAllocation<Digest>,
    witness_trace_holder: &mut TraceHolder<BF>,
    setup_trace_holder: &mut TraceHolder<BF>,
    base_layer_point_device: &DeviceSlice<E4>,
    original_lde_factor: usize,
    batching_challenge_source: impl Fn() -> E4 + Send + Sync + 'static,
    whir_steps_schedule: Vec<usize>,
    whir_queries_schedule: Vec<usize>,
    whir_steps_lde_factors: Vec<usize>,
    whir_pow_schedule: Vec<u32>,
    seed_source: impl Fn() -> Seed + Send + Sync + 'static,
    tree_cap_size: usize,
    trace_len_log2: usize,
    use_hypercube_evals_for_batching: bool,
    // Phase 3: slab + layout thread through so WHIR sub-phases can route
    // proof fields (`pow_nonces` today; caps, evals, queries, ood_samples,
    // sumcheck_polys, final_monomials in follow-up commits) into slab
    // offsets via `ProofLayout` accessors. `None` skips all slab routing
    // (test paths).
    proof_slab: Option<&DeviceAllocation<E4>>,
    proof_layout: &ProofLayout,
    // Deferred base-layer-claims metadata publication (built by
    // `schedule_prepare_base_layer_claims_with_sources` and handed off via
    // `take_pending_aggregation`). When `Some`, scheduled as the first start
    // callback inside `gkr.whir.schedule` so final proof parsing can see the
    // populated `base_layer_claims_shared_state.result`.
    // `None` for test paths that use `wait()` and don't go through this fn.
    pre_start_aggregation_callback: Option<Box<dyn Fn() + Send + Sync + 'static>>,
    context: &ProverContext,
) -> CudaResult<GpuWhirFoldScheduledExecution> {
    let trace_len = 1usize << trace_len_log2;
    assert_eq!(memory_trace_holder.log_domain_size as usize, trace_len_log2);
    assert_eq!(
        witness_trace_holder.log_domain_size as usize,
        trace_len_log2
    );
    assert_eq!(setup_trace_holder.log_domain_size as usize, trace_len_log2);
    assert_eq!(
        1usize << memory_trace_holder.log_lde_factor,
        original_lde_factor
    );
    // Base-layer memory/witness/setup oracles share `log_lde_factor`
    // (sourced from `ProverConfig`). The base-round query loop below relies
    // on this to share a single `device_internal_indexes` buffer across all
    // three calls per query.
    assert_eq!(
        witness_trace_holder.log_lde_factor,
        memory_trace_holder.log_lde_factor
    );
    assert_eq!(
        setup_trace_holder.log_lde_factor,
        memory_trace_holder.log_lde_factor
    );
    assert_eq!(
        1usize << memory_trace_holder.log_rows_per_leaf,
        1usize << whir_steps_schedule[0]
    );
    assert_eq!(
        1usize << witness_trace_holder.log_rows_per_leaf,
        1usize << whir_steps_schedule[0]
    );
    assert_eq!(
        1usize << setup_trace_holder.log_rows_per_leaf,
        1usize << whir_steps_schedule[0]
    );
    assert_eq!(whir_steps_schedule.len(), whir_queries_schedule.len());
    assert_eq!(whir_steps_schedule.len(), whir_pow_schedule.len());
    assert_eq!(whir_steps_schedule.len(), whir_steps_lde_factors.len() + 1);

    let stream = context.get_exec_stream();
    let mut tracing_ranges = Vec::new();
    memory_trace_holder.ensure_cosets_materialized(context)?;
    witness_trace_holder.ensure_cosets_materialized(context)?;
    setup_trace_holder.ensure_cosets_materialized(context)?;

    let schedule_range = Range::new("gkr.whir.schedule")?;
    schedule_range.start(stream)?;

    let total_sumcheck_polys = whir_steps_schedule.iter().sum::<usize>();
    let initial_query_count = whir_queries_schedule[0];
    let whir_pow_rounds = whir_pow_schedule.len();
    let memory_columns_count = memory_trace_holder.columns_count;
    let witness_columns_count = witness_trace_holder.columns_count;
    let setup_columns_count = setup_trace_holder.columns_count;
    let num_intermediate_oracles = whir_steps_lde_factors.len();
    let initial_values_per_leaf = 1usize << whir_steps_schedule[0];
    let tree_cap_log2 = tree_cap_size.trailing_zeros() as usize;
    let memory_base_query_path_len = (memory_trace_holder.log_domain_size
        - memory_trace_holder.log_rows_per_leaf
        - (memory_trace_holder.log_tree_cap_size - memory_trace_holder.log_lde_factor))
        as usize;
    let witness_base_query_path_len = (witness_trace_holder.log_domain_size
        - witness_trace_holder.log_rows_per_leaf
        - (witness_trace_holder.log_tree_cap_size - witness_trace_holder.log_lde_factor))
        as usize;
    let setup_base_query_path_len = (setup_trace_holder.log_domain_size
        - setup_trace_holder.log_rows_per_leaf
        - (setup_trace_holder.log_tree_cap_size - setup_trace_holder.log_lde_factor))
        as usize;
    let mut folded_trace_len_log2 = trace_len_log2;
    let intermediate_query_specs = whir_steps_lde_factors
        .iter()
        .enumerate()
        .map(|(oracle_idx, &lde_factor)| {
            folded_trace_len_log2 -= whir_steps_schedule[oracle_idx];
            let values_per_leaf_log2 = whir_steps_schedule[oracle_idx + 1];
            let path_len = folded_trace_len_log2 + lde_factor.trailing_zeros() as usize
                - values_per_leaf_log2
                - tree_cap_log2;
            (
                whir_queries_schedule[oracle_idx + 1],
                1usize << values_per_leaf_log2,
                path_len,
            )
        })
        .collect::<Vec<_>>();
    let witness_unified_device_cap = witness_trace_holder.unified_device_cap();
    let setup_unified_device_cap = if setup_columns_count == 0 {
        None
    } else {
        Some(setup_trace_holder.unified_device_cap())
    };
    let witness_cap_size = witness_unified_device_cap.len();
    let memory_cap_size = memory_unified_device_cap.len();
    let setup_cap_size = setup_unified_device_cap.as_ref().map_or(0, |cap| cap.len());
    let scheduled_proof = WhirPolyCommitProof {
        witness_commitment: WhirBaseLayerCommitmentAndQueries {
            commitment: WhirCommitment {
                cap: MerkleTreeCapVarLength {
                    cap: vec![Digest::default(); witness_cap_size],
                },
                _marker: PhantomData,
            },
            num_columns: witness_columns_count,
            evals: vec![E4::ZERO; witness_columns_count],
            queries: make_preallocated_base_queries(
                initial_query_count,
                witness_columns_count * initial_values_per_leaf,
                witness_base_query_path_len,
            ),
        },
        memory_commitment: WhirBaseLayerCommitmentAndQueries {
            commitment: WhirCommitment {
                cap: MerkleTreeCapVarLength {
                    cap: vec![Digest::default(); memory_cap_size],
                },
                _marker: PhantomData,
            },
            num_columns: memory_columns_count,
            evals: vec![E4::ZERO; memory_columns_count],
            queries: make_preallocated_base_queries(
                initial_query_count,
                memory_columns_count * initial_values_per_leaf,
                memory_base_query_path_len,
            ),
        },
        setup_commitment: WhirBaseLayerCommitmentAndQueries {
            commitment: WhirCommitment {
                cap: MerkleTreeCapVarLength {
                    cap: vec![Digest::default(); setup_cap_size],
                },
                _marker: PhantomData,
            },
            num_columns: setup_columns_count,
            evals: vec![E4::ZERO; setup_columns_count],
            queries: make_preallocated_base_queries(
                initial_query_count,
                setup_columns_count * initial_values_per_leaf,
                if setup_columns_count == 0 {
                    0
                } else {
                    setup_base_query_path_len
                },
            ),
        },
        sumcheck_polys: vec![[E4::ZERO; 3]; total_sumcheck_polys],
        intermediate_whir_oracles: intermediate_query_specs
            .iter()
            .map(
                |&(count, values_per_leaf, path_len)| WhirIntermediateCommitmentAndQueries {
                    commitment: WhirCommitment {
                        cap: MerkleTreeCapVarLength {
                            cap: vec![Digest::default(); tree_cap_size],
                        },
                        _marker: PhantomData,
                    },
                    queries: make_preallocated_extension_queries(count, values_per_leaf, path_len),
                },
            )
            .collect(),
        ood_samples: vec![E4::ZERO; num_intermediate_oracles],
        pow_nonces: vec![0u64; whir_pow_rounds],
        final_monomials: vec![],
        whir_schedule: WhirSchedule {
            base_lde_factor: original_lde_factor,
            cap_size: tree_cap_size,
            whir_steps_schedule: whir_steps_schedule.clone(),
            whir_queries_schedule: whir_queries_schedule.clone(),
            whir_steps_lde_factors: whir_steps_lde_factors.clone(),
            whir_pow_schedule: whir_pow_schedule.clone(),
        },
    };

    // Slab routing: D2D-copy each base-layer unified device cap into the slab's
    // `whir.{witness,memory,setup}.cap` range. Setup and memory unified caps
    // were H2D'd pre-prove on h2d_stream and the exec-stream waits on their
    // `Transfer::transferred` events were already recorded inside `prove()`.
    // Witness's unified cap was assembled by stage 1's per-coset commits on
    // exec_stream, so it's already visible here. One D2D per source replaces
    // the prior per-coset host-pinned H2D loop.
    //
    // We also schedule one D2H per source from the unified device cap into a
    // pinned host buffer; the start callback below `copy_from_slice`s those
    // pinned buffers into `proof.*_commitment.commitment.cap.cap`. Replaces
    // the prior `fill_full_cap_from_*` paths that walked per-coset host
    // accessors.
    use crate::prover::proof::layout::WhirBaseLayerKind;
    copy_base_layer_cap_to_slab(
        witness_unified_device_cap,
        proof_slab,
        proof_layout,
        WhirBaseLayerKind::Witness,
        stream,
    )?;
    copy_base_layer_cap_to_slab(
        memory_unified_device_cap,
        proof_slab,
        proof_layout,
        WhirBaseLayerKind::Memory,
        stream,
    )?;
    if let Some(setup_unified_device_cap) = setup_unified_device_cap {
        copy_base_layer_cap_to_slab(
            setup_unified_device_cap,
            proof_slab,
            proof_layout,
            WhirBaseLayerKind::Setup,
            stream,
        )?;
    }
    let witness_cap_host_for_proof =
        schedule_unified_cap_d2h(witness_unified_device_cap, context, stream)?;
    let witness_cap_host_accessor = witness_cap_host_for_proof.get_accessor();
    let memory_cap_host_for_proof =
        schedule_unified_cap_d2h(memory_unified_device_cap, context, stream)?;
    let memory_cap_host_accessor = memory_cap_host_for_proof.get_accessor();
    let setup_cap_host_for_proof = if let Some(setup_unified_device_cap) = setup_unified_device_cap
    {
        Some(schedule_unified_cap_d2h(
            setup_unified_device_cap,
            context,
            stream,
        )?)
    } else {
        None
    };
    let setup_cap_host_accessor = setup_cap_host_for_proof
        .as_ref()
        .map(HostAllocation::get_accessor);

    let mut shared_state = Box::new(ScheduledWhirProofState {
        proof: Some(scheduled_proof),
        #[cfg(test)]
        pre_pow_seeds: vec![Seed::default(); whir_pow_schedule.len()],
    });
    let shared_state_handle = UnsafeMutAccessor::new(shared_state.as_mut());
    let mut start_callbacks = Callbacks::new();
    if let Some(aggregation) = pre_start_aggregation_callback {
        // Replaces the former `gkr.base_layer_claims.schedule` finish callback.
        // Production extras are already device-gathered and committed into the
        // backward seed before this point; this callback publishes the metadata
        // needed by the final slab parse.
        start_callbacks.schedule(aggregation, stream)?;
    }
    // SAFETY: this pinned host allocation is written by the callback below
    // before any later host or device consumer reads it.
    let mut seed_host = unsafe { context.alloc_host_uninit::<Seed>() };
    let seed_accessor = seed_host.get_mut_accessor();
    start_callbacks.schedule(
        // SAFETY: the callback is the sole writer of `seed_host`, and it runs
        // on `exec_stream` before any downstream H2D or host read of the seed.
        move || unsafe {
            seed_accessor.write(seed_source());
        },
        stream,
    )?;
    let base_layer_point_len = base_layer_point_device.len();
    start_callbacks.schedule(
        {
            let shared_state = shared_state_handle;
            // SAFETY: the cap host buffers were filled by earlier D2Hs on the
            // same stream before this callback executes, and `shared_state`
            // stays alive for the whole scheduled proof assembly.
            move || unsafe {
                let proof_state = shared_state.get_mut();
                let proof = proof_state.proof.as_mut().unwrap();
                proof
                    .witness_commitment
                    .commitment
                    .cap
                    .cap
                    .copy_from_slice(witness_cap_host_accessor.get());
                proof
                    .memory_commitment
                    .commitment
                    .cap
                    .cap
                    .copy_from_slice(memory_cap_host_accessor.get());
                if let Some(setup_cap_host_accessor) = setup_cap_host_accessor {
                    proof
                        .setup_commitment
                        .commitment
                        .cap
                        .cap
                        .copy_from_slice(setup_cap_host_accessor.get());
                }
            }
        },
        stream,
    )?;

    let mut state = GpuWhirState::new(trace_len, context)?;

    let initialize_batched_forms_range = Range::new("gkr.whir.initialize_batched_forms")?;
    initialize_batched_forms_range.start(stream)?;
    schedule_initialize_batched_forms(
        memory_trace_holder,
        witness_trace_holder,
        setup_trace_holder,
        memory_trace_holder.columns_count,
        witness_trace_holder.columns_count,
        setup_trace_holder.columns_count,
        batching_challenge_source,
        use_hypercube_evals_for_batching,
        &mut state,
        &mut start_callbacks,
        context,
    )?;
    initialize_batched_forms_range.end(stream)?;
    tracing_ranges.push(initialize_batched_forms_range);

    memory_copy_async(
        &mut state.point_pows[..base_layer_point_len],
        base_layer_point_device,
        stream,
    )?;
    launch_build_eq_values_from_point(
        state.point_pows.as_ptr(),
        0,
        base_layer_point_len,
        state.eq_group_tables.as_mut_ptr(),
        state.eq_poly.as_mut_ptr(),
        trace_len,
        context,
    )?;

    let mut whir_steps_schedule = whir_steps_schedule.into_iter().peekable();
    let mut whir_queries_schedule = whir_queries_schedule.into_iter();
    let mut whir_steps_lde_factors = whir_steps_lde_factors.into_iter();
    let mut whir_pow_schedule = whir_pow_schedule.into_iter().enumerate();
    let num_whir_steps = num_intermediate_oracles;
    let mut rs_oracle: Option<GpuWhirExtensionOracle>;

    let folding_challenges: Vec<WhirHostUpload> = Vec::new();
    // Per-fold-round-group keepalives for the device-side transcript path:
    // d_seed, d_challenge, d_coeffs, plus host staging/mirror buffers and
    // the upload callbacks. Populated by `schedule_fold_round`.
    let mut fold_round_group_keepalives = FoldRoundGroupKeepalives::new();
    // Per-WHIR-round device/host state for the device-side PoW verify +
    // query-index assembly. Later callbacks consume the mirrored seed and
    // nonce, so these values are not just passive keepalives.
    let mut pow_round_state: Vec<PowAndQueryIndexesState> = Vec::new();
    let mut recursive_caps_keepalive: Vec<crate::prover::whir::GpuWhirExtensionOracleKeepalive> =
        Vec::new();
    // Pinned host buffers backing per-round D2Hs of intermediate oracle caps.
    // Each entry is read once by the corresponding final-callback that
    // populates `proof.intermediate_whir_oracles[round].commitment.cap.cap`,
    // and must outlive that callback.
    let mut intermediate_oracle_cap_hosts: Vec<HostAllocation<[Digest]>> = Vec::new();
    let mut ood_points = Vec::new();
    let mut ood_partial_readbacks = Vec::new();
    let mut ood_values = Vec::new();
    let mut query_index_callbacks = Vec::new();
    let mut query_indexes = Vec::new();
    let mut delinearization_challenges = Vec::new();
    let mut pow_nonces = Vec::new();
    let mut base_queries = Vec::new();
    let mut recursive_queries = Vec::new();
    let mut final_callbacks = Callbacks::new();
    let mut scheduled_sumcheck_poly_idx = 0usize;

    {
        let round_range = Range::new("gkr.whir.base_round.0")?;
        round_range.start(stream)?;
        let num_folding_steps = whir_steps_schedule
            .next()
            .expect("whir_steps_schedule exhausted before scheduling this round");
        let num_queries = whir_queries_schedule
            .next()
            .expect("whir_queries_schedule exhausted before scheduling this round");
        let (pow_round_idx, pow_bits) = whir_pow_schedule
            .next()
            .expect("whir_pow_schedule exhausted before scheduling this round");
        let folds_range = Range::new("gkr.whir.base_round.0.folds")?;
        folds_range.start(stream)?;
        schedule_fold_round(
            num_folding_steps,
            &mut state,
            &mut scheduled_sumcheck_poly_idx,
            &mut fold_round_group_keepalives,
            proof_slab,
            proof_layout,
            shared_state_handle,
            seed_accessor,
            stream,
            context,
        )?;
        folds_range.end(stream)?;
        tracing_ranges.push(folds_range);

        let lde_factor = whir_steps_lde_factors
            .next()
            .expect("whir_steps_lde_factors exhausted before scheduling this round");
        let next_folding_steps = *whir_steps_schedule
            .peek()
            .expect("whir_steps_schedule has no follow-up step for next-oracle sizing");
        let commit_next_oracle_range = Range::new("gkr.whir.base_round.0.commit_next_oracle")?;
        commit_next_oracle_range.start(stream)?;
        let oracle = schedule_commit_next_oracle_phase(
            &state,
            0,
            lde_factor,
            next_folding_steps,
            tree_cap_size,
            proof_slab,
            proof_layout,
            shared_state_handle,
            seed_accessor,
            &mut intermediate_oracle_cap_hosts,
            &mut final_callbacks,
            stream,
            context,
        )?;
        commit_next_oracle_range.end(stream)?;
        tracing_ranges.push(commit_next_oracle_range);
        rs_oracle = Some(oracle);

        let ood_sample_range = Range::new("gkr.whir.base_round.0.ood_sample")?;
        ood_sample_range.start(stream)?;
        let ood_point_host = schedule_ood_sample_phase(
            &mut state,
            0,
            proof_slab,
            proof_layout,
            shared_state_handle,
            seed_accessor,
            &mut ood_points,
            &mut ood_partial_readbacks,
            &mut ood_values,
            &mut final_callbacks,
            stream,
            context,
        )?;
        ood_sample_range.end(stream)?;
        tracing_ranges.push(ood_sample_range);

        let pow_and_query_indexes_range =
            Range::new("gkr.whir.base_round.0.pow_and_query_indexes")?;
        pow_and_query_indexes_range.start(stream)?;
        let query_domain_log2 =
            trace_len_log2 + original_lde_factor.trailing_zeros() as usize - num_folding_steps;
        let query_domain_size = 1u64 << query_domain_log2;
        let query_domain_generator = domain_generator_for_size::<BF>(query_domain_size);
        let (query_indexes_host, mut query_index_callbacks_for_round) =
            schedule_pow_and_query_indexes_phase(
                &mut seed_host,
                seed_accessor,
                shared_state_handle,
                num_queries,
                pow_bits,
                pow_round_idx,
                query_domain_log2,
                proof_slab,
                proof_layout,
                &mut pow_round_state,
                &mut pow_nonces,
                stream,
                context,
            )?;
        pow_and_query_indexes_range.end(stream)?;
        tracing_ranges.push(pow_and_query_indexes_range);

        let delinearization_eq_range = Range::new("gkr.whir.base_round.0.delinearization_eq")?;
        delinearization_eq_range.start(stream)?;
        let (delinearization_upload, delinearization_device) =
            schedule_delinearization_running_powers_phase(
                &mut state,
                num_queries,
                &ood_point_host,
                seed_accessor,
                &mut ood_points,
                context,
            )?;
        delinearization_eq_range.end(stream)?;
        tracing_ranges.push(delinearization_eq_range);

        let queries_range = Range::new("gkr.whir.base_round.0.queries")?;
        queries_range.start(stream)?;
        // Shared host + device buffers carrying `internal_index = query_index
        // / lde_factor` for every query of this base round. One alloc + one
        // fill callback + one H2D replaces `num_queries × 3` per-helper-call
        // host alloc + callback + device alloc + H2D.
        let base_lde_factor = 1u32 << memory_trace_holder.log_lde_factor;
        // SAFETY: this pinned host allocation is initialized by the callback
        // below before the H2D copy reads from it.
        let mut internal_indexes_host =
            unsafe { context.alloc_host_uninit_slice::<u32>(num_queries) };
        {
            let query_indexes_accessor = query_indexes_host.get_accessor();
            let internal_indexes_accessor = internal_indexes_host.get_mut_accessor();
            query_index_callbacks_for_round.schedule(
                // SAFETY: the callback is the sole writer of
                // `internal_indexes_host`, and it runs before the queued H2D.
                move || unsafe {
                    let src = query_indexes_accessor.get();
                    let dst = internal_indexes_accessor.get_mut();
                    for (dst_el, src_el) in dst.iter_mut().zip(src.iter()) {
                        *dst_el = src_el / base_lde_factor;
                    }
                },
                stream,
            )?;
        }
        let mut device_internal_indexes: DeviceAllocation<u32> =
            context.alloc(num_queries, AllocationPlacement::BestFit)?;
        memory_copy_async(&mut device_internal_indexes, &internal_indexes_host, stream)?;
        let mut round_base_queries = [Vec::new(), Vec::new(), Vec::new()];
        for query_idx in 0..num_queries {
            let device_internal_index = &device_internal_indexes[query_idx..query_idx + 1];

            let memory_query = schedule_unknown_coset_base_field_query(
                memory_trace_holder,
                device_internal_index,
                context,
            )?;
            let witness_query = schedule_unknown_coset_base_field_query(
                witness_trace_holder,
                device_internal_index,
                context,
            )?;
            let setup_query = schedule_unknown_coset_base_field_query(
                setup_trace_holder,
                device_internal_index,
                context,
            )?;

            let memory_leaf_accessors = memory_query
                .value_leafs
                .iter()
                .map(HostAllocation::get_accessor)
                .collect::<Vec<_>>();
            let memory_path_accessors = memory_query
                .path_merkle_paths
                .iter()
                .map(HostAllocation::get_accessor)
                .collect::<Vec<_>>();
            let witness_leaf_accessors = witness_query
                .value_leafs
                .iter()
                .map(HostAllocation::get_accessor)
                .collect::<Vec<_>>();
            let witness_path_accessors = witness_query
                .path_merkle_paths
                .iter()
                .map(HostAllocation::get_accessor)
                .collect::<Vec<_>>();
            let setup_leaf_accessors = setup_query
                .value_leafs
                .iter()
                .map(HostAllocation::get_accessor)
                .collect::<Vec<_>>();
            let setup_path_accessors = setup_query
                .path_merkle_paths
                .iter()
                .map(HostAllocation::get_accessor)
                .collect::<Vec<_>>();

            let query_indexes_accessor = query_indexes_host.get_accessor();
            let (eq_upload, _eq_host) = schedule_accumulate_eq_sample_in_place_device(
                &mut state,
                // SAFETY: `dst` is a callback-owned mutable slice provided by the
                // scheduler helper; the callback writes it sequentially before
                // the subsequent H2D reads it.
                move |dst| unsafe {
                    let point = E4::from_base(
                        query_domain_generator.pow(query_indexes_accessor.get()[query_idx]),
                    );
                    let mut value = point;
                    for dst_el in dst.iter_mut() {
                        *dst_el = value;
                        value.square();
                    }
                },
                &delinearization_device[query_idx + 1..query_idx + 2],
                context,
            )?;
            ood_points.push(eq_upload);

            final_callbacks.schedule(
                {
                    let shared_state = shared_state_handle;
                    let memory_values_per_leaf = memory_query.values_per_leaf;
                    let memory_columns_count = memory_query.columns_count;
                    let memory_coset_tree_size = memory_query.coset_tree_size;
                    let memory_log_lde_factor = memory_query.log_lde_factor;
                    let witness_values_per_leaf = witness_query.values_per_leaf;
                    let witness_columns_count = witness_query.columns_count;
                    let witness_coset_tree_size = witness_query.coset_tree_size;
                    let witness_log_lde_factor = witness_query.log_lde_factor;
                    let setup_values_per_leaf = setup_query.values_per_leaf;
                    let setup_columns_count = setup_query.columns_count;
                    let setup_coset_tree_size = setup_query.coset_tree_size;
                    let setup_log_lde_factor = setup_query.log_lde_factor;
                    // SAFETY: all accessors captured here point to host buffers
                    // materialized before this callback runs, and the shared
                    // proof state outlives every final callback.
                    move || unsafe {
                        let proof_state = shared_state.get_mut();
                        let proof = proof_state.proof.as_mut().unwrap();
                        let shared_index = query_indexes_accessor.get()[query_idx] as usize;
                        fill_unknown_coset_base_field_query_from_accessors(
                            &mut proof.memory_commitment.queries[query_idx],
                            shared_index,
                            memory_coset_tree_size,
                            memory_log_lde_factor,
                            memory_values_per_leaf,
                            memory_columns_count,
                            &memory_leaf_accessors,
                            &memory_path_accessors,
                        );
                        fill_unknown_coset_base_field_query_from_accessors(
                            &mut proof.witness_commitment.queries[query_idx],
                            shared_index,
                            witness_coset_tree_size,
                            witness_log_lde_factor,
                            witness_values_per_leaf,
                            witness_columns_count,
                            &witness_leaf_accessors,
                            &witness_path_accessors,
                        );
                        fill_unknown_coset_base_field_query_from_accessors(
                            &mut proof.setup_commitment.queries[query_idx],
                            shared_index,
                            setup_coset_tree_size,
                            setup_log_lde_factor,
                            setup_values_per_leaf,
                            setup_columns_count,
                            &setup_leaf_accessors,
                            &setup_path_accessors,
                        );
                    }
                },
                stream,
            )?;

            round_base_queries[0].push(memory_query);
            round_base_queries[1].push(witness_query);
            round_base_queries[2].push(setup_query);
        }
        queries_range.end(stream)?;
        tracing_ranges.push(queries_range);
        // `round_base_queries` retains every `ScheduledUnknownCosetBaseFieldQuery`
        // — including its `value_leafs` / `path_merkle_paths` host allocations —
        // so the per-query host buffers stay alive until the
        // `GpuWhirFoldScheduledExecution` is dropped (i.e. after `finish()` has
        // synced the stream). The previous `into_keepalive` step discarded those
        // host buffers while their `UnsafeAccessor`s were still in flight on the
        // final-readback callback.
        base_queries.push(round_base_queries);
        query_index_callbacks.push(query_index_callbacks_for_round);
        query_indexes.push(query_indexes_host);
        delinearization_challenges.push(delinearization_upload);
        round_range.end(stream)?;
        tracing_ranges.push(round_range);
    }

    let num_internal_whir_steps = num_whir_steps.saturating_sub(1);
    for internal_round_idx in 0..num_internal_whir_steps {
        let round_name = format!("gkr.whir.internal_round.{}", internal_round_idx);
        let round_range = Range::new(&*round_name)?;
        round_range.start(stream)?;
        let num_folding_steps = whir_steps_schedule
            .next()
            .expect("whir_steps_schedule exhausted before scheduling this round");
        let num_queries = whir_queries_schedule
            .next()
            .expect("whir_queries_schedule exhausted before scheduling this round");
        let (pow_round_idx, pow_bits) = whir_pow_schedule
            .next()
            .expect("whir_pow_schedule exhausted before scheduling this round");
        schedule_fold_round(
            num_folding_steps,
            &mut state,
            &mut scheduled_sumcheck_poly_idx,
            &mut fold_round_group_keepalives,
            proof_slab,
            proof_layout,
            shared_state_handle,
            seed_accessor,
            stream,
            context,
        )?;

        let lde_factor = whir_steps_lde_factors
            .next()
            .expect("whir_steps_lde_factors exhausted before scheduling this round");
        let next_folding_steps = *whir_steps_schedule
            .peek()
            .expect("whir_steps_schedule has no follow-up step for next-oracle sizing");
        let commit_name = format!("{round_name}.commit_next_oracle");
        let commit_next_oracle_range = Range::new(&*commit_name)?;
        commit_next_oracle_range.start(stream)?;
        let next_oracle = schedule_commit_next_oracle_phase(
            &state,
            internal_round_idx + 1,
            lde_factor,
            next_folding_steps,
            tree_cap_size,
            proof_slab,
            proof_layout,
            shared_state_handle,
            seed_accessor,
            &mut intermediate_oracle_cap_hosts,
            &mut final_callbacks,
            stream,
            context,
        )?;
        commit_next_oracle_range.end(stream)?;
        tracing_ranges.push(commit_next_oracle_range);
        let mut oracle_to_query = rs_oracle.replace(next_oracle).unwrap();

        let ood_point_host = schedule_ood_sample_phase(
            &mut state,
            internal_round_idx + 1,
            proof_slab,
            proof_layout,
            shared_state_handle,
            seed_accessor,
            &mut ood_points,
            &mut ood_partial_readbacks,
            &mut ood_values,
            &mut final_callbacks,
            stream,
            context,
        )?;

        let pow_and_query_indexes_name = format!("{round_name}.pow_and_query_indexes");
        let pow_and_query_indexes_range = Range::new(&*pow_and_query_indexes_name)?;
        pow_and_query_indexes_range.start(stream)?;
        let query_domain_log2 = state.current_len.trailing_zeros() as usize
            + oracle_to_query.lde_factor().trailing_zeros() as usize;
        let query_domain_size = 1u64 << query_domain_log2;
        let query_domain_generator = domain_generator_for_size::<BF>(query_domain_size);
        let (query_indexes_host, query_index_callbacks_for_round) =
            schedule_pow_and_query_indexes_phase(
                &mut seed_host,
                seed_accessor,
                shared_state_handle,
                num_queries,
                pow_bits,
                pow_round_idx,
                query_domain_log2,
                proof_slab,
                proof_layout,
                &mut pow_round_state,
                &mut pow_nonces,
                stream,
                context,
            )?;
        pow_and_query_indexes_range.end(stream)?;
        tracing_ranges.push(pow_and_query_indexes_range);

        let (delinearization_upload, delinearization_device) =
            schedule_delinearization_running_powers_phase(
                &mut state,
                num_queries,
                &ood_point_host,
                seed_accessor,
                &mut ood_points,
                context,
            )?;

        let queries_name = format!("{round_name}.queries");
        let queries_range = Range::new(&*queries_name)?;
        queries_range.start(stream)?;
        let mut round_recursive_queries = Vec::new();
        for query_idx in 0..num_queries {
            // SAFETY: this single-element pinned host allocation is written by
            // the callback below before the folded-query scheduler reads it.
            let mut single_query_index = unsafe { context.alloc_host_uninit_slice(1) };
            let single_query_index_accessor = single_query_index.get_mut_accessor();
            let query_indexes_accessor = query_indexes_host.get_accessor();
            let mut copy_callbacks = Callbacks::new();
            copy_callbacks.schedule(
                // SAFETY: the callback is the sole writer of
                // `single_query_index`, and it runs before query scheduling.
                move || unsafe {
                    single_query_index_accessor.get_mut()[0] =
                        query_indexes_accessor.get()[query_idx];
                },
                stream,
            )?;
            let query = oracle_to_query
                .schedule_query_for_folded_index_from_host(&single_query_index, context)?;
            let mut query = query;
            let query_values_per_leaf = query.values_per_leaf();
            let query_log_lde_factor = oracle_to_query.lde_factor().trailing_zeros();
            let query_coset_tree_size = oracle_to_query.packed_leaf_count();
            copy_intermediate_query_to_slab(
                &single_query_index,
                &mut query,
                proof_slab,
                proof_layout,
                internal_round_idx,
                query_idx,
                stream,
                context,
            )?;
            let query_leafs_accessor = query.leafs_accessor();
            let query_paths_accessor = query.merkle_paths_accessor();
            let query_indexes_accessor = query_indexes_host.get_accessor();
            let (eq_upload, _eq_host) = schedule_accumulate_eq_sample_in_place_device(
                &mut state,
                // SAFETY: `dst` is a callback-owned mutable slice provided by the
                // scheduler helper; the callback fills it before upload.
                move |dst| unsafe {
                    let point = E4::from_base(
                        query_domain_generator.pow(query_indexes_accessor.get()[query_idx]),
                    );
                    let mut value = point;
                    for dst_el in dst.iter_mut() {
                        *dst_el = value;
                        value.square();
                    }
                },
                &delinearization_device[query_idx + 1..query_idx + 2],
                context,
            )?;
            ood_points.push(eq_upload);

            final_callbacks.extend(copy_callbacks);
            final_callbacks.schedule(
                {
                    let shared_state = shared_state_handle;
                    let query_indexes_accessor = query_indexes_host.get_accessor();
                    // SAFETY: the query leaf/path accessors and shared proof
                    // state all outlive this callback, and the host buffers were
                    // filled before the callback runs.
                    move || unsafe {
                        let index = query_indexes_accessor.get()[query_idx] as usize;
                        fill_extension_query_from_accessors(
                            &mut shared_state
                                .get_mut()
                                .proof
                                .as_mut()
                                .unwrap()
                                .intermediate_whir_oracles[internal_round_idx]
                                .queries[query_idx],
                            index,
                            query_coset_tree_size,
                            query_log_lde_factor,
                            query_values_per_leaf,
                            query_leafs_accessor,
                            query_paths_accessor,
                        );
                    }
                },
                stream,
            )?;
            round_recursive_queries.push(query);
        }
        queries_range.end(stream)?;
        tracing_ranges.push(queries_range);
        recursive_caps_keepalive.push(oracle_to_query.into_host_keepalive());
        recursive_queries.push(
            round_recursive_queries
                .into_iter()
                .map(crate::prover::whir::GpuWhirScheduledExtensionQuery::into_keepalive)
                .collect(),
        );
        query_index_callbacks.push(query_index_callbacks_for_round);
        query_indexes.push(query_indexes_host);
        delinearization_challenges.push(delinearization_upload);
        round_range.end(stream)?;
        tracing_ranges.push(round_range);
    }

    let final_monomials_keepalive: Option<HostAllocation<[E4]>>;
    {
        let round_range = Range::new("gkr.whir.final_round")?;
        round_range.start(stream)?;
        let num_folding_steps = whir_steps_schedule
            .next()
            .expect("whir_steps_schedule exhausted before scheduling this round");
        let num_queries = whir_queries_schedule
            .next()
            .expect("whir_queries_schedule exhausted before scheduling this round");
        let (pow_round_idx, pow_bits) = whir_pow_schedule
            .next()
            .expect("whir_pow_schedule exhausted before scheduling this round");
        schedule_fold_round(
            num_folding_steps,
            &mut state,
            &mut scheduled_sumcheck_poly_idx,
            &mut fold_round_group_keepalives,
            proof_slab,
            proof_layout,
            shared_state_handle,
            seed_accessor,
            stream,
            context,
        )?;

        // Mirror CPU `prover/src/gkr/whir/mod.rs` lines 1297 and 1391: after the final fold
        // and before drawing the final PoW/query bits, CPU commits the remaining
        // monomial-form coefficients into the transcript seed, and later stores them on the
        // proof as `final_monomials`. Read them back asynchronously and do both in a single
        // stream-ordered callback so the seed update is sequenced before
        // `schedule_pow_verify_and_query_indexes` below.
        // SAFETY: this pinned host allocation is used purely as the D2H
        // destination before the final callback consumes it.
        let mut final_monomials_host =
            unsafe { context.alloc_host_uninit_slice::<E4>(state.current_len) };
        let mut final_monomials_device =
            context.alloc::<E4>(state.current_len, AllocationPlacement::BestFit)?;
        // SAFETY: `final_monomials_device` stores `E4` elements, so viewing it
        // as its underlying `BF` lanes for the transpose is layout-compatible.
        let mut transpose_dst = unsafe { final_monomials_device.transmute_mut::<BF>() };
        let mut transpose_dst_matrix = DeviceMatrixMut::new(&mut transpose_dst, EXT4_DEGREE);
        let monomials_matrix_chunk = DeviceMatrixChunk::new(
            state.sumchecked_poly_monomial_form.slice(),
            state.original_trace_len,
            0,
            state.current_len,
        );
        transpose(&monomials_matrix_chunk, &mut transpose_dst_matrix, stream)?;
        memory_copy_async(&mut final_monomials_host, &final_monomials_device, stream)?;
        let final_monomials_accessor = final_monomials_host.get_accessor();
        final_callbacks.schedule(
            {
                let shared_state = shared_state_handle;
                // SAFETY: `final_monomials_host` has been filled by the D2H
                // queued above before this callback runs; `seed_accessor` and
                // the shared proof state both outlive the callback.
                move || unsafe {
                    let mut monomials = final_monomials_accessor.get().to_vec();
                    bitreverse_enumeration_inplace(&mut monomials);
                    commit_field_els::<BF, E4>(seed_accessor.get_mut(), &monomials);
                    shared_state
                        .get_mut()
                        .proof
                        .as_mut()
                        .unwrap()
                        .final_monomials = monomials;
                }
            },
            stream,
        )?;
        final_monomials_keepalive = Some(final_monomials_host);

        let mut oracle_to_query = rs_oracle.take().unwrap();
        let query_domain_log2 = state.current_len.trailing_zeros() as usize
            + oracle_to_query.lde_factor().trailing_zeros() as usize;
        let pow_and_query_indexes_range = Range::new("gkr.whir.final_round.pow_and_query_indexes")?;
        pow_and_query_indexes_range.start(stream)?;
        let (query_indexes_host, query_index_callbacks_for_round) =
            schedule_pow_and_query_indexes_phase(
                &mut seed_host,
                seed_accessor,
                shared_state_handle,
                num_queries,
                pow_bits,
                pow_round_idx,
                query_domain_log2,
                proof_slab,
                proof_layout,
                &mut pow_round_state,
                &mut pow_nonces,
                stream,
                context,
            )?;
        pow_and_query_indexes_range.end(stream)?;
        tracing_ranges.push(pow_and_query_indexes_range);
        let queries_range = Range::new("gkr.whir.final_round.queries")?;
        queries_range.start(stream)?;
        let mut round_recursive_queries = Vec::new();
        let final_oracle_index = num_whir_steps.saturating_sub(1);
        for query_idx in 0..num_queries {
            // SAFETY: this single-element pinned host allocation is written by
            // the callback below before the folded-query scheduler reads it.
            let mut single_query_index = unsafe { context.alloc_host_uninit_slice(1) };
            let single_query_index_accessor = single_query_index.get_mut_accessor();
            let query_indexes_accessor = query_indexes_host.get_accessor();
            let mut copy_callbacks = Callbacks::new();
            copy_callbacks.schedule(
                // SAFETY: the callback is the sole writer of
                // `single_query_index`, and it runs before query scheduling.
                move || unsafe {
                    single_query_index_accessor.get_mut()[0] =
                        query_indexes_accessor.get()[query_idx];
                },
                stream,
            )?;
            let query = oracle_to_query
                .schedule_query_for_folded_index_from_host(&single_query_index, context)?;
            let mut query = query;
            let query_values_per_leaf = query.values_per_leaf();
            let query_log_lde_factor = oracle_to_query.lde_factor().trailing_zeros();
            let query_coset_tree_size = oracle_to_query.packed_leaf_count();
            copy_intermediate_query_to_slab(
                &single_query_index,
                &mut query,
                proof_slab,
                proof_layout,
                final_oracle_index,
                query_idx,
                stream,
                context,
            )?;
            let query_leafs_accessor = query.leafs_accessor();
            let query_paths_accessor = query.merkle_paths_accessor();
            final_callbacks.extend(copy_callbacks);
            final_callbacks.schedule(
                {
                    let shared_state = shared_state_handle;
                    let query_indexes_accessor = query_indexes_host.get_accessor();
                    // SAFETY: the query leaf/path accessors and shared proof
                    // state all outlive this callback, and the host buffers were
                    // filled before the callback runs.
                    move || unsafe {
                        let index = query_indexes_accessor.get()[query_idx] as usize;
                        fill_extension_query_from_accessors(
                            &mut shared_state
                                .get_mut()
                                .proof
                                .as_mut()
                                .unwrap()
                                .intermediate_whir_oracles[final_oracle_index]
                                .queries[query_idx],
                            index,
                            query_coset_tree_size,
                            query_log_lde_factor,
                            query_values_per_leaf,
                            query_leafs_accessor,
                            query_paths_accessor,
                        );
                    }
                },
                stream,
            )?;
            round_recursive_queries.push(query);
        }
        queries_range.end(stream)?;
        tracing_ranges.push(queries_range);
        recursive_caps_keepalive.push(oracle_to_query.into_host_keepalive());
        recursive_queries.push(
            round_recursive_queries
                .into_iter()
                .map(crate::prover::whir::GpuWhirScheduledExtensionQuery::into_keepalive)
                .collect(),
        );
        query_index_callbacks.push(query_index_callbacks_for_round);
        query_indexes.push(query_indexes_host);
        round_range.end(stream)?;
        tracing_ranges.push(round_range);
    }

    schedule_range.end(stream)?;
    tracing_ranges.push(schedule_range);

    Ok(GpuWhirFoldScheduledExecution {
        _tracing_ranges: tracing_ranges,
        _start_callbacks: start_callbacks,
        _folding_challenges: folding_challenges,
        _fold_round_group_keepalives: fold_round_group_keepalives,
        _pow_round_state: pow_round_state,
        _ood_points: ood_points,
        _query_index_callbacks: query_index_callbacks,
        _delinearization_challenges: delinearization_challenges,
        _base_queries: base_queries,
        _recursive_queries: recursive_queries,
        _witness_cap_host_for_proof: witness_cap_host_for_proof,
        _memory_cap_host_for_proof: memory_cap_host_for_proof,
        _setup_cap_host_for_proof: setup_cap_host_for_proof,
        _intermediate_oracle_cap_hosts: intermediate_oracle_cap_hosts,
        _recursive_caps_keepalive: recursive_caps_keepalive,
        _final_monomials_host: final_monomials_keepalive,
        _final_callbacks: final_callbacks,
        shared_state,
    })
}
