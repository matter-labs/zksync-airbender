use super::*;

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
    let mut seed_host = unsafe { context.alloc_host_uninit::<Seed>() };
    let seed_accessor = seed_host.get_mut_accessor();
    start_callbacks.schedule(
        move || unsafe {
            seed_accessor.write(seed_source());
        },
        stream,
    )?;
    let base_layer_point_len = base_layer_point_device.len();
    start_callbacks.schedule(
        {
            let shared_state = shared_state_handle;
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

    let folding_challenges: Vec<WhirHostUpload<E4>> = Vec::new();
    // Per-fold-round-group device/host keepalives for the device-side
    // transcript path: d_seed, d_challenge, d_coeffs, plus host staging/mirror
    // buffers and the upload callbacks.
    let mut fold_round_group_device_seeds: Vec<DeviceAllocation<u32>> = Vec::new();
    let mut fold_round_group_device_challenges: Vec<DeviceAllocation<E4>> = Vec::new();
    let mut fold_round_group_device_coeffs: Vec<DeviceAllocation<E4>> = Vec::new();
    let mut fold_round_group_host_seed_stagings: Vec<HostAllocation<[u32]>> = Vec::new();
    let mut fold_round_group_host_seed_mirrors: Vec<HostAllocation<[u32]>> = Vec::new();
    let mut fold_round_group_host_coeffs: Vec<HostAllocation<[E4]>> = Vec::new();
    let mut fold_round_group_upload_callbacks: Vec<Callbacks<'static>> = Vec::new();
    // Per-WHIR-round keepalives for the device-side PoW verify + query index
    // assembly: the contained device/host buffers must outlive the stream
    // work scheduled by the caller around them.
    let mut pow_keepalives_keepalive: Vec<PowAndQueryIndexesKeepalives> = Vec::new();
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

    let mut schedule_fold_round = |num_folding_steps: usize,
                                   state: &mut GpuWhirState|
     -> CudaResult<()> {
        if num_folding_steps == 0 {
            return Ok(());
        }

        // Allocate persistent per-round-group device buffers: seed is
        // threaded round-to-round, challenge is overwritten each round
        // (stream-ordered, so safe to reuse), coeffs are packed into one
        // contiguous [3 * num_folding_steps] block for bulk readback.
        let mut d_seed: DeviceAllocation<u32> =
            context.alloc(STATE_SIZE, AllocationPlacement::BestFit)?;
        let mut d_challenge: DeviceAllocation<E4> =
            context.alloc(1, AllocationPlacement::BestFit)?;
        let mut d_coeffs_all: DeviceAllocation<E4> =
            context.alloc(3 * num_folding_steps, AllocationPlacement::BestFit)?;

        // Seed upload: stage the host seed into a pinned buffer via a
        // pre-kernel callback, then H2D copy into d_seed.
        let mut h_seed_staging = unsafe { context.alloc_host_uninit_slice::<u32>(STATE_SIZE) };
        let mut upload_callbacks = Callbacks::new();
        let staging_accessor = h_seed_staging.get_mut_accessor();
        upload_callbacks.schedule(
            move || unsafe {
                staging_accessor
                    .get_mut()
                    .copy_from_slice(&seed_accessor.get().0);
            },
            stream,
        )?;
        memory_copy_async(&mut d_seed, &h_seed_staging, stream)?;

        let group_start_idx = scheduled_sumcheck_poly_idx;
        for round in 0..num_folding_steps {
            // Compute the 3 reductions into state.reduce_out (on device).
            schedule_special_three_point_eval_device_compute(state, context)?;

            // Fused kernel: reads reduce_out + d_seed, writes
            // d_coeffs[round*3..round*3+3], d_challenge, and the advanced
            // d_seed — all device-side, no host roundtrip.
            let coeff_range = (round * 3)..((round + 1) * 3);
            crate::ops::blake2s::whir_fold_round_update(
                &state.reduce_out[..3],
                &mut d_seed,
                &mut d_coeffs_all[coeff_range],
                &mut d_challenge,
                stream,
            )?;

            let current_len = state.current_len;
            let next_len = current_len / 2;
            whir_fold_split_half_in_place_vectorized(
                &mut state.sumchecked_poly_monomial_form,
                &d_challenge[0],
                next_len,
                stream,
            )?;
            whir_fold_split_half_in_place(
                &mut state.sumchecked_poly_evaluation_form[..current_len],
                &d_challenge[0],
                stream,
            )?;
            whir_fold_split_half_in_place(
                &mut state.eq_poly[..current_len],
                &d_challenge[0],
                stream,
            )?;
            state.current_len = next_len;
            scheduled_sumcheck_poly_idx += 1;
        }

        // Phase 3 slab routing: before the host-directed D2H, D2D-copy the
        // packed `d_coeffs_all` (the `[E4; 3]` sumcheck-round coefficients
        // for every round in this group) into the slab's
        // `whir.sumcheck_polys[group_start_idx * 3 .. (group_start_idx +
        // num_folding_steps) * 3]` region. The slab range is flat
        // `total_sumcheck_polys * 3` `E4` values in schedule order, which
        // matches `d_coeffs_all`'s packing exactly.
        if let Some(slab) = proof_slab {
            let (dst_base_ptr, dst_total_len) =
                unsafe { proof_layout.whir_sumcheck_polys_device_mut(slab.as_ptr() as *mut u8) };
            let dst_offset = group_start_idx * 3;
            let dst_len = num_folding_steps * 3;
            assert!(
                dst_offset + dst_len <= dst_total_len,
                "sumcheck_polys slab range overflow: {}+{} > {}",
                dst_offset,
                dst_len,
                dst_total_len,
            );
            // SAFETY: offset is 16-byte-aligned (slab base is, and
            // `E4` is 16 bytes so every element index is aligned);
            // the destination sub-range is disjoint from other slab
            // fields and from other fold-round groups.
            let dst = unsafe {
                era_cudart::slice::DeviceSlice::from_raw_parts_mut(
                    dst_base_ptr.add(dst_offset),
                    dst_len,
                )
            };
            memory_copy_async(dst, &d_coeffs_all[..dst_len], stream)?;
        }

        // Bulk D2H: all coeffs for this group, plus the updated seed.
        // Schedule a final callback that rehydrates both into the shared
        // proof state and the host seed (which subsequent host-side
        // transcript ops — oracle commit, OOD, pow, queries — rely on).
        let mut h_coeffs_all =
            unsafe { context.alloc_host_uninit_slice::<E4>(3 * num_folding_steps) };
        memory_copy_async(&mut h_coeffs_all, &d_coeffs_all, stream)?;
        let mut h_seed_mirror = unsafe { context.alloc_host_uninit_slice::<u32>(STATE_SIZE) };
        memory_copy_async(&mut h_seed_mirror, &d_seed, stream)?;
        let h_coeffs_accessor = h_coeffs_all.get_accessor();
        let h_seed_mirror_accessor = h_seed_mirror.get_accessor();
        // Rehydration callback goes into the same per-group Callbacks
        // container as the upload callback; their stream-order is decided
        // by scheduling position, not by the Callbacks object they belong
        // to. Keeping it local avoids a mutable borrow conflict with the
        // outer `final_callbacks` (which the surrounding scope also
        // writes to).
        {
            let shared_state = shared_state_handle;
            upload_callbacks.schedule(
                move || unsafe {
                    let all = h_coeffs_accessor.get();
                    let proof_state = shared_state.get_mut();
                    let proof = proof_state
                        .proof
                        .as_mut()
                        .expect("proof must be initialized");
                    for i in 0..num_folding_steps {
                        let base = i * 3;
                        proof.sumcheck_polys[group_start_idx + i] =
                            [all[base], all[base + 1], all[base + 2]];
                    }
                    // Mirror the device seed back into the host transcript
                    // seed for subsequent host-side transcript operations.
                    let new_seed = h_seed_mirror_accessor.get();
                    seed_accessor.get_mut().0.copy_from_slice(new_seed);
                },
                stream,
            )?;
        }

        fold_round_group_device_seeds.push(d_seed);
        fold_round_group_device_challenges.push(d_challenge);
        fold_round_group_device_coeffs.push(d_coeffs_all);
        fold_round_group_host_seed_stagings.push(h_seed_staging);
        fold_round_group_host_seed_mirrors.push(h_seed_mirror);
        fold_round_group_host_coeffs.push(h_coeffs_all);
        fold_round_group_upload_callbacks.push(upload_callbacks);
        Ok(())
    };

    {
        let round_range = Range::new("gkr.whir.base_round.0")?;
        round_range.start(stream)?;
        let num_folding_steps = whir_steps_schedule.next().unwrap();
        let num_queries = whir_queries_schedule.next().unwrap();
        let (pow_round_idx, pow_bits) = whir_pow_schedule.next().unwrap();
        let folds_range = Range::new("gkr.whir.base_round.0.folds")?;
        folds_range.start(stream)?;
        schedule_fold_round(num_folding_steps, &mut state)?;
        folds_range.end(stream)?;
        tracing_ranges.push(folds_range);

        let lde_factor = whir_steps_lde_factors.next().unwrap();
        let next_folding_steps = *whir_steps_schedule.peek().unwrap();
        let commit_next_oracle_range = Range::new("gkr.whir.base_round.0.commit_next_oracle")?;
        commit_next_oracle_range.start(stream)?;
        let oracle = GpuWhirExtensionOracle::schedule_from_device_monomial_coeffs(
            &state.sumchecked_poly_monomial_form,
            state.current_len,
            lde_factor,
            1 << next_folding_steps,
            tree_cap_size,
            context,
        )?;
        copy_intermediate_cap_to_slab(
            oracle.unified_device_cap(),
            proof_slab,
            proof_layout,
            0,
            stream,
        )?;
        // D2H the oracle's unified device cap into a pinned host buffer; the
        // final callback `copy_from_slice`s it into
        // `proof.intermediate_whir_oracles[0].commitment.cap.cap` and folds
        // that commitment into the transcript.
        let oracle_cap_host_for_proof =
            schedule_unified_cap_d2h(oracle.unified_device_cap(), context, stream)?;
        let oracle_cap_host_accessor = oracle_cap_host_for_proof.get_accessor();
        intermediate_oracle_cap_hosts.push(oracle_cap_host_for_proof);
        final_callbacks.schedule(
            {
                let shared_state = shared_state_handle;
                move || unsafe {
                    let proof_state = shared_state.get_mut();
                    let commitment = &mut proof_state
                        .proof
                        .as_mut()
                        .unwrap()
                        .intermediate_whir_oracles[0]
                        .commitment;
                    commitment
                        .cap
                        .cap
                        .copy_from_slice(oracle_cap_host_accessor.get());
                    add_whir_commitment_to_transcript(seed_accessor.get_mut(), commitment);
                }
            },
            stream,
        )?;
        commit_next_oracle_range.end(stream)?;
        tracing_ranges.push(commit_next_oracle_range);
        rs_oracle = Some(oracle);

        let ood_sample_range = Range::new("gkr.whir.base_round.0.ood_sample")?;
        ood_sample_range.start(stream)?;
        let (ood_point_upload, ood_point_host, ood_point_device) =
            schedule_callback_populated_upload(context, 1, move |dst: &mut [E4]| unsafe {
                dst[0] = draw_random_field_els::<BF, E4>(seed_accessor.get_mut(), 1)[0];
            })?;
        let ood_partials = schedule_monomial_eval_device(&mut state, &ood_point_device, context)?;
        let mut ood_value_host = unsafe { context.alloc_host_uninit_slice(1) };
        let ood_value_accessor = ood_value_host.get_mut_accessor();
        final_callbacks.schedule(
            {
                let shared_state = shared_state_handle;
                let partial_accessors = ood_partials
                    .iter()
                    .map(HostAllocation::get_accessor)
                    .collect::<Vec<_>>();
                move || unsafe {
                    let mut value = E4::ZERO;
                    for partial in partial_accessors.iter() {
                        value.add_assign(&partial.get()[0]);
                    }
                    ood_value_accessor.get_mut()[0] = value;
                    commit_field_els::<BF, E4>(seed_accessor.get_mut(), &[value]);
                    shared_state.get_mut().proof.as_mut().unwrap().ood_samples[0] = value;
                }
            },
            stream,
        )?;
        copy_ood_sample_to_slab(&ood_value_host, proof_slab, proof_layout, 0, stream)?;
        ood_partial_readbacks.push(ood_partials);
        ood_points.push(ood_point_upload);
        ood_values.push(ood_value_host);
        ood_sample_range.end(stream)?;
        tracing_ranges.push(ood_sample_range);

        let pow_and_query_indexes_range =
            Range::new("gkr.whir.base_round.0.pow_and_query_indexes")?;
        pow_and_query_indexes_range.start(stream)?;
        let mut nonce_host = unsafe { context.alloc_host_uninit::<u64>() };
        let query_domain_log2 =
            trace_len_log2 + original_lde_factor.trailing_zeros() as usize - num_folding_steps;
        let query_domain_size = 1u64 << query_domain_log2;
        let query_domain_generator = domain_generator_for_size::<BF>(query_domain_size);
        let mut query_indexes_host = unsafe { context.alloc_host_uninit_slice(num_queries) };
        let nonce_accessor = nonce_host.get_mut_accessor();
        let mut query_index_callbacks_for_round = Callbacks::new();
        #[cfg(test)]
        query_index_callbacks_for_round.schedule(
            {
                let shared_state = shared_state_handle;
                move || unsafe {
                    shared_state.get_mut().pre_pow_seeds[pow_round_idx] = *seed_accessor.get();
                }
            },
            stream,
        )?;
        let pow_keepalives = schedule_pow_verify_and_query_indexes(
            &mut seed_host,
            &mut nonce_host,
            &mut query_indexes_host,
            num_queries,
            pow_bits,
            query_domain_log2,
            context,
        )?;
        copy_pow_nonce_to_slab(
            &pow_keepalives,
            proof_slab,
            proof_layout,
            pow_round_idx,
            stream,
        )?;
        let h_seed_mirror_accessor = pow_keepalives.h_seed_mirror.get_accessor();
        pow_keepalives_keepalive.push(pow_keepalives);
        query_index_callbacks_for_round.schedule(
            {
                let shared_state = shared_state_handle;
                move || unsafe {
                    // Fused post-PoW host bookkeeping: advance the host seed
                    // from the device mirror, then publish the nonce.
                    let src = h_seed_mirror_accessor.get();
                    seed_accessor.get_mut().0.copy_from_slice(src);
                    shared_state.get_mut().proof.as_mut().unwrap().pow_nonces[pow_round_idx] =
                        *nonce_accessor.get();
                }
            },
            stream,
        )?;
        pow_and_query_indexes_range.end(stream)?;
        tracing_ranges.push(pow_and_query_indexes_range);

        let delinearization_eq_range = Range::new("gkr.whir.base_round.0.delinearization_eq")?;
        delinearization_eq_range.start(stream)?;
        // Upload running powers [x, x^2, ..., x^(num_queries + 1)]. CPU weights the OOD
        // contribution by x and the i-th query contribution by x^(i + 2) when accumulating
        // `contributions_to_eq_poly` (see prover/src/gkr/whir/mod.rs, `current_delinearization_challenge`
        // loop). The kernel reads a single scalar per call, so each call site selects the
        // matching power by sub-slicing the device buffer.
        let (delinearization_upload, _delinearization_host, delinearization_device) =
            schedule_callback_populated_upload(
                context,
                num_queries + 1,
                move |dst: &mut [E4]| unsafe {
                    let base = draw_random_field_els::<BF, E4>(seed_accessor.get_mut(), 1)[0];
                    let mut power = base;
                    for dst_el in dst.iter_mut() {
                        *dst_el = power;
                        power.mul_assign(&base);
                    }
                },
            )?;
        let ood_point_accessor = ood_point_host.get_accessor();
        let (eq_upload, _eq_host) = schedule_accumulate_eq_sample_in_place_device(
            &mut state,
            move |dst| unsafe {
                let mut value = ood_point_accessor.get()[0];
                for dst_el in dst.iter_mut() {
                    *dst_el = value;
                    value.square();
                }
            },
            &delinearization_device[0..1],
            context,
        )?;
        ood_points.push(eq_upload);
        delinearization_eq_range.end(stream)?;
        tracing_ranges.push(delinearization_eq_range);

        let queries_range = Range::new("gkr.whir.base_round.0.queries")?;
        queries_range.start(stream)?;
        let mut round_base_queries = [Vec::new(), Vec::new(), Vec::new()];
        for query_idx in 0..num_queries {
            let mut memory_query_index_host = unsafe { context.alloc_host_uninit_slice(1) };
            let mut witness_query_index_host = unsafe { context.alloc_host_uninit_slice(1) };
            let mut setup_query_index_host = unsafe { context.alloc_host_uninit_slice(1) };
            let query_indexes_accessor = query_indexes_host.get_accessor();
            let mut copy_callbacks = Callbacks::new();
            for single_accessor in [
                memory_query_index_host.get_mut_accessor(),
                witness_query_index_host.get_mut_accessor(),
                setup_query_index_host.get_mut_accessor(),
            ] {
                let query_indexes_accessor = query_indexes_accessor;
                copy_callbacks.schedule(
                    move || unsafe {
                        single_accessor.get_mut()[0] = query_indexes_accessor.get()[query_idx];
                    },
                    stream,
                )?;
            }

            let memory_query = schedule_unknown_coset_base_field_query(
                memory_trace_holder,
                memory_query_index_host,
                context,
            )?;
            let witness_query = schedule_unknown_coset_base_field_query(
                witness_trace_holder,
                witness_query_index_host,
                context,
            )?;
            let setup_query = schedule_unknown_coset_base_field_query(
                setup_trace_holder,
                setup_query_index_host,
                context,
            )?;

            let memory_query_index_accessor = memory_query.query_index.get_accessor();
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
            let witness_query_index_accessor = witness_query.query_index.get_accessor();
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
            let setup_query_index_accessor = setup_query.query_index.get_accessor();
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
                    move || unsafe {
                        let proof_state = shared_state.get_mut();
                        let proof = proof_state.proof.as_mut().unwrap();
                        let memory_index = memory_query_index_accessor.get()[0] as usize;
                        fill_unknown_coset_base_field_query_from_accessors(
                            &mut proof.memory_commitment.queries[query_idx],
                            memory_index,
                            memory_coset_tree_size,
                            memory_log_lde_factor,
                            memory_values_per_leaf,
                            memory_columns_count,
                            &memory_leaf_accessors,
                            &memory_path_accessors,
                        );
                        let witness_index = witness_query_index_accessor.get()[0] as usize;
                        fill_unknown_coset_base_field_query_from_accessors(
                            &mut proof.witness_commitment.queries[query_idx],
                            witness_index,
                            witness_coset_tree_size,
                            witness_log_lde_factor,
                            witness_values_per_leaf,
                            witness_columns_count,
                            &witness_leaf_accessors,
                            &witness_path_accessors,
                        );
                        let setup_index = setup_query_index_accessor.get()[0] as usize;
                        fill_unknown_coset_base_field_query_from_accessors(
                            &mut proof.setup_commitment.queries[query_idx],
                            setup_index,
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
        base_queries.push(round_base_queries.map(|queries| {
            queries
                .into_iter()
                .map(ScheduledUnknownCosetBaseFieldQuery::into_keepalive)
                .collect()
        }));
        query_index_callbacks.push(query_index_callbacks_for_round);
        query_indexes.push(query_indexes_host);
        delinearization_challenges.push(delinearization_upload);
        pow_nonces.push(nonce_host);
        round_range.end(stream)?;
        tracing_ranges.push(round_range);
    }

    let num_internal_whir_steps = num_whir_steps.saturating_sub(1);
    for internal_round_idx in 0..num_internal_whir_steps {
        let round_name = format!("gkr.whir.internal_round.{}", internal_round_idx);
        let round_range = Range::new(&*round_name)?;
        round_range.start(stream)?;
        let num_folding_steps = whir_steps_schedule.next().unwrap();
        let num_queries = whir_queries_schedule.next().unwrap();
        let (pow_round_idx, pow_bits) = whir_pow_schedule.next().unwrap();
        schedule_fold_round(num_folding_steps, &mut state)?;

        let lde_factor = whir_steps_lde_factors.next().unwrap();
        let next_folding_steps = *whir_steps_schedule.peek().unwrap();
        let commit_name = format!("{round_name}.commit_next_oracle");
        let commit_next_oracle_range = Range::new(&*commit_name)?;
        commit_next_oracle_range.start(stream)?;
        let next_oracle = GpuWhirExtensionOracle::schedule_from_device_monomial_coeffs(
            &state.sumchecked_poly_monomial_form,
            state.current_len,
            lde_factor,
            1 << next_folding_steps,
            tree_cap_size,
            context,
        )?;
        copy_intermediate_cap_to_slab(
            next_oracle.unified_device_cap(),
            proof_slab,
            proof_layout,
            internal_round_idx + 1,
            stream,
        )?;
        let next_oracle_cap_host_for_proof =
            schedule_unified_cap_d2h(next_oracle.unified_device_cap(), context, stream)?;
        let next_oracle_cap_host_accessor = next_oracle_cap_host_for_proof.get_accessor();
        intermediate_oracle_cap_hosts.push(next_oracle_cap_host_for_proof);
        final_callbacks.schedule(
            {
                let shared_state = shared_state_handle;
                move || unsafe {
                    let proof_state = shared_state.get_mut();
                    let commitment = &mut proof_state
                        .proof
                        .as_mut()
                        .unwrap()
                        .intermediate_whir_oracles[internal_round_idx + 1]
                        .commitment;
                    commitment
                        .cap
                        .cap
                        .copy_from_slice(next_oracle_cap_host_accessor.get());
                    add_whir_commitment_to_transcript(seed_accessor.get_mut(), commitment);
                }
            },
            stream,
        )?;
        commit_next_oracle_range.end(stream)?;
        tracing_ranges.push(commit_next_oracle_range);
        let mut oracle_to_query = rs_oracle.replace(next_oracle).unwrap();

        let (ood_point_upload, ood_point_host, ood_point_device) =
            schedule_callback_populated_upload(context, 1, move |dst: &mut [E4]| unsafe {
                dst[0] = draw_random_field_els::<BF, E4>(seed_accessor.get_mut(), 1)[0];
            })?;
        let ood_partials = schedule_monomial_eval_device(&mut state, &ood_point_device, context)?;
        let mut ood_value_host = unsafe { context.alloc_host_uninit_slice(1) };
        let ood_value_accessor = ood_value_host.get_mut_accessor();
        final_callbacks.schedule(
            {
                let shared_state = shared_state_handle;
                let partial_accessors = ood_partials
                    .iter()
                    .map(HostAllocation::get_accessor)
                    .collect::<Vec<_>>();
                move || unsafe {
                    let mut value = E4::ZERO;
                    for partial in partial_accessors.iter() {
                        value.add_assign(&partial.get()[0]);
                    }
                    ood_value_accessor.get_mut()[0] = value;
                    commit_field_els::<BF, E4>(seed_accessor.get_mut(), &[value]);
                    shared_state.get_mut().proof.as_mut().unwrap().ood_samples
                        [internal_round_idx + 1] = value;
                }
            },
            stream,
        )?;
        copy_ood_sample_to_slab(
            &ood_value_host,
            proof_slab,
            proof_layout,
            internal_round_idx + 1,
            stream,
        )?;
        ood_partial_readbacks.push(ood_partials);
        ood_points.push(ood_point_upload);
        ood_values.push(ood_value_host);

        let pow_and_query_indexes_name = format!("{round_name}.pow_and_query_indexes");
        let pow_and_query_indexes_range = Range::new(&*pow_and_query_indexes_name)?;
        pow_and_query_indexes_range.start(stream)?;
        let mut nonce_host = unsafe { context.alloc_host_uninit::<u64>() };
        let query_domain_log2 = state.current_len.trailing_zeros() as usize
            + oracle_to_query.lde_factor().trailing_zeros() as usize;
        let query_domain_size = 1u64 << query_domain_log2;
        let query_domain_generator = domain_generator_for_size::<BF>(query_domain_size);
        let mut query_indexes_host = unsafe { context.alloc_host_uninit_slice(num_queries) };
        let nonce_accessor = nonce_host.get_mut_accessor();
        let mut query_index_callbacks_for_round = Callbacks::new();
        #[cfg(test)]
        query_index_callbacks_for_round.schedule(
            {
                let shared_state = shared_state_handle;
                move || unsafe {
                    shared_state.get_mut().pre_pow_seeds[pow_round_idx] = *seed_accessor.get();
                }
            },
            stream,
        )?;
        let pow_keepalives = schedule_pow_verify_and_query_indexes(
            &mut seed_host,
            &mut nonce_host,
            &mut query_indexes_host,
            num_queries,
            pow_bits,
            query_domain_log2,
            context,
        )?;
        copy_pow_nonce_to_slab(
            &pow_keepalives,
            proof_slab,
            proof_layout,
            pow_round_idx,
            stream,
        )?;
        let h_seed_mirror_accessor = pow_keepalives.h_seed_mirror.get_accessor();
        pow_keepalives_keepalive.push(pow_keepalives);
        query_index_callbacks_for_round.schedule(
            {
                let shared_state = shared_state_handle;
                move || unsafe {
                    // Fused post-PoW host bookkeeping: advance the host seed
                    // from the device mirror, then publish the nonce.
                    let src = h_seed_mirror_accessor.get();
                    seed_accessor.get_mut().0.copy_from_slice(src);
                    shared_state.get_mut().proof.as_mut().unwrap().pow_nonces[pow_round_idx] =
                        *nonce_accessor.get();
                }
            },
            stream,
        )?;
        pow_and_query_indexes_range.end(stream)?;
        tracing_ranges.push(pow_and_query_indexes_range);

        // Upload running powers [x, x^2, ..., x^(num_queries + 1)] for this recursive WHIR
        // round; see base-round comment above for the weighting that CPU applies to OOD and
        // per-query contributions.
        let (delinearization_upload, _delinearization_host, delinearization_device) =
            schedule_callback_populated_upload(
                context,
                num_queries + 1,
                move |dst: &mut [E4]| unsafe {
                    let base = draw_random_field_els::<BF, E4>(seed_accessor.get_mut(), 1)[0];
                    let mut power = base;
                    for dst_el in dst.iter_mut() {
                        *dst_el = power;
                        power.mul_assign(&base);
                    }
                },
            )?;
        let ood_point_accessor = ood_point_host.get_accessor();
        let (eq_upload, _eq_host) = schedule_accumulate_eq_sample_in_place_device(
            &mut state,
            move |dst| unsafe {
                let mut value = ood_point_accessor.get()[0];
                for dst_el in dst.iter_mut() {
                    *dst_el = value;
                    value.square();
                }
            },
            &delinearization_device[0..1],
            context,
        )?;
        ood_points.push(eq_upload);

        let queries_name = format!("{round_name}.queries");
        let queries_range = Range::new(&*queries_name)?;
        queries_range.start(stream)?;
        let mut round_recursive_queries = Vec::new();
        for query_idx in 0..num_queries {
            let mut single_query_index = unsafe { context.alloc_host_uninit_slice(1) };
            let single_query_index_accessor = single_query_index.get_mut_accessor();
            let query_indexes_accessor = query_indexes_host.get_accessor();
            let mut copy_callbacks = Callbacks::new();
            copy_callbacks.schedule(
                move || unsafe {
                    single_query_index_accessor.get_mut()[0] =
                        query_indexes_accessor.get()[query_idx];
                },
                stream,
            )?;
            let query = oracle_to_query
                .schedule_query_for_folded_index_from_host(single_query_index, context)?;
            let query_leafs_accessor = query.leafs_accessor();
            let query_paths_accessor = query.merkle_paths_accessor();
            let query_values_per_leaf = query.values_per_leaf();
            let query_log_lde_factor = oracle_to_query.lde_factor().trailing_zeros();
            let query_coset_tree_size = oracle_to_query.packed_leaf_count();
            copy_intermediate_query_to_slab(
                query_indexes_host.get_accessor(),
                query_leafs_accessor,
                query_paths_accessor,
                proof_slab,
                proof_layout,
                internal_round_idx,
                query_idx,
                stream,
            )?;
            let query_indexes_accessor = query_indexes_host.get_accessor();
            let (eq_upload, _eq_host) = schedule_accumulate_eq_sample_in_place_device(
                &mut state,
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
        pow_nonces.push(nonce_host);
        round_range.end(stream)?;
        tracing_ranges.push(round_range);
    }

    let final_monomials_keepalive: Option<HostAllocation<[E4]>>;
    {
        let round_range = Range::new("gkr.whir.final_round")?;
        round_range.start(stream)?;
        let num_folding_steps = whir_steps_schedule.next().unwrap();
        let num_queries = whir_queries_schedule.next().unwrap();
        let (pow_round_idx, pow_bits) = whir_pow_schedule.next().unwrap();
        schedule_fold_round(num_folding_steps, &mut state)?;

        // Mirror CPU `prover/src/gkr/whir/mod.rs` lines 1297 and 1391: after the final fold
        // and before drawing the final PoW/query bits, CPU commits the remaining
        // monomial-form coefficients into the transcript seed, and later stores them on the
        // proof as `final_monomials`. Read them back asynchronously and do both in a single
        // stream-ordered callback so the seed update is sequenced before
        // `schedule_pow_verify_and_query_indexes` below.
        let mut final_monomials_host =
            unsafe { context.alloc_host_uninit_slice::<E4>(state.current_len) };
        let mut final_monomials_device =
            context.alloc::<E4>(state.current_len, AllocationPlacement::BestFit)?;
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
        let mut nonce_host = unsafe { context.alloc_host_uninit::<u64>() };
        let mut query_indexes_host = unsafe { context.alloc_host_uninit_slice(num_queries) };
        let nonce_accessor = nonce_host.get_mut_accessor();
        let mut query_index_callbacks_for_round = Callbacks::new();
        #[cfg(test)]
        query_index_callbacks_for_round.schedule(
            {
                let shared_state = shared_state_handle;
                move || unsafe {
                    shared_state.get_mut().pre_pow_seeds[pow_round_idx] = *seed_accessor.get();
                }
            },
            stream,
        )?;
        let pow_keepalives = schedule_pow_verify_and_query_indexes(
            &mut seed_host,
            &mut nonce_host,
            &mut query_indexes_host,
            num_queries,
            pow_bits,
            query_domain_log2,
            context,
        )?;
        copy_pow_nonce_to_slab(
            &pow_keepalives,
            proof_slab,
            proof_layout,
            pow_round_idx,
            stream,
        )?;
        let h_seed_mirror_accessor = pow_keepalives.h_seed_mirror.get_accessor();
        pow_keepalives_keepalive.push(pow_keepalives);
        query_index_callbacks_for_round.schedule(
            {
                let shared_state = shared_state_handle;
                move || unsafe {
                    // Fused post-PoW host bookkeeping: advance the host seed
                    // from the device mirror, then publish the nonce.
                    let src = h_seed_mirror_accessor.get();
                    seed_accessor.get_mut().0.copy_from_slice(src);
                    shared_state.get_mut().proof.as_mut().unwrap().pow_nonces[pow_round_idx] =
                        *nonce_accessor.get();
                }
            },
            stream,
        )?;
        pow_and_query_indexes_range.end(stream)?;
        tracing_ranges.push(pow_and_query_indexes_range);
        let queries_range = Range::new("gkr.whir.final_round.queries")?;
        queries_range.start(stream)?;
        let mut round_recursive_queries = Vec::new();
        let final_oracle_index = num_whir_steps.saturating_sub(1);
        for query_idx in 0..num_queries {
            let mut single_query_index = unsafe { context.alloc_host_uninit_slice(1) };
            let single_query_index_accessor = single_query_index.get_mut_accessor();
            let query_indexes_accessor = query_indexes_host.get_accessor();
            let mut copy_callbacks = Callbacks::new();
            copy_callbacks.schedule(
                move || unsafe {
                    single_query_index_accessor.get_mut()[0] =
                        query_indexes_accessor.get()[query_idx];
                },
                stream,
            )?;
            let query = oracle_to_query
                .schedule_query_for_folded_index_from_host(single_query_index, context)?;
            let query_leafs_accessor = query.leafs_accessor();
            let query_paths_accessor = query.merkle_paths_accessor();
            let query_values_per_leaf = query.values_per_leaf();
            let query_log_lde_factor = oracle_to_query.lde_factor().trailing_zeros();
            let query_coset_tree_size = oracle_to_query.packed_leaf_count();
            copy_intermediate_query_to_slab(
                query_indexes_host.get_accessor(),
                query_leafs_accessor,
                query_paths_accessor,
                proof_slab,
                proof_layout,
                final_oracle_index,
                query_idx,
                stream,
            )?;
            final_callbacks.extend(copy_callbacks);
            final_callbacks.schedule(
                {
                    let shared_state = shared_state_handle;
                    let query_indexes_accessor = query_indexes_host.get_accessor();
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
        pow_nonces.push(nonce_host);
        round_range.end(stream)?;
        tracing_ranges.push(round_range);
    }

    schedule_range.end(stream)?;
    tracing_ranges.push(schedule_range);

    Ok(GpuWhirFoldScheduledExecution {
        _tracing_ranges: tracing_ranges,
        _start_callbacks: start_callbacks,
        _folding_challenges: folding_challenges,
        _fold_round_group_device_seeds: fold_round_group_device_seeds,
        _fold_round_group_device_challenges: fold_round_group_device_challenges,
        _fold_round_group_device_coeffs: fold_round_group_device_coeffs,
        _fold_round_group_host_seed_stagings: fold_round_group_host_seed_stagings,
        _fold_round_group_host_seed_mirrors: fold_round_group_host_seed_mirrors,
        _fold_round_group_host_coeffs: fold_round_group_host_coeffs,
        _fold_round_group_upload_callbacks: fold_round_group_upload_callbacks,
        _pow_keepalives: pow_keepalives_keepalive,
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
