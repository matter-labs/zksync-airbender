use super::*;

use crate::ops::bit_reverse::bit_reverse_in_place;
use crate::ops::blake2s::transcript_commit;

mod fold_round;
mod round_phases;

use fold_round::schedule_fold_round;
use round_phases::{
    schedule_commit_next_oracle_phase, schedule_delinearization_running_powers_phase,
    schedule_ood_sample_phase, schedule_pow_and_query_indexes_phase,
};

pub(crate) fn schedule_gpu_whir_fold_with_sources(
    memory_trace_holder: &mut TraceHolder<BF>,
    witness_trace_holder: &mut TraceHolder<BF>,
    setup_trace_holder: &mut TraceHolder<BF>,
    base_layer_point_device: &DeviceSlice<E4>,
    // Rolling device-resident transcript seed for the WHIR phase. Owned by the
    // caller — typically the backward scheduler's `final_device_seed` buffer
    // borrowed for the duration of this call. Advanced in place by each
    // device transcript op (`transcript_commit`, `transcript_squeeze`,
    // `whir_fold_round_update`, `blake2s_pow`).
    final_device_seed: &mut DeviceSlice<u32>,
    // Pre-drawn WHIR base batching challenge, materialized on device by the
    // caller via `transcript_squeeze_e4(final_device_seed, ...)` before this
    // function is invoked.
    batching_challenge_device: &DeviceSlice<E4>,
    original_lde_factor: usize,
    whir_steps_schedule: Vec<usize>,
    whir_queries_schedule: Vec<usize>,
    whir_steps_lde_factors: Vec<usize>,
    whir_pow_schedule: Vec<u32>,
    tree_cap_size: usize,
    trace_len_log2: usize,
    use_hypercube_evals_for_batching: bool,
    // Phase 3: slab + layout thread through so WHIR sub-phases can route
    // proof fields (`pow_nonces` today; caps, evals, queries, ood_samples,
    // sumcheck_polys, final_monomials in follow-up commits) into slab
    // offsets via `ProofLayout` accessors.
    proof_slab: &DeviceAllocation<E4>,
    proof_layout: &ProofLayout,
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
    let num_whir_steps = whir_steps_lde_factors.len();
    // Phase 8: base-layer unified caps (witness/memory/setup) are written
    // directly into the slab earlier — witness by stage 1's commit kernel
    // via `commit_all_into(slab.whir.witness.cap, ...)`, memory and setup
    // by the H2Ds scheduled in `prepare_stage1_and_forward_setup` that
    // land in `slab.whir.memory.cap` / `slab.whir.setup.cap`. No D2Ds
    // here.

    let base_layer_point_len = base_layer_point_device.len();

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
        batching_challenge_device,
        use_hypercube_evals_for_batching,
        &mut state,
        context,
    )?;
    initialize_batched_forms_range.end(stream)?;
    tracing_ranges.push(initialize_batched_forms_range);

    launch_build_eq_values_from_point(
        base_layer_point_device.as_ptr(),
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
    let mut rs_oracle: Option<GpuWhirExtensionOracle>;

    // Per-fold-round-group device buffers (challenge + packed coeffs); the
    // rolling device seed is owned by the caller and threaded in directly.
    let mut fold_round_group_keepalives = FoldRoundGroupKeepalives::new();
    // Per-WHIR-round device state for the device-side PoW verify +
    // query-index assembly. Later callbacks consume the nonce.
    let mut pow_round_state: Vec<PowAndQueryIndexesState> = Vec::new();
    let mut recursive_caps_keepalive: Vec<crate::prover::whir::GpuWhirExtensionOracleKeepalive> =
        Vec::new();
    // Per-round device-resident OOD points produced by `schedule_ood_sample_phase`
    // and consumed by `schedule_delinearization_running_powers_phase`. Kept on
    // the orchestrator so the device buffers outlive all kernels reading them.
    let mut ood_point_devices: Vec<DeviceAllocation<E4>> = Vec::new();
    // Per-round device-side ephemerals used by delinearization (delin_base,
    // anchor_powers, per_query_pows). Kept alive for the duration of the
    // WHIR schedule.
    let mut delinearization_ephemerals: Vec<DeviceAllocation<E4>> = Vec::new();
    let mut query_index_callbacks = Vec::new();
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
            final_device_seed,
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
            final_device_seed,
            stream,
            context,
        )?;
        commit_next_oracle_range.end(stream)?;
        tracing_ranges.push(commit_next_oracle_range);
        rs_oracle = Some(oracle);

        let ood_sample_range = Range::new("gkr.whir.base_round.0.ood_sample")?;
        ood_sample_range.start(stream)?;
        schedule_ood_sample_phase(
            &mut state,
            0,
            proof_slab,
            proof_layout,
            final_device_seed,
            &mut ood_point_devices,
            stream,
            context,
        )?;
        let ood_point_device_idx = ood_point_devices.len() - 1;
        ood_sample_range.end(stream)?;
        tracing_ranges.push(ood_sample_range);

        let pow_and_query_indexes_range =
            Range::new("gkr.whir.base_round.0.pow_and_query_indexes")?;
        pow_and_query_indexes_range.start(stream)?;
        let query_domain_log2 =
            trace_len_log2 + original_lde_factor.trailing_zeros() as usize - num_folding_steps;
        let query_domain_size = 1u64 << query_domain_log2;
        let query_domain_generator = domain_generator_for_size::<BF>(query_domain_size);
        let query_index_callbacks_for_round = schedule_pow_and_query_indexes_phase(
            final_device_seed,
            num_queries,
            pow_bits,
            pow_round_idx,
            query_domain_log2,
            proof_slab,
            proof_layout,
            &mut pow_round_state,
            stream,
            context,
        )?;
        pow_and_query_indexes_range.end(stream)?;
        tracing_ranges.push(pow_and_query_indexes_range);

        let delinearization_eq_range = Range::new("gkr.whir.base_round.0.delinearization_eq")?;
        delinearization_eq_range.start(stream)?;
        let delinearization_device = schedule_delinearization_running_powers_phase(
            &mut state,
            num_queries,
            &ood_point_devices[ood_point_device_idx][..],
            final_device_seed,
            &mut delinearization_ephemerals,
            context,
        )?;
        delinearization_eq_range.end(stream)?;
        tracing_ranges.push(delinearization_eq_range);

        let queries_range = Range::new("gkr.whir.base_round.0.queries")?;
        queries_range.start(stream)?;
        // Phase 3 (WHIR-on-device): compute per-query tree-indices on device
        // (= bitreverse(coset) * coset_tree_size + internal), D2D-copy them
        // into each base oracle's slab `query_indices` range, and let each
        // coset's gather kernel write directly into the slab's `query_leaves`
        // / `query_paths` ranges. Replaces the prior per-query / per-coset host
        // gather + final-callback host-fill loop.
        let device_query_indexes_for_base: &era_cudart::slice::DeviceSlice<u32> = &pow_round_state
            .last()
            .expect("pow_round_state pushed above for base round")
            .d_indexes[..];
        let log_lde_factor_base = memory_trace_holder.log_lde_factor;
        let lde_factor_base = 1usize << log_lde_factor_base;
        let coset_tree_size_log2 =
            (memory_trace_holder.log_domain_size - memory_trace_holder.log_rows_per_leaf) as u32;
        // The three base oracles (setup/memory/witness) sample the same
        // tree-space indices, so the slab stores a single shared range.
        // SAFETY: `whir_base_query_indices_device_mut` returns the live
        // shared `base_query_indices` slab range; the `&mut DeviceSlice<u32>`
        // view below is the sole writer for this region.
        let (base_idx_ptr, base_idx_len) = unsafe {
            proof_layout.whir_base_query_indices_device_mut(proof_slab.as_ptr() as *mut u8)
        };
        assert_eq!(base_idx_len, num_queries);
        let base_indices_dst = unsafe {
            era_cudart::slice::DeviceSlice::from_raw_parts_mut(base_idx_ptr, base_idx_len)
        };
        crate::ops::blake2s::query_index_to_tree_index(
            device_query_indexes_for_base,
            base_indices_dst,
            log_lde_factor_base,
            coset_tree_size_log2,
            stream,
        )?;
        // Single-launch multi-oracle base-round gather (Step 3 consolidation).
        // Memory / Witness / Setup share `log_lde_factor`, `log_domain_size`,
        // and `log_rows_per_leaf` (asserted above) and all run in
        // `TreesCacheMode::CachePartial`. We descriptor-pack the three
        // oracles and launch the consolidated leaf and partial-path kernels
        // once each, replacing the legacy 3 × lde_factor per-coset filter
        // pattern. Empty-`columns_count` oracles are skipped in-kernel.
        memory_trace_holder.ensure_cosets_materialized(context)?;
        witness_trace_holder.ensure_cosets_materialized(context)?;
        setup_trace_holder.ensure_cosets_materialized(context)?;
        let base_log_domain_size = memory_trace_holder.log_domain_size;
        let base_log_rows_per_leaf = memory_trace_holder.log_rows_per_leaf;
        debug_assert_eq!(witness_trace_holder.log_domain_size, base_log_domain_size);
        debug_assert_eq!(setup_trace_holder.log_domain_size, base_log_domain_size);
        debug_assert_eq!(
            witness_trace_holder.log_rows_per_leaf,
            base_log_rows_per_leaf
        );
        debug_assert_eq!(
            setup_trace_holder.log_rows_per_leaf,
            base_log_rows_per_leaf
        );
        let base_log_total_leaves_count = base_log_domain_size - base_log_rows_per_leaf;
        let base_oracle_descs = |holders: [&TraceHolder<BF>; 3],
                                 slab_ptrs: [u64; 6]|
         -> (
            [crate::ops::blake2s::OracleGatherDesc; 3],
            [crate::ops::blake2s::OraclePartialPathDesc; 3],
            u32,
        ) {
            let mut leaves = [crate::ops::blake2s::OracleGatherDesc::default(); 3];
            let mut paths = [crate::ops::blake2s::OraclePartialPathDesc::default(); 3];
            let mut common_stride: Option<u32> = None;
            for (i, holder) in holders.iter().enumerate() {
                if holder.columns_count == 0 {
                    continue;
                }
                let cosets = holder.get_consolidated_cosets();
                let tree = holder
                    .get_consolidated_tree()
                    .expect("base oracles run with TreesCacheMode::CachePartial");
                let stride = (tree.len() / (1usize << holder.log_lde_factor)) as u32;
                match common_stride {
                    None => common_stride = Some(stride),
                    Some(s) => debug_assert_eq!(s, stride),
                }
                leaves[i] = crate::ops::blake2s::OracleGatherDesc {
                    cosets_ptr: cosets.as_ptr() as u64,
                    columns_count: holder.columns_count as u32,
                    _pad: 0,
                    slab_dst_ptr: slab_ptrs[i * 2],
                };
                paths[i] = crate::ops::blake2s::OraclePartialPathDesc {
                    cosets_ptr: cosets.as_ptr() as u64,
                    partial_tree_ptr: tree.as_ptr() as u64,
                    columns_count: holder.columns_count as u32,
                    _pad: 0,
                    slab_dst_ptr: slab_ptrs[i * 2 + 1],
                };
            }
            (leaves, paths, common_stride.unwrap_or(0))
        };
        // SAFETY: layout returns disjoint slab regions for each oracle's
        // leaves and paths; the six destinations are pairwise non-aliasing.
        let memory_leaves_ptr = unsafe {
            proof_layout.whir_base_query_leaves_device_mut(
                proof_slab.as_ptr() as *mut u8,
                crate::prover::proof::layout::WhirBaseLayerKind::Memory,
            )
        }
        .0 as u64;
        let memory_paths_ptr = unsafe {
            proof_layout.whir_base_query_paths_device_mut(
                proof_slab.as_ptr() as *mut u8,
                crate::prover::proof::layout::WhirBaseLayerKind::Memory,
            )
        }
        .0 as u64;
        let witness_leaves_ptr = unsafe {
            proof_layout.whir_base_query_leaves_device_mut(
                proof_slab.as_ptr() as *mut u8,
                crate::prover::proof::layout::WhirBaseLayerKind::Witness,
            )
        }
        .0 as u64;
        let witness_paths_ptr = unsafe {
            proof_layout.whir_base_query_paths_device_mut(
                proof_slab.as_ptr() as *mut u8,
                crate::prover::proof::layout::WhirBaseLayerKind::Witness,
            )
        }
        .0 as u64;
        let setup_leaves_ptr = unsafe {
            proof_layout.whir_base_query_leaves_device_mut(
                proof_slab.as_ptr() as *mut u8,
                crate::prover::proof::layout::WhirBaseLayerKind::Setup,
            )
        }
        .0 as u64;
        let setup_paths_ptr = unsafe {
            proof_layout.whir_base_query_paths_device_mut(
                proof_slab.as_ptr() as *mut u8,
                crate::prover::proof::layout::WhirBaseLayerKind::Setup,
            )
        }
        .0 as u64;
        let slab_ptrs: [u64; 6] = [
            memory_leaves_ptr,
            memory_paths_ptr,
            witness_leaves_ptr,
            witness_paths_ptr,
            setup_leaves_ptr,
            setup_paths_ptr,
        ];
        let (leaves_descs, paths_descs, stride_per_coset_in_digests) = base_oracle_descs(
            [
                &*memory_trace_holder,
                &*witness_trace_holder,
                &*setup_trace_holder,
            ],
            slab_ptrs,
        );
        crate::ops::blake2s::gather_leaves_for_queries(
            &leaves_descs,
            3,
            log_lde_factor_base,
            base_log_domain_size,
            base_log_rows_per_leaf,
            device_query_indexes_for_base,
            stream,
        )?;
        // Mirrors `TraceHolder::query_merkle_path_layout`'s `layers_count`
        // formula. All three base oracles share the inputs (asserted above).
        let base_layers_count = memory_trace_holder.log_domain_size
            - memory_trace_holder.log_rows_per_leaf
            - (memory_trace_holder.log_tree_cap_size - memory_trace_holder.log_lde_factor);
        crate::ops::blake2s::gather_merkle_paths_partial_for_queries(
            &paths_descs,
            3,
            log_lde_factor_base,
            base_log_rows_per_leaf,
            base_log_total_leaves_count,
            stride_per_coset_in_digests,
            base_layers_count,
            device_query_indexes_for_base,
            stream,
        )?;
        // Phase C (WHIR-on-device): materialize all per-query squaring
        // sequences in a single kernel launch reading device-resident query
        // indices, then loop over the queries to dispatch the inner
        // eq-sample accumulation against device-resident point_pows. No
        // host callbacks, no D2H of query indices, no per-query H2D of
        // point_pows.
        let count_per_query = state.current_len.trailing_zeros() as usize;
        let mut per_query_pows: DeviceAllocation<E4> =
            context.alloc(count_per_query * num_queries, AllocationPlacement::BestFit)?;
        crate::ops::squaring::query_squaring_sequences_bf_to_e4(
            query_domain_generator,
            device_query_indexes_for_base,
            &mut per_query_pows[..],
            count_per_query as u32,
            stream,
        )?;
        let (eq_high_scratch, eq_low_scratch) = schedule_accumulate_eq_samples_batched(
            &mut state,
            &per_query_pows[..],
            &delinearization_device[1..1 + num_queries],
            num_queries,
            count_per_query,
            context,
        )?;
        queries_range.end(stream)?;
        tracing_ranges.push(queries_range);
        // Retain the per-round callbacks so they outlive every scheduled
        // stream op holding into them.
        query_index_callbacks.push(query_index_callbacks_for_round);
        delinearization_ephemerals.push(delinearization_device);
        delinearization_ephemerals.push(per_query_pows);
        delinearization_ephemerals.push(eq_high_scratch);
        delinearization_ephemerals.push(eq_low_scratch);
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
            final_device_seed,
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
            final_device_seed,
            stream,
            context,
        )?;
        commit_next_oracle_range.end(stream)?;
        tracing_ranges.push(commit_next_oracle_range);
        let mut oracle_to_query = rs_oracle.replace(next_oracle).unwrap();

        schedule_ood_sample_phase(
            &mut state,
            internal_round_idx + 1,
            proof_slab,
            proof_layout,
            final_device_seed,
            &mut ood_point_devices,
            stream,
            context,
        )?;
        let ood_point_device_idx = ood_point_devices.len() - 1;

        let pow_and_query_indexes_name = format!("{round_name}.pow_and_query_indexes");
        let pow_and_query_indexes_range = Range::new(&*pow_and_query_indexes_name)?;
        pow_and_query_indexes_range.start(stream)?;
        let query_domain_log2 = state.current_len.trailing_zeros() as usize
            + oracle_to_query.lde_factor().trailing_zeros() as usize;
        let query_domain_size = 1u64 << query_domain_log2;
        let query_domain_generator = domain_generator_for_size::<BF>(query_domain_size);
        let query_index_callbacks_for_round = schedule_pow_and_query_indexes_phase(
            final_device_seed,
            num_queries,
            pow_bits,
            pow_round_idx,
            query_domain_log2,
            proof_slab,
            proof_layout,
            &mut pow_round_state,
            stream,
            context,
        )?;
        pow_and_query_indexes_range.end(stream)?;
        tracing_ranges.push(pow_and_query_indexes_range);

        let delinearization_device = schedule_delinearization_running_powers_phase(
            &mut state,
            num_queries,
            &ood_point_devices[ood_point_device_idx][..],
            final_device_seed,
            &mut delinearization_ephemerals,
            context,
        )?;

        let queries_name = format!("{round_name}.queries");
        let queries_range = Range::new(&*queries_name)?;
        queries_range.start(stream)?;
        // Phase 4 (WHIR-on-device): batched device-side tree-index transform
        // + slab-direct gather replaces the per-query host-callback round-trip.
        let device_query_indexes_for_round: &era_cudart::slice::DeviceSlice<u32> = &pow_round_state
            .last()
            .expect("pow_round_state pushed above for this round")
            .d_indexes[..];
        {
            // SAFETY: layout returns live, non-overlapping mutable regions for
            // this round's intermediate slab subranges.
            let (idx_ptr, idx_len) = unsafe {
                proof_layout.whir_intermediate_query_indices_device_mut(
                    proof_slab.as_ptr() as *mut u8,
                    internal_round_idx,
                )
            };
            let (leaves_ptr_e4, leaves_total_e4) = unsafe {
                proof_layout.whir_intermediate_query_leaves_device_mut(
                    proof_slab.as_ptr() as *mut u8,
                    internal_round_idx,
                )
            };
            let (paths_ptr, paths_total_u32) = unsafe {
                proof_layout.whir_intermediate_query_paths_device_mut(
                    proof_slab.as_ptr() as *mut u8,
                    internal_round_idx,
                )
            };
            assert_eq!(idx_len, num_queries);
            // SAFETY: idx range is u32-aligned within the live slab.
            let slab_indices_dst =
                unsafe { era_cudart::slice::DeviceSlice::from_raw_parts_mut(idx_ptr, idx_len) };
            // SAFETY: leaves range is 16-byte aligned; viewing as flat BFs is layout-safe.
            let leaves_total_bf = leaves_total_e4 * EXT4_DEGREE;
            let slab_leaves_dst_bf = unsafe {
                era_cudart::slice::DeviceSlice::from_raw_parts_mut(
                    leaves_ptr_e4 as *mut BF,
                    leaves_total_bf,
                )
            };
            // SAFETY: paths range is u32-aligned.
            let slab_paths_dst = unsafe {
                era_cudart::slice::DeviceSlice::from_raw_parts_mut(paths_ptr, paths_total_u32)
            };
            oracle_to_query.schedule_query_for_folded_indexes_to_slab(
                device_query_indexes_for_round,
                slab_indices_dst,
                slab_leaves_dst_bf,
                slab_paths_dst,
                context,
            )?;
        }
        // Phase C (WHIR-on-device): materialize all per-query squaring
        // sequences in a single kernel launch and dispatch per-query
        // accumulation against device-resident point_pows.
        let count_per_query = state.current_len.trailing_zeros() as usize;
        let mut per_query_pows: DeviceAllocation<E4> =
            context.alloc(count_per_query * num_queries, AllocationPlacement::BestFit)?;
        crate::ops::squaring::query_squaring_sequences_bf_to_e4(
            query_domain_generator,
            device_query_indexes_for_round,
            &mut per_query_pows[..],
            count_per_query as u32,
            stream,
        )?;
        let (eq_high_scratch, eq_low_scratch) = schedule_accumulate_eq_samples_batched(
            &mut state,
            &per_query_pows[..],
            &delinearization_device[1..1 + num_queries],
            num_queries,
            count_per_query,
            context,
        )?;
        queries_range.end(stream)?;
        tracing_ranges.push(queries_range);
        recursive_caps_keepalive.push(oracle_to_query.into_host_keepalive());
        query_index_callbacks.push(query_index_callbacks_for_round);
        delinearization_ephemerals.push(delinearization_device);
        delinearization_ephemerals.push(per_query_pows);
        delinearization_ephemerals.push(eq_high_scratch);
        delinearization_ephemerals.push(eq_low_scratch);
        round_range.end(stream)?;
        tracing_ranges.push(round_range);
    }

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
            final_device_seed,
            stream,
            context,
        )?;

        // Mirror CPU `prover/src/gkr/whir/mod.rs` lines 1297 and 1391: after the final fold
        // and before drawing the final PoW/query bits, CPU commits the remaining
        // monomial-form coefficients into the transcript seed, and later stores them on the
        // proof as `final_monomials`. Phase D (WHIR-on-device) keeps this entirely on the
        // device: transpose writes the monomials directly into the slab
        // `whir.final_monomials` range, then `bit_reverse_in_place` runs in
        // place on the same slab range before the transcript commit.
        //
        // Phase 1 (WHIR-on-device) cross-check: confirm that `state.current_len`
        // at the end of the final fold matches the slab-allocated
        // `final_monomials_len` from `build_proof_layout_inputs`. Both should
        // equal `1 << (trace_len_log2 - sum(whir_steps_schedule))`.
        assert_eq!(
            state.current_len,
            1usize << (trace_len_log2 - total_sumcheck_polys),
            "WHIR final-fold current_len must match slab final_monomials_len",
        );
        // Phase D (WHIR-on-device): transpose writes the pre-bitreverse
        // monomials directly into the slab `whir.final_monomials` range, then
        // `bit_reverse_in_place::<E4>` reorders them in place on the same
        // range. The transcript commit hashes the bit-reversed slab range so
        // the device-side seed advances identically to the CPU prover's
        // `commit_field_els`. This removes the temp `final_monomials_device`
        // allocation and the per-proof D2D into the slab.
        {
            let (dst_ptr, dst_len) = unsafe {
                proof_layout.whir_final_monomials_device_mut(proof_slab.as_ptr() as *mut u8)
            };
            assert_eq!(
                state.current_len, dst_len,
                "final_monomials length must match slab final_monomials range",
            );
            // SAFETY: the slab `whir.final_monomials` range is `dst_len` E4
            // elements — equivalently `dst_len * EXT4_DEGREE` BF lanes. The
            // slab pointer is 16-byte aligned (E4 alignment) so it is also
            // 4-byte aligned (BF alignment). The range is disjoint from every
            // other slab subrange and is exclusively written here by the
            // transpose, then by the subsequent in-place bit-reverse, all on
            // `exec_stream`, before the transcript commit reads it.
            let mut slab_bf_view = unsafe {
                era_cudart::slice::DeviceSlice::from_raw_parts_mut(
                    dst_ptr as *mut BF,
                    dst_len * EXT4_DEGREE,
                )
            };
            let mut transpose_dst_matrix = DeviceMatrixMut::new(&mut slab_bf_view, EXT4_DEGREE);
            let monomials_matrix_chunk = DeviceMatrixChunk::new(
                state.sumchecked_poly_monomial_form.slice(),
                state.original_trace_len,
                0,
                state.current_len,
            );
            transpose(&monomials_matrix_chunk, &mut transpose_dst_matrix, stream)?;
            // SAFETY: same slab range viewed as `dst_len` E4 elements. The
            // previous BF view above is dropped before this point, so the slab
            // range is exclusively reborrowed here for the in-place
            // `bit_reverse_in_place::<E4>` reorder.
            let dst =
                unsafe { era_cudart::slice::DeviceSlice::from_raw_parts_mut(dst_ptr, dst_len) };
            // Device-side bit-reverse in place on the slab range using the
            // `BIT_REVERSE(e4, bf, 2)` instantiation of `bit_reverse_in_place`.
            let mut dst_matrix = DeviceMatrixMut::<E4>::new(dst, dst_len);
            bit_reverse_in_place::<E4>(&mut dst_matrix, stream)?;
            // SAFETY: same slab range, viewed as `state.current_len * EXT4_DEGREE`
            // LE u32 words for transcript_commit.
            let slot_as_u32 = unsafe {
                era_cudart::slice::DeviceSlice::from_raw_parts(
                    dst_ptr as *const u32,
                    dst_len * EXT4_DEGREE,
                )
            };
            transcript_commit(final_device_seed, slot_as_u32, stream)?;
        }

        let mut oracle_to_query = rs_oracle.take().unwrap();
        let query_domain_log2 = state.current_len.trailing_zeros() as usize
            + oracle_to_query.lde_factor().trailing_zeros() as usize;
        let pow_and_query_indexes_range = Range::new("gkr.whir.final_round.pow_and_query_indexes")?;
        pow_and_query_indexes_range.start(stream)?;
        let query_index_callbacks_for_round = schedule_pow_and_query_indexes_phase(
            final_device_seed,
            num_queries,
            pow_bits,
            pow_round_idx,
            query_domain_log2,
            proof_slab,
            proof_layout,
            &mut pow_round_state,
            stream,
            context,
        )?;
        pow_and_query_indexes_range.end(stream)?;
        tracing_ranges.push(pow_and_query_indexes_range);
        let queries_range = Range::new("gkr.whir.final_round.queries")?;
        queries_range.start(stream)?;
        let final_oracle_index = num_whir_steps.saturating_sub(1);
        // Phase 4 (WHIR-on-device): batched device-side gather replaces the
        // per-query host-callback round-trip for the final round too.
        let device_query_indexes_for_round: &era_cudart::slice::DeviceSlice<u32> = &pow_round_state
            .last()
            .expect("pow_round_state pushed above for final round")
            .d_indexes[..];
        {
            // SAFETY: layout returns live, non-overlapping mutable regions for
            // this round's intermediate slab subranges.
            let (idx_ptr, idx_len) = unsafe {
                proof_layout.whir_intermediate_query_indices_device_mut(
                    proof_slab.as_ptr() as *mut u8,
                    final_oracle_index,
                )
            };
            let (leaves_ptr_e4, leaves_total_e4) = unsafe {
                proof_layout.whir_intermediate_query_leaves_device_mut(
                    proof_slab.as_ptr() as *mut u8,
                    final_oracle_index,
                )
            };
            let (paths_ptr, paths_total_u32) = unsafe {
                proof_layout.whir_intermediate_query_paths_device_mut(
                    proof_slab.as_ptr() as *mut u8,
                    final_oracle_index,
                )
            };
            assert_eq!(idx_len, num_queries);
            // SAFETY: u32-aligned slab region.
            let slab_indices_dst =
                unsafe { era_cudart::slice::DeviceSlice::from_raw_parts_mut(idx_ptr, idx_len) };
            // SAFETY: leaves range is 16-byte aligned; viewing as flat BFs is layout-safe.
            let leaves_total_bf = leaves_total_e4 * EXT4_DEGREE;
            let slab_leaves_dst_bf = unsafe {
                era_cudart::slice::DeviceSlice::from_raw_parts_mut(
                    leaves_ptr_e4 as *mut BF,
                    leaves_total_bf,
                )
            };
            // SAFETY: u32-aligned paths range.
            let slab_paths_dst = unsafe {
                era_cudart::slice::DeviceSlice::from_raw_parts_mut(paths_ptr, paths_total_u32)
            };
            oracle_to_query.schedule_query_for_folded_indexes_to_slab(
                device_query_indexes_for_round,
                slab_indices_dst,
                slab_leaves_dst_bf,
                slab_paths_dst,
                context,
            )?;
        }
        queries_range.end(stream)?;
        tracing_ranges.push(queries_range);
        recursive_caps_keepalive.push(oracle_to_query.into_host_keepalive());
        query_index_callbacks.push(query_index_callbacks_for_round);
        round_range.end(stream)?;
        tracing_ranges.push(round_range);
    }

    schedule_range.end(stream)?;
    tracing_ranges.push(schedule_range);

    Ok(GpuWhirFoldScheduledExecution {
        _tracing_ranges: tracing_ranges,
        _fold_round_group_keepalives: fold_round_group_keepalives,
        _pow_round_state: pow_round_state,
        _ood_point_devices: ood_point_devices,
        _delinearization_ephemerals: delinearization_ephemerals,
        _query_index_callbacks: query_index_callbacks,
        _recursive_caps_keepalive: recursive_caps_keepalive,
    })
}
