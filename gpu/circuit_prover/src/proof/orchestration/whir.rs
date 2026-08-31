use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;

use crate::upstream::{GKRCircuitArtifact, WhirSchedule};
use gpu_core::primitives::context::{DeviceAllocation, UnsafeAccessor};
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::{BF, E4};
use gpu_gkr::backward::GpuGKRBackwardScheduledExecution;
use gpu_gkr::base_layer_claims::{
    schedule_prepare_base_layer_claims_with_sources, GpuGKRBaseLayerClaimsScheduledExecution,
    ScheduledBaseLayerClaimsState,
};
use gpu_gkr::proof_layout::ProofLayout;
use gpu_gkr::setup::GpuGKRSetupTransfer;
use gpu_gkr::stage1::GpuGKRStage1Output;
use gpu_prover_context::ProverContext;
use gpu_trace::trace::holder::{
    allocate_trees, TraceHolder, TreesHolder, PARTIAL_TREE_REDUCTION_LAYERS,
};
use gpu_whir::fold::{schedule_gpu_whir_fold_with_sources, GpuWhirFoldScheduledExecution};

pub(in crate::proof) struct WhirPhaseResult {
    pub(in crate::proof) transition_ranges: Vec<Range>,
    pub(in crate::proof) base_layer_claims_scheduled: GpuGKRBaseLayerClaimsScheduledExecution,
    pub(in crate::proof) base_layer_claims_shared_state:
        UnsafeAccessor<ScheduledBaseLayerClaimsState>,
    pub(in crate::proof) whir_scheduled: GpuWhirFoldScheduledExecution,
}

fn materialize_pre_whir_trace_inputs<'a>(
    setup_transfer: &mut Option<GpuGKRSetupTransfer<'a>>,
    synthetic_setup_trace_holder: &mut Option<TraceHolder<BF>>,
    stage1_output: &mut GpuGKRStage1Output,
    context: &ProverContext,
) -> CudaResult<[Range; 2]> {
    let stream = context.get_exec_stream();

    // Materialize deferred cosets for setup and memory right before WHIR fold queries.
    // Setup: cosets allocated on demand; partial trees already transferred from host.
    let pre_whir_setup_cosets_range = Range::new("gkr.proof.pre_whir.setup_cosets")?;
    pre_whir_setup_cosets_range.start(stream)?;
    if let Some(setup_transfer) = setup_transfer.as_mut() {
        setup_transfer
            .trace_holder
            .ensure_cosets_materialized(context)?;
    } else {
        let setup_trace_holder = synthetic_setup_trace_holder
            .as_mut()
            .expect("setup-less proof path must materialize a synthetic setup holder");
        if setup_trace_holder.columns_count > 0 {
            setup_trace_holder.commit_all(context)?;
        }
    }
    pre_whir_setup_cosets_range.end(stream)?;

    // Memory: cosets allocated on demand, then build and cache partial trees from cosets.
    let pre_whir_memory_commit_range = Range::new("gkr.proof.pre_whir.memory_commit")?;
    pre_whir_memory_commit_range.start(stream)?;
    stage1_output
        .memory_trace_holder
        .ensure_cosets_materialized(context)?;
    {
        let instances_count = 1usize << stage1_output.memory_trace_holder.log_lde_factor;
        stage1_output.memory_trace_holder.trees = TreesHolder::Partial(allocate_trees(
            instances_count,
            stage1_output.memory_trace_holder.log_domain_size - PARTIAL_TREE_REDUCTION_LAYERS,
            stage1_output.memory_trace_holder.log_rows_per_leaf,
            context,
        )?);
        stage1_output
            .memory_trace_holder
            .build_and_cache_partial_trees(context)?;
    }
    pre_whir_memory_commit_range.end(stream)?;

    Ok([pre_whir_setup_cosets_range, pre_whir_memory_commit_range])
}

pub(in crate::proof) fn schedule_whir_phase<'a>(
    compiled_circuit: &GKRCircuitArtifact<BF>,
    whir_schedule: &WhirSchedule,
    setup_transfer: &mut Option<GpuGKRSetupTransfer<'a>>,
    synthetic_setup_trace_holder: &mut Option<TraceHolder<BF>>,
    stage1_output: &mut GpuGKRStage1Output,
    backward_scheduled: &mut GpuGKRBackwardScheduledExecution,
    proof_slab: &DeviceAllocation<E4>,
    proof_layout: &ProofLayout,
    batching_pow_bits: u32,
    context: &ProverContext,
) -> CudaResult<WhirPhaseResult> {
    let mut transition_ranges = Vec::new();

    let setup_trace_holder = setup_transfer
        .as_ref()
        .map(|setup| &setup.trace_holder)
        .unwrap_or_else(|| {
            synthetic_setup_trace_holder
                .as_ref()
                .expect("setup-less proof path must materialize a synthetic setup holder")
        });
    let final_claim_addresses = backward_scheduled.final_claim_addresses().to_vec();
    let (final_device_seed, final_device_claim_point) =
        backward_scheduled.final_device_seed_and_claim_point_mut();
    let base_layer_claims_scheduled = schedule_prepare_base_layer_claims_with_sources(
        compiled_circuit.layers[0].clone(),
        final_device_claim_point,
        // Layer-1 incoming claim addresses are schedule-time-known (the
        // `ClaimBufferLayout` built when backward staged its final claims),
        // so the base-layer extras plan is built without a host claim map.
        &final_claim_addresses,
        setup_trace_holder,
        &stage1_output.memory_trace_holder,
        &stage1_output.witness_trace_holder,
        proof_slab,
        proof_layout,
        final_device_seed,
        context,
    )?;
    let base_layer_claims_shared_state = base_layer_claims_scheduled.shared_state_handle();
    transition_ranges.extend(materialize_pre_whir_trace_inputs(
        setup_transfer,
        synthetic_setup_trace_holder,
        stage1_output,
        context,
    )?);

    // Draw the WHIR base batching challenge on device from the rolling backward
    // seed. Pow-aware (`draw_random_field_els_with_pow(seed, 1, bits)`): grinds
    // the configured batched-proximity PoW, advances the seed, and honors the
    // skip-first-word convention. The nonce lands in its slab slot.
    // SAFETY: `ProofLayout` computes a live, aligned, non-overlapping E4 region
    // inside `proof_slab`. The draw and every WHIR consumer are ordered on the
    // exec stream, and the slab outlives the scheduled work.
    let (batching_challenge_ptr, batching_challenge_len) =
        unsafe { proof_layout.whir_batching_challenge_device_mut(proof_slab.as_ptr() as *mut u8) };
    assert_eq!(batching_challenge_len, 1);
    let batching_challenge_device =
        unsafe { DeviceSlice::from_raw_parts_mut(batching_challenge_ptr, batching_challenge_len) };
    // SAFETY: `ProofLayout` computes a live, non-overlapping single-`u64` region
    // for the batching pow nonce inside the slab; the kernel write here and the
    // terminal readback are both exec-stream-ordered.
    let (batching_nonce_ptr, _batching_nonce_len) = unsafe {
        proof_layout.batched_proximity_pow_nonce_device_mut(proof_slab.as_ptr() as *mut u8)
    };
    let batching_nonce_dst: &mut era_cudart::slice::DeviceVariable<u64> =
        unsafe { era_cudart::slice::DeviceVariable::from_raw_parts_mut(batching_nonce_ptr) };
    let (final_device_seed_mut, _claim_point_for_squeeze) =
        backward_scheduled.final_device_seed_and_claim_point_mut();
    gpu_whir::pow::schedule_draw_e4_challenges_with_pow(
        final_device_seed_mut,
        &mut *batching_challenge_device,
        batching_pow_bits,
        batching_nonce_dst,
        context,
    )?;
    {
        let (_final_device_seed, claim_point) =
            backward_scheduled.final_device_seed_and_claim_point_mut();
        // SAFETY: the destination is a live, aligned E4 region inside the proof
        // slab. This device-to-device copy is scheduled on exec_stream; neither
        // the constant-symbol source nor destination is host-dereferenced.
        let (point_slab_ptr, point_slab_len) = unsafe {
            proof_layout.whir_original_evaluation_point_device_mut(proof_slab.as_ptr() as *mut u8)
        };
        assert_eq!(point_slab_len, claim_point.len());
        let point_slab_dst =
            unsafe { DeviceSlice::from_raw_parts_mut(point_slab_ptr, point_slab_len) };
        memory_copy_async(point_slab_dst, claim_point, context.get_exec_stream())?;
    }
    let whir_scheduled = {
        let setup_trace_holder = if let Some(setup_transfer) = setup_transfer.as_mut() {
            &mut setup_transfer.trace_holder
        } else {
            synthetic_setup_trace_holder
                .as_mut()
                .expect("setup-less proof path must materialize a synthetic setup holder")
        };
        let (final_device_seed_mut, claim_point) =
            backward_scheduled.final_device_seed_and_claim_point_mut();
        schedule_gpu_whir_fold_with_sources(
            &mut stage1_output.memory_trace_holder,
            &mut stage1_output.witness_trace_holder,
            setup_trace_holder,
            claim_point,
            final_device_seed_mut,
            &*batching_challenge_device,
            whir_schedule.base_lde_factor,
            whir_schedule.whir_steps_schedule.clone(),
            whir_schedule.whir_queries_schedule.clone(),
            whir_schedule.whir_steps_lde_factors.clone(),
            whir_schedule.whir_pow_schedule.clone(),
            whir_schedule.cap_size,
            compiled_circuit.trace_len.trailing_zeros(),
            true, // use_hypercube_evals_for_batching
            proof_slab,
            proof_layout,
            context,
        )?
    };

    Ok(WhirPhaseResult {
        transition_ranges,
        base_layer_claims_scheduled,
        base_layer_claims_shared_state,
        whir_scheduled,
    })
}
