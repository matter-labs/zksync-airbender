use era_cudart::result::CudaResult;

use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{DeviceAllocation, ProverContext, UnsafeMutAccessor};
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E4};
use crate::prover::gkr::backward::kernels::ScheduledBackwardWorkflowStateHandle;
use crate::prover::gkr::backward::{current_backward_seed, GpuGKRBackwardScheduledExecution};
use crate::prover::gkr::base_layer_claims::{
    schedule_prepare_base_layer_claims_with_sources, GpuGKRBaseLayerClaimsScheduledExecution,
    ScheduledBaseLayerClaimsState,
};
use crate::prover::gkr::setup::GpuGKRSetupTransfer;
use crate::prover::gkr::stage1::GpuGKRStage1Output;
use crate::prover::proof::layout::ProofLayout;
use crate::prover::trace::holder::{
    allocate_trees, TraceHolder, TreesHolder, PARTIAL_TREE_REDUCTION_LAYERS,
};
use crate::prover::trace::memory_transfer::GpuGKRMemoryTransfer;
use crate::prover::whir::fold::{
    schedule_gpu_whir_fold_with_sources, GpuWhirFoldScheduledExecution, ScheduledWhirProofState,
};
use crate::upstream::{draw_random_field_els, GKRCircuitArtifact, WhirSchedule};

pub(in crate::prover::proof) struct WhirPhaseResult {
    pub(in crate::prover::proof) transition_ranges: Vec<Range>,
    pub(in crate::prover::proof) post_backward_callbacks: Callbacks<'static>,
    pub(in crate::prover::proof) base_layer_claims_scheduled:
        GpuGKRBaseLayerClaimsScheduledExecution<E4>,
    pub(in crate::prover::proof) base_layer_claims_shared_state:
        UnsafeMutAccessor<ScheduledBaseLayerClaimsState<E4>>,
    pub(in crate::prover::proof) whir_scheduled: GpuWhirFoldScheduledExecution,
    pub(in crate::prover::proof) whir_shared_state: UnsafeMutAccessor<ScheduledWhirProofState>,
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

pub(in crate::prover::proof) fn schedule_whir_phase<'a>(
    compiled_circuit: &GKRCircuitArtifact<BF>,
    whir_schedule: &WhirSchedule,
    setup_transfer: &mut Option<GpuGKRSetupTransfer<'a>>,
    synthetic_setup_trace_holder: &mut Option<TraceHolder<BF>>,
    stage1_output: &mut GpuGKRStage1Output,
    memory_transfer: &GpuGKRMemoryTransfer<'a>,
    backward_scheduled: &mut GpuGKRBackwardScheduledExecution<BF, E4>,
    backward_shared_state: ScheduledBackwardWorkflowStateHandle<E4>,
    proof_slab: Option<&DeviceAllocation<E4>>,
    proof_layout: &ProofLayout,
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
    let mut base_layer_claims_scheduled = schedule_prepare_base_layer_claims_with_sources(
        compiled_circuit.layers[0].clone(),
        final_device_claim_point,
        // Layer-1 incoming claim addresses are schedule-time-known (the
        // `ClaimBufferLayout` built when backward staged its final claims),
        // so the base-layer extras plan is built at schedule time without
        // waiting for the backward post-handoff callback to materialize a
        // host BTreeMap.
        &final_claim_addresses,
        setup_trace_holder,
        &stage1_output.memory_trace_holder,
        &stage1_output.witness_trace_holder,
        proof_slab,
        proof_layout,
        Some(final_device_seed),
        context,
    )?;
    let base_layer_claims_shared_state = base_layer_claims_scheduled.shared_state_handle();
    transition_ranges.extend(materialize_pre_whir_trace_inputs(
        setup_transfer,
        synthetic_setup_trace_holder,
        stage1_output,
        context,
    )?);

    let stream = context.get_exec_stream();
    let post_backward_handoff_range = Range::new("gkr.proof.post_backward_handoff")?;
    post_backward_handoff_range.start(stream)?;
    let post_backward_callbacks = backward_scheduled.schedule_post_backward_handoff(context)?;
    post_backward_handoff_range.end(stream)?;
    transition_ranges.push(post_backward_handoff_range);

    let mut whir_scheduled = {
        let setup_trace_holder = if let Some(setup_transfer) = setup_transfer.as_mut() {
            &mut setup_transfer.trace_holder
        } else {
            synthetic_setup_trace_holder
                .as_mut()
                .expect("setup-less proof path must materialize a synthetic setup holder")
        };
        schedule_gpu_whir_fold_with_sources(
            &mut stage1_output.memory_trace_holder,
            memory_transfer.unified_device_cap(),
            &mut stage1_output.witness_trace_holder,
            setup_trace_holder,
            backward_scheduled.final_device_claim_point(),
            whir_schedule.base_lde_factor,
            {
                let backward_shared_state = backward_shared_state;
                move || {
                    let mut seed = current_backward_seed(backward_shared_state);
                    draw_random_field_els::<BF, E4>(&mut seed, 1)[0]
                }
            },
            whir_schedule.whir_steps_schedule.clone(),
            whir_schedule.whir_queries_schedule.clone(),
            whir_schedule.whir_steps_lde_factors.clone(),
            whir_schedule.whir_pow_schedule.clone(),
            {
                let backward_shared_state = backward_shared_state;
                move || {
                    let mut seed = current_backward_seed(backward_shared_state);
                    let _whir_batching_challenge = draw_random_field_els::<BF, E4>(&mut seed, 1);
                    seed
                }
            },
            whir_schedule.cap_size,
            compiled_circuit.trace_len.trailing_zeros() as usize,
            true, // use_hypercube_evals_for_batching
            proof_slab,
            proof_layout,
            Some(base_layer_claims_scheduled.take_pending_aggregation()),
            context,
        )?
    };
    let whir_shared_state = whir_scheduled.shared_state_handle();

    Ok(WhirPhaseResult {
        transition_ranges,
        post_backward_callbacks,
        base_layer_claims_scheduled,
        base_layer_claims_shared_state,
        whir_scheduled,
        whir_shared_state,
    })
}
