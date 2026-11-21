use crate::precomputations::CircuitPrecomputations;
use crate::upstream::{OperationMode, L1_WRAP_EXPLICIT_OUTPUT_LOG2};
use crate::workers::gpu::{
    follower_label, JobType, PhaseOne, PhaseOneInputs, RequestKind, RequestState,
};
use crate::workers::gpu_manager::GpuWorkResult;
use crate::A;
use era_cudart::result::CudaResult;
use execution_prover::messages::{L1WrapProofRequest, L1WrapProofResult};
use execution_prover::ProofProfile;
use gpu_circuit_prover::proth120::{GpuL1WrapProofJob, L1WrapInputs};
use gpu_core::primitives::device_tracing::Range;
use gpu_gkr::proth120::backward::{prepare_dr_tail_resources_pr, DrTailProofPlanPr};
use gpu_prover_context::ProverContext;
use gpu_trace::trace::tracing_data::{TracingDataHost, UnrolledTracingDataHost};
use log::{debug, trace};
use std::sync::Arc;

const WRAP_FINAL_TRACE_SIZE_LOG_2: u32 = L1_WRAP_EXPLICIT_OUTPUT_LOG2 as u32;

pub(crate) fn schedule_l1_wrap_phase_one<'a>(
    device_id: i32,
    context: &ProverContext,
    request: L1WrapProofRequest<A, CircuitPrecomputations>,
) -> CudaResult<PhaseOne<'a>> {
    let L1WrapProofRequest {
        batch_id,
        circuit_type,
        precomputations,
        inits_and_teardowns,
        tracing_data,
        operation_mode,
    } = request;
    assert!(
        circuit_type.is_l1_wrap(),
        "Proth120 GPU requires an L1 wrap circuit type, got {circuit_type:?}"
    );
    let request_range = Range::new("l1_wrap.request")?;
    request_range.start(context.get_exec_stream())?;
    let precomputed = Arc::clone(precomputations.l1_wrap());
    assert_eq!(
        precomputed.circuit_type, circuit_type,
        "L1 wrap request {circuit_type:?} disagrees with its precomputations"
    );
    let state = RequestState {
        batch_id,
        circuit_type,
        sequence_id: 0,
        precomputations,
        kind: RequestKind::L1WrapProof,
        external_challenges: None,
        memory_caps: None,
        memory_partial_trees: None,
        partial_tree_buffer: None,
        inits_and_teardowns_result: Some(inits_and_teardowns.clone()),
        tracing_data_result: Some(TracingDataHost::Unrolled(UnrolledTracingDataHost::Unified(
            tracing_data.clone(),
        ))),
        profile: ProofProfile::L1Wrap,
        device_peak_bytes: None,
        direction: None,
        follower: None,
    };
    let dr_tail_plan =
        prepare_dr_tail_resources_pr(&precomputed.programs, WRAP_FINAL_TRACE_SIZE_LOG_2, context);
    let mut inputs = L1WrapInputs::new(
        &precomputed.geometry,
        precomputed.decoder_host.clone(),
        inits_and_teardowns,
        tracing_data,
        precomputed.host(),
        precomputed.constants(),
        &operation_mode,
        context,
    )?;
    inputs.time_request(request_range);
    trace!("BATCH[{batch_id}] GPU_WORKER[{device_id}] scheduling L1 wrap H2D bundle");
    inputs.schedule(context)?;
    Ok(PhaseOne {
        state,
        inputs: PhaseOneInputs::L1Wrap(inputs, dr_tail_plan, operation_mode),
    })
}

pub(crate) fn enqueue_phase_two<'a>(
    device_id: i32,
    context: &ProverContext,
    state: &mut RequestState,
    inputs: L1WrapInputs<'a, A>,
    dr_tail_plan: DrTailProofPlanPr,
    operation_mode: OperationMode,
) -> CudaResult<JobType<'a>> {
    let precomputed = Arc::clone(state.precomputations.l1_wrap());
    trace!(
        "BATCH[{}] GPU_WORKER[{device_id}] producing L1 wrap proof",
        state.batch_id
    );
    context.reset_used_mem_peak();
    let job = gpu_circuit_prover::proof::prove(
        gpu_circuit_prover::proth120::L1WrapProofRequest::new(
            &precomputed.programs,
            &precomputed.circuit,
            &precomputed.geometry,
            &precomputed.config,
            operation_mode,
            inputs,
            &dr_tail_plan,
            crate::memory_policy::partial_trees(state.circuit_type, ProofProfile::L1Wrap),
        ),
        context,
    )?;
    state.device_peak_bytes = Some(context.get_used_mem_peak());
    Ok(JobType::L1Wrap(job))
}

pub(crate) fn finish_l1_wrap(
    device_id: i32,
    state: RequestState,
    job: GpuL1WrapProofJob<'_>,
) -> CudaResult<GpuWorkResult<A>> {
    let RequestState {
        batch_id,
        circuit_type,
        sequence_id,
        inits_and_teardowns_result,
        tracing_data_result,
        profile,
        device_peak_bytes,
        direction,
        follower,
        ..
    } = state;
    let follower = follower_label(follower);
    let result = job.finish()?;
    let bytes = device_peak_bytes.expect("L1 wrap proof device peak was recorded");
    let direction = direction.expect("L1 wrap proof allocation direction was recorded");
    debug!(
        "BATCH[{batch_id}] GPU_WORKER[{device_id}] produced L1 wrap proof for circuit {circuit_type:?}[{sequence_id}] profile {profile:?} direction {direction:?} follower {follower} device peak {bytes} B"
    );
    let inits_and_teardowns =
        inits_and_teardowns_result.expect("L1 wrap proof returns its inits and teardowns");
    let Some(TracingDataHost::Unrolled(UnrolledTracingDataHost::Unified(tracing_data))) =
        tracing_data_result
    else {
        panic!("L1 wrap proof returns its unified tracing data")
    };
    Ok(GpuWorkResult::L1WrapProof(L1WrapProofResult {
        batch_id,
        circuit_type,
        inits_and_teardowns,
        tracing_data,
        result,
    }))
}

#[cfg(test)]
pub(crate) mod tests;
