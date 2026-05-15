pub(crate) mod layout;
mod orchestration;

use std::sync::Arc;

use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;

use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStreamWaitEventFlags;
use fft::GoodAllocator;

use crate::primitives::callbacks::Callbacks;
use crate::primitives::circuit_type::CircuitType;
use crate::primitives::context::{ProverContext, UnsafeMutAccessor};
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E4};
use crate::prover::gkr::backward::make_deferred_backward_workflow_state;
use crate::prover::gkr::forward::{schedule_forward_pass, ForwardOutputSlabTarget};
use crate::prover::gkr::setup::GpuGKRSetupTransfer;
use crate::prover::trace::decoder::DecoderTableTransfer;
use crate::prover::trace::memory_transfer::GpuGKRMemoryTransfer;
use crate::prover::trace::tracing_data::{InitsAndTeardownsTransfer, TracingDataTransfer};
use crate::upstream::{GKRCircuitArtifact, GKRExternalChallenges, ProverConfig};

pub(crate) use orchestration::{
    assert_gpu_supported_pow_config, grand_product_accumulator_from_explicit_evaluations,
    GpuGKRProofJob,
};
use orchestration::{
    canonical_inits_and_teardowns_top_bits, prepare_backward_handoff,
    prepare_stage1_and_forward_setup, schedule_backward_phase, schedule_terminal_proof_assembly,
    schedule_whir_phase, BackwardPhaseResult, ForwardToBackwardHandoff, GpuGKRProofJobKeepalive,
    Stage1AndForwardPreparation, WhirPhaseResult,
};

#[allow(clippy::too_many_arguments)]
pub(crate) fn prove<'a, A: GoodAllocator + 'a>(
    circuit_type: CircuitType,
    compiled_circuit: GKRCircuitArtifact<BF>,
    external_challenges: GKRExternalChallenges<BF, E4>,
    prover_config: &ProverConfig,
    final_trace_size_log_2: usize,
    mut setup_transfer: Option<GpuGKRSetupTransfer<'a>>,
    decoder_transfer: Option<DecoderTableTransfer<'a>>,
    inits_and_teardowns_transfer: Option<InitsAndTeardownsTransfer<'a>>,
    tracing_data_transfer: Option<TracingDataTransfer<'a, A>>,
    memory_transfer: GpuGKRMemoryTransfer<'a>,
    context: &ProverContext,
) -> CudaResult<GpuGKRProofJob<'a>> {
    assert_gpu_supported_pow_config(prover_config);
    assert_eq!(
        prover_config.base_oracles_values_per_leaf.trailing_zeros() as usize,
        prover_config.whir_schedule.whir_steps_schedule[0]
    );
    let whir_schedule = &prover_config.whir_schedule;
    if let Some(setup_transfer) = setup_transfer.as_ref() {
        assert_eq!(
            setup_transfer.trace_holder.log_lde_factor,
            prover_config.lde_factor.trailing_zeros()
        );
        assert_eq!(
            setup_transfer.trace_holder.log_rows_per_leaf,
            prover_config.base_oracles_values_per_leaf.trailing_zeros()
        );
        assert_eq!(
            setup_transfer.trace_holder.log_tree_cap_size,
            prover_config.cap_size.trailing_zeros()
        );
        setup_transfer.ensure_transferred(context)?;
    }
    if let Some(decoder_transfer) = decoder_transfer.as_ref() {
        decoder_transfer.transfer.ensure_transferred(context)?;
    }
    if let Some(inits_and_teardowns_transfer) = inits_and_teardowns_transfer.as_ref() {
        inits_and_teardowns_transfer
            .transfer
            .ensure_transferred(context)?;
    }
    if let Some(tracing_data_transfer) = tracing_data_transfer.as_ref() {
        tracing_data_transfer.transfer.ensure_transferred(context)?;
    }
    // Memory cap H2D was scheduled pre-prove on h2d_stream; the D2D into the
    // transcript input slot below needs the H2D to be visible on exec_stream.
    memory_transfer.ensure_transferred(context)?;

    let stream = context.get_exec_stream();
    let mut callbacks = Callbacks::new();
    let mut proof = Box::new(None);
    let proof_handle = UnsafeMutAccessor::new(proof.as_mut());
    let mut ranges = Vec::new();
    let proof_range = Range::new("gkr.proof")?;
    proof_range.start(stream)?;

    context.reset_used_mem_peak();

    let Stage1AndForwardPreparation {
        mut stage1_output,
        mut synthetic_setup_trace_holder,
        proof_layout,
        proof_slab,
        mut forward_setup,
        d_seed,
        d_external_challenges_e4,
        canonical_top_bits_host,
        external_challenges_host,
    } = prepare_stage1_and_forward_setup(
        circuit_type,
        &compiled_circuit,
        &external_challenges,
        prover_config,
        final_trace_size_log_2,
        whir_schedule,
        &setup_transfer,
        decoder_transfer,
        inits_and_teardowns_transfer,
        tracing_data_transfer,
        &memory_transfer,
        &mut callbacks,
        context,
    )?;

    let output_evaluations_slab = proof_slab.as_ref().and_then(|slab| {
        let (ptr, len) =
            unsafe { proof_layout.output_evaluations_device_mut(slab.as_ptr() as *mut u8) }?;
        assert_eq!(
            ptr,
            slab.as_ptr() as *mut E4,
            "output_evaluations must be the proof slab prefix for direct forward writes",
        );
        Some(ForwardOutputSlabTarget {
            backing: Arc::clone(slab),
            len,
        })
    });
    let forward_output = schedule_forward_pass(
        setup_transfer.as_ref().map(|setup| &setup.trace_holder),
        synthetic_setup_trace_holder.as_ref(),
        &mut stage1_output,
        &mut forward_setup,
        &compiled_circuit,
        &external_challenges,
        final_trace_size_log_2,
        output_evaluations_slab,
        context,
    )?;
    let ForwardToBackwardHandoff {
        post_forward_handoff_range,
        transcript_handoff,
        backward_state,
        forward_setup_keepalive,
        d_lookup_challenges_for_backward,
        d_seed,
        d_evaluation_point_and_batching,
        top_layer_claim_layout,
        initial_d_claims,
    } = prepare_backward_handoff(
        forward_output,
        forward_setup,
        d_seed,
        final_trace_size_log_2,
        context,
    )?;

    // No host mirror of the initial claims / evaluation_point / batching / seed / lookup
    // challenges is needed on the hot path: backward consumes them as device buffers, and
    // post-backward overwrites the layer-0 host fields that downstream base-layer / WHIR
    // setup reads. `backward_shared_state` is created empty and populated by the
    // post-backward handoff for layer 0.
    let backward_shared_state = make_deferred_backward_workflow_state();
    ranges.push(post_forward_handoff_range);

    let BackwardPhaseResult {
        mut backward_scheduled,
        backward_shared_state,
    } = schedule_backward_phase(
        backward_state,
        compiled_circuit.clone(),
        external_challenges.clone(),
        d_external_challenges_e4.as_ptr(),
        backward_shared_state,
        d_seed,
        d_evaluation_point_and_batching,
        initial_d_claims,
        top_layer_claim_layout,
        d_lookup_challenges_for_backward,
        proof_slab.as_deref(),
        &proof_layout,
        context,
    )?;
    let WhirPhaseResult {
        transition_ranges,
        post_backward_callbacks,
        base_layer_claims_scheduled,
        base_layer_claims_shared_state,
        whir_scheduled,
        whir_shared_state,
    } = schedule_whir_phase(
        &compiled_circuit,
        whir_schedule,
        &mut setup_transfer,
        &mut synthetic_setup_trace_holder,
        &mut stage1_output,
        &memory_transfer,
        &mut backward_scheduled,
        backward_shared_state,
        proof_slab.as_deref(),
        &proof_layout,
        context,
    )?;
    ranges.extend(transition_ranges);
    callbacks.extend(post_backward_callbacks);

    // `backward_scheduled` itself is the keepalive — the per-layer device
    // handles were already taken by the orchestrator (or remain as `Some`
    // for the proof-lifetime final-seed/claim-point buffers), and the
    // callbacks/tracing/host-staging buffers all ride on this struct.
    let backward_keepalive = backward_scheduled;
    let setup_keepalive = setup_transfer.map(GpuGKRSetupTransfer::into_host_keepalive);
    let memory_keepalive = memory_transfer.into_host_keepalive();

    let slab = proof_slab
        .as_ref()
        .expect("proof slab must be allocated for prove()");
    let proof_host_mirror = Some(schedule_terminal_proof_assembly(
        slab,
        &proof_layout,
        proof_handle,
        whir_shared_state,
        base_layer_claims_shared_state,
        external_challenges.clone(),
        canonical_inits_and_teardowns_top_bits(&compiled_circuit),
        &mut callbacks,
        context,
    )?);
    drop(transcript_handoff);

    {
        let event = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
        event.record(stream)?;
        context
            .get_h2d_stream()
            .wait_event(&event, CudaStreamWaitEventFlags::DEFAULT)?;
    }

    proof_range.end(stream)?;
    ranges.push(proof_range);

    let is_finished_event = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
    is_finished_event.record(stream)?;
    Ok(GpuGKRProofJob {
        is_finished_event,
        callbacks,
        proof,
        ranges,
        keepalive: GpuGKRProofJobKeepalive {
            _stage1: stage1_output.into_keepalive(),
            _setup: setup_keepalive,
            _memory: memory_keepalive,
            _forward_setup: forward_setup_keepalive,
            _backward: backward_keepalive,
            _base_layer_claims: base_layer_claims_scheduled,
            _whir: whir_scheduled,
            _initial_transcript_canonical_top_bits_host: canonical_top_bits_host,
            _external_challenges_host: external_challenges_host,
            _external_challenges_device: d_external_challenges_e4,
            _proof_host_mirror: proof_host_mirror,
            _proof_slab: proof_slab,
        },
    })
}

#[cfg(test)]
mod tests;
