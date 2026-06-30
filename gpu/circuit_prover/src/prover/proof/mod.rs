pub mod inputs;
pub(crate) mod layout;
mod orchestration;

use std::sync::Arc;

use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStreamWaitEventFlags;
use fft::GoodAllocator;

use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::UnsafeMutAccessor;
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E4};
use crate::prover::config::assert_gpu_supported_pow_config;
use crate::prover::gkr::backward::make_deferred_backward_workflow_state;
use crate::prover::gkr::forward::{schedule_forward_pass, ForwardOutputSlabTarget};
use crate::prover::proof::inputs::GpuGKRProofTransfer;
use crate::prover::ProverContext;
use crate::upstream::{GKRCircuitArtifact, ProverConfig};
use crate::witness::circuit_type::CircuitType;

#[cfg(test)]
pub(crate) use orchestration::grand_product_accumulator_from_explicit_evaluations;
pub use orchestration::{canonical_inits_and_teardowns_top_bits, GpuGKRProofJob};
use orchestration::{
    prepare_backward_handoff, prepare_stage1_and_forward_setup, schedule_backward_phase,
    schedule_terminal_proof_assembly, schedule_whir_phase, stage1_forward::BundleDeviceRefs,
    BackwardPhaseResult, ForwardToBackwardHandoff, GpuGKRProofJobKeepalive,
    Stage1AndForwardPreparation, WhirPhaseResult,
};

/// `prove` is circuit-type-driven: it dispatches purely on `circuit_type` and
/// the `GpuGKRProofTransfer` shape, with no per-family whitelist. The Unified
/// path is therefore *selected*, not special-cased here — feed
/// `CircuitType::Unrolled(UnrolledCircuitType::Unified)`, the unified compiled
/// circuit, and the `UnrolledTracingDataDevice::Unified` transfer. All
/// Unified-specific handling lives in the inner stages: stage1 dispatch
/// (`gkr/stage1/mod.rs`), commit-memory (`prover/trace/memory.rs`), setup
/// (`execution_prover::precomputations`), and the claim-layout/accumulator
/// arms.
#[allow(clippy::too_many_arguments)]
pub fn prove<'a, A: GoodAllocator + 'a>(
    circuit_type: CircuitType,
    compiled_circuit: GKRCircuitArtifact<BF>,
    prover_config: &ProverConfig,
    final_trace_size_log_2: usize,
    inputs: GpuGKRProofTransfer<'a, A>,
    context: &ProverContext,
) -> CudaResult<GpuGKRProofJob<'a, A>> {
    assert_gpu_supported_pow_config(prover_config);
    assert_eq!(
        prover_config.base_oracles_values_per_leaf.trailing_zeros() as usize,
        prover_config.whir_schedule.whir_steps_schedule[0]
    );
    let whir_schedule = &prover_config.whir_schedule;

    let GpuGKRProofTransfer {
        transfer,
        mut setup,
        decoder,
        inits_and_teardowns,
        tracing_data,
        memory,
        canonical_top_bits,
        external_challenges,
    } = inputs;

    if let Some(setup_transfer) = setup.as_ref() {
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
    }

    // Single fork/join from h2d_stream → exec_stream covering every pre-prove
    // H2D bundled by `inputs` (setup, decoder, inits_and_teardowns, tracing_data,
    // memory caps, canonical_top_bits, external_challenges).
    transfer.ensure_transferred(context)?;

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
    } = prepare_stage1_and_forward_setup::<A>(
        circuit_type,
        &compiled_circuit,
        &external_challenges.value,
        prover_config,
        final_trace_size_log_2,
        whir_schedule,
        BundleDeviceRefs {
            setup: setup.as_ref(),
            decoder: decoder.as_ref(),
            inits_and_teardowns: inits_and_teardowns.as_ref(),
            memory: &memory,
            canonical_top_bits_device: canonical_top_bits.as_ref().map(|t| &t.device),
            external_challenges_device: &external_challenges.device,
        },
        tracing_data.as_ref(),
        context,
    )?;

    let output_evaluations_slab =
        unsafe { proof_layout.output_evaluations_device_mut(proof_slab.as_ptr() as *mut u8) }.map(
            |(ptr, len)| {
                assert_eq!(
                    ptr,
                    proof_slab.as_ptr() as *mut E4,
                    "output_evaluations must be the proof slab prefix for direct forward writes",
                );
                ForwardOutputSlabTarget {
                    backing: Arc::clone(&proof_slab),
                    len,
                }
            },
        );
    let forward_output = schedule_forward_pass(
        setup.as_ref().map(|setup| &setup.trace_holder),
        synthetic_setup_trace_holder.as_ref(),
        &mut stage1_output,
        &mut forward_setup,
        &compiled_circuit,
        &external_challenges.value,
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
        external_challenges.value.clone(),
        external_challenges.device.as_ptr(),
        backward_shared_state,
        d_seed,
        d_evaluation_point_and_batching,
        initial_d_claims,
        top_layer_claim_layout,
        d_lookup_challenges_for_backward,
        &proof_slab,
        &proof_layout,
        context,
    )?;
    let WhirPhaseResult {
        transition_ranges,
        post_backward_callbacks,
        mut base_layer_claims_scheduled,
        base_layer_claims_shared_state,
        whir_scheduled,
        batching_challenge_device: _batching_challenge_device,
    } = schedule_whir_phase(
        &compiled_circuit,
        whir_schedule,
        &mut setup,
        &mut synthetic_setup_trace_holder,
        &mut stage1_output,
        &mut backward_scheduled,
        backward_shared_state,
        &proof_slab,
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

    let pending_aggregation = base_layer_claims_scheduled.take_pending_aggregation();
    let proof_host_mirror = Some(schedule_terminal_proof_assembly(
        &proof_slab,
        &proof_layout,
        proof_handle,
        whir_schedule.clone(),
        base_layer_claims_shared_state,
        pending_aggregation,
        external_challenges.value.clone(),
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

    // Reassemble the bundle so we can produce a single keepalive that owns
    // every transferless wrapper + the shared Transfer's accumulated callbacks.
    let inputs_keepalive = GpuGKRProofTransfer {
        transfer,
        setup,
        decoder,
        inits_and_teardowns,
        tracing_data,
        memory,
        canonical_top_bits,
        external_challenges,
    }
    .into_keepalive();

    Ok(GpuGKRProofJob {
        is_finished_event,
        callbacks,
        proof,
        ranges,
        keepalive: GpuGKRProofJobKeepalive {
            _stage1: stage1_output.into_keepalive(),
            _inputs: inputs_keepalive,
            _forward_setup: forward_setup_keepalive,
            _backward: backward_keepalive,
            _base_layer_claims: base_layer_claims_scheduled,
            _whir: whir_scheduled,
            _whir_batching_challenge_device: _batching_challenge_device,
            _proof_host_mirror: proof_host_mirror,
            _proof_slab: proof_slab,
        },
    })
}

#[cfg(test)]
mod tests;
