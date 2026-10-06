pub mod inputs;
pub mod memory_policy;

use memory_policy::ProofMemoryPolicy;
mod orchestration;

use std::sync::Arc;

use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStreamWaitEventFlags;
use fft::GoodAllocator;

use crate::proof::inputs::GpuGKRProofTransfer;
use crate::upstream::{validate_sumcheck_schedule, ProverConfig, SumcheckScheduleClass};
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::context::UnsafeMutAccessor;
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::BF;
use gpu_core::primitives::field::E4;
use gpu_gkr::backward::GKRBackwardStageSnapshotSink;
use gpu_gkr::backward::GpuGKRBackwardScheduledExecution;
use gpu_gkr::base_layer_claims::{BaseLayerExtrasLayout, GpuGKRBaseLayerClaimsScheduledExecution};
use gpu_gkr::forward::GpuGKRTranscriptHandoff;
use gpu_gkr::forward::{schedule_forward_pass, ForwardOutputSlabTarget};
use gpu_gkr::proof_layout::ProofLayout;
use gpu_gkr::replay::GkrReplayValues;
use gpu_gkr::setup::{GpuGKRForwardSetupHostKeepalive, GpuGKRSetupTransfer};
use gpu_gkr::stage1::GpuGKRStage1Output;
use gpu_gkr::GkrPrograms;
use gpu_prover_context::replay::{PhaseOutcome, ReplayInputs};
use gpu_prover_context::{CudaGraphMode, ProverContext};
use gpu_trace::trace::decoder::DecoderTableTransfer;
use gpu_trace::trace::holder::{device_range, TraceHolder};
use gpu_trace::trace::memory_transfer::GpuGKRMemoryTransfer;
use gpu_trace::trace::tracing_data::{InitsAndTeardownsTransfer, TracingDataTransfer};
use gpu_trace::witness::memory_unrolled::InitsAndTeardownsPages;
use gpu_trace::witness::trace_unrolled::TraceCycles;
use gpu_whir::fold::GpuWhirFoldScheduledExecution;

pub use orchestration::GpuGKRProofJob;
use orchestration::{
    prepare_backward_handoff, prepare_stage1_and_forward_setup, schedule_backward_phase,
    schedule_terminal_proof_assembly, schedule_whir_phase, stage1_forward::BundleDeviceRefs,
    BackwardPhaseResult, ComputeKeepalive, ForwardToBackwardHandoff, GpuGKRProofJobKeepalive,
    Stage1AndForwardPreparation, WhirPhaseResult,
};

pub fn validate_windowed_schedule(gkr_programs: &GkrPrograms, prover_config: &ProverConfig) {
    assert_eq!(
        validated_schedule_class(gkr_programs, prover_config),
        Some(SumcheckScheduleClass::Windowed)
    );
}

fn validated_schedule_class(
    gkr_programs: &GkrPrograms,
    prover_config: &ProverConfig,
) -> Option<SumcheckScheduleClass> {
    validate_sumcheck_schedule(
        &prover_config.same_size_sumcheck_schedule,
        main_folding_steps(gkr_programs),
    )
    .ok()
}

fn main_folding_steps(gkr_programs: &GkrPrograms) -> usize {
    gkr_programs.compiled_circuit().trace_len.trailing_zeros() as usize
}

/// What the DR preflight boundary needs in order to admit a proof request.
///
/// `None` at the boundary means the request is not a proof, so neither the
/// windowed lowering preflight nor DR-tail resource admission applies.
#[derive(Clone, Copy)]
pub struct DrTailPreflightRequest<'a> {
    pub gkr_programs: &'a GkrPrograms,
    pub prover_config: &'a ProverConfig,
    pub final_trace_size_log_2: u32,
    pub device_id: i32,
}

/// Preflight before constructing transfers so the plan can be owned by them.
pub fn admit_dr_tail_before_transfers<T>(
    request: Option<DrTailPreflightRequest<'_>>,
    construct_transfers: impl FnOnce(Option<gpu_gkr::DrTailProofPlan>) -> T,
) -> CudaResult<T> {
    let Some(request) = request else {
        return Ok(construct_transfers(None));
    };
    validate_windowed_schedule(request.gkr_programs, request.prover_config);
    let plan = gpu_gkr::preflight_dr_tail_resources(
        request.gkr_programs,
        request.final_trace_size_log_2,
        request.device_id,
    )?;
    Ok(construct_transfers(Some(plan)))
}

/// Enqueues one `prove()` phase on exec, timed by a range named `name`.
fn run_phase<R>(
    name: &str,
    ranges: &mut Vec<Range>,
    context: &ProverContext,
    phase: impl FnOnce() -> CudaResult<R>,
) -> CudaResult<R> {
    let stream = context.get_exec_stream();
    let range = Range::new(name)?;
    let result = context.enqueue_phase(|| range.start(stream), phase)?;
    range.end(stream)?;
    ranges.push(range);
    Ok(result)
}

/// Enqueue a proof with explicit representation choices. Setup and memory
/// always defer materialization until their separate query phases.
pub fn prove<'a, A: GoodAllocator + 'a>(
    gkr_programs: &Arc<GkrPrograms>,
    prover_config: &ProverConfig,
    final_trace_size_log_2: u32,
    inputs: GpuGKRProofTransfer<'a, A>,
    dr_tail_plan: &gpu_gkr::DrTailProofPlan,
    memory_policy: ProofMemoryPolicy,
    context: &ProverContext,
) -> CudaResult<GpuGKRProofJob<'a>> {
    prove_inner(
        gkr_programs,
        prover_config,
        final_trace_size_log_2,
        inputs,
        dr_tail_plan,
        memory_policy,
        None,
        context,
    )
}

#[cfg(test)]
pub(crate) fn prove_stagewise<'a, A: GoodAllocator + 'a>(
    gkr_programs: &Arc<GkrPrograms>,
    prover_config: &ProverConfig,
    final_trace_size_log_2: u32,
    inputs: GpuGKRProofTransfer<'a, A>,
    context: &ProverContext,
) -> CudaResult<GpuGKRProofJob<'a>> {
    let dr_tail_plan = gpu_gkr::preflight_dr_tail_resources(
        gkr_programs,
        final_trace_size_log_2,
        era_cudart::device::get_device()?,
    )?;
    prove_inner(
        gkr_programs,
        prover_config,
        final_trace_size_log_2,
        inputs,
        &dr_tail_plan,
        ProofMemoryPolicy::default(),
        Some(Box::default()),
        context,
    )
}

fn prove_inner<'a, A: GoodAllocator + 'a>(
    gkr_programs: &Arc<GkrPrograms>,
    prover_config: &ProverConfig,
    final_trace_size_log_2: u32,
    inputs: GpuGKRProofTransfer<'a, A>,
    dr_tail_plan: &gpu_gkr::DrTailProofPlan,
    memory_policy: ProofMemoryPolicy,
    mut stage_snapshots: Option<Box<GKRBackwardStageSnapshotSink>>,
    context: &ProverContext,
) -> CudaResult<GpuGKRProofJob<'a>> {
    assert!(
        memory_policy.witness.is_valid(),
        "invalid witness memory policy"
    );
    dr_tail_plan.validate_before_enqueue(gkr_programs, final_trace_size_log_2, context);
    let compiled_circuit = gkr_programs.compiled_circuit().as_ref();
    validate_windowed_schedule(gkr_programs, prover_config);
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
        top_bits,
        top_bits_host,
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
    // memory caps, top_bits, external_challenges).
    transfer.ensure_transferred(context)?;

    let stream = context.get_exec_stream();
    let mut callbacks = Callbacks::new();
    let mut proof = Box::new(None);
    let proof_handle = UnsafeMutAccessor::new(proof.as_mut());
    let mut ranges = Vec::new();
    let proof_range = Range::new("gkr.proof")?;
    proof_range.start(stream)?;

    context.reset_used_mem_peak();

    let replay = context.cuda_graph_mode() == CudaGraphMode::Replay;
    assert!(
        !replay || stage_snapshots.is_none(),
        "graph replay does not support backward stage snapshots"
    );
    let (replay_ranges, trace_cycles) = proof_replay_inputs(
        setup.as_ref(),
        decoder.as_ref(),
        inits_and_teardowns.as_ref(),
        tracing_data.as_ref(),
        &memory,
        top_bits.as_ref(),
        &external_challenges,
    );
    let mut replay_values = ReplayInputs::default();
    if let Some(cycles) = trace_cycles {
        replay_values.insert(TraceCycles(cycles));
    }
    if let Some(it) = inits_and_teardowns.as_ref() {
        replay_values.insert(InitsAndTeardownsPages(
            it.data_device.page_indices.len() as u32
        ));
    }
    replay_values.insert(GkrReplayValues {
        external_challenges: external_challenges.value,
        inits_and_teardowns_top_bits: top_bits_host.clone(),
    });

    let compute = |ranges: &mut Vec<Range>| -> CudaResult<ComputeOutputs> {
        let Stage1AndForwardPreparation {
            mut stage1_output,
            mut synthetic_setup_trace_holder,
            proof_layout,
            proof_slab,
            mut forward_setup,
            d_seed,
        } = run_phase("gkr.proof.stage1", ranges, context, || {
            prepare_stage1_and_forward_setup::<A>(
                gkr_programs,
                prover_config,
                final_trace_size_log_2,
                whir_schedule,
                BundleDeviceRefs {
                    setup: setup.as_ref(),
                    decoder: decoder.as_ref(),
                    inits_and_teardowns: inits_and_teardowns.as_ref(),
                    memory: &memory,
                    top_bits_device: top_bits.as_ref(),
                    external_challenges_device: &external_challenges.device,
                },
                tracing_data.as_ref(),
                memory_policy.witness,
                context,
            )
        })?;
        // Their final device readers are enqueued; Transfer still owns the H2D sources.
        drop(tracing_data);
        drop(inits_and_teardowns);
        drop(decoder);

        let output_evaluations_slab =
            unsafe { proof_layout.output_evaluations_device_mut(proof_slab.as_ptr() as *mut u8) }
                .map(|(ptr, len)| {
                    assert_eq!(
                ptr,
                proof_slab.as_ptr() as *mut E4,
                "output_evaluations must be the proof slab prefix for direct forward writes",
            );
                    ForwardOutputSlabTarget {
                        backing: Arc::clone(&proof_slab),
                        len,
                    }
                });
        let forward_output = run_phase("gkr.proof.forward", ranges, context, || {
            schedule_forward_pass(
                setup.as_ref().map(|setup| &setup.trace_holder),
                synthetic_setup_trace_holder.as_ref(),
                &mut stage1_output,
                &mut forward_setup,
                &external_challenges.value,
                &top_bits_host,
                final_trace_size_log_2,
                output_evaluations_slab,
                gkr_programs,
                memory_policy.gkr,
                context,
            )
        })?;
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
        } = run_phase("gkr.proof.handoff", ranges, context, || {
            prepare_backward_handoff(
                forward_output,
                forward_setup,
                d_seed,
                final_trace_size_log_2,
                context,
            )
        })?;

        ranges.push(post_forward_handoff_range);

        let BackwardPhaseResult {
            mut backward_scheduled,
        } = run_phase("gkr.proof.backward", ranges, context, || {
            schedule_backward_phase(
                backward_state,
                top_bits_host.clone(),
                Arc::clone(gkr_programs),
                dr_tail_plan,
                external_challenges.device.as_ptr(),
                d_seed,
                d_evaluation_point_and_batching,
                initial_d_claims,
                top_layer_claim_layout,
                d_lookup_challenges_for_backward,
                &proof_slab,
                &proof_layout,
                stage_snapshots.as_deref_mut().map(UnsafeMutAccessor::new),
                &mut callbacks,
                context,
            )
        })?;
        let batching_pow_bits =
            crate::config::batched_proximity_check_pow_bits(prover_config, compiled_circuit);
        let WhirPhaseResult {
            base_layer_claims_scheduled,
            whir_scheduled,
        } = run_phase("gkr.proof.whir", ranges, context, || {
            schedule_whir_phase(
                compiled_circuit,
                whir_schedule,
                &mut setup,
                &mut synthetic_setup_trace_holder,
                &mut stage1_output,
                &mut backward_scheduled,
                &proof_slab,
                &proof_layout,
                batching_pow_bits,
                memory_policy,
                context,
            )
        })?;
        Ok(ComputeOutputs {
            stage1_output,
            synthetic_setup_trace_holder,
            proof_layout,
            proof_slab,
            forward_setup_keepalive,
            transcript_handoff,
            backward_scheduled,
            base_layer_claims_scheduled,
            whir_scheduled,
        })
    };

    let computed = if replay {
        let key = format!(
            "prove|{:?}|{prover_config:?}|{final_trace_size_log_2}|{memory_policy:?}",
            gkr_programs.circuit_type()
        );
        context.replay_phase(
            &key,
            &replay_ranges,
            &[],
            &replay_values,
            || Ok(()),
            || compute(&mut ranges),
            TerminalMetadata::of,
        )?
    } else {
        PhaseOutcome::Executed(compute(&mut ranges)?)
    };
    let (terminal, computed) = match computed {
        PhaseOutcome::Executed(outputs) => (TerminalMetadata::of(&outputs), Some(outputs)),
        PhaseOutcome::Replayed(terminal) => (terminal, None),
    };

    let proof_host_mirror = Some(schedule_terminal_proof_assembly(
        terminal.slab as *const E4,
        &terminal.proof_layout,
        proof_handle,
        whir_schedule.clone(),
        terminal.extras,
        external_challenges.value,
        // The ACTUAL per-circuit top bits (all-zero for trivial unified
        // chunks): they land in `GKRProof::inits_and_teardowns_top_bits`,
        // which the full-statement verifier asserts to be zero for the
        // leading (dummy) unified instances.
        top_bits_host.clone(),
        &mut callbacks,
        context,
    )?);

    {
        let event = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
        event.record(stream)?;
        context
            .get_h2d_stream()
            .wait_event(&event, CudaStreamWaitEventFlags::DEFAULT)?;
    }

    proof_range.end(stream)?;
    ranges.push(proof_range);

    // All device readers are enqueued on exec, so these reservations can be
    // reused by subsequent stream work. Input reservations drop at function
    // exit; the returned job retains host data and callback owners through finish().
    let compute_keepalive = computed.map(|outputs| {
        let ComputeOutputs {
            stage1_output,
            synthetic_setup_trace_holder,
            proof_layout: _,
            proof_slab,
            forward_setup_keepalive,
            transcript_handoff,
            mut backward_scheduled,
            mut base_layer_claims_scheduled,
            whir_scheduled,
        } = outputs;
        drop(transcript_handoff);
        drop(synthetic_setup_trace_holder);
        // `backward_scheduled` itself is the keepalive — the per-layer device
        // handles were already taken by the orchestrator, and the
        // callbacks/tracing/host-staging buffers all ride on this struct.
        backward_scheduled.release_device_buffers();
        base_layer_claims_scheduled.release_device_buffers();
        // Proof slab: last scheduled use is the terminal D2H on exec_stream.
        drop(proof_slab);
        ComputeKeepalive {
            _stage1: stage1_output.into_keepalive(),
            _forward_setup: forward_setup_keepalive,
            _backward: backward_scheduled,
            _base_layer_claims: base_layer_claims_scheduled,
            _whir: whir_scheduled,
        }
    });

    let is_finished_event = CudaEvent::create_with_flags(
        CudaEventCreateFlags::DISABLE_TIMING | CudaEventCreateFlags::BLOCKING_SYNC,
    )?;
    is_finished_event.record(stream)?;

    let inputs_keepalive = inputs::GpuGKRProofTransferKeepalive {
        _setup_host: setup.as_ref().map(|setup| Arc::clone(&setup.host)),
        _transfer: transfer.into_keepalive(),
    };

    Ok(GpuGKRProofJob {
        is_finished_event,
        callbacks,
        proof,
        ranges,
        stage_snapshots,
        keepalive: GpuGKRProofJobKeepalive {
            _compute: compute_keepalive,
            _inputs: inputs_keepalive,
            _proof_host_mirror: proof_host_mirror,
        },
    })
}

/// Phase results the terminal assembly and the job keepalive need.
struct ComputeOutputs {
    stage1_output: GpuGKRStage1Output,
    synthetic_setup_trace_holder: Option<TraceHolder<BF>>,
    proof_layout: ProofLayout,
    proof_slab: Arc<DeviceAllocation<E4>>,
    forward_setup_keepalive: GpuGKRForwardSetupHostKeepalive,
    transcript_handoff: GpuGKRTranscriptHandoff<E4>,
    backward_scheduled: GpuGKRBackwardScheduledExecution,
    base_layer_claims_scheduled: GpuGKRBaseLayerClaimsScheduledExecution,
    whir_scheduled: GpuWhirFoldScheduledExecution,
}

/// What the terminal assembly reads, fixed per replay key.
#[derive(Clone)]
struct TerminalMetadata {
    slab: usize,
    proof_layout: ProofLayout,
    extras: BaseLayerExtrasLayout,
}

impl TerminalMetadata {
    fn of(outputs: &ComputeOutputs) -> Self {
        Self {
            slab: outputs.proof_slab.as_ptr() as usize,
            proof_layout: outputs.proof_layout.clone(),
            extras: outputs.base_layer_claims_scheduled.extras_layout(),
        }
    }
}

/// Device ranges a proof graph reads, and the visible trace length.
fn proof_replay_inputs<A: GoodAllocator>(
    setup: Option<&GpuGKRSetupTransfer<'_>>,
    decoder: Option<&DecoderTableTransfer<'_>>,
    inits_and_teardowns: Option<&InitsAndTeardownsTransfer<'_, A>>,
    tracing_data: Option<&TracingDataTransfer<'_, A>>,
    memory: &GpuGKRMemoryTransfer<'_>,
    top_bits: Option<&DeviceAllocation<u32>>,
    external_challenges: &inputs::ExternalChallengesTransfer<'_>,
) -> (Vec<(usize, usize)>, Option<u32>) {
    let mut ranges = Vec::new();
    let mut cycles = None;
    if let Some(setup) = setup {
        ranges.extend(setup.trace_holder.device_ranges());
    }
    if let Some(decoder) = decoder {
        ranges.push(device_range(&decoder.data_device));
    }
    if let Some(it) = inits_and_teardowns {
        ranges.extend([
            device_range(&it.data_device.page_indices),
            device_range(&it.data_device.values_packed),
            device_range(&it.data_device.timestamps_packed),
        ]);
    }
    if let Some(tracing_data) = tracing_data {
        let (range, len) = tracing_data.data_device.range_and_len();
        ranges.push(range);
        cycles = Some(len as u32);
    }
    ranges.push(device_range(memory.unified_device_cap()));
    if let Some(top_bits) = top_bits {
        ranges.push(device_range(top_bits));
    }
    ranges.push(device_range(&external_challenges.device));
    (ranges, cycles)
}
