pub mod inputs;
mod orchestration;

use std::sync::Arc;

use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
use era_cudart::stream::CudaStreamWaitEventFlags;
use fft::GoodAllocator;

use crate::proof::inputs::GpuGKRProofTransfer;
use crate::upstream::{validate_sumcheck_schedule, ProverConfig, SumcheckScheduleClass};
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::context::UnsafeMutAccessor;
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::E4;
use gpu_gkr::backward::GKRBackwardStageSnapshotSink;
use gpu_gkr::forward::{schedule_forward_pass, ForwardOutputSlabTarget};
use gpu_gkr::{
    backward_execution_strategy, main_continuation_window_count, BackwardExecutionStrategy,
    GkrBackwardOptions, GkrPrograms, MainContinuationWindowLoweringRejection,
    MainLayerExecutionPlanError, MainLayerScheduleError, MainTailLoweringRejection,
    WindowLoweringRejection,
};
#[cfg(all(feature = "task8_continuation_differential_test", not(no_cuda)))]
use gpu_prover_context::DeviceMemoryHighWaterObserver;
use gpu_prover_context::ProverContext;

pub use orchestration::GpuGKRProofJob;
use orchestration::{
    prepare_backward_handoff, prepare_stage1_and_forward_setup, schedule_backward_phase,
    schedule_terminal_proof_assembly, schedule_whir_phase, stage1_forward::BundleDeviceRefs,
    BackwardPhaseResult, ForwardToBackwardHandoff, GpuGKRProofJobKeepalive,
    Stage1AndForwardPreparation, WhirPhaseResult,
};

/// A typed preflight or enqueue-time proof failure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GpuProveError {
    Cuda(era_cudart_sys::CudaError),
    WindowLowering {
        circuit: String,
        layer: usize,
        resource: String,
    },
    MainContinuationWindowLowering {
        circuit: String,
        layer: usize,
        resource: String,
    },
    MainTailLowering {
        circuit: String,
        layer: usize,
        resource: String,
    },
    MainLayerExecutionPlan {
        error: MainLayerExecutionPlanError,
    },
    MainLayerSchedule {
        error: MainLayerScheduleError,
    },
}

impl std::fmt::Display for GpuProveError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Cuda(error) => write!(formatter, "CUDA proof scheduling failed: {error:?}"),
            Self::WindowLowering {
                circuit,
                layer,
                resource,
            } => write!(
                formatter,
                "windowed R0 lowering rejected for {circuit}/{layer}: {resource}"
            ),
            Self::MainContinuationWindowLowering {
                circuit,
                layer,
                resource,
            } => write!(
                formatter,
                "main continuation window lowering rejected for {circuit}/{layer}: {resource}"
            ),
            Self::MainTailLowering {
                circuit,
                layer,
                resource,
            } => write!(
                formatter,
                "main-tail lowering rejected for {circuit}/{layer}: {resource}"
            ),
            Self::MainLayerExecutionPlan { error } => {
                write!(formatter, "main-layer execution plan rejected: {error:?}")
            }
            Self::MainLayerSchedule { error } => {
                write!(formatter, "main-layer scheduling rejected: {error}")
            }
        }
    }
}

impl std::error::Error for GpuProveError {}

impl From<era_cudart_sys::CudaError> for GpuProveError {
    fn from(error: era_cudart_sys::CudaError) -> Self {
        Self::Cuda(error)
    }
}

impl From<MainLayerScheduleError> for GpuProveError {
    fn from(error: MainLayerScheduleError) -> Self {
        Self::MainLayerSchedule { error }
    }
}

impl From<&WindowLoweringRejection> for GpuProveError {
    fn from(rejection: &WindowLoweringRejection) -> Self {
        Self::WindowLowering {
            circuit: rejection.circuit.clone(),
            layer: rejection.layer,
            resource: rejection.resource.clone(),
        }
    }
}

impl From<&MainContinuationWindowLoweringRejection> for GpuProveError {
    fn from(rejection: &MainContinuationWindowLoweringRejection) -> Self {
        Self::MainContinuationWindowLowering {
            circuit: rejection.circuit.clone(),
            layer: rejection.layer,
            resource: rejection.resource.clone(),
        }
    }
}

impl From<&MainTailLoweringRejection> for GpuProveError {
    fn from(rejection: &MainTailLoweringRejection) -> Self {
        Self::MainTailLowering {
            circuit: rejection.circuit.clone(),
            layer: rejection.layer,
            resource: rejection.resource.clone(),
        }
    }
}

/// The main-layer arm this proof request runs, from the caller's options and the
/// prover config's validated same-size schedule. Pure; `prove()` computes the
/// same value and logs a requested-but-unavailable window once per proof.
pub fn resolve_backward_execution_strategy(
    gkr_programs: &GkrPrograms,
    prover_config: &ProverConfig,
    options: GkrBackwardOptions,
) -> BackwardExecutionStrategy {
    backward_execution_strategy(
        options,
        validated_schedule_class(gkr_programs, prover_config),
    )
}

/// Production-only resolver. An enabled production request is never
/// converted into the legacy per-round strategy: a schedule that cannot run
/// the complete windowed MAIN chain is rejected before transfer construction.
pub fn resolve_backward_execution_strategy_checked(
    gkr_programs: &GkrPrograms,
    prover_config: &ProverConfig,
    options: GkrBackwardOptions,
) -> Result<BackwardExecutionStrategy, GpuProveError> {
    if !options.windowed_r0 {
        return Ok(BackwardExecutionStrategy::PerRound);
    }
    if validated_schedule_class(gkr_programs, prover_config)
        != Some(SumcheckScheduleClass::Windowed)
    {
        return Err(GpuProveError::MainLayerExecutionPlan {
            error: MainLayerExecutionPlanError::WindowedStrategyUnavailable,
        });
    }
    Ok(BackwardExecutionStrategy::WindowedR0)
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

/// Resolve every lazy bundle selected by the full backward options before any
/// proof H2D transfer is constructed or scheduled. A per-round strategy does
/// not lower either main-window family.
pub fn preflight_windowed_backward(
    gkr_programs: &GkrPrograms,
    strategy: BackwardExecutionStrategy,
    options: GkrBackwardOptions,
    final_trace_size_log_2: u32,
) -> Result<(), GpuProveError> {
    // Reserved for later DR bundle checks. Main-layer geometry belongs to the
    // compiled circuit and must not be inferred from the final reduced trace.
    let _ = final_trace_size_log_2;
    if options.windowed_r0 && matches!(strategy, BackwardExecutionStrategy::PerRound) {
        return Err(GpuProveError::MainLayerExecutionPlan {
            error: MainLayerExecutionPlanError::WindowedStrategyUnavailable,
        });
    }
    match strategy {
        BackwardExecutionStrategy::PerRound => {}
        BackwardExecutionStrategy::WindowedR0 => gkr_programs
            .resolve_window_programs()
            .map(|_| ())
            .map_err(GpuProveError::from)?,
    }
    let window_count =
        main_continuation_window_count(options, strategy, main_folding_steps(gkr_programs))
            .map_err(|error| GpuProveError::MainLayerExecutionPlan { error })?;
    if gpu_gkr::production_main_chain_selected(options, strategy) {
        gkr_programs
            .resolve_main_continuation_window_programs()
            .map(|_| ())
            .map_err(GpuProveError::from)?;
        gkr_programs
            .resolve_main_tail_programs()
            .map(|_| ())
            .map_err(GpuProveError::from)?;
    }
    Ok(())
}

#[cfg(test)]
pub(crate) fn construct_after_windowed_backward_preflight<T>(
    gkr_programs: &GkrPrograms,
    strategy: BackwardExecutionStrategy,
    options: GkrBackwardOptions,
    final_trace_size_log_2: u32,
    construct_transfers: impl FnOnce() -> T,
) -> Result<T, GpuProveError> {
    preflight_windowed_backward(gkr_programs, strategy, options, final_trace_size_log_2)?;
    Ok(construct_transfers())
}

pub fn prove<'a, A: GoodAllocator + 'a>(
    gkr_programs: &Arc<GkrPrograms>,
    prover_config: &ProverConfig,
    final_trace_size_log_2: u32,
    inputs: GpuGKRProofTransfer<'a, A>,
    backward_options: GkrBackwardOptions,
    context: &ProverContext,
) -> Result<GpuGKRProofJob<'a, A>, GpuProveError> {
    prove_inner(
        gkr_programs,
        prover_config,
        final_trace_size_log_2,
        inputs,
        backward_options,
        None,
        #[cfg(all(feature = "task8_continuation_differential_test", not(no_cuda)))]
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
    backward_options: GkrBackwardOptions,
    context: &ProverContext,
) -> Result<GpuGKRProofJob<'a, A>, GpuProveError> {
    prove_inner(
        gkr_programs,
        prover_config,
        final_trace_size_log_2,
        inputs,
        backward_options,
        Some(Box::default()),
        #[cfg(all(feature = "task8_continuation_differential_test", not(no_cuda)))]
        None,
        context,
    )
}

#[cfg(all(feature = "task8_continuation_differential_test", not(no_cuda)))]
pub(crate) fn prove_main_continuation_differential<'a, A: GoodAllocator + 'a>(
    gkr_programs: &Arc<GkrPrograms>,
    prover_config: &ProverConfig,
    final_trace_size_log_2: u32,
    inputs: GpuGKRProofTransfer<'a, A>,
    backward_options: GkrBackwardOptions,
    sink: Box<GKRBackwardStageSnapshotSink>,
    context: &ProverContext,
) -> Result<GpuGKRProofJob<'a, A>, GpuProveError> {
    prove_inner(
        gkr_programs,
        prover_config,
        final_trace_size_log_2,
        inputs,
        backward_options,
        Some(sink),
        None,
        context,
    )
}

#[cfg(all(feature = "task8_continuation_differential_test", not(no_cuda)))]
pub(crate) fn prove_with_exact_memory<'a, 'context, A: GoodAllocator + 'a>(
    gkr_programs: &Arc<GkrPrograms>,
    prover_config: &ProverConfig,
    final_trace_size_log_2: u32,
    inputs: GpuGKRProofTransfer<'a, A>,
    backward_options: GkrBackwardOptions,
    sink: Box<GKRBackwardStageSnapshotSink>,
    context: &'context ProverContext,
) -> Result<
    (
        GpuGKRProofJob<'a, A>,
        DeviceMemoryHighWaterObserver<'context>,
    ),
    GpuProveError,
> {
    let mut backward_observer = None;
    let job = prove_inner(
        gkr_programs,
        prover_config,
        final_trace_size_log_2,
        inputs,
        backward_options,
        Some(sink),
        Some(&mut backward_observer),
        context,
    )?;
    Ok((
        job,
        backward_observer.expect("exact-memory prove must start its backward observer"),
    ))
}

fn prove_inner<'a, 'context, A: GoodAllocator + 'a>(
    gkr_programs: &Arc<GkrPrograms>,
    prover_config: &ProverConfig,
    final_trace_size_log_2: u32,
    inputs: GpuGKRProofTransfer<'a, A>,
    backward_options: GkrBackwardOptions,
    mut stage_snapshots: Option<Box<GKRBackwardStageSnapshotSink>>,
    #[cfg(all(feature = "task8_continuation_differential_test", not(no_cuda)))]
    mut backward_observer_out: Option<&mut Option<DeviceMemoryHighWaterObserver<'context>>>,
    context: &'context ProverContext,
) -> Result<GpuGKRProofJob<'a, A>, GpuProveError> {
    let compiled_circuit = gkr_programs.compiled_circuit().as_ref();
    let backward_strategy =
        resolve_backward_execution_strategy_checked(gkr_programs, prover_config, backward_options)?;
    match backward_strategy {
        BackwardExecutionStrategy::PerRound if backward_options.windowed_r0 => {
            return Err(GpuProveError::MainLayerExecutionPlan {
                error: MainLayerExecutionPlanError::WindowedStrategyUnavailable,
            });
        }
        BackwardExecutionStrategy::WindowedR0 => assert!(
            gkr_programs.window_programs_ready(),
            "prove() with the windowed arm requires preflight_windowed_backward first"
        ),
        BackwardExecutionStrategy::PerRound => {}
    }
    let _continuation_window_count = main_continuation_window_count(
        backward_options,
        backward_strategy,
        main_folding_steps(gkr_programs),
    )
    .expect("prove() requires a main-layer execution plan accepted by preflight");
    if gpu_gkr::production_main_chain_selected(backward_options, backward_strategy) {
        assert!(
            gkr_programs.main_continuation_window_programs_ready(),
            "the production main chain requires continuation preflight"
        );
        assert!(
            gkr_programs.main_tail_programs_ready(),
            "the production main chain requires main-tail preflight"
        );
    }
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

    let Stage1AndForwardPreparation {
        mut stage1_output,
        mut synthetic_setup_trace_holder,
        proof_layout,
        proof_slab,
        mut forward_setup,
        d_seed,
    } = prepare_stage1_and_forward_setup::<A>(
        gkr_programs,
        prover_config,
        final_trace_size_log_2,
        whir_schedule,
        BundleDeviceRefs {
            setup: setup.as_ref(),
            decoder: decoder.as_ref(),
            inits_and_teardowns: inits_and_teardowns.as_ref(),
            memory: &memory,
            top_bits_device: top_bits.as_ref().map(|t| &t.device),
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
        &external_challenges.value,
        &top_bits_host,
        final_trace_size_log_2,
        output_evaluations_slab,
        gkr_programs,
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

    ranges.push(post_forward_handoff_range);

    #[cfg(all(feature = "task8_continuation_differential_test", not(no_cuda)))]
    if let Some(observer_out) = backward_observer_out.as_deref_mut() {
        assert!(observer_out.is_none());
        *observer_out = Some(context.observe_device_memory_high_water());
    }

    let BackwardPhaseResult {
        mut backward_scheduled,
    } = schedule_backward_phase(
        backward_state,
        top_bits_host.clone(),
        Arc::clone(gkr_programs),
        backward_options,
        backward_strategy,
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
    )?;
    #[cfg(all(feature = "task8_continuation_differential_test", not(no_cuda)))]
    if let Some(observer) = backward_observer_out
        .as_deref_mut()
        .and_then(Option::as_mut)
    {
        observer.seal();
    }
    let batching_pow_bits =
        crate::config::batched_proximity_check_pow_bits(prover_config, compiled_circuit);
    let WhirPhaseResult {
        transition_ranges,
        mut base_layer_claims_scheduled,
        base_layer_claims_shared_state,
        mut whir_scheduled,
    } = schedule_whir_phase(
        compiled_circuit,
        whir_schedule,
        &mut setup,
        &mut synthetic_setup_trace_holder,
        &mut stage1_output,
        &mut backward_scheduled,
        &proof_slab,
        &proof_layout,
        batching_pow_bits,
        context,
    )?;
    ranges.extend(transition_ranges);

    // `backward_scheduled` itself is the keepalive — the per-layer device
    // handles were already taken by the orchestrator (or remain as `Some`
    // for the proof-lifetime final-seed/claim-point buffers), and the
    // callbacks/tracing/host-staging buffers all ride on this struct.
    let mut backward_keepalive = backward_scheduled;

    let proof_host_mirror = Some(schedule_terminal_proof_assembly(
        &proof_slab,
        &proof_layout,
        proof_handle,
        whir_schedule.clone(),
        base_layer_claims_shared_state,
        external_challenges.value,
        // The ACTUAL per-circuit top bits (all-zero for trivial unified
        // chunks): they land in `GKRProof::inits_and_teardowns_top_bits`,
        // which the full-statement verifier asserts to be zero for the
        // leading (dummy) unified instances.
        top_bits_host.clone(),
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

    // Release the device reservations whose last scheduled use is inside
    // prove(), so the job returns to the caller holding only the inputs it was
    // given plus host bookkeeping — i.e. used device memory after prove()
    // equals used device memory before it. The allocator pool is a reservation
    // tracker (immediate bookkeeping release); physical safety is exec-stream
    // ordering, so the next proof's exec-stream work serializes after this
    // proof's and can reuse these regions. Only host bits — pending callbacks,
    // base-layer claim metadata, and the pinned proof host mirror read by the
    // terminal callback — ride on to finish(). Each release is a single statement so an
    // individual buffer class can be re-retained when bisecting a
    // multi-schedule regression.
    //
    // Synthetic setup trace holder (when present): its last scheduled use is
    // the WHIR open of the setup commitment in schedule_whir_phase. Drop it
    // explicitly here rather than leaving it to function-scope drop.
    drop(synthetic_setup_trace_holder);
    // Real setup commitment: the WHIR open materializes its LDE cosets
    // on-demand (~the trace's full LDE). Those cosets are prove-internal — once
    // the open kernels are scheduled they are dead — but the setup wrapper
    // itself (raw hypercube evals + cached partial trees + unified cap) is a
    // caller-provided input that rides on in `_inputs`. Release just the cosets
    // so prove()'s net device footprint is zero without freeing the input.
    if let Some(setup) = setup.as_mut() {
        setup.trace_holder.release_cosets();
    }
    backward_keepalive.release_device_buffers();
    base_layer_claims_scheduled.release_device_buffers();
    whir_scheduled.release_device_buffers();
    // Proof slab: last scheduled use is the terminal D2H on exec_stream.
    drop(proof_slab);

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
        top_bits,
        top_bits_host,
        external_challenges,
    }
    .into_keepalive();

    Ok(GpuGKRProofJob {
        is_finished_event,
        callbacks,
        proof,
        ranges,
        stage_snapshots,
        keepalive: GpuGKRProofJobKeepalive {
            _stage1: stage1_output.into_keepalive(),
            _inputs: inputs_keepalive,
            _forward_setup: forward_setup_keepalive,
            _backward: backward_keepalive,
            _base_layer_claims: base_layer_claims_scheduled,
            _whir: whir_scheduled,
            _proof_host_mirror: proof_host_mirror,
        },
    })
}

#[cfg(test)]
mod tests;
