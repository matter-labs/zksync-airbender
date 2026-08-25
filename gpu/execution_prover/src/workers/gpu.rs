use crate::messages::{
    GpuWorkRequest, GpuWorkResult, MemoryCommitmentRequest, MemoryCommitmentResult, ProofRequest,
    ProofResult, SetupInitializationRequest, SetupInitializationResult,
};
use crate::precomputations::CircuitPrecomputations;
use crate::A;
use crossbeam_channel::{Receiver, Sender};
use era_cudart::device::{get_device_properties, set_device};
use era_cudart::result::CudaResult;
use gpu_circuit_prover::proof::{
    admit_dr_tail_before_transfers, resolve_backward_execution_strategy, DrTailPreflightRequest,
    ExactMemoryConfig, GpuGKRProofJob, GpuProveError, GpuProveResult,
};
use gpu_core::primitives::field::{BF, E4};
use gpu_gkr::setup::GpuGKRSetupTransfer;
use gpu_gkr::{DrTailEntrySelection, GkrBackwardOptions, WindowTailArm};
use gpu_prover_context::{ProverContext, ProverContextConfig};
use gpu_trace::trace::decoder::DecoderTableTransfer;
use gpu_trace::trace::memory::{commit_memory_from_transfers, MemoryCommitmentJob};
use gpu_trace::trace::memory_transfer::{GpuGKRMemoryTransfer, GpuGKRMemoryTransferHost};
use gpu_trace::trace::tracing_data::{InitsAndTeardownsTransfer, TracingDataTransfer};
use gpu_trace::witness::circuit_type::CircuitType;
use gpu_trace::witness::trace_unrolled::InitsAndTeardownsTraceHost;
use log::{debug, error, info, trace};

use crate::upstream::{GKRExternalChallenges, MerkleTreeCapVarLength, SecurityLevel};
use std::collections::VecDeque;
use std::ffi::CStr;
use std::mem;
use std::process::exit;
use std::sync::Arc;

pub(crate) fn get_gpu_worker_func(
    device_id: i32,
    prover_context_config: ProverContextConfig,
    is_initialized: Sender<()>,
    requests: Receiver<Option<GpuWorkRequest<A>>>,
    results: Sender<Option<GpuWorkResult<A>>>,
) -> impl FnOnce() + Send + 'static {
    move || {
        let result = gpu_worker(
            device_id,
            prover_context_config,
            is_initialized,
            requests,
            results,
        );
        if let Err(e) = result {
            error!("GPU_WORKER[{device_id}] worker encountered an error: {e}");
            exit(1);
        }
    }
}

const DR_TAIL_TUNING_ENV: &str = "AB_GKR_DR_TAIL";

/// Default production selects the inseparable R0/continuation/recursive-tail
/// chain. The only override is a worker-start diagnostic switch that disables
/// the whole DR layer; no scheduler, binder, or kernel reads the environment.
const PRODUCTION_BACKWARD_OPTIONS: GkrBackwardOptions = GkrBackwardOptions {
    dr_tail_megakernel: true,
    windowed_r0: true,
    windowed_main_continuations: true,
    windowed_dr: true,
    windowed_dr_continuations: true,
    window_tail: WindowTailArm::Split,
};

const LEGACY_DIAGNOSTIC_BACKWARD_OPTIONS: GkrBackwardOptions = GkrBackwardOptions {
    dr_tail_megakernel: false,
    windowed_r0: true,
    windowed_main_continuations: true,
    windowed_dr: false,
    windowed_dr_continuations: false,
    window_tail: WindowTailArm::Split,
};

#[derive(Clone, Debug, PartialEq, Eq)]
enum DrTailTuningError {
    InvalidValue(String),
    NonUnicode,
}

impl core::fmt::Display for DrTailTuningError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::InvalidValue(value) => write!(
                formatter,
                "{DR_TAIL_TUNING_ENV} must be exactly 0 or 1, got {value:?}"
            ),
            Self::NonUnicode => write!(formatter, "{DR_TAIL_TUNING_ENV} must be valid UTF-8"),
        }
    }
}

fn backward_options_from_tail_tuning(
    value: Option<&str>,
) -> Result<GkrBackwardOptions, DrTailTuningError> {
    match value {
        None | Some("1") => Ok(PRODUCTION_BACKWARD_OPTIONS),
        Some("0") => Ok(LEGACY_DIAGNOSTIC_BACKWARD_OPTIONS),
        Some(value) => Err(DrTailTuningError::InvalidValue(value.to_owned())),
    }
}

fn backward_options_from_environment() -> Result<GkrBackwardOptions, DrTailTuningError> {
    match std::env::var_os(DR_TAIL_TUNING_ENV) {
        None => backward_options_from_tail_tuning(None),
        Some(value) => value
            .into_string()
            .map_err(|_| DrTailTuningError::NonUnicode)
            .and_then(|value| backward_options_from_tail_tuning(Some(&value))),
    }
}

const FINAL_TRACE_SIZE_LOG_2: u32 = 4;

#[cfg(test)]
mod task7_tests {
    use super::*;

    #[test]
    fn cpu_task7_worker_tail_tuning_is_single_value_and_whole_layer() {
        let production = backward_options_from_tail_tuning(None).unwrap();
        let forced_production = backward_options_from_tail_tuning(Some("1")).unwrap();
        let legacy = backward_options_from_tail_tuning(Some("0")).unwrap();

        assert_eq!(production, forced_production);
        assert!(production.dr_tail_megakernel);
        assert!(production.windowed_r0);
        assert!(production.windowed_main_continuations);
        assert!(production.windowed_dr);
        assert!(production.windowed_dr_continuations);
        assert!(!legacy.dr_tail_megakernel);
        assert!(legacy.windowed_r0);
        assert!(legacy.windowed_main_continuations);
        assert!(!legacy.windowed_dr);
        assert!(!legacy.windowed_dr_continuations);
        assert_eq!(
            backward_options_from_tail_tuning(Some("invalid")),
            Err(DrTailTuningError::InvalidValue("invalid".to_owned())),
        );
    }
}

enum RequestKind {
    MemoryCommitment,
    Proof,
    SetupInitialization,
}

/// Per-request bookkeeping carried across all three phases. Owns the
/// precomputations Arc (which holds the compiled circuit, lazy-init setup
/// host, and optional decoder host), so it outlives any Phase-2 borrow,
/// and the original host data the orchestrator expects back on the
/// memory-commit path.
struct RequestState {
    batch_id: u64,
    circuit_type: CircuitType,
    sequence_id: usize,
    precomputations: CircuitPrecomputations,
    kind: RequestKind,
    /// Set only for Proof requests; consumed in Phase 2 by `prove()`.
    external_challenges: Option<GKRExternalChallenges<BF, E4>>,
    /// Per-coset caps from a prior commit_memory phase; only present for
    /// Proof requests and consumed in Phase 1 to build the memory transfer.
    memory_caps: Option<Vec<MerkleTreeCapVarLength>>,
    /// Original host witnesses returned to the orchestrator after the GPU work
    /// completes so their allocators return to the pool.
    inits_and_teardowns_result: Option<InitsAndTeardownsTraceHost>,
    tracing_data_result: Option<gpu_trace::trace::tracing_data::TracingDataHost<A>>,
    security_level: SecurityLevel,
}

/// Phase-1 state: H2D transfers scheduled, no GPU job enqueued yet.
struct PhaseOne<'a, 'context> {
    state: RequestState,
    inputs: PhaseOneInputs<'a, 'context>,
}

/// Per-phase-1 bundle, scheduled on h2d_stream against a single shared
/// `Transfer`. Variant matches the eventual phase-2 job type.
// Short-lived per-request state moved through the worker's hot dispatch
// loop (one instance per in-flight request, swapped every iteration), not a
// long-lived collection; boxing `Proof` would add a heap alloc per request
// for no steady-state benefit.
#[allow(clippy::large_enum_variant)]
enum PhaseOneInputs<'a, 'context> {
    Proof(
        gpu_circuit_prover::proof::inputs::GpuGKRProofTransfer<'a, A>,
        Option<gpu_gkr::DrTailProofPlan>,
        Option<gpu_circuit_prover::proof::ExactMemoryGateSink<'context>>,
    ),
    MemoryCommitment(gpu_trace::trace::memory_transfer::GpuGKRCommitMemoryTransfer<'a, A>),
    SetupInitialization,
}

/// Phase-2 state: GPU job enqueued, awaiting `finish()`.
struct PhaseTwo<'a, 'context> {
    state: RequestState,
    job: JobType<'a, 'context>,
}

// Same rationale as `PhaseOneInputs` above: one instance per in-flight
// request, swapped through the worker's hot dispatch loop, so boxing `Proof`
// would add a per-request heap alloc rather than shrink a steady-state
// collection.
#[allow(clippy::large_enum_variant)]
enum JobType<'a, 'context> {
    MemoryCommitment(MemoryCommitmentJob<'a, A>),
    Proof(GpuGKRProofJob<'a, 'context, A>),
    SetupInitialization,
}

#[derive(Debug)]
enum GpuWorkerError {
    Cuda(era_cudart_sys::CudaError),
    Prove(GpuProveError),
}

impl From<era_cudart_sys::CudaError> for GpuWorkerError {
    fn from(error: era_cudart_sys::CudaError) -> Self {
        Self::Cuda(error)
    }
}

impl From<GpuProveError> for GpuWorkerError {
    fn from(error: GpuProveError) -> Self {
        Self::Prove(error)
    }
}

impl std::fmt::Display for GpuWorkerError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Cuda(error) => write!(formatter, "CUDA worker failure: {error:?}"),
            Self::Prove(error) => write!(formatter, "GPU proof failure: {error}"),
        }
    }
}

impl std::error::Error for GpuWorkerError {}

fn gpu_worker(
    device_id: i32,
    prover_context_config: ProverContextConfig,
    is_initialized: Sender<()>,
    requests: Receiver<Option<GpuWorkRequest<A>>>,
    results: Sender<Option<GpuWorkResult<A>>>,
) -> Result<(), GpuWorkerError> {
    trace!("GPU_WORKER[{device_id}] started");
    let backward_options = backward_options_from_environment()
        .unwrap_or_else(|error| panic!("GPU_WORKER[{device_id}] {error}"));
    // The complete measurement identity is resolved exactly once here, beside
    // the single arm read, and is then immutable for the worker's lifetime. No
    // proof rereads the process environment.
    let measurement = ExactMemoryConfig::from_environment(backward_options)
        .unwrap_or_else(|error| panic!("GPU_WORKER[{device_id}] {error}"));
    gpu_gkr::backward::round_timing::configure_first3_timing(
        measurement.as_ref().map(ExactMemoryConfig::timing_output),
    )
    .map_err(|message| GpuProveError::ExactMemoryMeasurement { message })?;
    if measurement.is_some() {
        info!(
            "GPU_WORKER[{device_id}] exact-memory measurement enabled; using the serialized measurement topology"
        );
    }
    set_device(device_id)?;
    let props = get_device_properties(device_id)?;
    let name = unsafe { CStr::from_ptr(props.name.as_ptr()).to_string_lossy() };
    info!(
        "GPU_WORKER[{device_id}] GPU: {} ({} SMs, {:.3} GB RAM)",
        name,
        props.multiProcessorCount,
        props.totalGlobalMem as f64 / 1024.0 / 1024.0 / 1024.0
    );
    let mut context = ProverContext::new(&prover_context_config)?;
    info!(
        "GPU_WORKER[{device_id}] initialized the GPU memory allocator with {:.3} GB of usable memory",
        context.get_mem_size() as f64 / 1024.0 / 1024.0 / 1024.0
    );
    is_initialized
        .send(())
        .expect("GPU worker initialization channel closed before readiness signal");
    drop(is_initialized);
    let mut even_odd_index = 0;
    if let Some(measurement) = measurement.as_ref() {
        // Measurement-only topology.
        //
        // The production loop below keeps two proofs in flight, so in steady
        // state proof A holds its whole observation while proof B schedules
        // phase one. That is two problems at once: the allocator admits only
        // two live observations (whole + backward already uses both), and A's
        // whole interval would absorb B's phase-one allocations, destroying
        // per-proof attribution.
        //
        // While measuring, each proof therefore runs phase one, phase two, and
        // phase three back to back, so exactly one proof ever holds
        // observations. The request/result cadence is deliberately unchanged:
        // `pending_results` reproduces the same two-deep skew the GPU manager's
        // pre-seeded queue expects, so no manager bookkeeping changes and every
        // result still lands against its own batch id.
        let mut pending_results: VecDeque<Option<GpuWorkResult<A>>> = VecDeque::from([None, None]);
        for request in requests {
            context.set_reversed_allocation_placement(even_odd_index == 1);
            let completed = if let Some(request) = request {
                let p1 = schedule_phase_one(
                    device_id,
                    &context,
                    backward_options,
                    Some(measurement),
                    request,
                )?;
                let p2 = enqueue_phase_two(device_id, &context, backward_options, p1)?;
                Some(finish_phase_three(device_id, p2)?)
            } else {
                None
            };
            even_odd_index = 1 - even_odd_index;
            pending_results.push_back(completed);
            let result = pending_results
                .pop_front()
                .expect("the measured result queue keeps one entry per iteration");
            results
                .send(result)
                .expect("GPU worker results channel closed before queued work completed")
        }
        assert!(
            pending_results.iter().all(Option::is_none),
            "every measured proof result must reach the GPU manager"
        );
        trace!("GPU_WORKER[{device_id}] finished");
        return Ok(());
    }
    let mut current_phase_one: Option<PhaseOne> = None;
    let mut current_phase_two: Option<PhaseTwo> = None;
    for request in requests {
        context.set_reversed_allocation_placement(even_odd_index == 1);
        let mut phase_one = if let Some(request) = request {
            Some(schedule_phase_one(
                device_id,
                &context,
                backward_options,
                None,
                request,
            )?)
        } else {
            None
        };
        mem::swap(&mut current_phase_one, &mut phase_one);
        context.set_reversed_allocation_placement(even_odd_index == 0);
        let mut phase_two = if let Some(p1) = phase_one {
            Some(enqueue_phase_two(
                device_id,
                &context,
                backward_options,
                p1,
            )?)
        } else {
            None
        };
        mem::swap(&mut current_phase_two, &mut phase_two);
        even_odd_index = 1 - even_odd_index;
        let result = if let Some(p2) = phase_two {
            Some(finish_phase_three(device_id, p2)?)
        } else {
            None
        };
        results
            .send(result)
            .expect("GPU worker results channel closed before queued work completed")
    }
    assert!(current_phase_one.is_none());
    assert!(current_phase_two.is_none());
    trace!("GPU_WORKER[{device_id}] finished");
    Ok(())
}

fn schedule_phase_one<'a, 'context>(
    device_id: i32,
    context: &'context ProverContext,
    backward_options: GkrBackwardOptions,
    measurement: Option<&ExactMemoryConfig>,
    request: GpuWorkRequest<A>,
) -> Result<PhaseOne<'a, 'context>, GpuWorkerError> {
    if let GpuWorkRequest::SetupInitialization(request) = request {
        let SetupInitializationRequest {
            batch_id,
            circuit_type,
            sequence_id,
            precomputations,
            security_level,
        } = request;
        trace!(
            "BATCH[{batch_id}] GPU_WORKER[{device_id}] initializing setup for circuit {circuit_type:?}[{sequence_id}]"
        );
        let timer = std::time::Instant::now();
        precomputations.setup_host.get_or_init(context)?;
        debug!(
            "BATCH[{batch_id}] GPU_WORKER[{device_id}] initialized setup for circuit {circuit_type:?}[{sequence_id}] in {:.3} ms",
            timer.elapsed().as_secs_f64() * 1e3
        );
        let state = RequestState {
            batch_id,
            circuit_type,
            sequence_id,
            precomputations,
            kind: RequestKind::SetupInitialization,
            external_challenges: None,
            memory_caps: None,
            inits_and_teardowns_result: None,
            tracing_data_result: None,
            security_level,
        };
        return Ok(PhaseOne {
            state,
            inputs: PhaseOneInputs::SetupInitialization,
        });
    }
    // Decompose the request into bookkeeping plus the host buffers that
    // become Phase 1 H2D inputs.
    let (state, inits_and_teardowns_host, tracing_data_host) = match request {
        GpuWorkRequest::MemoryCommitment(req) => {
            let MemoryCommitmentRequest {
                batch_id,
                circuit_type,
                sequence_id,
                precomputations,
                inits_and_teardowns,
                tracing_data,
                security_level,
            } = req;
            let state = RequestState {
                batch_id,
                circuit_type,
                sequence_id,
                precomputations,
                kind: RequestKind::MemoryCommitment,
                external_challenges: None,
                memory_caps: None,
                inits_and_teardowns_result: inits_and_teardowns.clone(),
                tracing_data_result: tracing_data.clone(),
                security_level,
            };
            (state, inits_and_teardowns, tracing_data)
        }
        GpuWorkRequest::Proof(req) => {
            let ProofRequest {
                batch_id,
                circuit_type,
                sequence_id,
                precomputations,
                inits_and_teardowns,
                tracing_data,
                external_challenges,
                memory_caps,
                security_level,
            } = req;
            let state = RequestState {
                batch_id,
                circuit_type,
                sequence_id,
                precomputations,
                kind: RequestKind::Proof,
                external_challenges: Some(external_challenges),
                memory_caps: Some(memory_caps),
                inits_and_teardowns_result: inits_and_teardowns.clone(),
                tracing_data_result: tracing_data.clone(),
                security_level,
            };
            (state, inits_and_teardowns, tracing_data)
        }
        GpuWorkRequest::SetupInitialization(_) => {
            unreachable!("setup initialization returns early above")
        }
    };
    let batch_id = state.batch_id;
    let circuit_type = state.circuit_type;
    let sequence_id = state.sequence_id;
    let is_proof = matches!(state.kind, RequestKind::Proof);

    // The whole-proof observation opens here: before the prover config, before
    // every preflight, and before the first transfer is constructed. The
    // measured worker topology (see `gpu_worker`) guarantees no other proof
    // holds an observation or allocates while this one is live.
    let exact_memory = if is_proof {
        measurement
            .cloned()
            .map(|config| {
                gpu_circuit_prover::proof::ExactMemoryGateSink::begin(
                    context,
                    config,
                    gpu_gkr::backward::round_timing::RoundTimingProofIdentity {
                        batch_id,
                        circuit_type: format!("{circuit_type:?}"),
                        sequence_id,
                        device_id,
                    },
                )
            })
            .transpose()?
    } else {
        None
    };
    let entry = exact_memory
        .as_ref()
        .map_or(DrTailEntrySelection::Portable, |sink| sink.entry());

    let proof_prover_config = is_proof.then(|| {
        gpu_circuit_prover::config::prover_config(circuit_type, state.security_level)
            .expect("ExecutionProverConfiguration validated GPU security level before GPU work")
    });
    // Every preflight the request needs runs at this boundary, before the
    // first transfer is constructed, so a rejection leaves no H2D allocation,
    // no enqueue, and no execution-arm selection behind.
    let preflight_request =
        proof_prover_config
            .as_ref()
            .map(|prover_config| DrTailPreflightRequest {
                gkr_programs: &state.precomputations.gkr_programs,
                strategy: resolve_backward_execution_strategy(
                    &state.precomputations.gkr_programs,
                    prover_config,
                    backward_options,
                ),
                options: backward_options,
                final_trace_size_log_2: FINAL_TRACE_SIZE_LOG_2,
                device_id,
                entry,
            });

    let mut exact_memory = exact_memory;
    let inputs = admit_dr_tail_before_transfers(
        preflight_request,
        |dr_tail_plan| -> CudaResult<PhaseOneInputs<'a, 'context>> {
            // Admission has returned, so the first production operation of a
            // measured proof is complete before any transfer is constructed.
            if let Some(sink) = exact_memory.as_mut() {
                sink.record_resource_plan(device_id, dr_tail_plan.as_ref());
                sink.record_operation("resource_preflight");
            }
            let decoder_transfer = if let Some(host) = state.precomputations.decoder_host.as_ref() {
                Some(DecoderTableTransfer::new(Arc::clone(host), context)?)
            } else {
                None
            };

            // Captured before the host buffer is consumed below. `None` covers both
            // circuits that carry no i&t at all and the TRIVIAL (dummy) leading unified
            // chunks — only a unified execution's trailing circuits hold real i&t data.
            let carried_top_bits = inits_and_teardowns_host
                .as_ref()
                .map(|host| host.top_bits.clone());

            let inits_and_teardowns_transfer = if let Some(host) = inits_and_teardowns_host {
                Some(InitsAndTeardownsTransfer::new(host, context)?)
            } else {
                None
            };

            let tracing_data_transfer = if let Some(tracing_data_host) = tracing_data_host {
                Some(TracingDataTransfer::new(tracing_data_host, context)?)
            } else {
                None
            };

            let inputs: PhaseOneInputs<'a, 'context> = if is_proof {
                let setup_transfer =
                    if let Some(setup_host) = state.precomputations.setup_host.get_initialized() {
                        Some(GpuGKRSetupTransfer::new(setup_host, context)?)
                    } else {
                        None
                    };
                // Geometry must match the configuration used to commit the caps.
                // `circuit_type.get_lde_factor()` / `get_tree_cap_size()` are derived
                // from `OPTIMAL_FOLDING_PROPERTIES` and can disagree with the
                // `prover_config` the commit phase actually used, so use the
                // prover_config geometry directly here.
                let prover_config = proof_prover_config
                    .as_ref()
                    .expect("proof requests construct their prover config before transfers");
                let log_lde_factor = prover_config.lde_factor.trailing_zeros();
                let log_tree_cap_size = prover_config.cap_size.trailing_zeros();
                let memory_caps = state
                    .memory_caps
                    .as_ref()
                    .expect("Proof requires memory_caps");
                let memory_host = GpuGKRMemoryTransferHost::from_per_coset_caps(
                    memory_caps,
                    log_lde_factor,
                    log_tree_cap_size,
                )?;
                let memory_transfer = GpuGKRMemoryTransfer::new(Arc::new(memory_host), context)?;
                let external_challenges_value = state
                    .external_challenges
                    .expect("Proof requires external_challenges");
                let compiled_circuit = state
                    .precomputations
                    .gkr_programs
                    .compiled_circuit()
                    .as_ref();
                // Without i&t data the windows are all zero, which is what the unified
                // verifier requires of its leading instances.
                let num_teardown_sets = compiled_circuit.memory_layout.teardown_sets.len();
                let top_bits = carried_top_bits.unwrap_or_else(|| vec![0u32; num_teardown_sets]);
                assert_eq!(
                top_bits.len(),
                num_teardown_sets,
                "inits-and-teardowns top bits must cover every teardown set of {circuit_type:?}"
            );
                let mut bundle =
                    gpu_circuit_prover::proof::inputs::GpuGKRProofTransfer::<'_, A>::new(
                        setup_transfer,
                        decoder_transfer,
                        inits_and_teardowns_transfer,
                        tracing_data_transfer,
                        memory_transfer,
                        &top_bits,
                        external_challenges_value,
                        context,
                    )?;
                trace!(
            "BATCH[{batch_id}] GPU_WORKER[{device_id}] scheduling proof H2D bundle for circuit {circuit_type:?}[{sequence_id}]"
        );
                bundle.schedule(context)?;
                if let Some(sink) = exact_memory.as_mut() {
                    sink.record_operation("initial_input_h2d");
                }
                PhaseOneInputs::Proof(bundle, dr_tail_plan, exact_memory.take())
            } else {
                let mut bundle =
                    gpu_trace::trace::memory_transfer::GpuGKRCommitMemoryTransfer::<'_, A>::new(
                        decoder_transfer,
                        inits_and_teardowns_transfer,
                        tracing_data_transfer,
                        context,
                    )?;
                trace!(
            "BATCH[{batch_id}] GPU_WORKER[{device_id}] scheduling commit-memory H2D bundle for circuit {circuit_type:?}[{sequence_id}]"
        );
                bundle.schedule(context)?;
                PhaseOneInputs::MemoryCommitment(bundle)
            };
            Ok(inputs)
        },
    )??;

    Ok(PhaseOne { state, inputs })
}

fn enqueue_phase_two<'a, 'context>(
    device_id: i32,
    context: &'context ProverContext,
    backward_options: GkrBackwardOptions,
    p1: PhaseOne<'a, 'context>,
) -> GpuProveResult<PhaseTwo<'a, 'context>> {
    let PhaseOne { state, inputs } = p1;
    let batch_id = state.batch_id;
    let circuit_type = state.circuit_type;
    let sequence_id = state.sequence_id;
    let prover_config =
        gpu_circuit_prover::config::prover_config(circuit_type, state.security_level)
            .expect("ExecutionProverConfiguration validated GPU security level before GPU work");
    let final_trace_size_log_2 = FINAL_TRACE_SIZE_LOG_2;
    let compiled_circuit_arc = Arc::clone(state.precomputations.gkr_programs.compiled_circuit());

    let job = match inputs {
        PhaseOneInputs::Proof(bundle, dr_tail_plan, exact_memory) => {
            trace!(
                "BATCH[{batch_id}] GPU_WORKER[{device_id}] producing proof for circuit {circuit_type:?}[{sequence_id}]"
            );
            let mut job = gpu_circuit_prover::proof::prove_with_measurement::<A>(
                &state.precomputations.gkr_programs,
                &prover_config,
                final_trace_size_log_2,
                bundle,
                backward_options,
                dr_tail_plan,
                exact_memory,
                context,
            )?;
            // Everything the proof needs is enqueued, including the single
            // terminal final-slab D2H the unchanged terminal owner scheduled.
            job.record_measured_operation("prove_enqueue");
            job.record_measured_operation("final_slab_d2h");
            JobType::Proof(job)
        }
        PhaseOneInputs::MemoryCommitment(bundle) => {
            trace!(
                "BATCH[{batch_id}] GPU_WORKER[{device_id}] producing memory commitment for circuit {circuit_type:?}[{sequence_id}]"
            );
            let job = commit_memory_from_transfers::<A>(
                circuit_type,
                &compiled_circuit_arc,
                bundle,
                &prover_config,
                context,
            )?;
            JobType::MemoryCommitment(job)
        }
        PhaseOneInputs::SetupInitialization => JobType::SetupInitialization,
    };

    Ok(PhaseTwo { state, job })
}

/// Phase 3 completes the enqueued job. It returns the worker error type
/// because a measurement failure surfaced by `GpuGKRProofJob::finish` is a
/// typed failed invocation, not a log line.
fn finish_phase_three<'a, 'context>(
    device_id: i32,
    p2: PhaseTwo<'a, 'context>,
) -> Result<GpuWorkResult<A>, GpuWorkerError> {
    let PhaseTwo { state, job } = p2;
    let RequestState {
        batch_id,
        circuit_type,
        sequence_id,
        inits_and_teardowns_result,
        tracing_data_result,
        ..
    } = state;
    match job {
        JobType::MemoryCommitment(job) => {
            let (merkle_tree_caps, commitment_time_ms) = job.finish()?;
            debug!(
                "BATCH[{batch_id}] GPU_WORKER[{device_id}] produced memory commitment for circuit {circuit_type:?}[{sequence_id}] in {commitment_time_ms:.3} ms"
            );
            Ok(GpuWorkResult::MemoryCommitment(MemoryCommitmentResult {
                batch_id,
                circuit_type,
                sequence_id,
                inits_and_teardowns: inits_and_teardowns_result,
                tracing_data: tracing_data_result,
                merkle_tree_caps,
            }))
        }
        JobType::Proof(job) => {
            let (proof, proof_time_ms) = job.finish()?;
            debug!(
                "BATCH[{batch_id}] GPU_WORKER[{device_id}] produced proof for circuit {circuit_type:?}[{sequence_id}] in {proof_time_ms:.3} ms"
            );
            Ok(GpuWorkResult::Proof(ProofResult {
                batch_id,
                circuit_type,
                sequence_id,
                inits_and_teardowns: inits_and_teardowns_result,
                tracing_data: tracing_data_result,
                proof,
            }))
        }
        JobType::SetupInitialization => {
            trace!(
                "BATCH[{batch_id}] GPU_WORKER[{device_id}] initialized setup for circuit {circuit_type:?}[{sequence_id}]"
            );
            Ok(GpuWorkResult::SetupInitialization(
                SetupInitializationResult {
                    batch_id,
                    circuit_type,
                    sequence_id,
                },
            ))
        }
    }
}
