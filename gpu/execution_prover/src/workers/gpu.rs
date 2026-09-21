use crate::errors::GpuBackendError;
use crate::host_storage::GpuTraceAllocator;
use crate::precomputations::CircuitPrecomputations;
use crate::workers::gpu_manager::{GpuWorkRequest, GpuWorkResult};
use crossbeam_channel::{Receiver, Sender};
use era_cudart::device::{get_device_properties, set_device};
use era_cudart::result::CudaResult;
use execution_prover::messages::{
    MemoryCommitmentRequest, MemoryCommitmentResult, ProofRequest, ProofResult,
    SetupInitializationRequest, SetupInitializationResult,
};
use gpu_circuit_prover::proof::{
    admit_dr_tail_before_transfers, DrTailPreflightRequest, GpuGKRProofJob,
};
use gpu_core::primitives::field::{BF, E4};
use gpu_gkr::setup::GpuGKRSetupTransfer;
use gpu_prover_context::{ProverContext, ProverContextConfig};
use gpu_trace::trace::decoder::DecoderTableTransfer;
use gpu_trace::trace::memory::{commit_memory_from_transfers, MemoryCommitmentJob};
use gpu_trace::trace::memory_transfer::{GpuGKRMemoryTransfer, GpuGKRMemoryTransferHost};
use gpu_trace::trace::tracing_data::{InitsAndTeardownsTransfer, TracingDataTransfer};
use gpu_trace::witness::circuit_type::CircuitType;
use gpu_trace::witness::trace_unrolled::InitsAndTeardownsTraceHost;
use log::{debug, error, info, trace};

use crate::upstream::{GKRExternalChallenges, MerkleTreeCapVarLength, SecurityLevel};
use std::ffi::CStr;
use std::mem;
use std::sync::Arc;

pub(crate) fn get_gpu_worker_func(
    device_id: i32,
    prover_context_config: ProverContextConfig,
    is_initialized: Sender<Result<(), GpuBackendError>>,
    requests: Receiver<Option<GpuWorkRequest>>,
    results: Sender<Result<Option<GpuWorkResult>, GpuBackendError>>,
) -> impl FnOnce() + Send + 'static {
    move || {
        // Startup is acknowledged with its result, not a bare rendezvous: the
        // caller has to tell "came up" from "died on the way".
        let mut context = match initialize_worker(device_id, prover_context_config) {
            Ok(context) => {
                is_initialized
                    .send(Ok(()))
                    .expect("GPU worker initialization channel closed before readiness signal");
                context
            }
            Err(error) => {
                // If the manager has already given up there is no one to tell.
                let _ = is_initialized.send(Err(error));
                return;
            }
        };
        drop(is_initialized);
        if let Err(error) = run_worker(device_id, &mut context, &requests, &results) {
            // Reported rather than fatal: the manager turns this into a
            // `BackendFailure` on every live batch so callers can cancel.
            error!("GPU_WORKER[{device_id}] worker encountered an error: {error}");
            let _ = results.send(Err(error));
        }
    }
}

fn initialize_worker(
    device_id: i32,
    prover_context_config: ProverContextConfig,
) -> Result<ProverContext, GpuBackendError> {
    let init = |source| {
        GpuBackendError::cuda(
            format!("GPU worker {device_id} failed to initialize"),
            source,
        )
    };
    trace!("GPU_WORKER[{device_id}] started");
    set_device(device_id).map_err(init)?;
    let props = get_device_properties(device_id).map_err(init)?;
    let name = unsafe { CStr::from_ptr(props.name.as_ptr()).to_string_lossy() };
    info!(
        "GPU_WORKER[{device_id}] GPU: {} ({} SMs, {:.3} GB RAM)",
        name,
        props.multiProcessorCount,
        props.totalGlobalMem as f64 / 1024.0 / 1024.0 / 1024.0
    );
    let context = ProverContext::new_with_auto_arena_size(
        &prover_context_config,
        crate::memory_policy::select_arena_bytes,
    )
    .map_err(init)?;
    crate::memory_policy::select_arena_bytes(context.get_mem_size());
    info!(
        "GPU_WORKER[{device_id}] initialized the GPU memory allocator with {:.3} GB of usable memory",
        context.get_mem_size() as f64 / 1024.0 / 1024.0 / 1024.0
    );
    Ok(context)
}

const FINAL_TRACE_SIZE_LOG_2: u32 = 4;

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
    inits_and_teardowns_result: Option<InitsAndTeardownsTraceHost<GpuTraceAllocator>>,
    tracing_data_result: Option<gpu_trace::trace::tracing_data::TracingDataHost<GpuTraceAllocator>>,
    security_level: SecurityLevel,
}

/// Phase-1 state: H2D transfers scheduled, no GPU job enqueued yet.
struct PhaseOne<'a> {
    state: RequestState,
    inputs: PhaseOneInputs<'a>,
}

/// Per-phase-1 bundle, scheduled on h2d_stream against a single shared
/// `Transfer`. Variant matches the eventual phase-2 job type.
// Short-lived per-request state moved through the worker's hot dispatch
// loop (one instance per in-flight request, swapped every iteration), not a
// long-lived collection; boxing `Proof` would add a heap alloc per request
// for no steady-state benefit.
#[allow(clippy::large_enum_variant)]
enum PhaseOneInputs<'a> {
    Proof(
        gpu_circuit_prover::proof::inputs::GpuGKRProofTransfer<'a, GpuTraceAllocator>,
        gpu_gkr::DrTailProofPlan,
    ),
    MemoryCommitment(
        gpu_trace::trace::memory_transfer::GpuGKRCommitMemoryTransfer<'a, GpuTraceAllocator>,
    ),
    SetupInitialization,
}

/// Phase-2 state: GPU job enqueued, awaiting `finish()`.
struct PhaseTwo<'a> {
    state: RequestState,
    job: JobType<'a>,
}

// Same rationale as `PhaseOneInputs` above: one instance per in-flight
// request, swapped through the worker's hot dispatch loop, so boxing `Proof`
// would add a per-request heap alloc rather than shrink a steady-state
// collection.
#[allow(clippy::large_enum_variant)]
enum JobType<'a> {
    MemoryCommitment(MemoryCommitmentJob<'a>),
    Proof(GpuGKRProofJob<'a>),
    SetupInitialization,
}

/// Which retained slots a teardown drain actually retired.
#[derive(Debug, Default, Clone, Copy)]
pub(crate) struct Drained {
    /// A phase-two job was finished (its completion event synchronized).
    pub(crate) enqueued_job: bool,
    /// A phase-one transfer was promoted and then finished.
    pub(crate) scheduled_transfer: bool,
}

fn run_worker(
    device_id: i32,
    context: &mut ProverContext,
    requests: &Receiver<Option<GpuWorkRequest>>,
    results: &Sender<Result<Option<GpuWorkResult>, GpuBackendError>>,
) -> Result<(), GpuBackendError> {
    let runtime = |source| {
        GpuBackendError::cuda(
            format!("GPU worker {device_id} failed during execution"),
            source,
        )
    };
    let mut even_odd_index = 0;
    let mut current_phase_one: Option<PhaseOne> = None;
    let mut current_phase_two: Option<PhaseTwo> = None;
    let mut outcome = Ok(());
    for request in requests.iter() {
        context.set_reversed_allocation_placement(even_odd_index == 1);
        let mut phase_one = match request {
            Some(request) => match schedule_phase_one(device_id, context, request) {
                Ok(phase_one) => Some(phase_one),
                Err(error) => {
                    // The failing helper already dropped its own state; quiesce
                    // before the retained slots drain below, so no further
                    // owner is released mid-flight.
                    synchronize_before_teardown(device_id, context);
                    outcome = Err(runtime(error));
                    break;
                }
            },
            None => None,
        };
        mem::swap(&mut current_phase_one, &mut phase_one);
        context.set_reversed_allocation_placement(even_odd_index == 0);
        let mut phase_two = match phase_one {
            Some(p1) => match enqueue_phase_two(device_id, context, p1) {
                Ok(phase_two) => Some(phase_two),
                Err(error) => {
                    // As above: quiesce before the retained slots drain.
                    synchronize_before_teardown(device_id, context);
                    outcome = Err(runtime(error));
                    break;
                }
            },
            None => None,
        };
        mem::swap(&mut current_phase_two, &mut phase_two);
        even_odd_index = 1 - even_odd_index;
        let result = match phase_two {
            Some(p2) => match finish_phase_three(device_id, p2) {
                Ok(result) => Some(result),
                Err(error) => {
                    // As above: quiesce before the retained slots drain.
                    synchronize_before_teardown(device_id, context);
                    outcome = Err(runtime(error));
                    break;
                }
            },
            None => None,
        };
        if results.send(Ok(result)).is_err() {
            // The manager stopped serving and is already broadcasting a failure
            // of its own, so leave through the drain instead of panicking.
            trace!("GPU_WORKER[{device_id}] results channel closed, draining");
            break;
        }
    }

    // Every exit path lands here. The normal one leaves both slots empty and
    // drains nothing; an early exit can still hold scheduled work.
    //
    // Those slots own `Transfer`/`Callbacks` and job state, and the scheduling
    // contract requires a `Callbacks` owner to survive until synchronization
    // confirms its callbacks ran — dropping one earlier can release a host
    // source while its H2D copy is in flight. So they are FINISHED (which
    // synchronizes) rather than dropped. `prove()` stays enqueue-only on the
    // normal path; this is failure cleanup only.
    let drained = drain_in_flight(
        device_id,
        context,
        current_phase_one.take(),
        current_phase_two.take(),
    );
    trace!("GPU_WORKER[{device_id}] finished, drained {drained:?}");
    match (outcome, drained) {
        (Err(error), _) => Err(error),
        (Ok(()), Err(error)) => Err(runtime(error)),
        (Ok(()), Ok(_)) => Ok(()),
    }
}

/// Best-effort quiescing of both streams before anything further is dropped:
/// it stops a *further* owner being released while its transfer or kernel is
/// in flight, but cannot un-drop one a consuming call already took.
///
/// Errors are swallowed because a failure is already being reported, which
/// also means this is damage limitation and not a barrier: on a lost device
/// the synchronize fails and the following drops are as unsafe as ever.
fn synchronize_before_teardown(device_id: i32, context: &ProverContext) {
    trace!("GPU_WORKER[{device_id}] synchronizing before teardown");
    let _ = context.get_h2d_stream().synchronize();
    let _ = context.get_exec_stream().synchronize();
}

/// Retire every scheduled-but-unfinished slot before its owners drop.
///
/// Phase two is finished directly; phase one has H2D scheduled but no job, so
/// it is promoted and then finished. Results are discarded — the
/// synchronization inside `finish` is the point, because it confirms the
/// callbacks ran. BOTH slots are retired even when the first reports an error,
/// since returning early would drop the other one un-retired.
fn drain_in_flight(
    device_id: i32,
    context: &ProverContext,
    phase_one: Option<PhaseOne<'_>>,
    phase_two: Option<PhaseTwo<'_>>,
) -> CudaResult<Drained> {
    let mut drained = Drained::default();
    let mut first_error = None;
    // Phase two was enqueued first, so it is retired first. `finish`
    // synchronizes its completion event first, so only a successful return
    // confirms this job's callbacks ran — a failure may come from that very
    // synchronize, with the consumed state already dropped.
    if let Some(p2) = phase_two {
        trace!("GPU_WORKER[{device_id}] draining an enqueued job");
        drained.enqueued_job = true;
        if let Err(error) = finish_phase_three(device_id, p2) {
            synchronize_before_teardown(device_id, context);
            first_error = Some(error);
        }
    }
    if let Some(p1) = phase_one {
        trace!("GPU_WORKER[{device_id}] draining a scheduled transfer");
        drained.scheduled_transfer = true;
        let result = enqueue_phase_two(device_id, context, p1)
            .and_then(|p2| finish_phase_three(device_id, p2).map(|_| ()));
        if let Err(error) = result {
            synchronize_before_teardown(device_id, context);
            if first_error.is_none() {
                first_error = Some(error);
            }
        }
    }
    match first_error {
        Some(error) => Err(error),
        None => Ok(drained),
    }
}

fn schedule_phase_one<'a>(
    device_id: i32,
    context: &ProverContext,
    request: GpuWorkRequest,
) -> CudaResult<PhaseOne<'a>> {
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

    let proof_prover_config = is_proof.then(|| {
        gpu_circuit_prover::config::prover_config(circuit_type, state.security_level)
            .expect("ExecutionProverConfiguration validated GPU security level before GPU work")
    });
    let preflight_request =
        proof_prover_config
            .as_ref()
            .map(|prover_config| DrTailPreflightRequest {
                gkr_programs: &state.precomputations.gkr_programs,
                prover_config,
                final_trace_size_log_2: FINAL_TRACE_SIZE_LOG_2,
                device_id,
            });

    let inputs = admit_dr_tail_before_transfers(
        preflight_request,
        |dr_tail_plan| -> CudaResult<PhaseOneInputs<'a>> {
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

            let inputs: PhaseOneInputs<'a> = if is_proof {
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
                let mut bundle = gpu_circuit_prover::proof::inputs::GpuGKRProofTransfer::<
                    '_,
                    GpuTraceAllocator,
                >::new(
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
                // Synchronize before `bundle` drops on the error path: it owns
                // callbacks that may already be scheduled, and this is the one
                // ownership transition here the caller's drain cannot reach.
                if let Err(error) = bundle.schedule(context) {
                    synchronize_before_teardown(device_id, context);
                    return Err(error);
                }
                PhaseOneInputs::Proof(
                    bundle,
                    dr_tail_plan.expect("proof preflight must return a DR-tail plan"),
                )
            } else {
                let mut bundle = gpu_trace::trace::memory_transfer::GpuGKRCommitMemoryTransfer::<
                    '_,
                    GpuTraceAllocator,
                >::new(
                    decoder_transfer,
                    inits_and_teardowns_transfer,
                    tracing_data_transfer,
                    context,
                )?;
                trace!(
            "BATCH[{batch_id}] GPU_WORKER[{device_id}] scheduling commit-memory H2D bundle for circuit {circuit_type:?}[{sequence_id}]"
        );
                if let Err(error) = bundle.schedule(context) {
                    synchronize_before_teardown(device_id, context);
                    return Err(error);
                }
                PhaseOneInputs::MemoryCommitment(bundle)
            };
            Ok(inputs)
        },
    )??;

    Ok(PhaseOne { state, inputs })
}

/// Enqueue the job for an already-transferred bundle.
///
/// The enqueue calls below CONSUME the bundle, so a failure inside one of them
/// has already dropped it — and its scheduled `Callbacks`, which
/// `gpu_core::primitives::callbacks` warns can skip the callback and release
/// its captures early — by the time the error reaches this frame. Nothing here
/// can prevent that; the caller's `synchronize_before_teardown` only limits
/// the damage to that one bundle. Fixing it properly needs the consuming APIs
/// to hand their bundle back on error, which is a lower-crate change.
fn enqueue_phase_two<'a>(
    device_id: i32,
    context: &ProverContext,
    p1: PhaseOne<'a>,
) -> CudaResult<PhaseTwo<'a>> {
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
        PhaseOneInputs::Proof(bundle, dr_tail_plan) => {
            trace!(
                "BATCH[{batch_id}] GPU_WORKER[{device_id}] producing proof for circuit {circuit_type:?}[{sequence_id}]"
            );
            let job = gpu_circuit_prover::proof::prove::<GpuTraceAllocator>(
                &state.precomputations.gkr_programs,
                &prover_config,
                final_trace_size_log_2,
                bundle,
                &dr_tail_plan,
                crate::memory_policy::policy(circuit_type, context.get_mem_size()),
                context,
            )?;
            JobType::Proof(job)
        }
        PhaseOneInputs::MemoryCommitment(bundle) => {
            trace!(
                "BATCH[{batch_id}] GPU_WORKER[{device_id}] producing memory commitment for circuit {circuit_type:?}[{sequence_id}]"
            );
            let job = commit_memory_from_transfers::<GpuTraceAllocator>(
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

fn finish_phase_three<'a>(device_id: i32, p2: PhaseTwo<'a>) -> CudaResult<GpuWorkResult> {
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
