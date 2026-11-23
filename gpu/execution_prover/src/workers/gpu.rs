use crate::precomputations::CircuitPrecomputations;
use crate::upstream::{GKRExternalChallenges, MerkleTreeCapVarLength, OperationMode};
use crate::workers::gpu_manager::{GpuWorkRequest, GpuWorkResult};
use crate::A;
use crossbeam_channel::{Receiver, Sender};
use era_cudart::device::{get_device_properties, set_device};
use era_cudart::result::CudaResult;
use execution_prover::messages::{SetupInitializationRequest, SetupInitializationResult};
use execution_prover::ProofProfile;
use execution_prover_model::allocator::PooledHostAllocator;
use gpu_circuit_prover::baby_bear::GpuGKRProofJob;
use gpu_circuit_prover::proth120::{GpuL1WrapProofJob, L1WrapInputs};
use gpu_core::allocator::tracker::AllocationDirection::{Ascending, Descending};
use gpu_core::primitives::field::{BF, E4};
use gpu_gkr::baby_bear::stage1::merged_commitment::GpuGKRMergedCommitTransfer;
use gpu_gkr::proth120::backward::DrTailProofPlanPr;
use gpu_prover_context::{AllocationMode, ProverContext, ProverContextConfig};
use gpu_trace::baby_bear::trace::memory::MemoryCommitmentJob;
use gpu_trace::witness::circuit_type::CircuitType;
use gpu_trace::witness::trace_unrolled::InitsAndTeardownsTraceHost;
use log::{debug, error, info, trace};
use std::ffi::CStr;
use std::mem;
use std::process::exit;

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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RequestKind {
    L1WrapProof,
    MemoryCommitment,
    Proof,
    SetupInitialization,
}

/// Per-request bookkeeping carried across all three phases. Owns the
/// precomputations Arc (which holds the compiled circuit, lazy-init setup
/// host, and optional decoder host), so it outlives any Phase-2 borrow,
/// and the original host data the orchestrator expects back on the
/// memory-commit path.
pub(crate) struct RequestState {
    pub(crate) batch_id: u64,
    pub(crate) circuit_type: CircuitType,
    pub(crate) sequence_id: usize,
    pub(crate) precomputations: CircuitPrecomputations,
    pub(crate) kind: RequestKind,
    /// Set only for Proof requests; consumed in Phase 2 by `prove()`.
    pub(crate) external_challenges: Option<GKRExternalChallenges<BF, E4>>,
    /// Per-coset caps from a prior commit_memory phase; only present for
    /// Proof requests and consumed in Phase 1 to build the memory transfer.
    pub(crate) memory_caps: Option<Vec<MerkleTreeCapVarLength>>,
    /// Original host witnesses returned to the orchestrator after the GPU work
    /// completes so their allocators return to the pool.
    pub(crate) inits_and_teardowns_result: Option<InitsAndTeardownsTraceHost<A>>,
    pub(crate) tracing_data_result: Option<gpu_trace::trace::tracing_data::TracingDataHost<A>>,
    pub(crate) profile: ProofProfile,
}

/// Phase-1 state: H2D transfers scheduled, no GPU job enqueued yet.
pub(crate) struct PhaseOne<'a> {
    pub(crate) state: RequestState,
    pub(crate) inputs: PhaseOneInputs<'a>,
}

/// Per-phase-1 bundle, scheduled on h2d_stream against a single shared
/// `Transfer`. Variant matches the eventual phase-2 job type.
// Short-lived per-request state moved through the worker's hot dispatch
// loop (one instance per in-flight request, swapped every iteration), not a
// long-lived collection; boxing `Proof` would add a heap alloc per request
// for no steady-state benefit.
#[allow(clippy::large_enum_variant)]
pub(crate) enum PhaseOneInputs<'a> {
    Proof(gpu_circuit_prover::baby_bear::inputs::GpuGKRProofTransfer<'a, A>),
    MemoryCommitment(gpu_trace::baby_bear::trace::memory::GpuGKRCommitMemoryTransfer<'a, A>),
    MergedCommitment(
        GpuGKRMergedCommitTransfer<'a, A>,
        Option<PooledHostAllocator<A>>,
    ),
    L1Wrap(L1WrapInputs<'a, A>, DrTailProofPlanPr, OperationMode),
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
pub(crate) enum JobType<'a> {
    MemoryCommitment(MemoryCommitmentJob<'a, A>),
    Proof(GpuGKRProofJob<'a>),
    L1Wrap(GpuL1WrapProofJob<'a>),
    SetupInitialization,
}

pub(crate) fn gpu_worker(
    device_id: i32,
    prover_context_config: ProverContextConfig,
    is_initialized: Sender<()>,
    requests: Receiver<Option<GpuWorkRequest<A>>>,
    results: Sender<Option<GpuWorkResult<A>>>,
) -> CudaResult<()> {
    trace!("GPU_WORKER[{device_id}] started");
    set_device(device_id)?;
    let props = get_device_properties(device_id)?;
    let name = unsafe { CStr::from_ptr(props.name.as_ptr()).to_string_lossy() };
    info!(
        "GPU_WORKER[{device_id}] GPU: {} ({} SMs, {:.3} GB RAM)",
        name,
        props.multiProcessorCount,
        props.totalGlobalMem as f64 / 1024.0 / 1024.0 / 1024.0
    );
    let mut context = ProverContext::new_with_auto_arena_size(
        &prover_context_config,
        crate::memory_policy::select_arena_bytes,
    )?;
    info!(
        "GPU_WORKER[{device_id}] initialized the GPU memory allocator with {:.3} GB ({} B) of usable memory",
        context.get_mem_size() as f64 / 1024.0 / 1024.0 / 1024.0,
        context.get_mem_size()
    );
    is_initialized
        .send(())
        .expect("GPU worker initialization channel closed before readiness signal");
    drop(is_initialized);
    let mut even_odd_index = 0;
    let mut current_phase_one: Option<PhaseOne> = None;
    let mut current_phase_two: Option<PhaseTwo> = None;
    for request in requests {
        let mut phase_one = if let Some(request) = request {
            context.set_allocation_mode(match request {
                GpuWorkRequest::SetupInitialization(_) => AllocationMode::Unbounded,
                _ => AllocationMode::Inputs([Ascending, Descending][even_odd_index]),
            });
            Some(schedule_phase_one(device_id, &context, request)?)
        } else {
            None
        };
        mem::swap(&mut current_phase_one, &mut phase_one);
        let direction = [Descending, Ascending][even_odd_index];
        context.set_allocation_mode(AllocationMode::Proof(direction));
        let mut phase_two = if let Some(p1) = phase_one {
            Some(enqueue_phase_two(device_id, &context, p1)?)
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

fn schedule_phase_one<'a>(
    device_id: i32,
    context: &ProverContext,
    request: GpuWorkRequest<A>,
) -> CudaResult<PhaseOne<'a>> {
    if let GpuWorkRequest::SetupInitialization(request) = request {
        let SetupInitializationRequest {
            batch_id,
            circuit_type,
            sequence_id,
            precomputations,
        } = request;

        trace!(
            "BATCH[{batch_id}] GPU_WORKER[{device_id}] initializing setup for circuit {circuit_type:?}[{sequence_id}]"
        );
        let timer = std::time::Instant::now();
        match &precomputations {
            CircuitPrecomputations::BabyBear(precomputations) => {
                precomputations.setup_host.get_or_init(context)?
            }
            CircuitPrecomputations::L1Wrap(precomputed) => precomputed.initialize(context)?,
        }
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

            profile: if circuit_type == CircuitType::L1Wrap {
                ProofProfile::L1Wrap
            } else {
                ProofProfile::Standard
            },
        };
        return Ok(PhaseOne {
            state,
            inputs: PhaseOneInputs::SetupInitialization,
        });
    }
    if let GpuWorkRequest::L1WrapProof(request) = request {
        return crate::proth120::workers::gpu::schedule_l1_wrap_phase_one(
            device_id, context, request,
        );
    }
    crate::baby_bear::workers::gpu::schedule_phase_one(device_id, context, request)
}

fn enqueue_phase_two<'a>(
    device_id: i32,
    context: &ProverContext,
    p1: PhaseOne<'a>,
) -> CudaResult<PhaseTwo<'a>> {
    let PhaseOne { state, inputs } = p1;
    if let PhaseOneInputs::SetupInitialization = inputs {
        return Ok(PhaseTwo {
            state,
            job: JobType::SetupInitialization,
        });
    }
    let job = match inputs {
        PhaseOneInputs::L1Wrap(inputs, dr_tail_plan, operation_mode) => {
            crate::proth120::workers::gpu::enqueue_phase_two(
                device_id,
                context,
                &state,
                inputs,
                dr_tail_plan,
                operation_mode,
            )?
        }
        inputs => {
            crate::baby_bear::workers::gpu::enqueue_phase_two(device_id, context, &state, inputs)?
        }
    };
    Ok(PhaseTwo { state, job })
}

fn finish_phase_three<'a>(device_id: i32, p2: PhaseTwo<'a>) -> CudaResult<GpuWorkResult<A>> {
    let PhaseTwo { state, job } = p2;
    match job {
        JobType::MemoryCommitment(job) => {
            crate::baby_bear::workers::gpu::finish_memory_commitment(device_id, state, job)
        }
        JobType::Proof(job) => crate::baby_bear::workers::gpu::finish_proof(device_id, state, job),
        JobType::L1Wrap(job) => {
            crate::proth120::workers::gpu::finish_l1_wrap(device_id, state, job)
        }
        JobType::SetupInitialization => {
            let RequestState {
                batch_id,
                circuit_type,
                sequence_id,
                ..
            } = state;
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
