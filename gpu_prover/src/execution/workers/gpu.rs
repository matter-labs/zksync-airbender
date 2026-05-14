use crate::execution::messages::{
    GpuWorkRequest, GpuWorkResult, MemoryCommitmentRequest, MemoryCommitmentResult, ProofRequest,
    ProofResult,
};
use crate::execution::precomputations::CircuitPrecomputations;
use crate::execution::A;
use crate::primitives::circuit_type::CircuitType;
use crate::primitives::context::{ProverContext, ProverContextConfig};
use crate::primitives::field::{BF, E4};
use crate::prover::gkr::setup::GpuGKRSetupTransfer;
use crate::prover::proof::{prove, GpuGKRProofJob};
use crate::prover::trace::decoder::DecoderTableTransfer;
use crate::prover::trace::memory::{commit_memory_from_transfers, MemoryCommitmentJob};
use crate::prover::trace::memory_transfer::{GpuGKRMemoryTransfer, GpuGKRMemoryTransferHost};
use crate::prover::trace::tracing_data::{InitsAndTeardownsTransfer, TracingDataTransfer};
use crate::witness::trace_unrolled::InitsAndTeardownsTraceHost;
use crossbeam_channel::{Receiver, Sender};
use era_cudart::device::{get_device_properties, set_device};
use era_cudart::result::CudaResult;
use log::{debug, error, info, trace};

use crate::upstream::{GKRExternalChallenges, MerkleTreeCapVarLength, SecurityLevel};
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
    /// Set only for Proof requests; consumed in Phase 2 by `prove()`.
    external_challenges: Option<GKRExternalChallenges<BF, E4>>,
    /// Per-coset caps from a prior commit_memory phase; only present for
    /// Proof requests and consumed in Phase 1 to build the memory transfer.
    memory_caps: Option<Vec<MerkleTreeCapVarLength>>,
    /// Original host witnesses returned to the orchestrator after the GPU work
    /// completes so allocator ownership stays symmetric with the old prover.
    inits_and_teardowns_result: Option<InitsAndTeardownsTraceHost>,
    tracing_data_result: Option<crate::prover::trace::tracing_data::TracingDataHost<A>>,
    security_level: SecurityLevel,
}

impl RequestState {
    fn is_proof(&self) -> bool {
        self.external_challenges.is_some()
    }
}

/// Phase-1 state: H2D transfers scheduled, no GPU job enqueued yet.
struct PhaseOne<'a> {
    state: RequestState,
    setup_transfer: Option<GpuGKRSetupTransfer<'a>>,
    decoder_transfer: Option<DecoderTableTransfer<'a>>,
    inits_and_teardowns_transfer: Option<InitsAndTeardownsTransfer<'a>>,
    tracing_data_transfer: Option<TracingDataTransfer<'a, A>>,
    memory_transfer: Option<GpuGKRMemoryTransfer<'a>>,
}

/// Phase-2 state: GPU job enqueued, awaiting `finish()`.
struct PhaseTwo<'a> {
    state: RequestState,
    job: JobType<'a>,
}

enum JobType<'a> {
    MemoryCommitment(MemoryCommitmentJob<'a>),
    Proof(GpuGKRProofJob<'a>),
}

fn gpu_worker(
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
    let mut context = ProverContext::new(&prover_context_config)?;
    info!(
        "GPU_WORKER[{device_id}] initialized the GPU memory allocator with {:.3} GB of usable memory",
        context.get_mem_size() as f64 / 1024.0 / 1024.0 / 1024.0
    );
    is_initialized.send(()).unwrap();
    drop(is_initialized);
    let mut even_odd_index = 0;
    let mut current_phase_one: Option<PhaseOne> = None;
    let mut current_phase_two: Option<PhaseTwo> = None;
    for request in requests {
        context.set_reversed_allocation_placement(even_odd_index == 1);
        let mut phase_one = if let Some(request) = request {
            Some(schedule_phase_one(device_id, &context, request)?)
        } else {
            None
        };
        mem::swap(&mut current_phase_one, &mut phase_one);
        context.set_reversed_allocation_placement(even_odd_index == 0);
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
        results.send(result).unwrap()
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
                external_challenges: Some(external_challenges),
                memory_caps: Some(memory_caps),
                inits_and_teardowns_result: inits_and_teardowns.clone(),
                tracing_data_result: tracing_data.clone(),
                security_level,
            };
            (state, inits_and_teardowns, tracing_data)
        }
    };
    let batch_id = state.batch_id;
    let circuit_type = state.circuit_type;
    let sequence_id = state.sequence_id;
    let is_proof = state.is_proof();

    // Setup transfer (Proof only) — lazy-init the GPU setup host on first
    // use against this worker's context.
    let setup_transfer = if is_proof {
        if let Some(setup_host) = state.precomputations.setup_host.get_or_init(context)? {
            let mut transfer = GpuGKRSetupTransfer::new(setup_host, context)?;
            trace!(
                "BATCH[{batch_id}] GPU_WORKER[{device_id}] transferring setup for circuit {circuit_type:?}[{sequence_id}]"
            );
            transfer.schedule_transfer(context)?;
            Some(transfer)
        } else {
            None
        }
    } else {
        None
    };

    let decoder_transfer = if let Some(host) = state.precomputations.decoder_host.as_ref() {
        let mut t = DecoderTableTransfer::new(Arc::clone(host), context)?;
        trace!(
            "BATCH[{batch_id}] GPU_WORKER[{device_id}] transferring decoder table for circuit {circuit_type:?}"
        );
        t.schedule_transfer(context)?;
        Some(t)
    } else {
        None
    };

    let inits_and_teardowns_transfer = if let Some(host) = inits_and_teardowns_host {
        let mut t = InitsAndTeardownsTransfer::new(host, context)?;
        trace!(
            "BATCH[{batch_id}] GPU_WORKER[{device_id}] transferring inits and teardowns for circuit {circuit_type:?}[{sequence_id}]"
        );
        t.schedule_transfer(context)?;
        Some(t)
    } else {
        None
    };

    let tracing_data_transfer = if let Some(tracing_data_host) = tracing_data_host {
        let mut tracing_data_transfer = TracingDataTransfer::new(tracing_data_host, context)?;
        trace!(
            "BATCH[{batch_id}] GPU_WORKER[{device_id}] transferring trace for circuit {circuit_type:?}[{sequence_id}]"
        );
        tracing_data_transfer.schedule_transfer(context)?;
        Some(tracing_data_transfer)
    } else {
        None
    };

    let memory_transfer = if let Some(caps) = state.memory_caps.as_ref() {
        // Geometry must match what `commit_memory_inner` used to produce the
        // caps (it reads `lde_factor` and `cap_size` from `prover_config`).
        // `circuit_type.get_lde_factor()` / `get_tree_cap_size()` are derived
        // from `OPTIMAL_FOLDING_PROPERTIES` and can disagree with the
        // `prover_config` the commit phase actually used, so use the
        // prover_config geometry directly here.
        let prover_config = circuit_type.prover_config(state.security_level);
        let log_lde_factor = prover_config.lde_factor.trailing_zeros();
        let log_tree_cap_size = prover_config.cap_size.trailing_zeros();
        let host =
            GpuGKRMemoryTransferHost::from_per_coset_caps(caps, log_lde_factor, log_tree_cap_size)?;
        let mut t = GpuGKRMemoryTransfer::new(Arc::new(host), context)?;
        trace!(
            "BATCH[{batch_id}] GPU_WORKER[{device_id}] transferring memory caps for circuit {circuit_type:?}[{sequence_id}]"
        );
        t.schedule_transfer(context)?;
        Some(t)
    } else {
        None
    };

    Ok(PhaseOne {
        state,
        setup_transfer,
        decoder_transfer,
        inits_and_teardowns_transfer,
        tracing_data_transfer,
        memory_transfer,
    })
}

fn enqueue_phase_two<'a>(
    device_id: i32,
    context: &ProverContext,
    p1: PhaseOne<'a>,
) -> CudaResult<PhaseTwo<'a>> {
    let PhaseOne {
        state,
        setup_transfer,
        decoder_transfer,
        inits_and_teardowns_transfer,
        tracing_data_transfer,
        memory_transfer,
    } = p1;
    let batch_id = state.batch_id;
    let circuit_type = state.circuit_type;
    let sequence_id = state.sequence_id;
    let prover_config = circuit_type.prover_config(state.security_level);
    let final_trace_size_log_2 = 4usize;
    let compiled_circuit_arc = state.precomputations.compiled_circuit.clone();

    let job = if state.is_proof() {
        let memory_transfer = memory_transfer.expect("Proof requires memory_transfer");
        let external_challenges = state
            .external_challenges
            .expect("Proof requires external_challenges");
        let compiled_circuit_value = (*compiled_circuit_arc).clone();
        trace!(
            "BATCH[{batch_id}] GPU_WORKER[{device_id}] producing proof for circuit {circuit_type:?}[{sequence_id}]"
        );
        let job = prove::<A>(
            circuit_type,
            compiled_circuit_value,
            external_challenges,
            &prover_config,
            final_trace_size_log_2,
            setup_transfer,
            decoder_transfer,
            inits_and_teardowns_transfer,
            tracing_data_transfer,
            memory_transfer,
            context,
        )?;
        JobType::Proof(job)
    } else {
        trace!(
            "BATCH[{batch_id}] GPU_WORKER[{device_id}] producing memory commitment for circuit {circuit_type:?}[{sequence_id}]"
        );
        let job = commit_memory_from_transfers::<A>(
            circuit_type,
            &compiled_circuit_arc,
            decoder_transfer,
            inits_and_teardowns_transfer,
            tracing_data_transfer,
            &prover_config,
            context,
        )?;
        let _ = (setup_transfer, memory_transfer);
        JobType::MemoryCommitment(job)
    };

    Ok(PhaseTwo { state, job })
}

fn finish_phase_three<'a>(device_id: i32, p2: PhaseTwo<'a>) -> CudaResult<GpuWorkResult<A>> {
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
    }
}
