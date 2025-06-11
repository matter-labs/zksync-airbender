use crate::logger::LOCAL_LOGGER;
use crate::messages::WorkerResult;
use crossbeam_channel::{Receiver, Sender};
use cs::one_row_compiler::CompiledCircuitArtifact;
use fft::GoodAllocator;
use field::Mersenne31Field;
use gpu_prover::cudart::device::set_device;
use gpu_prover::cudart::result::CudaResult;
use gpu_prover::prover::context::{ProverContext, ProverContextConfig};
use gpu_prover::prover::memory::{commit_memory, MemoryCommitmentJob};
use gpu_prover::prover::proof::ProofJob;
use gpu_prover::prover::tracing_data::{TracingDataHost, TracingDataTransfer};
use gpu_prover::witness::CircuitType;
use prover::merkle_trees::MerkleTreeCapVarLength;
use prover::prover_stages::Proof;
use std::mem;
use std::sync::Arc;
use std::time::Instant;

type BF = Mersenne31Field;

pub struct MemoryCommitmentRequest<A: GoodAllocator> {
    pub circuit_type: CircuitType,
    pub circuit: Arc<CompiledCircuitArtifact<BF>>,
    pub log_lde_factor: u32,
    pub log_tree_cap_size: u32,
    pub index: usize,
    pub tracing_data: TracingDataHost<A>,
}

pub struct MemoryCommitmentResult<A: GoodAllocator> {
    pub index: usize,
    pub tracing_data: TracingDataHost<A>,
    pub merkle_tree_caps: Vec<MerkleTreeCapVarLength>,
}

pub enum GpuWorkRequest<A: GoodAllocator> {
    MemoryCommitment(MemoryCommitmentRequest<A>),
    Proof(ProofRequest<A>),
}

pub struct ProofRequest<A: GoodAllocator> {
    pub circuit_type: CircuitType,
    pub circuit: Arc<CompiledCircuitArtifact<BF>>,
    pub log_lde_factor: u32,
    pub log_tree_cap_size: u32,
    pub index: usize,
    pub tracing_data: TracingDataHost<A>,
}

pub struct ProofResult<A: GoodAllocator> {
    pub index: usize,
    pub tracing_data: TracingDataHost<A>,
    pub proof: Proof,
}

pub fn get_gpu_worker_func<C: ProverContext>(
    device_id: i32,
    prover_context_config: ProverContextConfig,
    is_initialized: Sender<()>,
    timer_reset: Receiver<Instant>,
    requests: Receiver<Option<GpuWorkRequest<C::HostAllocator>>>,
    results: Sender<Option<WorkerResult<C::HostAllocator>>>,
) -> impl FnOnce() + Send + 'static {
    move || {
        gpu_worker::<C>(
            device_id,
            prover_context_config,
            is_initialized,
            timer_reset,
            requests,
            results,
        )
        .unwrap()
    }
}

enum JobType<'a, C: ProverContext> {
    MemoryCommitment(MemoryCommitmentJob<'a, C>),
    Proof(ProofJob<'a, C>),
}

fn gpu_worker<C: ProverContext>(
    device_id: i32,
    prover_context_config: ProverContextConfig,
    is_initialized: Sender<()>,
    timer_reset: Receiver<Instant>,
    requests: Receiver<Option<GpuWorkRequest<C::HostAllocator>>>,
    results: Sender<Option<WorkerResult<C::HostAllocator>>>,
) -> CudaResult<()> {
    LOCAL_LOGGER.with_borrow_mut(|l| {
        l.name = format!("GPU[{device_id}]");
    });
    set_device(device_id)?;
    let context = C::new(&prover_context_config)?;
    log::info!("GPU worker initialized");
    is_initialized.send(()).unwrap();
    drop(is_initialized);
    let timer = timer_reset.recv().unwrap();
    drop(timer_reset);
    LOCAL_LOGGER.with_borrow_mut(|l| {
        l.timer = timer;
    });
    log::info!("timer reset");
    let mut current_transfer = None;
    let mut current_job = None;
    for request in requests {
        let mut transfer = if let Some(request) = request {
            let (circuit_type, index, data) = match &request {
                GpuWorkRequest::MemoryCommitment(request) => (
                    request.circuit_type,
                    request.index,
                    request.tracing_data.clone(),
                ),
                GpuWorkRequest::Proof(_) => todo!(),
            };
            log::info!(
                "transferring trace for circuit type: {:?}, index: {}",
                circuit_type,
                index
            );
            let mut transfer = TracingDataTransfer::new(circuit_type, data, &context)?;
            transfer.schedule_transfer(&context)?;
            Some((request, transfer))
        } else {
            None
        };
        mem::swap(&mut current_transfer, &mut transfer);
        let mut job = if let Some((request, transfer)) = transfer {
            let job = match &request {
                GpuWorkRequest::MemoryCommitment(request) => {
                    log::info!(
                        "producing memory commitment for circuit type: {:?}, index: {}",
                        request.circuit_type,
                        request.index
                    );
                    let job = commit_memory(
                        transfer,
                        &request.circuit,
                        request.log_lde_factor,
                        request.log_tree_cap_size,
                        &context,
                    )?;
                    JobType::MemoryCommitment(job)
                }
                GpuWorkRequest::Proof(_) => todo!(),
            };
            Some((request, job))
        } else {
            None
        };
        mem::swap(&mut current_job, &mut job);
        let result = if let Some((request, job)) = job {
            match request {
                GpuWorkRequest::MemoryCommitment(request) => {
                    let MemoryCommitmentRequest {
                        circuit_type,
                        index,
                        tracing_data,
                        ..
                    } = request;
                    let merkle_tree_caps = match job {
                        JobType::MemoryCommitment(job) => job.finish()?,
                        JobType::Proof(_) => unreachable!(),
                    };
                    log::info!(
                        "produced memory commitment for circuit type: {:?}, index: {}",
                        circuit_type,
                        index
                    );
                    let result = MemoryCommitmentResult {
                        index,
                        tracing_data,
                        merkle_tree_caps,
                    };
                    Some(WorkerResult::MemoryCommitment(result))
                }
                GpuWorkRequest::Proof(_) => todo!(),
            }
        } else {
            None
        };
        results.send(result).unwrap()
    }
    assert!(current_transfer.is_none());
    assert!(current_job.is_none());
    log::info!("GPU worker finished");
    Ok(())
}
