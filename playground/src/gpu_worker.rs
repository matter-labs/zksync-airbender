use std::sync::Arc;
use crate::logger::LOCAL_LOGGER;
use crossbeam_channel::{Receiver, Sender};
use cs::one_row_compiler::CompiledCircuitArtifact;
use fft::GoodAllocator;
use field::Mersenne31Field;
use gpu_prover::cudart::device::set_device;
use gpu_prover::cudart::result::CudaResult;
use gpu_prover::prover::context::{MemPoolProverContext, ProverContextConfig};
use gpu_prover::prover::tracing_data::{TracingDataHost, TracingDataTransfer};
use gpu_prover::witness::CircuitType;
use prover::merkle_trees::MerkleTreeCapVarLength;
use prover::prover_stages::Proof;
use std::time::Instant;
use gpu_prover::allocator::host::ConcurrentStaticHostAllocator;
use gpu_prover::prover::memory::commit_memory;

type BF = Mersenne31Field;
type A = ConcurrentStaticHostAllocator;

pub struct MemoryCommitmentRequest {
    pub circuit_type: CircuitType,
    pub circuit: Arc<CompiledCircuitArtifact<BF>>,
    pub log_lde_factor: u32,
    pub log_tree_cap_size: u32,
    pub index: usize,
    pub tracing_data: TracingDataHost<A>,
}

pub struct MemoryCommitmentResult {
    pub index: usize,
    pub tracing_data: TracingDataHost<A>,
    pub merkle_tree_caps: Vec<MerkleTreeCapVarLength>,
}

pub struct ProofRequest {
    pub circuit_type: CircuitType,
    pub circuit: Arc<CompiledCircuitArtifact<BF>>,
    pub log_lde_factor: u32,
    pub log_tree_cap_size: u32,
    pub index: usize,
    pub tracing_data: TracingDataHost<A>,
}

pub struct ProofResult {
    pub index: usize,
    pub tracing_data: TracingDataHost<A>,
    pub proof: Proof,
}

pub enum GpuWorkBatch {
    MemoryCommitment {
        timer: Instant,
        requests: Receiver<MemoryCommitmentRequest>,
        results: Sender<MemoryCommitmentResult>,
    },
    Proof {
        timer: Instant,
        receiver: Receiver<ProofRequest>,
        sender: Sender<ProofResult>,
    },
}

struct GpuWorker<'a> {
    device_id: i32,
    context: MemPoolProverContext<'a>,
}

impl<'a> GpuWorker<'a> {
    fn new(device_id: i32, prover_context_config: ProverContextConfig) -> CudaResult<Self> {
        LOCAL_LOGGER.with_borrow_mut(|l| {
            l.name = format!("GPU[{device_id}]");
        });
        set_device(device_id)?;
        let context = MemPoolProverContext::new(&prover_context_config)?;
        Ok(GpuWorker { device_id, context })
    }

    fn process_memory_commitment_batch(
        &self,
        timer: Instant,
        requests: Receiver<MemoryCommitmentRequest>,
        results: Sender<MemoryCommitmentResult>,
    ) -> CudaResult<()> {
        LOCAL_LOGGER.with_borrow_mut(|l| {
            l.timer = timer;
        });
        log::info!("started processing memory commitment batch");
        let context = &self.context;
        for request in requests {
            let MemoryCommitmentRequest {
                circuit_type,
                circuit,
                log_lde_factor,
                log_tree_cap_size,
                index,
                tracing_data,
            } = request;
            let mut transfer = TracingDataTransfer::new(circuit_type, tracing_data.clone(), context)?;
            transfer.schedule_transfer(context)?;
            let job = commit_memory(
                transfer,
                &circuit,
                log_lde_factor,
                log_tree_cap_size,
                context,
            )?;
            let merkle_tree_caps = job.finish()?;
            let result = MemoryCommitmentResult {
                index,
                tracing_data,
                merkle_tree_caps,
            };
            results.send(result).unwrap()
        }
        log::info!("finished processing memory commitment batch");
        Ok(())
    }

    fn process_proof_batch(
        &self,
        timer: Instant,
        requests: Receiver<ProofRequest>,
        results: Sender<ProofResult>,
    ) -> CudaResult<()> {
        LOCAL_LOGGER.with_borrow_mut(|l| {
            l.timer = timer;
        });
        log::info!("started processing proof batch");
        for request in requests {
            let ProofRequest {
                circuit_type,
                circuit,
                log_lde_factor,
                log_tree_cap_size,
                index,
                tracing_data,
            } = request;

            // Process the proof request
            todo!()
        }
        log::info!("finished processing proof batch");
        Ok(())
    }

    fn process_batches(
        &mut self,
        batches: Receiver<GpuWorkBatch>,
    ) -> CudaResult<()> {
        for batch in batches {
            match batch {
                GpuWorkBatch::MemoryCommitment {
                    timer,
                    requests,
                    results,
                } => {
                    self.process_memory_commitment_batch(timer, requests, results)?;
                }
                GpuWorkBatch::Proof {
                    timer,
                    receiver,
                    sender,
                } => {
                    self.process_proof_batch(timer, receiver, sender)?;
                }
            }
        }
        Ok(())
    }
}

pub fn get_gpu_worker_func(
    device_id: i32,
    timer: Instant,
    prover_context_config: ProverContextConfig,
    batches: Receiver<GpuWorkBatch>,
    is_initialized: Sender<()>,
) -> impl FnOnce() + Send + 'static {
    move || {
        LOCAL_LOGGER.with_borrow_mut(|l| {
            l.timer = timer;
        });
        let mut worker = GpuWorker::new(device_id, prover_context_config).unwrap();
        is_initialized.send(()).unwrap();
        worker.process_batches(batches).unwrap();
    }
}
