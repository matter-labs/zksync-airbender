use crate::logger::LOCAL_LOGGER;
use crate::messages::WorkerResult;
use crossbeam_channel::{Receiver, Sender};
use cs::one_row_compiler::CompiledCircuitArtifact;
use fft::GoodAllocator;
use field::Mersenne31Field;
use gpu_prover::cudart::device::set_device;
use gpu_prover::cudart::result::CudaResult;
use gpu_prover::prover::context::{ProverContext, ProverContextConfig};
use gpu_prover::prover::memory::commit_memory;
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

pub enum GpuWorkBatch<A: GoodAllocator> {
    MemoryCommitment {
        timer: Instant,
        requests: Receiver<MemoryCommitmentRequest<A>>,
        results: Sender<WorkerResult<A>>,
    },
    Proof {
        timer: Instant,
        requests: Receiver<ProofRequest<A>>,
        results: Sender<WorkerResult<A>>,
    },
}

#[allow(dead_code)]
struct GpuWorker<C: ProverContext> {
    device_id: i32,
    context: C,
}

impl<C: ProverContext> GpuWorker<C> {
    fn new(device_id: i32, prover_context_config: ProverContextConfig) -> CudaResult<Self> {
        LOCAL_LOGGER.with_borrow_mut(|l| {
            l.name = format!("GPU[{device_id}]");
        });
        set_device(device_id)?;
        let context = C::new(&prover_context_config)?;
        Ok(GpuWorker { device_id, context })
    }

    fn process_memory_commitment_batch(
        &self,
        timer: Instant,
        requests: Receiver<MemoryCommitmentRequest<C::HostAllocator>>,
        results: Sender<WorkerResult<C::HostAllocator>>,
    ) -> CudaResult<()> {
        LOCAL_LOGGER.with_borrow_mut(|l| {
            l.timer = timer;
        });
        log::info!("started processing memory commitment batch");
        let context = &self.context;
        let mut current_transfer = None;
        let mut current_job = None;
        for request in requests.iter().map(|r| Some(r)).chain([None, None]) {
            let mut transfer = if let Some(request) = request {
                log::info!(
                    "transferring trace for memory commitment for circuit type: {:?}, index: {}",
                    request.circuit_type,
                    request.index
                );
                let mut transfer = TracingDataTransfer::new(
                    request.circuit_type,
                    request.tracing_data.clone(),
                    context,
                )?;
                transfer.schedule_transfer(context)?;
                Some((request, transfer))
            } else {
                None
            };
            mem::swap(&mut current_transfer, &mut transfer);
            let mut job = if let Some((request, transfer)) = transfer {
                log::info!(
                    "producing commitment for circuit type: {:?}, index: {}",
                    request.circuit_type,
                    request.index
                );
                let job = commit_memory(
                    transfer,
                    &request.circuit,
                    request.log_lde_factor,
                    request.log_tree_cap_size,
                    context,
                )?;
                Some((request, job))
            } else {
                None
            };
            mem::swap(&mut current_job, &mut job);
            if let Some((request, job)) = job {
                let MemoryCommitmentRequest {
                    circuit_type,
                    index,
                    tracing_data,
                    ..
                } = request;
                let merkle_tree_caps = job.finish()?;
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
                results
                    .send(WorkerResult::MemoryCommitment(result))
                    .unwrap()
            }
        }
        assert!(current_transfer.is_none());
        assert!(current_job.is_none());
        log::info!("finished processing memory commitment batch");
        Ok(())
    }

    fn process_proof_batch(
        &self,
        _timer: Instant,
        _requests: Receiver<ProofRequest<C::HostAllocator>>,
        _results: Sender<WorkerResult<C::HostAllocator>>,
    ) -> CudaResult<()> {
        todo!()
        // LOCAL_LOGGER.with_borrow_mut(|l| {
        //     l.timer = timer;
        // });
        // log::info!("started processing proof batch");
        // for request in requests {
        //     let ProofRequest {
        //         circuit_type,
        //         circuit,
        //         log_lde_factor,
        //         log_tree_cap_size,
        //         index,
        //         tracing_data,
        //     } = request;
        //
        //     // Process the proof request
        // }
        // log::info!("finished processing proof batch");
        // Ok(())
    }

    fn process_batches(
        &mut self,
        batches: Receiver<GpuWorkBatch<C::HostAllocator>>,
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
                    requests,
                    results,
                } => {
                    self.process_proof_batch(timer, requests, results)?;
                }
            }
        }
        Ok(())
    }
}

pub fn get_gpu_worker_func<C: ProverContext>(
    device_id: i32,
    timer: Instant,
    prover_context_config: ProverContextConfig,
    batches: Receiver<GpuWorkBatch<C::HostAllocator>>,
    is_initialized: Sender<()>,
) -> impl FnOnce() + Send + 'static {
    move || {
        LOCAL_LOGGER.with_borrow_mut(|l| {
            l.timer = timer;
        });
        let mut worker = GpuWorker::<C>::new(device_id, prover_context_config).unwrap();
        is_initialized.send(()).unwrap();
        worker.process_batches(batches).unwrap();
        log::info!("GPU worker finished processing batches");
    }
}
