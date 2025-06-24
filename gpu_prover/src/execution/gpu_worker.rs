use super::messages::WorkerResult;
use super::precomputations::CircuitPrecomputationsHost;
use crate::circuit_type::CircuitType;
use crate::cudart::device::set_device;
use crate::cudart::result::CudaResult;
use crate::prover::context::{ProverContext, ProverContextConfig};
use crate::prover::memory::{commit_memory, MemoryCommitmentJob};
use crate::prover::proof::{prove, ProofJob};
use crate::prover::setup::SetupPrecomputations;
use crate::prover::tracing_data::{TracingDataHost, TracingDataTransfer};
use crate::witness::trace_main::get_aux_arguments_boundary_values;
use crossbeam_channel::{Receiver, Sender};
use era_cudart::device::get_device_properties;
use fft::GoodAllocator;
use field::Mersenne31Field;
use log::{debug, error, info, trace};
use prover::definitions::{
    AuxArgumentsBoundaryValues, ExternalChallenges, ExternalValues, OPTIMAL_FOLDING_PROPERTIES,
};
use prover::merkle_trees::MerkleTreeCapVarLength;
use prover::prover_stages::Proof;
use std::alloc::Global;
use std::cell::RefCell;
use std::ffi::CStr;
use std::mem;
use std::process::exit;
use std::rc::Rc;
use std::sync::Arc;

type BF = Mersenne31Field;

const NUM_QUERIES: usize = 53;
const POW_BITS: u32 = 28;

pub struct MemoryCommitmentRequest<A: GoodAllocator, B: GoodAllocator = Global> {
    pub batch_id: u64,
    pub circuit_type: CircuitType,
    pub circuit_sequence: usize,
    pub precomputations: CircuitPrecomputationsHost<A, B>,
    pub tracing_data: TracingDataHost<A>,
}

pub struct MemoryCommitmentResult<A: GoodAllocator> {
    pub batch_id: u64,
    pub circuit_type: CircuitType,
    pub circuit_sequence: usize,
    pub tracing_data: TracingDataHost<A>,
    pub merkle_tree_caps: Vec<MerkleTreeCapVarLength>,
}

pub struct ProofRequest<A: GoodAllocator, B: GoodAllocator = Global> {
    pub batch_id: u64,
    pub circuit_type: CircuitType,
    pub circuit_sequence: usize,
    pub precomputations: CircuitPrecomputationsHost<A, B>,
    pub tracing_data: TracingDataHost<A>,
    pub external_challenges: ExternalChallenges,
}

pub struct ProofResult<A: GoodAllocator> {
    pub batch_id: u64,
    pub circuit_type: CircuitType,
    pub circuit_sequence: usize,
    pub tracing_data: TracingDataHost<A>,
    pub proof: Proof,
}

pub enum GpuWorkRequest<A: GoodAllocator, B: GoodAllocator = Global> {
    MemoryCommitment(MemoryCommitmentRequest<A, B>),
    Proof(ProofRequest<A, B>),
}

impl<A: GoodAllocator, B: GoodAllocator> GpuWorkRequest<A, B> {
    pub fn batch_id(&self) -> u64 {
        match self {
            GpuWorkRequest::MemoryCommitment(request) => request.batch_id,
            GpuWorkRequest::Proof(request) => request.batch_id,
        }
    }
}

pub fn get_gpu_worker_func<C: ProverContext>(
    device_id: i32,
    prover_context_config: ProverContextConfig,
    is_initialized: Sender<()>,
    requests: Receiver<Option<GpuWorkRequest<C::HostAllocator, impl GoodAllocator + 'static>>>,
    results: Sender<Option<WorkerResult<C::HostAllocator>>>,
) -> impl FnOnce() + Send + 'static {
    move || {
        let result = gpu_worker::<C>(
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

enum JobType<'a, C: ProverContext> {
    MemoryCommitment(MemoryCommitmentJob<'a, C>),
    Proof(ProofJob<'a, C>),
}

const fn get_tree_cap_size(log_domain_size: u32) -> u32 {
    OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize].total_caps_size_log2 as u32
}

#[derive(Clone)]
struct SetupHolder<'a, C: ProverContext> {
    pub setup: Rc<RefCell<SetupPrecomputations<'a, C>>>,
    pub trace: Arc<Vec<BF, C::HostAllocator>>,
}

fn gpu_worker<C: ProverContext>(
    device_id: i32,
    prover_context_config: ProverContextConfig,
    is_initialized: Sender<()>,
    requests: Receiver<Option<GpuWorkRequest<C::HostAllocator, impl GoodAllocator>>>,
    results: Sender<Option<WorkerResult<C::HostAllocator>>>,
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
    let context = C::new(&prover_context_config)?;
    info!(
        "GPU_WORKER[{device_id}] initialized the GPU memory allocator with {:.3} GB of usable memory",
        context.get_mem_size() as f64 / 1024.0 / 1024.0 / 1024.0
    );
    is_initialized.send(()).unwrap();
    drop(is_initialized);
    let mut current_setup: Option<SetupHolder<C>> = None;
    let mut current_transfer = None;
    let mut current_job = None;
    for request in requests {
        let mut transfer = if let Some(request) = request {
            let (batch_id, circuit_type, circuit_sequence, setup, tracing_data) = match &request {
                GpuWorkRequest::MemoryCommitment(request) => (
                    request.batch_id,
                    request.circuit_type,
                    request.circuit_sequence,
                    None,
                    request.tracing_data.clone(),
                ),
                GpuWorkRequest::Proof(request) => {
                    let batch_id = request.batch_id;
                    let precomputations = &request.precomputations;
                    let setup = if let Some(holder) = &current_setup
                        && Arc::ptr_eq(&holder.trace, &precomputations.setup)
                    {
                        trace!(
                            "BATCH[{batch_id}] GPU_WORKER[{device_id}] proof request reusing setup for circuit {:?}",
                            request.circuit_type,
                        );
                        holder.setup.clone()
                    } else {
                        let lde_factor = precomputations.lde_precomputations.lde_factor;
                        assert!(lde_factor.is_power_of_two());
                        let log_lde_factor = lde_factor.trailing_zeros();
                        let domain_size = precomputations.lde_precomputations.domain_size;
                        assert!(domain_size.is_power_of_two());
                        let log_domain_size = domain_size.trailing_zeros();
                        let log_tree_cap_size = get_tree_cap_size(log_domain_size);
                        let mut setup = SetupPrecomputations::new(
                            &precomputations.compiled_circuit,
                            log_lde_factor,
                            log_tree_cap_size,
                            &context,
                        )?;
                        trace!(
                            "BATCH[{batch_id}] GPU_WORKER[{device_id}] transferring setup for circuit {:?}",
                            request.circuit_type,
                        );
                        setup.schedule_transfer(precomputations.setup.clone(), &context)?;
                        let setup = Rc::new(RefCell::new(setup));
                        current_setup = Some(SetupHolder {
                            setup: setup.clone(),
                            trace: precomputations.setup.clone(),
                        });
                        setup
                    };
                    (
                        request.batch_id,
                        request.circuit_type,
                        request.circuit_sequence,
                        Some(setup),
                        request.tracing_data.clone(),
                    )
                }
            };
            match circuit_type {
                CircuitType::Main(main) => trace!(
                    "BATCH[{batch_id}] GPU_WORKER[{device_id}] transferring trace for main circuit {:?} chunk {}",
                    main,
                    circuit_sequence
                ),
                CircuitType::Delegation(delegation) => trace!(
                    "BATCH[{batch_id}] GPU_WORKER[{device_id}] transferring trace for delegation circuit {:?}",
                    delegation,
                ),
            }
            let mut transfer = TracingDataTransfer::new(circuit_type, tracing_data, &context)?;
            transfer.schedule_transfer(&context)?;
            Some((request, setup, transfer))
        } else {
            None
        };
        mem::swap(&mut current_transfer, &mut transfer);
        let mut job = if let Some((request, setup, transfer)) = transfer {
            let job = match &request {
                GpuWorkRequest::MemoryCommitment(request) => {
                    let batch_id = request.batch_id;
                    match request.circuit_type {
                        CircuitType::Main(main) => trace!(
                            "BATCH[{batch_id}] GPU_WORKER[{device_id}] producing memory commitment for main circuit {:?} chunk {}",
                            main,
                            request.circuit_sequence
                        ),
                        CircuitType::Delegation(delegation) => trace!(
                            "BATCH[{batch_id}] GPU_WORKER[{device_id}] producing memory commitment for delegation circuit {:?}",
                            delegation,
                        ),
                    }
                    let precomputations = &request.precomputations;
                    let lde_factor = precomputations.lde_precomputations.lde_factor;
                    assert!(lde_factor.is_power_of_two());
                    let log_lde_factor = lde_factor.trailing_zeros();
                    let domain_size = precomputations.lde_precomputations.domain_size;
                    assert!(domain_size.is_power_of_two());
                    let log_domain_size = domain_size.trailing_zeros();
                    let log_tree_cap_size = get_tree_cap_size(log_domain_size);
                    let job = commit_memory(
                        transfer,
                        &precomputations.compiled_circuit,
                        log_lde_factor,
                        log_tree_cap_size,
                        &context,
                    )?;
                    JobType::MemoryCommitment(job)
                }
                GpuWorkRequest::Proof(request) => {
                    let batch_id = request.batch_id;
                    match request.circuit_type {
                        CircuitType::Main(main) => trace!(
                            "BATCH[{batch_id}] GPU_WORKER[{device_id}] producing proof for main circuit {:?} chunk {}",
                            main,
                            request.circuit_sequence
                        ),
                        CircuitType::Delegation(delegation) => trace!(
                            "BATCH[{batch_id}] GPU_WORKER[{device_id}] producing proof for delegation circuit {:?}",
                            delegation,
                        ),
                    }
                    let precomputations = &request.precomputations;
                    let aux_boundary_values = match &transfer.data_host {
                        TracingDataHost::Main {
                            setup_and_teardown,
                            trace: _,
                        } => {
                            if let Some(setup_and_teardown) = setup_and_teardown {
                                get_aux_arguments_boundary_values(
                                    &setup_and_teardown.lazy_init_data,
                                    setup_and_teardown.lazy_init_data.len(),
                                )
                            } else {
                                AuxArgumentsBoundaryValues::default()
                            }
                        }
                        TracingDataHost::Delegation(_) => AuxArgumentsBoundaryValues::default(),
                    };
                    let external_values = ExternalValues {
                        challenges: request.external_challenges,
                        aux_boundary_values,
                    };
                    let setup = setup.unwrap();
                    let delegation_processing_type = match request.circuit_type {
                        CircuitType::Main(_) => None,
                        CircuitType::Delegation(delegation) => Some(delegation as u16),
                    };
                    let job = prove(
                        precomputations.compiled_circuit.clone(),
                        external_values,
                        &mut setup.borrow_mut(),
                        transfer,
                        &precomputations.twiddles,
                        &precomputations.lde_precomputations,
                        request.circuit_sequence,
                        delegation_processing_type,
                        precomputations.lde_precomputations.lde_factor,
                        NUM_QUERIES,
                        POW_BITS,
                        None,
                        &context,
                    )?;
                    JobType::Proof(job)
                }
            };
            Some((request, job))
        } else {
            None
        };
        mem::swap(&mut current_job, &mut job);
        let result = if let Some((request, job)) = job {
            match request {
                GpuWorkRequest::MemoryCommitment(request) => {
                    let batch_id = request.batch_id;
                    let MemoryCommitmentRequest {
                        circuit_type,
                        circuit_sequence,
                        tracing_data,
                        ..
                    } = request;
                    let (merkle_tree_caps, commitment_time_ms) = match job {
                        JobType::MemoryCommitment(job) => job.finish()?,
                        JobType::Proof(_) => unreachable!(),
                    };
                    match request.circuit_type {
                        CircuitType::Main(main) => debug!(
                            "BATCH[{batch_id}] GPU_WORKER[{device_id}] produced memory commitment for main circuit {:?} chunk {} in {:.3} ms",
                            main,
                            request.circuit_sequence,
                            commitment_time_ms
                        ),
                        CircuitType::Delegation(delegation) => debug!(
                            "BATCH[{batch_id}] GPU_WORKER[{device_id}] produced memory commitment for delegation circuit {:?} in {:.3} ms",
                            delegation,
                            commitment_time_ms
                        ),
                    }
                    let result = MemoryCommitmentResult {
                        batch_id,
                        circuit_type,
                        tracing_data,
                        merkle_tree_caps,
                        circuit_sequence,
                    };
                    Some(WorkerResult::MemoryCommitment(result))
                }
                GpuWorkRequest::Proof(request) => {
                    let batch_id = request.batch_id;
                    let ProofRequest {
                        circuit_type,
                        circuit_sequence,
                        tracing_data,
                        ..
                    } = request;
                    let (proof, proof_time_ms) = match job {
                        JobType::MemoryCommitment(_) => unreachable!(),
                        JobType::Proof(job) => job.finish()?,
                    };
                    match request.circuit_type {
                        CircuitType::Main(main) => debug!(
                            "BATCH[{batch_id}] GPU_WORKER[{device_id}] produced proof for main circuit {:?} chunk {} in {:.3} ms",
                            main,
                            request.circuit_sequence,
                            proof_time_ms,
                        ),
                        CircuitType::Delegation(delegation) => debug!(
                            "BATCH[{batch_id}] GPU_WORKER[{device_id}] produced proof for delegation circuit {:?} in {:.3} ms",
                            delegation,
                            proof_time_ms,
                        ),
                    }
                    let result = ProofResult {
                        batch_id,
                        circuit_type,
                        tracing_data,
                        proof,
                        circuit_sequence,
                    };
                    Some(WorkerResult::Proof(result))
                }
            }
        } else {
            None
        };
        results.send(result).unwrap()
    }
    assert!(current_transfer.is_none());
    assert!(current_job.is_none());
    trace!("GPU_WORKER[{device_id}] finished");
    Ok(())
}
