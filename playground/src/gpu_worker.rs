use crate::logger::LOCAL_LOGGER;
use crate::messages::WorkerResult;
use crate::precomputations::CircuitPrecomputationsHost;
use crossbeam_channel::{Receiver, Sender};
use fft::GoodAllocator;
use field::Mersenne31Field;
use gpu_prover::cudart::device::set_device;
use gpu_prover::cudart::result::CudaResult;
use gpu_prover::prover::context::{ProverContext, ProverContextConfig};
use gpu_prover::prover::memory::{commit_memory, MemoryCommitmentJob};
use gpu_prover::prover::proof::{prove, ProofJob};
use gpu_prover::prover::setup::SetupPrecomputations;
use gpu_prover::prover::tracing_data::{TracingDataHost, TracingDataTransfer};
use gpu_prover::witness::trace_main::get_aux_arguments_boundary_values;
use gpu_prover::witness::CircuitType;
use prover::definitions::{
    AuxArgumentsBoundaryValues, ExternalChallenges, ExternalValues, OPTIMAL_FOLDING_PROPERTIES,
};
use prover::merkle_trees::MerkleTreeCapVarLength;
use prover::prover_stages::Proof;
use std::cell::RefCell;
use std::mem;
use std::rc::Rc;
use std::sync::Arc;
use std::time::Instant;

type BF = Mersenne31Field;

const NUM_QUERIES: usize = 53;
const POW_BITS: u32 = 28;

pub struct MemoryCommitmentRequest<A: GoodAllocator, B: GoodAllocator> {
    pub circuit_type: CircuitType,
    pub circuit_sequence: usize,
    pub precomputations: CircuitPrecomputationsHost<A, B>,
    pub tracing_data: TracingDataHost<B>,
}

pub struct MemoryCommitmentResult<A: GoodAllocator> {
    pub circuit_type: CircuitType,
    pub circuit_sequence: usize,
    pub tracing_data: TracingDataHost<A>,
    pub merkle_tree_caps: Vec<MerkleTreeCapVarLength>,
}

pub struct ProofRequest<A: GoodAllocator, B: GoodAllocator> {
    pub circuit_type: CircuitType,
    pub circuit_sequence: usize,
    pub precomputations: CircuitPrecomputationsHost<A, B>,
    pub tracing_data: TracingDataHost<B>,
    pub external_challenges: ExternalChallenges,
}

pub struct ProofResult<A: GoodAllocator> {
    pub circuit_type: CircuitType,
    pub circuit_sequence: usize,
    pub tracing_data: TracingDataHost<A>,
    pub proof: Proof,
}

pub enum GpuWorkRequest<A: GoodAllocator, B: GoodAllocator> {
    MemoryCommitment(MemoryCommitmentRequest<A, B>),
    Proof(ProofRequest<A, B>),
}

pub fn get_gpu_worker_func<C: ProverContext>(
    timer: Instant,
    device_id: i32,
    prover_context_config: ProverContextConfig,
    is_initialized: Sender<()>,
    timer_reset: Receiver<Instant>,
    requests: Receiver<Option<GpuWorkRequest<impl GoodAllocator + 'static, C::HostAllocator>>>,
    results: Sender<Option<WorkerResult<C::HostAllocator>>>,
) -> impl FnOnce() + Send + 'static {
    move || {
        gpu_worker::<C>(
            timer,
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

const fn get_tree_cap_size(log_domain_size: u32) -> u32 {
    OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize].total_caps_size_log2 as u32
}

#[derive(Clone)]
struct SetupHolder<'a, C: ProverContext> {
    pub setup: Rc<RefCell<SetupPrecomputations<'a, C>>>,
    pub trace: Arc<Vec<BF, C::HostAllocator>>,
}

fn gpu_worker<C: ProverContext>(
    timer: Instant,
    device_id: i32,
    prover_context_config: ProverContextConfig,
    is_initialized: Sender<()>,
    timer_reset: Receiver<Instant>,
    requests: Receiver<Option<GpuWorkRequest<impl GoodAllocator, C::HostAllocator>>>,
    results: Sender<Option<WorkerResult<C::HostAllocator>>>,
) -> CudaResult<()> {
    LOCAL_LOGGER.with_borrow_mut(|l| {
        l.name = format!("GPU[{device_id}]");
        l.timer = timer;
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
    let mut current_setup: Option<SetupHolder<C>> = None;
    let mut current_transfer = None;
    let mut current_job = None;
    for request in requests {
        let mut transfer = if let Some(request) = request {
            let (circuit_type, circuit_sequence, setup, tracing_data) = match &request {
                GpuWorkRequest::MemoryCommitment(request) => (
                    request.circuit_type,
                    request.circuit_sequence,
                    None,
                    request.tracing_data.clone(),
                ),
                GpuWorkRequest::Proof(request) => {
                    let precomputations = &request.precomputations;
                    let setup = if let Some(holder) = &current_setup
                        && Arc::ptr_eq(&holder.trace, &precomputations.setup)
                    {
                        log::info!(
                            "reusing setup for circuit type: {:?}",
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
                        log::info!(
                            "transferring setup for circuit type: {:?}",
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
                        request.circuit_type,
                        request.circuit_sequence,
                        Some(setup),
                        request.tracing_data.clone(),
                    )
                }
            };
            match circuit_type {
                CircuitType::Main(main) => log::info!(
                    "transferring trace for main circuit type: {:?} circuit sequence: {}",
                    main,
                    circuit_sequence
                ),
                CircuitType::Delegation(delegation) => log::info!(
                    "transferring trace for delegation circuit type: {:?}",
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
                    match request.circuit_type {
                        CircuitType::Main(main) => log::info!(
                            "producing memory commitment for main circuit type: {:?} circuit sequence: {}",
                            main,
                            request.circuit_sequence
                        ),
                        CircuitType::Delegation(delegation) => log::info!(
                            "producing memory commitment for delegation circuit type: {:?}",
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
                    match request.circuit_type {
                        CircuitType::Main(main) => log::info!(
                            "producing proof for main circuit type: {:?} circuit sequence: {}",
                            main,
                            request.circuit_sequence
                        ),
                        CircuitType::Delegation(delegation) => log::info!(
                            "producing proof for delegation circuit type: {:?}",
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
                    let MemoryCommitmentRequest {
                        circuit_type,
                        circuit_sequence,
                        tracing_data,
                        ..
                    } = request;
                    let merkle_tree_caps = match job {
                        JobType::MemoryCommitment(job) => job.finish()?,
                        JobType::Proof(_) => unreachable!(),
                    };
                    match request.circuit_type {
                        CircuitType::Main(main) => log::info!(
                            "produced memory commitment for main circuit type: {:?} circuit sequence: {}",
                            main,
                            request.circuit_sequence
                        ),
                        CircuitType::Delegation(delegation) => log::info!(
                            "produced memory commitment for delegation circuit type: {:?}",
                            delegation,
                        ),
                    }
                    let result = MemoryCommitmentResult {
                        circuit_type,
                        tracing_data,
                        merkle_tree_caps,
                        circuit_sequence,
                    };
                    Some(WorkerResult::MemoryCommitment(result))
                }
                GpuWorkRequest::Proof(request) => {
                    let ProofRequest {
                        circuit_type,
                        circuit_sequence,
                        tracing_data,
                        ..
                    } = request;
                    let proof = match job {
                        JobType::MemoryCommitment(_) => unreachable!(),
                        JobType::Proof(job) => job.finish()?,
                    };
                    match request.circuit_type {
                        CircuitType::Main(main) => log::info!(
                            "produced proof for main circuit type: {:?} circuit sequence: {}",
                            main,
                            request.circuit_sequence
                        ),
                        CircuitType::Delegation(delegation) => log::info!(
                            "produced proof for delegation circuit type: {:?}",
                            delegation,
                        ),
                    }
                    let result = ProofResult {
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
    log::info!("GPU worker finished");
    Ok(())
}
