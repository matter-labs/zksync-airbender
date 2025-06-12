#![feature(allocator_api)]
#![feature(vec_push_within_capacity)]
#![feature(new_zeroed_alloc)]
#![feature(iter_array_chunks)]
#![feature(let_chains)]

pub mod cpu_worker;
pub mod gpu_worker;
pub mod logger;
pub mod messages;
// mod old_tracer;
mod gpu_manager;
mod precomputations;
pub mod tracer;

use crate::cpu_worker::{get_cpu_worker_func, CpuWorkerMode, CyclesChunk, SetupAndTeardownChunk};
use crate::gpu_manager::{get_gpu_manager_func, GpuWorkBatch};
use crate::gpu_worker::{GpuWorkRequest, MemoryCommitmentRequest, MemoryCommitmentResult, ProofRequest, ProofResult};
use crate::logger::{GLOBAL_LOGGER, LOCAL_LOGGER};
use crate::messages::WorkerResult;
use crate::precomputations::CircuitPrecomputationsHost;
use crate::tracer::CycleTracingData;
use crossbeam_channel::{bounded, unbounded};
use execution_utils::get_padded_binary;
use gpu_prover::allocator::host::ConcurrentStaticHostAllocator;
use gpu_prover::prover::context::{MemPoolProverContext, ProverContext};
use gpu_prover::prover::tracing_data::TracingDataHost;
use gpu_prover::witness::trace_delegation::DelegationTraceHost;
use gpu_prover::witness::trace_main::MainCircuitType::RiscVCycles;
use gpu_prover::witness::trace_main::MainTraceHost;
use gpu_prover::witness::CircuitType;
use prover::risc_v_simulator::abstractions::non_determinism::QuasiUARTSource;
use prover::risc_v_simulator::cycle::IMStandardIsaConfig;
use prover::tracers::delegation::DelegationWitness;
use prover::ShuffleRamSetupAndTeardown;
use std::alloc::Global;
use std::collections::HashMap;
use std::io::Read;
use std::sync::Arc;
use field::{Field, Mersenne31Field, Mersenne31Quartic};
use prover::definitions::{ExternalChallenges, ExternalDelegationArgumentChallenges};
use trace_and_split::setups;
use worker::Worker;

fn main() {
    rayon::scope(main_in_scope)
}

fn main_in_scope(scope: &rayon::Scope) {
    type C = IMStandardIsaConfig;
    type A = ConcurrentStaticHostAllocator;

    log::set_logger(&GLOBAL_LOGGER).unwrap();
    log::set_max_level(log::LevelFilter::Info);
    let timer = std::time::Instant::now();
    LOCAL_LOGGER.with_borrow_mut(|l| {
        l.name = "main".to_string();
        l.timer = timer;
    });
    let (gpu_workers_initialized_sender, gpu_workers_initialized_receiver) = bounded(0);
    let (gpu_workers_timer_reset_sender, gpu_workers_timer_reset_receiver) = bounded(0);
    let (gpu_work_batches_sender, gpu_work_batches_receiver) = unbounded();
    let gpu_manager_func = get_gpu_manager_func::<MemPoolProverContext>(
        timer,
        gpu_workers_initialized_sender,
        gpu_workers_timer_reset_receiver,
        gpu_work_batches_receiver,
    );
    scope.spawn(gpu_manager_func);
    log::info!("GPU manager spawned");
    gpu_workers_initialized_receiver.recv().unwrap();
    log::info!("GPU workers initialized");
    let mut binary = vec![];
    std::fs::File::open("examples/hashed_fibonacci/app.bin")
        .unwrap()
        .read_to_end(&mut binary)
        .unwrap();
    let binary = get_padded_binary(&binary);
    log::info!("loaded binary");
    let worker = Worker::new();
    let main_circuit_precomputations: CircuitPrecomputationsHost<Global, A> =
        setups::get_main_riscv_circuit_setup::<Global, A>(&binary, &worker).into();
    log::info!("got main circuit precomputations");
    let delegation_circuits_precomputations: HashMap<_, CircuitPrecomputationsHost<Global, A>> =
        setups::all_delegation_circuits_precomputations::<Global, A>(&worker)
            .into_iter()
            .map(|(id, p)| (id as u16, p.into()))
            .collect();
    log::info!("got delegation circuits precomputations");
    let delegation_factories = setups::delegation_factories_for_machine::<C, _>();
    log::info!("got delegation factories");
    let non_determinism_source = Arc::new(QuasiUARTSource::new_with_reads(vec![0, 1 << 19]));
    let cycles_per_circuit = setups::num_cycles_for_machine::<C>();
    let trace_len = setups::trace_len_for_machine::<C>();
    assert_eq!(cycles_per_circuit + 1, trace_len);
    let binary = Arc::new(binary.into_boxed_slice());
    const NUM_INSTANCES_UPPER_BOUND: usize = 64;
    const NUM_THREADS: usize = 6;
    const NUM_CYCLES_TRACING_WORKERS: usize = NUM_THREADS - 2;
    let thread_pool = rayon::ThreadPoolBuilder::new()
        .num_threads(12)
        .build()
        .unwrap();
    log::info!(
        "thread pool created with {} threads",
        thread_pool.current_num_threads()
    );
    let (free_setup_and_teardowns_sender, free_setup_and_teardowns_receiver) = unbounded();
    for _ in 0..3 {
        let mut lazy_init_data = Vec::with_capacity_in(
            cycles_per_circuit,
            <MemPoolProverContext as ProverContext>::HostAllocator::default(),
        );
        unsafe {
            lazy_init_data.set_len(cycles_per_circuit);
        }
        let message = ShuffleRamSetupAndTeardown { lazy_init_data };
        free_setup_and_teardowns_sender.send(message).unwrap();
    }
    let (free_cycle_tracing_data_sender, free_cycle_tracing_data_receiver) = unbounded();
    for _ in 0..3 * NUM_CYCLES_TRACING_WORKERS {
        let message = CycleTracingData::with_cycles_capacity(cycles_per_circuit);
        free_cycle_tracing_data_sender.send(message).unwrap();
    }
    let mut free_delegation_witness_senders = HashMap::new();
    let mut free_delegation_witness_receivers = HashMap::new();
    for (&id, factory) in &delegation_factories {
        let (sender, receiver) = unbounded();
        for _ in 0..3 {
            sender.send(factory()).unwrap();
        }
        free_delegation_witness_senders.insert(id, sender);
        free_delegation_witness_receivers.insert(id, receiver);
    }
    log::info!("channels are initialized");
    log::info!("resetting timer");
    let timer = std::time::Instant::now();
    LOCAL_LOGGER.with_borrow_mut(|l| l.timer = timer);
    gpu_workers_timer_reset_sender.send(timer).unwrap();
    log::info!("go!");
    let (work_results_sender, worker_results_receiver) = unbounded();
    log::info!("spawning CPU workers");
    let ram_tracing_mode = CpuWorkerMode::TraceTouchedRam {
        free_setup_and_teardowns: free_setup_and_teardowns_receiver.clone(),
    };
    let mut cpu_worker_id = 0;
    let ram_tracing_worker = get_cpu_worker_func::<C, _>(
        cpu_worker_id,
        timer,
        NUM_INSTANCES_UPPER_BOUND,
        binary.clone(),
        non_determinism_source.clone(),
        ram_tracing_mode,
        work_results_sender.clone(),
    );
    thread_pool.spawn(ram_tracing_worker);
    cpu_worker_id += 1;
    for split_index in 0..NUM_CYCLES_TRACING_WORKERS {
        let ram_tracing_mode = CpuWorkerMode::TraceCycles {
            split_count: NUM_CYCLES_TRACING_WORKERS,
            split_index,
            free_cycle_tracing_data: free_cycle_tracing_data_receiver.clone(),
        };
        let cycles_tracing_worker = get_cpu_worker_func::<C, _>(
            cpu_worker_id,
            timer,
            NUM_INSTANCES_UPPER_BOUND,
            binary.clone(),
            non_determinism_source.clone(),
            ram_tracing_mode,
            work_results_sender.clone(),
        );
        thread_pool.spawn(cycles_tracing_worker);
        cpu_worker_id += 1;
    }
    let delegation_mode = CpuWorkerMode::TraceDelegations {
        free_delegation_witnesses: free_delegation_witness_receivers.clone(),
    };
    let delegation_tracing_worker = get_cpu_worker_func::<C, _>(
        cpu_worker_id,
        timer,
        NUM_INSTANCES_UPPER_BOUND,
        binary.clone(),
        non_determinism_source.clone(),
        delegation_mode,
        work_results_sender.clone(),
    );
    thread_pool.spawn(delegation_tracing_worker);
    log::info!("CPU workers spawned");
    let (gpu_work_requests_sender, gpu_work_requests_receiver) = unbounded();
    let gpu_work_batch = GpuWorkBatch {
        receiver: gpu_work_requests_receiver,
        sender: work_results_sender.clone(),
    };
    gpu_work_batches_sender.send(gpu_work_batch).unwrap();
    drop(work_results_sender);
    let mut final_main_chunks_count = None;
    let mut final_register_values = None;
    let mut final_delegation_chunks_counts = None;
    let mut main_memory_commitments = vec![];
    let mut delegation_memory_commitments = HashMap::new();
    let mut main_proofs = vec![];
    let mut delegation_proofs = HashMap::new();
    let mut setup_and_teardown_chunks = HashMap::new();
    let mut cycles_chunks = HashMap::new();
    let mut delegation_work_sender = Some(gpu_work_requests_sender.clone());
    let proving = true;
    let send_main_work_request =
        move |circuit_sequence: usize,
              setup_and_teardown_chunk: Option<ShuffleRamSetupAndTeardown<_>>,
              cycles_chunk: CycleTracingData<_>| {
            if proving {
                log::info!("sending main circuit proof request for chunk {circuit_sequence}");
            } else {
                log::info!("sending main circuit memory commitment request for chunk {circuit_sequence}");
            }
            let setup_and_teardown = setup_and_teardown_chunk.map(|chunk| chunk.into());
            let trace = MainTraceHost {
                cycles_traced: cycles_chunk.per_cycle_data.len(),
                cycle_data: Arc::new(cycles_chunk.per_cycle_data),
                num_cycles_chunk_size: cycles_per_circuit,
            };
            let tracing_data = TracingDataHost::Main {
                setup_and_teardown,
                trace,
            };
            let request = if proving {
                let proof_request = ProofRequest {
                    circuit_type: CircuitType::Main(RiscVCycles),
                    circuit_sequence,
                    precomputations: main_circuit_precomputations.clone(),
                    tracing_data,
                    external_challenges: ExternalChallenges {
                        memory_argument: Default::default(),
                        delegation_argument: Some(ExternalDelegationArgumentChallenges{
                            delegation_argument_linearization_challenges: Default::default(),
                            delegation_argument_gamma: Mersenne31Quartic::from_array_of_base([Mersenne31Field::ONE; 4]),
                        }),
                    },
                };
                GpuWorkRequest::Proof(proof_request)
            }
            else {
                let memory_commitment_request = MemoryCommitmentRequest {
                    circuit_type: CircuitType::Main(RiscVCycles),
                    circuit_sequence,
                    precomputations: main_circuit_precomputations.clone(),
                    tracing_data,
                };
                GpuWorkRequest::MemoryCommitment(memory_commitment_request)
            };
            gpu_work_requests_sender.send(request).unwrap();
        };
    let mut send_main_work_request = Some(send_main_work_request);
    let mut main_work_requests_count = 0;
    for result in worker_results_receiver {
        match result {
            WorkerResult::SetupAndTeardownChunk(chunk) => {
                let SetupAndTeardownChunk {
                    index,
                    chunk: setup_and_teardown_chunk,
                } = chunk;
                log::info!("received setup and teardown chunk {index}");
                if let Some(cycles_chunk) = cycles_chunks.remove(&index) {
                    let send = send_main_work_request.as_ref().unwrap();
                    send(index, setup_and_teardown_chunk, cycles_chunk);
                    main_work_requests_count += 1;
                } else {
                    setup_and_teardown_chunks.insert(index, setup_and_teardown_chunk);
                }
            }
            WorkerResult::RAMTracingResult {
                chunks_traced_count,
                final_register_values: values,
            } => {
                log::info!("received RAM tracing result with final register values, chunks traced: {chunks_traced_count}");
                let previous_count = final_main_chunks_count.replace(chunks_traced_count);
                assert!(previous_count.is_none_or(|v| v == chunks_traced_count));
                final_register_values = Some(values);
            }
            WorkerResult::CyclesChunk(chunk) => {
                let CyclesChunk { index, data } = chunk;
                log::info!("received cycles chunk {index}");
                if let Some(setup_and_teardown_chunk) = setup_and_teardown_chunks.remove(&index) {
                    let send = send_main_work_request.as_ref().unwrap();
                    send(index, setup_and_teardown_chunk, data);
                    main_work_requests_count += 1;
                } else {
                    cycles_chunks.insert(index, data);
                }
            }
            WorkerResult::CyclesTracingResult {
                chunks_traced_count,
            } => {
                log::info!("received cycles tracing result, chunks traced: {chunks_traced_count}");
                let previous_count = final_main_chunks_count.replace(chunks_traced_count);
                assert!(previous_count.is_none_or(|v| v == chunks_traced_count));
            }
            WorkerResult::DelegationWitness(witness) => {
                let id = witness.delegation_type;
                log::info!("received delegation witnesses for delegation id {id}");
                let tracing_data = TracingDataHost::Delegation(witness.into());
                let request = if proving {
                    log::info!("sending delegation proof request for delegation id {id}");
                    let proof_request = ProofRequest {
                        circuit_type: CircuitType::from_delegation_type(id),
                        circuit_sequence: 0,
                        precomputations: delegation_circuits_precomputations[&id].clone(),
                        tracing_data,
                        external_challenges: ExternalChallenges {
                            memory_argument: Default::default(),
                            delegation_argument: Some(ExternalDelegationArgumentChallenges{
                                delegation_argument_linearization_challenges: Default::default(),
                                delegation_argument_gamma: Mersenne31Quartic::from_array_of_base([Mersenne31Field::ONE; 4]),
                            }),
                        },
                    };
                    GpuWorkRequest::Proof(proof_request)
                } else {
                    log::info!("sending delegation memory commitment request for delegation id {id}");
                    let memory_commitment_request = MemoryCommitmentRequest {
                        circuit_type: CircuitType::from_delegation_type(id),
                        circuit_sequence: 0,
                        precomputations: delegation_circuits_precomputations[&id].clone(),
                        tracing_data,
                    };
                    GpuWorkRequest::MemoryCommitment(memory_commitment_request)
                };
                delegation_work_sender
                    .as_ref()
                    .unwrap()
                    .send(request)
                    .unwrap();
            }
            WorkerResult::DelegationTracingResult {
                delegation_chunks_counts,
            } => {
                for (id, count) in delegation_chunks_counts.iter() {
                    log::info!("received delegation tracing result for delegation id {id}, chunks traced: {count}");
                }
                final_delegation_chunks_counts = Some(delegation_chunks_counts);
                log::info!("sent all delegation memory commitment requests");
                delegation_work_sender = None;
            }
            WorkerResult::MemoryCommitment(commitment) => {
                let MemoryCommitmentResult {
                    circuit_type,
                    circuit_sequence,
                    tracing_data,
                    merkle_tree_caps,
                } = commitment;
                match tracing_data {
                    TracingDataHost::Main {
                        setup_and_teardown,
                        trace,
                    } => {
                        log::info!(
                            "received memory commitment for main circuit type: {:?} circuit sequence: {}",
                            circuit_type, circuit_sequence
                        );
                        if let Some(setup_and_teardown) = setup_and_teardown {
                            let lazy_init_data =
                                Arc::into_inner(setup_and_teardown.lazy_init_data).unwrap();
                            let setup_and_teardown = ShuffleRamSetupAndTeardown { lazy_init_data };
                            log::info!("returning free setup and teardown");
                            free_setup_and_teardowns_sender
                                .send(setup_and_teardown)
                                .unwrap();
                        }
                        let mut per_cycle_data = Arc::into_inner(trace.cycle_data).unwrap();
                        per_cycle_data.clear();
                        let cycle_tracing_data = CycleTracingData { per_cycle_data };
                        log::info!("returning free cycle tracing data");
                        free_cycle_tracing_data_sender
                            .send(cycle_tracing_data)
                            .unwrap();
                        main_memory_commitments.push((circuit_sequence, merkle_tree_caps));
                    }
                    TracingDataHost::Delegation(witness) => {
                        log::info!(
                            "received memory commitment for delegation circuit type: {:?}",
                            circuit_type
                        );
                        let DelegationTraceHost {
                            num_requests,
                            num_register_accesses_per_delegation,
                            num_indirect_reads_per_delegation,
                            num_indirect_writes_per_delegation,
                            base_register_index,
                            delegation_type,
                            indirect_accesses_properties,
                            write_timestamp,
                            register_accesses,
                            indirect_reads,
                            indirect_writes,
                        } = witness;
                        let mut write_timestamp = Arc::into_inner(write_timestamp).unwrap();
                        write_timestamp.clear();
                        let mut register_accesses = Arc::into_inner(register_accesses).unwrap();
                        register_accesses.clear();
                        let mut indirect_reads = Arc::into_inner(indirect_reads).unwrap();
                        indirect_reads.clear();
                        let mut indirect_writes = Arc::into_inner(indirect_writes).unwrap();
                        indirect_writes.clear();
                        let witness = DelegationWitness {
                            num_requests,
                            num_register_accesses_per_delegation,
                            num_indirect_reads_per_delegation,
                            num_indirect_writes_per_delegation,
                            base_register_index,
                            delegation_type,
                            indirect_accesses_properties,
                            write_timestamp,
                            register_accesses,
                            indirect_reads,
                            indirect_writes,
                        };
                        log::info!("returning free delegation tracing data");
                        free_delegation_witness_senders
                            .get(&delegation_type)
                            .unwrap()
                            .send(witness)
                            .unwrap();
                        delegation_memory_commitments
                            .entry(delegation_type)
                            .or_insert_with(Vec::new)
                            .push(merkle_tree_caps);
                    }
                }
            }
            WorkerResult::Proof(proof) => {
                let ProofResult {
                    circuit_type,
                    circuit_sequence,
                    tracing_data,
                    proof,
                } = proof;
                match tracing_data {
                    TracingDataHost::Main {
                        setup_and_teardown,
                        trace,
                    } => {
                        log::info!(
                            "received proof for main circuit type: {:?} circuit sequence: {}",
                            circuit_type, circuit_sequence
                        );
                        if let Some(setup_and_teardown) = setup_and_teardown {
                            let lazy_init_data =
                                Arc::into_inner(setup_and_teardown.lazy_init_data).unwrap();
                            let setup_and_teardown = ShuffleRamSetupAndTeardown { lazy_init_data };
                            log::info!("returning free setup and teardown");
                            free_setup_and_teardowns_sender
                                .send(setup_and_teardown)
                                .unwrap();
                        }
                        let mut per_cycle_data = Arc::into_inner(trace.cycle_data).unwrap();
                        per_cycle_data.clear();
                        let cycle_tracing_data = CycleTracingData { per_cycle_data };
                        log::info!("returning free cycle tracing data");
                        free_cycle_tracing_data_sender
                            .send(cycle_tracing_data)
                            .unwrap();
                        main_proofs.push((circuit_sequence, proof));
                    }
                    TracingDataHost::Delegation(witness) => {
                        log::info!(
                            "received memory commitment for delegation circuit type: {:?}",
                            circuit_type
                        );
                        let DelegationTraceHost {
                            num_requests,
                            num_register_accesses_per_delegation,
                            num_indirect_reads_per_delegation,
                            num_indirect_writes_per_delegation,
                            base_register_index,
                            delegation_type,
                            indirect_accesses_properties,
                            write_timestamp,
                            register_accesses,
                            indirect_reads,
                            indirect_writes,
                        } = witness;
                        let mut write_timestamp = Arc::into_inner(write_timestamp).unwrap();
                        write_timestamp.clear();
                        let mut register_accesses = Arc::into_inner(register_accesses).unwrap();
                        register_accesses.clear();
                        let mut indirect_reads = Arc::into_inner(indirect_reads).unwrap();
                        indirect_reads.clear();
                        let mut indirect_writes = Arc::into_inner(indirect_writes).unwrap();
                        indirect_writes.clear();
                        let witness = DelegationWitness {
                            num_requests,
                            num_register_accesses_per_delegation,
                            num_indirect_reads_per_delegation,
                            num_indirect_writes_per_delegation,
                            base_register_index,
                            delegation_type,
                            indirect_accesses_properties,
                            write_timestamp,
                            register_accesses,
                            indirect_reads,
                            indirect_writes,
                        };
                        log::info!("returning free delegation tracing data");
                        free_delegation_witness_senders
                            .get(&delegation_type)
                            .unwrap()
                            .send(witness)
                            .unwrap();
                        delegation_proofs
                            .entry(delegation_type)
                            .or_insert_with(Vec::new)
                            .push(proof);
                    }
                }
            }
        };
        if send_main_work_request.is_none() {
            continue;
        }
        if let Some(count) = final_main_chunks_count {
            if main_work_requests_count == count {
                log::info!("sent all main memory commitment requests");
                send_main_work_request = None;
            }
        }
    }
    let final_main_chunks_count = final_main_chunks_count.unwrap();
    assert_ne!(final_main_chunks_count, 0);
    let _final_register_values = final_register_values.as_ref().unwrap();
    if proving {
        assert_eq!(main_proofs.len(), final_main_chunks_count);
        for (id, count) in final_delegation_chunks_counts.unwrap() {
            assert_eq!(count, delegation_proofs.get(&id).unwrap().len());
        }
    }
    else {
        assert_eq!(main_memory_commitments.len(), final_main_chunks_count);
        for (id, count) in final_delegation_chunks_counts.unwrap() {
            assert_eq!(count, delegation_memory_commitments.get(&id).unwrap().len());
        }
    }
    assert!(send_main_work_request.is_none());
    assert!(delegation_work_sender.is_none());
    assert!(setup_and_teardown_chunks.is_empty());
    assert!(cycles_chunks.is_empty());
    drop(gpu_work_batches_sender);
}
