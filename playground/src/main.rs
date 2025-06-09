#![feature(allocator_api)]
#![feature(vec_push_within_capacity)]
#![feature(new_zeroed_alloc)]
#![feature(iter_array_chunks)]

pub mod cpu_worker;
pub mod gpu_worker;
pub mod logger;
pub mod messages;
// mod old_tracer;
pub mod tracer;

use crate::cpu_worker::{get_cpu_worker_func, CpuWorkerMode, CyclesChunk, SetupAndTeardownChunk};
use crate::gpu_worker::{
    get_gpu_worker_func, GpuWorkBatch, MemoryCommitmentRequest, MemoryCommitmentResult,
};
use crate::logger::{GLOBAL_LOGGER, LOCAL_LOGGER};
use crate::messages::WorkerResult;
use crate::tracer::CycleTracingData;
use crossbeam_channel::{bounded, unbounded};
use execution_utils::get_padded_binary;
use gpu_prover::prover::context::{MemPoolProverContext, ProverContext, ProverContextConfig};
use gpu_prover::prover::tracing_data::TracingDataHost;
use gpu_prover::witness::trace_main::MainCircuitType::RiscVCycles;
use gpu_prover::witness::trace_main::MainTraceHost;
use gpu_prover::witness::CircuitType;
use prover::risc_v_simulator::abstractions::non_determinism::QuasiUARTSource;
use prover::risc_v_simulator::cycle::IMStandardIsaConfig;
use prover::ShuffleRamSetupAndTeardown;
use rayon::{Scope, ThreadPoolBuilder};
use std::alloc::Global;
use std::collections::HashMap;
use std::io::Read;
use std::sync::Arc;
use trace_and_split::setups;
use trace_and_split::setups::MainCircuitPrecomputations;
use worker::Worker;

fn main() {
    rayon::scope(main_in_scope)
}

fn main_in_scope(scope: &Scope) {
    type C = IMStandardIsaConfig;
    // type A = <MemPoolProverContext as ProverContext>::HostAllocator;
    log::set_logger(&GLOBAL_LOGGER).unwrap();
    log::set_max_level(log::LevelFilter::Info);
    LOCAL_LOGGER.with_borrow_mut(|l| {
        l.name = "main".to_string();
    });
    MemPoolProverContext::initialize_host_allocator(8, 1 << 8, 22).unwrap();
    let (gpu_worker_batches_sender, gpu_worker_batches_receiver) = unbounded();
    let (gpu_worker_initialized_sender, gpu_worker_initialized_receiver) = bounded(0);
    let gpu_worker = get_gpu_worker_func::<MemPoolProverContext>(
        0,
        LOCAL_LOGGER.with_borrow(|l| l.timer),
        ProverContextConfig::default(),
        gpu_worker_batches_receiver,
        gpu_worker_initialized_sender,
    );
    scope.spawn(|_| gpu_worker());
    log::info!("GPU workers spawned");
    let mut binary = vec![];
    std::fs::File::open("examples/hashed_fibonacci/app.bin")
        .unwrap()
        .read_to_end(&mut binary)
        .unwrap();
    let binary = get_padded_binary(&binary);
    log::info!("loaded binary");
    let main_circuit_precomputations =
        setups::get_main_riscv_circuit_setup::<Global, Global>(&binary, &Worker::new());
    log::info!("got main circuit precomputations");
    let MainCircuitPrecomputations {
        compiled_circuit, ..
    } = main_circuit_precomputations;
    let compiled_circuit = Arc::new(compiled_circuit);
    let non_determinism_source = Arc::new(QuasiUARTSource::new_with_reads(vec![1 << 24, 0]));
    let delegation_factories = setups::delegation_factories_for_machine::<C, _>();
    log::info!("got delegation factories");
    let cycles_per_circuit = setups::num_cycles_for_machine::<C>();
    let trace_len = setups::trace_len_for_machine::<C>();
    assert_eq!(cycles_per_circuit + 1, trace_len);
    let num_instances_upper_bound = 64;
    let binary = Arc::new(binary.into_boxed_slice());
    let thread_pool = ThreadPoolBuilder::new().num_threads(12).build().unwrap();
    log::info!(
        "thread pool created with {} threads",
        thread_pool.current_num_threads()
    );
    let (free_setup_and_teardowns_sender, free_setup_and_teardowns_receiver) = unbounded();
    for _ in 0..2 {
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
    for _ in 0..8 {
        let message = CycleTracingData::with_cycles_capacity(cycles_per_circuit);
        free_cycle_tracing_data_sender.send(message).unwrap();
    }
    let mut free_delegation_witness_senders = HashMap::new();
    let mut free_delegation_witness_receivers = HashMap::new();
    for (&id, factory) in &delegation_factories {
        let (sender, receiver) = unbounded();
        for _ in 0..2 {
            sender.send(factory()).unwrap();
        }
        free_delegation_witness_senders.insert(id, sender);
        free_delegation_witness_receivers.insert(id, receiver);
    }
    let timer = std::time::Instant::now();
    log::info!("channels are initialized");
    gpu_worker_initialized_receiver.recv().unwrap();
    log::info!("GPU worker is ready");
    log::info!("resetting timer");
    LOCAL_LOGGER.with_borrow_mut(|l| l.timer = timer);
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
        num_instances_upper_bound,
        binary.clone(),
        non_determinism_source.clone(),
        ram_tracing_mode,
        work_results_sender.clone(),
    );
    thread_pool.spawn(ram_tracing_worker);
    cpu_worker_id += 1;
    let split_count = 4;
    for split_index in 0..split_count {
        let ram_tracing_mode = CpuWorkerMode::TraceCycles {
            split_count,
            split_index,
            free_cycle_tracing_data: free_cycle_tracing_data_receiver.clone(),
        };
        let cycles_tracing_worker = get_cpu_worker_func::<C, _>(
            cpu_worker_id,
            timer,
            num_instances_upper_bound,
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
        num_instances_upper_bound,
        binary.clone(),
        non_determinism_source.clone(),
        delegation_mode,
        work_results_sender.clone(),
    );
    thread_pool.spawn(delegation_tracing_worker);
    log::info!("CPU workers spawned");
    drop(free_delegation_witness_senders);
    let (memory_commitment_requests_sender, memory_commitment_requests_receiver) = unbounded();
    let gpu_work_batch = GpuWorkBatch::MemoryCommitment {
        timer,
        requests: memory_commitment_requests_receiver,
        results: work_results_sender.clone(),
    };
    gpu_worker_batches_sender.send(gpu_work_batch).unwrap();
    drop(work_results_sender);
    let mut final_chunks_count = None;
    let mut final_register_values = None;
    let mut memory_commitments = vec![];
    let mut memory_commitment_requests_count = 0;
    let mut setup_and_teardown_chunks = HashMap::new();
    let mut cycles_chunks = HashMap::new();
    let send_memory_commitment_request =
        move |index: usize,
              setup_and_teardown_chunk: Option<ShuffleRamSetupAndTeardown<_>>,
              cycles_chunk: CycleTracingData<_>| {
            log::info!("sending memory commitment request for chunk {index}");
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
            let memory_commitment_request = MemoryCommitmentRequest {
                circuit_type: CircuitType::Main(RiscVCycles),
                circuit: compiled_circuit.clone(),
                log_lde_factor: 1,
                log_tree_cap_size: 5,
                index,
                tracing_data,
            };
            memory_commitment_requests_sender
                .send(memory_commitment_request)
                .unwrap();
        };
    let mut send_memory_commitment_request = Some(send_memory_commitment_request);
    for result in worker_results_receiver {
        match result {
            WorkerResult::SetupAndTeardownChunk(chunk) => {
                let SetupAndTeardownChunk {
                    index,
                    chunk: setup_and_teardown_chunk,
                } = chunk;
                log::info!("received setup and teardown chunk {index}");
                if let Some(cycles_chunk) = cycles_chunks.remove(&index) {
                    let send = send_memory_commitment_request.as_ref().unwrap();
                    send(index, setup_and_teardown_chunk, cycles_chunk);
                    memory_commitment_requests_count += 1;
                } else {
                    setup_and_teardown_chunks.insert(index, setup_and_teardown_chunk);
                }
            }
            WorkerResult::RAMTracingResult {
                chunks_traced_count,
                final_register_values: values,
            } => {
                log::info!("received RAM tracing result with final register values, chunks traced: {chunks_traced_count}");
                final_chunks_count = Some(chunks_traced_count);
                final_register_values = Some(values);
            }
            WorkerResult::CyclesChunk(chunk) => {
                let CyclesChunk { index, data } = chunk;
                log::info!("received cycles chunk {index}");
                if let Some(setup_and_teardown_chunk) = setup_and_teardown_chunks.remove(&index) {
                    let send = send_memory_commitment_request.as_ref().unwrap();
                    send(index, setup_and_teardown_chunk, data);
                    memory_commitment_requests_count += 1;
                } else {
                    cycles_chunks.insert(index, data);
                }
            }
            WorkerResult::CyclesTracingResult {
                chunks_traced_count,
            } => {
                log::info!("received cycles tracing result, chunks traced: {chunks_traced_count}");
            }
            WorkerResult::DelegationWitness(witness) => {
                let id = witness.delegation_type;
                log::info!("received delegation witnesses for delegation id {id}");
            }
            WorkerResult::DelegationTracingResult {
                delegation_chunks_counts,
            } => {
                for (id, count) in delegation_chunks_counts {
                    log::info!("received delegation tracing result for delegation id {id}, chunks traced: {count}");
                }
            }
            WorkerResult::MemoryCommitment(commitment) => {
                let MemoryCommitmentResult {
                    index,
                    tracing_data,
                    merkle_tree_caps,
                } = commitment;
                log::info!("received memory commitment result for chunk {index}");
                match tracing_data {
                    TracingDataHost::Main {
                        setup_and_teardown,
                        trace,
                    } => {
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
                    }
                    _ => panic!("unexpected tracing data type"),
                }
                memory_commitments.push((index, merkle_tree_caps));
            }
        };
        if send_memory_commitment_request.is_none() {
            continue;
        }
        if let Some(count) = final_chunks_count {
            if memory_commitment_requests_count == count {
                log::info!("sent all memory commitment requests");
                send_memory_commitment_request = None;
            }
        }
    }
    let final_chunks_count = final_chunks_count.unwrap();
    assert_ne!(final_chunks_count, 0);
    let _final_register_values = final_register_values.as_ref().unwrap();
    assert_eq!(memory_commitments.len(), final_chunks_count);
    assert!(send_memory_commitment_request.is_none());
    assert!(setup_and_teardown_chunks.is_empty());
    assert!(cycles_chunks.is_empty());
    drop(gpu_worker_batches_sender);
}
