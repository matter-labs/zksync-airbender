#![feature(allocator_api)]
#![feature(vec_push_within_capacity)]
#![feature(new_zeroed_alloc)]
#![feature(iter_array_chunks)]

mod cpu_worker;
mod gpu_worker;
mod logger;
mod messages;
mod old_tracer;
mod tracer;

use crate::cpu_worker::{get_cpu_worker_func, CpuWorkerMode, SetupAndTeardownChunk};
use crate::gpu_worker::{get_gpu_worker_func, GpuWorkBatch, MemoryCommitmentRequest};
use crate::logger::{LOCAL_LOGGER, GLOBAL_LOGGER};
use crossbeam_channel::{bounded, unbounded, Receiver, Sender};
use execution_utils::get_padded_binary;
use gpu_prover::allocator::host::ConcurrentStaticHostAllocator;
use gpu_prover::prover::context::{MemPoolProverContext, ProverContext, ProverContextConfig};
use gpu_prover::prover::tracing_data::TracingDataHost;
use gpu_prover::witness::trace_main::MainCircuitType::{MachineWithoutSignedMulDiv, RiscVCycles};
use gpu_prover::witness::trace_main::MainTraceHost;
use gpu_prover::witness::CircuitType;
use log::log;
use prover::risc_v_simulator::abstractions::non_determinism::QuasiUARTSource;
use prover::risc_v_simulator::cycle::IMStandardIsaConfig;
use prover::tracers::delegation::DelegationWitness;
use prover::tracers::main_cycle_optimized::CycleData;
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
    type A = ConcurrentStaticHostAllocator;
    log::set_logger(&GLOBAL_LOGGER).unwrap();
    log::set_max_level(log::LevelFilter::Info);
    LOCAL_LOGGER.with_borrow_mut(|l| {
        l.name = "main".to_string();
    });
    MemPoolProverContext::initialize_host_allocator(8, 1 << 8, 22).unwrap();
    let (gpu_worker_batches_sender, gpu_worker_batches_receiver) = unbounded();
    let (gpu_worker_initialized_sender, gpu_worker_initialized_receiver) = bounded(0);
    let gpu_worker = get_gpu_worker_func(
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
    let main_circuit_precomputations =
        setups::get_main_riscv_circuit_setup::<Global, A>(&binary, &Worker::new());
    let MainCircuitPrecomputations {
        compiled_circuit, ..
    } = main_circuit_precomputations;
    let compiled_circuit = Arc::new(compiled_circuit);
    let non_determinism_source = Arc::new(QuasiUARTSource::new_with_reads(vec![0, 1 << 17]));
    let delegation_factories = setups::delegation_factories_for_machine::<C, A>();
    let cycles_per_circuit = setups::num_cycles_for_machine::<C>();
    let trace_len = setups::trace_len_for_machine::<C>();
    assert_eq!(cycles_per_circuit + 1, trace_len);
    let num_instances_upper_bound = 64;
    let binary = Arc::new(binary.into_boxed_slice());
    let thread_pool = ThreadPoolBuilder::new().num_threads(12).build().unwrap();
    let (free_setup_and_teardowns_sender, free_setup_and_teardowns_receiver) = unbounded();
    for _ in 0..8 {
        let mut lazy_init_data = Vec::with_capacity_in(cycles_per_circuit, A::default());
        unsafe {
            lazy_init_data.set_len(cycles_per_circuit);
        }
        let message = ShuffleRamSetupAndTeardown { lazy_init_data };
        free_setup_and_teardowns_sender.send(message).unwrap();
    }
    let (free_cycle_data_sender, free_cycle_data_receiver) = unbounded();
    for _ in 0..16 {
        let message = CycleData::<C, A>::new_with_cycles_capacity(cycles_per_circuit);
        free_cycle_data_sender.send(message).unwrap();
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
    gpu_worker_initialized_receiver.recv().unwrap();
    log::info!("resetting timer");
    LOCAL_LOGGER.with_borrow_mut(|l| l.timer = timer);
    log::info!("go!");
    let (setup_and_teardown_chunks_sender, setup_and_teardown_chunks_receiver) = unbounded();
    let (final_register_values_sender, final_register_values_receiver) = unbounded();
    let (cycles_chunks_sender, cycles_chunks_receiver) = unbounded();
    let mut delegation_witness_senders = HashMap::new();
    let mut delegation_witness_receivers = HashMap::new();
    for &id in delegation_factories.keys() {
        let (sender, receiver) = unbounded();
        delegation_witness_senders.insert(id, sender);
        delegation_witness_receivers.insert(id, receiver);
    }
    log::info!("spawning CPU workers");
    let ram_tracing_mode = CpuWorkerMode::TraceTouchedRam {
        free_setup_and_teardowns: free_setup_and_teardowns_receiver,
        setup_and_teardown_chunks: setup_and_teardown_chunks_sender,
        final_register_values: final_register_values_sender,
    };
    let mut cpu_worker_id = 0;
    let ram_tracing_worker = get_cpu_worker_func::<C, _>(
        cpu_worker_id,
        timer,
        num_instances_upper_bound,
        binary.clone(),
        non_determinism_source.clone(),
        ram_tracing_mode,
    );
    thread_pool.spawn(ram_tracing_worker);
    cpu_worker_id += 1;
    let split_count = 4;
    for split_index in 0..split_count {
        let ram_tracing_mode = CpuWorkerMode::TraceCycles {
            split_count,
            split_index,
            free_cycle_data: free_cycle_data_receiver.clone(),
            chunks: cycles_chunks_sender.clone(),
        };
        let cycles_tracing_worker = get_cpu_worker_func::<C, _>(
            cpu_worker_id,
            timer,
            num_instances_upper_bound,
            binary.clone(),
            non_determinism_source.clone(),
            ram_tracing_mode,
        );
        thread_pool.spawn(cycles_tracing_worker);
        cpu_worker_id += 1;
    }
    let delegation_mode = CpuWorkerMode::TraceDelegations {
        free_delegation_witnesses: free_delegation_witness_receivers,
        delegation_witnesses: delegation_witness_senders,
    };
    let delegation_tracing_worker = get_cpu_worker_func::<C, _>(
        cpu_worker_id,
        timer,
        num_instances_upper_bound,
        binary.clone(),
        non_determinism_source.clone(),
        delegation_mode,
    );
    thread_pool.spawn(delegation_tracing_worker);
    log::info!("CPU workers spawned");
    drop(free_cycle_data_receiver);
    drop(cycles_chunks_sender);
    drop(free_delegation_witness_senders);
    let (memory_commitment_requests_sender, memory_commitment_requests_receiver) = unbounded();
    let (memory_commitment_results_sender, memory_commitment_results_receiver) = unbounded();
    let gpu_work_batch = GpuWorkBatch::MemoryCommitment {
        timer,
        requests: memory_commitment_requests_receiver,
        results: memory_commitment_results_sender,
    };
    gpu_worker_batches_sender.send(gpu_work_batch).unwrap();
    let mut cycles_chunks = HashMap::new();
    for setup_and_teardown_chunk in setup_and_teardown_chunks_receiver {
        let SetupAndTeardownChunk {
            index,
            chunk: setup_and_teardown_chunk,
        } = setup_and_teardown_chunk;
        log::info!("received setup and teardown chunk {}", index);
        while !cycles_chunks.contains_key(&index) {
            let cycles_chunk = cycles_chunks_receiver.recv().unwrap();
            log::info!("received cycles chunk {}", index);
            cycles_chunks.insert(cycles_chunk.index, cycles_chunk);
        }
        let cycles_chunk = cycles_chunks.remove(&index).unwrap();
        let tracing_data = TracingDataHost::Main {
            setup_and_teardown: setup_and_teardown_chunk.map(|chunk| chunk.into()),
            trace: cycles_chunk.chunk.into(),
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
    }
    drop(memory_commitment_requests_sender);
    drop(gpu_worker_batches_sender);
    let _ = final_register_values_receiver.recv().unwrap();
    log::info!("received final register values");
    for (id, receiver) in delegation_witness_receivers.iter() {
        let count = receiver.iter().count();
        log::info!("received delegation witnesses for {id}: {count}");
    }
    for result in memory_commitment_results_receiver {
        log::info!("received memory commitment result for {:?}", result.index);
    }
}
