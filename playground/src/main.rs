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

use crate::cpu_worker::{get_cpu_worker, CpuWorkerMode};
use crate::logger::LOCAL_LOGGER;
use crossbeam_channel::{unbounded, Receiver, Sender};
use execution_utils::get_padded_binary;
use gpu_prover::allocator::host::ConcurrentStaticHostAllocator;
use gpu_prover::prover::context::{MemPoolProverContext, ProverContext};
use prover::risc_v_simulator::abstractions::non_determinism::QuasiUARTSource;
use prover::risc_v_simulator::cycle::IMStandardIsaConfig;
use prover::tracers::delegation::DelegationWitness;
use prover::tracers::main_cycle_optimized::CycleData;
use prover::ShuffleRamSetupAndTeardown;
use rayon::ThreadPoolBuilder;
use std::collections::HashMap;
use std::io::Read;
use std::sync::Arc;
use trace_and_split::setups;

fn main() {
    type C = IMStandardIsaConfig;
    type A = ConcurrentStaticHostAllocator;
    log::set_logger(&logger::LOGGER).unwrap();
    log::set_max_level(log::LevelFilter::Info);
    MemPoolProverContext::initialize_host_allocator(8, 1 << 8, 22).unwrap();
    let thread_pool = ThreadPoolBuilder::new().num_threads(12).build().unwrap();
    let mut binary = vec![];
    std::fs::File::open("examples/hashed_fibonacci/app.bin")
        .unwrap()
        .read_to_end(&mut binary)
        .unwrap();
    let binary = get_padded_binary(&binary);
    let non_determinism_source = Arc::new(QuasiUARTSource::new_with_reads(vec![0, 1 << 17]));
    let delegation_factories = setups::delegation_factories_for_machine::<C, A>();
    let cycles_per_circuit = setups::num_cycles_for_machine::<C>();
    let trace_len = setups::trace_len_for_machine::<C>();
    assert_eq!(cycles_per_circuit + 1, trace_len);
    let num_instances_upper_bound = 64;
    let binary = Arc::new(binary.into_boxed_slice());
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
        for _ in 0..2 { sender.send(factory()).unwrap(); }
        free_delegation_witness_senders.insert(id, sender);
        free_delegation_witness_receivers.insert(id, receiver);
    }
    let timer = std::time::Instant::now();
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
    log::info!("spawning workers");
    let ram_tracing_mode = CpuWorkerMode::TraceTouchedRam {
        free_setup_and_teardowns: free_setup_and_teardowns_receiver,
        setup_and_teardown_chunks: setup_and_teardown_chunks_sender,
        final_register_values: final_register_values_sender,
    };
    let mut cpu_worker_id = 0;
    let ram_tracing_worker = get_cpu_worker::<C, _>(
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
        let cycles_tracing_worker = get_cpu_worker::<C, _>(
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
    let delegation_tracing_worker = get_cpu_worker::<C, _>(
        cpu_worker_id,
        timer,
        num_instances_upper_bound,
        binary.clone(),
        non_determinism_source.clone(),
        delegation_mode,
    );
    thread_pool.spawn(delegation_tracing_worker);
    log::info!("workers spawned");
    drop(free_cycle_data_receiver);
    drop(cycles_chunks_sender);
    drop(free_delegation_witness_senders);
    let _ = final_register_values_receiver.recv().unwrap();
    log::info!("received final register values");
    let setup_and_teardown_chunks_count = setup_and_teardown_chunks_receiver.iter().count();
    log::info!("received setup and teardown chunks: {setup_and_teardown_chunks_count}");
    let cycles_chunks_count = cycles_chunks_receiver.iter().count();
    log::info!("received cycles chunks: {cycles_chunks_count}");
    for (id, receiver) in delegation_witness_receivers.iter() {
        let count = receiver.iter().count();
        log::info!("received delegation witnesses for {id}: {count}");
    }
}
