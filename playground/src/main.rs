#![feature(generic_const_exprs)]
#![feature(allocator_api)]
#![feature(vec_push_within_capacity)]
#![feature(new_zeroed_alloc)]
#![feature(iter_array_chunks)]

mod cpu_worker;
mod gpu_worker;
mod messages;
mod old_tracer;
mod tracer;
mod logger;

use crate::cpu_worker::get_cpu_worker;
use crate::tracer::{
    create_setup_and_teardown_chunker, BoxedMemoryImplWithRom, DelegationTracingData,
    RamTracingData, YetAnotherTracer,
};
use crossbeam_channel::unbounded;
use cs::definitions::timestamp_from_chunk_cycle_and_sequence;
use execution_utils::get_padded_binary;
use fft::GoodAllocator;
use gpu_prover::allocator::host::ConcurrentStaticHostAllocator;
use gpu_prover::prover::context::{MemPoolProverContext, ProverContext};
use itertools::Itertools;
use prover::risc_v_simulator::abstractions::non_determinism::{
    NonDeterminismCSRSource, QuasiUARTSource,
};
use prover::risc_v_simulator::cycle::{IMStandardIsaConfig, MachineConfig};
use prover::tracers::delegation::DelegationWitness;
use prover::tracers::main_cycle_optimized::CycleData;
use prover::ShuffleRamSetupAndTeardown;
use rayon::{spawn, ThreadPoolBuilder};
use std::cell::RefCell;
use std::collections::HashMap;
use std::io::Read;
use std::ops::Deref;
use std::sync::Arc;
use trace_and_split::setups::trace_len_for_machine;
use trace_and_split::{setups, FinalRegisterValue, ENTRY_POINT};
use crate::logger::LOCAL_LOGGER;

const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize =
    setups::risc_v_cycles::ROM_ADDRESS_SPACE_SECOND_WORD_BITS;
const LOG_ROM_SIZE: u32 = 16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS as u32;
const RAM_SIZE: usize = 1 << 30;

// fn run_and_split_for_gpu<
//     ND: NonDeterminismCSRSource<BoxedMemoryImplWithRom<RAM_SIZE, LOG_ROM_SIZE>> + Send,
//     C: MachineConfig,
//     A: GoodAllocator + 'static,
// >(
//     num_cycles_upper_bound: usize,
//     binary: &[u32],
//     mut non_determinism: ND,
//     delegation_tracing_data_factories: &HashMap<u16, Box<dyn Fn() -> DelegationWitness<A>>>,
// ) -> (
//     Vec<CycleData<C, A>>,
//     (
//         usize, // number of empty ones to assume
//         Vec<ShuffleRamSetupAndTeardown<A>>,
//     ),
//     HashMap<u16, Vec<DelegationWitness<A>>>,
//     Vec<FinalRegisterValue>,
// ) {
//     const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize =
//         setups::risc_v_cycles::ROM_ADDRESS_SPACE_SECOND_WORD_BITS;
//
//     assert_eq!(
//         setups::reduced_risc_v_machine::ROM_ADDRESS_SPACE_SECOND_WORD_BITS,
//         ROM_ADDRESS_SPACE_SECOND_WORD_BITS
//     );
//     assert_eq!(
//         setups::final_reduced_risc_v_machine::ROM_ADDRESS_SPACE_SECOND_WORD_BITS,
//         ROM_ADDRESS_SPACE_SECOND_WORD_BITS
//     );
//
//     let domain_size = trace_len_for_machine::<C>();
//
//     use setups::prover::risc_v_simulator::cycle::state_new::RiscV32StateForUnrolledProver;
//     use setups::prover::risc_v_simulator::delegations::DelegationsCSRProcessor;
//
//     assert!(domain_size.is_power_of_two());
//
//     let mut memory = BoxedMemoryImplWithRom::<RAM_SIZE, LOG_ROM_SIZE>::new(); // use full RAM
//     for (idx, insn) in binary.iter().enumerate() {
//         memory.populate(ENTRY_POINT + idx as u32 * 4, *insn);
//     }
//
//     let cycles_per_chunk = domain_size - 1;
//     let num_cycles_upper_bound2 = num_cycles_upper_bound.next_multiple_of(cycles_per_chunk);
//     let num_circuits_upper_bound = num_cycles_upper_bound2 / cycles_per_chunk;
//
//     let mut state = RiscV32StateForUnrolledProver::<C>::initial(ENTRY_POINT);
//
//     const TRACE_TOUCHED_RAM: bool = true;
//     const TRACE_CYCLES: bool = false;
//     const TRACE_DELEGATIONS: bool = false;
//
//     let mut custom_csr_processor = DelegationsCSRProcessor;
//     let ram_tracing_data = RamTracingData::<RAM_SIZE, TRACE_TOUCHED_RAM>::new();
//     let cycle_data = if TRACE_CYCLES {
//         CycleData::new_with_cycles_capacity(cycles_per_chunk)
//     } else {
//         CycleData::dummy()
//     };
//     let delegation_tracing_data = DelegationTracingData::default();
//     let mut main_chunks = vec![];
//     let delegation_chunks = RefCell::new(HashMap::new());
//     let initial_timestamp = timestamp_from_chunk_cycle_and_sequence(0, cycles_per_chunk, 0);
//     let delegation_swap_fn = |delegation_id, witness| {
//         if let Some(witness) = witness {
//             println!("Delegation {} witness produced", delegation_id,);
//             delegation_chunks
//                 .borrow_mut()
//                 .entry(delegation_id)
//                 .or_insert_with(Vec::new)
//                 .push(witness);
//         }
//         delegation_tracing_data_factories
//             .get(&delegation_id)
//             .unwrap()()
//     };
//     let tracer = YetAnotherTracer::<
//         RAM_SIZE,
//         LOG_ROM_SIZE,
//         _,
//         _,
//         A,
//         TRACE_TOUCHED_RAM,
//         TRACE_CYCLES,
//         TRACE_DELEGATIONS,
//     >::new(
//         ram_tracing_data,
//         cycle_data,
//         delegation_tracing_data,
//         delegation_swap_fn,
//         initial_timestamp,
//     );
//     let mut tracer = Some(tracer);
//     let mut end_reached = false;
//     let mut circuits_needed = 0;
//
//     let now = std::time::Instant::now();
//
//     for chunk_idx in 0..num_circuits_upper_bound {
//         circuits_needed = chunk_idx + 1;
//
//         let finished = state.run_cycles(
//             &mut memory,
//             tracer.as_mut().unwrap(),
//             &mut non_determinism,
//             &mut custom_csr_processor,
//             cycles_per_chunk,
//         );
//
//         if finished {
//             println!("Ended at address 0x{:08x}", state.pc);
//             println!("Took {} circuits to finish execution", circuits_needed);
//             end_reached = true;
//             break;
//         }
//         let new_timestamp =
//             timestamp_from_chunk_cycle_and_sequence(0, cycles_per_chunk, chunk_idx + 1);
//         if TRACE_CYCLES {
//             let new_cycle_data = CycleData::new_with_cycles_capacity(cycles_per_chunk);
//             let old_tracer = tracer.take().unwrap();
//             let (new_tracer, chunk) =
//                 old_tracer.prepare_for_next_chunk(new_cycle_data, new_timestamp);
//             tracer = Some(new_tracer);
//             main_chunks.push(chunk);
//         } else {
//             tracer.as_mut().unwrap().current_timestamp = new_timestamp;
//         }
//     }
//
//     assert!(end_reached, "end of the execution was never reached");
//
//     let elapsed = now.elapsed();
//     let cycles_upper_bound = circuits_needed * cycles_per_chunk;
//     let speed = (cycles_upper_bound as f64) / elapsed.as_secs_f64() / 1_000_000f64;
//     println!(
//         "Simulator running speed with witness tracing is {} MHz: ran {} cycles over {:?}",
//         speed, cycles_upper_bound, elapsed
//     );
//
//     let YetAnotherTracer {
//         ram_tracing_data,
//         cycle_data,
//         mut delegation_tracing_data,
//         ..
//     } = tracer.unwrap();
//     dbg!(delegation_tracing_data.witnesses.len());
//     if TRACE_CYCLES {
//         main_chunks.push(cycle_data);
//         assert_eq!(main_chunks.len(), circuits_needed);
//     }
//     if TRACE_DELEGATIONS {
//         delegation_tracing_data
//             .witnesses
//             .drain()
//             .for_each(|(delegation_id, witness)| {
//                 delegation_chunks
//                     .borrow_mut()
//                     .entry(delegation_id)
//                     .or_insert_with(Vec::new)
//                     .push(witness);
//             });
//     }
//
//     let instant = std::time::Instant::now();
//     let iat_count = ram_tracing_data.get_touched_ram_cells_count();
//     println!("{iat_count} touched RAM cells");
//     dbg!(instant.elapsed());
//     let non_zero_pages = ram_tracing_data
//         .num_touched_ram_cells_in_pages
//         .iter()
//         .cloned()
//         .filter(|&x| x != 0)
//         .count();
//     dbg!(instant.elapsed());
//     dbg!(non_zero_pages);
//     for (i, count) in ram_tracing_data
//         .num_touched_ram_cells_in_pages
//         .iter()
//         .cloned()
//         .enumerate()
//         .filter(|&(_, x)| x != 0)
//     {
//         println!("Page {i} touched in {count} addresses");
//     }
//
//     let RamTracingData {
//         register_last_live_timestamps,
//         ram_words_last_live_timestamps,
//         num_touched_ram_cells_in_pages,
//         ..
//     } = ram_tracing_data;
//     let instant = std::time::Instant::now();
//     let memory_final_state = memory.get_final_ram_state();
//     let mut chunker = create_setup_and_teardown_chunker(
//         &num_touched_ram_cells_in_pages,
//         &memory_final_state,
//         &ram_words_last_live_timestamps,
//         cycles_per_chunk,
//     );
//     dbg!(instant.elapsed());
//     dbg!(chunker.touched_ram_cells_count);
//     dbg!(chunker.get_chunks_count());
//     let mut teardown_chunks = Vec::with_capacity(chunker.get_chunks_count());
//     for i in 0..chunker.get_chunks_count() {
//         let mut lazy_init_data = Vec::with_capacity_in(cycles_per_chunk, A::default());
//         unsafe {
//             lazy_init_data.set_len(cycles_per_chunk);
//         }
//         chunker.populate_next_chunk(&mut lazy_init_data);
//         dbg!(instant.elapsed());
//         teardown_chunks.push(ShuffleRamSetupAndTeardown { lazy_init_data });
//     }
//     println!(
//         "Lazy init/teardown chunks collected in {:?}",
//         instant.elapsed()
//     );
//
//     let mut registers_final_states = Vec::with_capacity(32);
//     for register_idx in 0..32 {
//         let last_timestamp = register_last_live_timestamps[register_idx];
//         let register_state = FinalRegisterValue {
//             value: state.registers[register_idx],
//             last_access_timestamp: last_timestamp,
//         };
//         registers_final_states.push(register_state);
//     }
//
//     (
//         main_chunks,
//         (circuits_needed - teardown_chunks.len(), teardown_chunks),
//         delegation_chunks.into_inner(),
//         registers_final_states,
//     )
// }

fn main() {
    type C = IMStandardIsaConfig;
    type A = ConcurrentStaticHostAllocator;
    log::set_logger(&logger::LOGGER).unwrap();
    log::set_max_level(log::LevelFilter::Info);
    MemPoolProverContext::initialize_host_allocator(8, 1 << 8, 22).unwrap();
    let thread_pool = ThreadPoolBuilder::new().num_threads(8).build().unwrap();
    let mut binary = vec![];
    std::fs::File::open("examples/hashed_fibonacci/app.bin")
        .unwrap()
        .read_to_end(&mut binary)
        .unwrap();
    let binary = get_padded_binary(&binary);
    // let non_determinism_source = QuasiUARTSource::new_with_reads(vec![0, (1 << 20)/10]);
    let non_determinism_source = QuasiUARTSource::new_with_reads(vec![1 << 22, 0]);
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
    let timer = std::time::Instant::now();
    LOCAL_LOGGER.with_borrow_mut(|l| l.timer = timer);
    log::info!("yay");
    let (setup_and_teardown_chunks_sender, setup_and_teardown_chunks_receiver) = unbounded();
    let (final_register_values_sender, final_register_values_receiver) = unbounded();
    let mode = cpu_worker::CpuWorkerMode::TraceTouchedRam {
        free_setup_and_teardowns: free_setup_and_teardowns_receiver,
        setup_and_teardown_chunks: setup_and_teardown_chunks_sender,
        final_register_values: final_register_values_sender,
    };
    let worker = get_cpu_worker::<_, C, _>(
        0,
        timer,
        num_instances_upper_bound,
        binary.clone(),
        non_determinism_source.clone(),
        mode,
    );
    thread_pool.spawn(worker);
    log::info!("spawned worker");
    let _ = final_register_values_receiver.recv().unwrap();
    log::info!("received final register values");
    // let max_cycles_to_run = num_instances_upper_bound * cycles_per_circuit;
    // let delegation_factories = setups::delegation_factories_for_machine::<C, A>();
    //
    // let (
    //     main_circuits_witness,
    //     inits_and_teardowns,
    //     delegation_circuits_witness,
    //     final_register_values,
    // ) = run_and_split_for_gpu::<_, C, _>(
    //     max_cycles_to_run,
    //     &binary,
    //     non_determinism_source.clone(),
    //     &delegation_factories,
    // );
    //
    // let (
    //     old_main_circuits_witness,
    //     old_inits_and_teardowns,
    //     old_delegation_circuits_witness,
    //     old_final_register_values,
    // ) = old_tracer::trace_execution_for_gpu::<_, C, A>(
    //     num_instances_upper_bound,
    //     &binary,
    //     non_determinism_source.clone(),
    //     worker_ref,
    // );
    //
    // assert_eq!(final_register_values, old_final_register_values);
    //
    // assert_eq!(main_circuits_witness.len(), old_main_circuits_witness.len());
    // for (i, (new, old)) in main_circuits_witness
    //     .into_iter()
    //     .zip(old_main_circuits_witness.into_iter())
    //     .enumerate()
    // {
    //     assert_eq!(
    //         new.per_cycle_data, old.per_cycle_data,
    //         "Main circuit witness mismatch at index {i}"
    //     );
    // }
    //
    // assert_eq!(
    //     inits_and_teardowns.0, old_inits_and_teardowns.0,
    //     "Init/teardown empty chunks count mismatch"
    // );
    //
    // assert_eq!(
    //     inits_and_teardowns.1.len(),
    //     old_inits_and_teardowns.1.len(),
    //     "Init/teardown chunks count mismatch"
    // );
    //
    // for (i, (new, old)) in inits_and_teardowns
    //     .1
    //     .into_iter()
    //     .zip(old_inits_and_teardowns.1.into_iter())
    //     .enumerate()
    // {
    //     for (j, (new_lazy_init, old_lazy_init)) in new
    //         .lazy_init_data
    //         .into_iter()
    //         .zip(old.lazy_init_data.into_iter())
    //         .enumerate()
    //     {
    //         assert_eq!(
    //             new_lazy_init, old_lazy_init,
    //             "Lazy init data mismatch at index {j}, chunk {i}"
    //         );
    //     }
    // }
    //
    // assert_eq!(
    //     delegation_circuits_witness.len(),
    //     old_delegation_circuits_witness.len(),
    //     "Delegation circuits witness count mismatch"
    // );
    //
    // for (i, ((new_idx, new_witnesses), (old_idx, old_witnesses))) in delegation_circuits_witness
    //     .into_iter()
    //     .zip(old_delegation_circuits_witness.into_iter())
    //     .enumerate()
    // {
    //     assert_eq!(
    //         new_idx, old_idx,
    //         "Delegation circuit index mismatch at index {i}"
    //     );
    //     assert_eq!(
    //         new_witnesses.len(),
    //         old_witnesses.len(),
    //         "Delegation witness count mismatch at index {i}"
    //     );
    //     for (j, (new_witness, old_witness)) in new_witnesses
    //         .into_iter()
    //         .zip(old_witnesses.into_iter())
    //         .enumerate()
    //     {
    //         assert_eq!(new_witness.write_timestamp, old_witness.write_timestamp);
    //         assert_eq!(new_witness.indirect_reads, old_witness.indirect_reads);
    //         assert_eq!(new_witness.indirect_writes, old_witness.indirect_writes);
    //         assert_eq!(new_witness.register_accesses, old_witness.register_accesses);
    //     }
    // }

    // let pool = ThreadPoolBuilder::new().num_threads(8).build().unwrap();
    // pool.scope(|s| {
    //     let instant = std::time::Instant::now();
    //     for i in 0..8 {
    //         let binary = binary.clone();
    //         let mut non_determinism_source = non_determinism_source.clone();
    //         println!("[{i}] spawning {:?}", instant.elapsed());
    //         s.spawn(move |_| {
    //             let thread_instant = std::time::Instant::now();
    //             println!("[{i}] running {:?}", instant.elapsed());
    //             let delegation_factories = setups::delegation_factories_for_machine::<C, A>();
    //             // let _ = run_without_tracing::<_, C, A>(max_cycles_to_run, &binary, &mut non_determinism_source);
    //             let (
    //                 _final_pc,
    //                 // main_circuits_witness,
    //                 // delegation_circuits_witness,
    //                 // final_register_values,
    //                 // inits_and_teardowns,
    //             ) = run_and_split_for_gpu::<_, C, _>(
    //                 max_cycles_to_run,
    //                 &binary,
    //                 &mut non_determinism_source,
    //                 delegation_factories,
    //                 worker_ref,
    //             );
    //             println!(
    //                 "[{i}] finished {:?} took {:?}",
    //                 instant.elapsed(),
    //                 thread_instant.elapsed()
    //             );
    //         });
    //         println!("[{i}] spawned {:?}", instant.elapsed());
    //     }
    // });
    // let _ = run_without_tracing::<_, C, A>(max_cycles_to_run, &binary, &mut non_determinism_source);
    //
    // let (
    //     final_pc,
    //     main_circuits_witness,
    //     delegation_circuits_witness,
    //     final_register_values,
    //     inits_and_teardowns,
    // ) = run_and_split_for_gpu::<_, C, _>(
    //     max_cycles_to_run,
    //     &binary,
    //     &mut non_determinism_source,
    //     delegation_factories,
    //     &worker,
    // );
    //
    // // we just need to chunk inits/teardowns
    //
    // let inits_and_teardowns = chunk_lazy_init_and_teardown(
    //     main_circuits_witness.len(),
    //     cycles_per_circuit,
    //     &inits_and_teardowns,
    //     &worker,
    // );
}
