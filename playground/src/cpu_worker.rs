use crate::tracer::{
    create_setup_and_teardown_chunker, BoxedMemoryImplWithRom, DelegationTracingData,
    RamTracingData, YetAnotherTracer,
};
use crossbeam_channel::{Receiver, Sender};
use cs::definitions::timestamp_from_chunk_cycle_and_sequence;
use fft::GoodAllocator;
use itertools::Itertools;
use prover::tracers::delegation::DelegationWitness;
use prover::tracers::main_cycle_optimized::CycleData;
use prover::ShuffleRamSetupAndTeardown;
use risc_v_simulator::abstractions::non_determinism::NonDeterminismCSRSource;
use risc_v_simulator::cycle::state_new::RiscV32StateForUnrolledProver;
use risc_v_simulator::cycle::MachineConfig;
use risc_v_simulator::delegations::DelegationsCSRProcessor;
use std::collections::HashMap;
use std::ops::Deref;
use std::time::Instant;
use trace_and_split::setups::trace_len_for_machine;
use trace_and_split::{setups, FinalRegisterValue, ENTRY_POINT};

pub trait NonDeterminism:
    NonDeterminismCSRSource<BoxedMemoryImplWithRom<RAM_SIZE, LOG_ROM_SIZE>> + Clone
{
}

impl<T> NonDeterminism for T where
    T: NonDeterminismCSRSource<BoxedMemoryImplWithRom<RAM_SIZE, LOG_ROM_SIZE>> + Clone
{
}

const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize = {
    const BITS: usize = setups::risc_v_cycles::ROM_ADDRESS_SPACE_SECOND_WORD_BITS;
    assert!(setups::final_reduced_risc_v_machine::ROM_ADDRESS_SPACE_SECOND_WORD_BITS == BITS);
    BITS
};

const LOG_ROM_SIZE: u32 = 16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS as u32;
const RAM_SIZE: usize = 1 << 30;

pub struct SetupAndTeardownChunk<A: GoodAllocator> {
    pub index: usize,
    pub chunk: Option<ShuffleRamSetupAndTeardown<A>>,
}

pub struct CyclesChunk<C: MachineConfig, A: GoodAllocator> {
    pub index: usize,
    pub chunk: CycleData<C, A>,
}

#[derive(Clone)]
pub enum CpuWorkerMode<C: MachineConfig, A: GoodAllocator> {
    TraceTouchedRam {
        free_setup_and_teardowns: Receiver<ShuffleRamSetupAndTeardown<A>>,
        setup_and_teardown_chunks: Sender<SetupAndTeardownChunk<A>>,
        final_register_values: Sender<[FinalRegisterValue; 32]>,
    },
    TraceCycles {
        split_count: usize,
        split_index: usize,
        free_cycle_data: Receiver<CycleData<C, A>>,
        chunks: Sender<CyclesChunk<C, A>>,
    },
    TraceDelegations {
        free_delegation_witnesses: HashMap<u16, Receiver<DelegationWitness<A>>>,
        delegation_witnesses: HashMap<u16, Sender<DelegationWitness<A>>>,
    },
}

pub fn get_cpu_worker<C: MachineConfig, A: GoodAllocator + 'static>(
    worker_id: usize,
    timer: Instant,
    num_main_chunks_upper_bound: usize,
    binary: impl Deref<Target = impl Deref<Target = [u32]>> + Send + 'static,
    non_determinism: impl Deref<Target = impl NonDeterminism> + Send + 'static,
    mode: CpuWorkerMode<C, A>,
) -> impl FnOnce() + Send + 'static {
    move || {
        crate::logger::LOCAL_LOGGER.with_borrow_mut(|l| {
            l.name = format!("CPU[{worker_id}]");
            l.timer = timer;
        });
        match mode {
            CpuWorkerMode::TraceTouchedRam {
                free_setup_and_teardowns,
                setup_and_teardown_chunks,
                final_register_values,
            } => trace_touched_ram::<C, A>(
                num_main_chunks_upper_bound,
                binary,
                non_determinism,
                free_setup_and_teardowns,
                setup_and_teardown_chunks,
                final_register_values,
            ),
            CpuWorkerMode::TraceCycles {
                split_count,
                split_index,
                free_cycle_data,
                chunks,
            } => trace_cycles::<C, A>(
                num_main_chunks_upper_bound,
                binary,
                non_determinism,
                split_count,
                split_index,
                free_cycle_data,
                chunks,
            ),
            CpuWorkerMode::TraceDelegations {
                free_delegation_witnesses,
                delegation_witnesses,
            } => trace_delegations::<C, A>(
                num_main_chunks_upper_bound,
                binary,
                non_determinism,
                free_delegation_witnesses,
                delegation_witnesses,
            ),
        }
    }
}

fn trace_touched_ram<C: MachineConfig, A: GoodAllocator + 'static>(
    num_main_chunks_upper_bound: usize,
    binary: impl Deref<Target = impl Deref<Target = [u32]>> + Send + 'static,
    non_determinism: impl Deref<Target = impl NonDeterminism> + Send + 'static,
    free_setup_and_teardowns: Receiver<ShuffleRamSetupAndTeardown<A>>,
    setup_and_teardown_chunks: Sender<SetupAndTeardownChunk<A>>,
    final_register_values: Sender<[FinalRegisterValue; 32]>,
) {
    log::info!("worker for tracing touched RAM started");
    let domain_size = trace_len_for_machine::<C>();
    assert!(domain_size.is_power_of_two());
    let log_domain_size = domain_size.trailing_zeros();
    let mut non_determinism = non_determinism.clone();
    let mut memory = BoxedMemoryImplWithRom::<RAM_SIZE, LOG_ROM_SIZE>::new();
    for (idx, insn) in binary.iter().enumerate() {
        memory.populate(ENTRY_POINT + idx as u32 * 4, *insn);
    }
    let cycles_per_chunk = domain_size - 1;
    let mut state = RiscV32StateForUnrolledProver::<C>::initial(ENTRY_POINT);
    let mut custom_csr_processor = DelegationsCSRProcessor;
    let mut ram_tracing_data = RamTracingData::<RAM_SIZE, true>::new();
    let cycle_data = CycleData::dummy();
    let delegation_tracing_data = DelegationTracingData::default();
    let delegation_swap_fn = |_, _| unreachable!();
    let initial_timestamp = timestamp_from_chunk_cycle_and_sequence(0, cycles_per_chunk, 0);
    let mut tracer = YetAnotherTracer::<RAM_SIZE, LOG_ROM_SIZE, _, _, A, true, false, false>::new(
        &mut ram_tracing_data,
        cycle_data,
        delegation_tracing_data,
        delegation_swap_fn,
        initial_timestamp,
    );
    let mut end_reached = false;
    let mut chunks_traced_count = 0;
    let mut next_chunk_index_with_no_setup_and_teardown = 0;
    log::info!("starting simulation");
    let now = Instant::now();
    for _chunk_index in 0..num_main_chunks_upper_bound {
        let chunk_now = Instant::now();
        let finished = state.run_cycles(
            &mut memory,
            &mut tracer,
            &mut non_determinism,
            &mut custom_csr_processor,
            cycles_per_chunk,
        );
        let elapsed_ms = chunk_now.elapsed().as_secs_f64() * 1000.0;
        let mhz = (cycles_per_chunk as f64) / (elapsed_ms * 1000.0);
        log::info!("chunk {chunks_traced_count} finished in {elapsed_ms:.3} ms @ {mhz:.3} MHz)");
        chunks_traced_count += 1;
        let touched_ram_cells_count =
            tracer.ram_tracing_data.get_touched_ram_cells_count() as usize;
        let chunks_needed_for_setup_and_teardowns =
            touched_ram_cells_count.div_ceil(cycles_per_chunk);
        if chunks_needed_for_setup_and_teardowns
            < (chunks_traced_count - next_chunk_index_with_no_setup_and_teardown)
        {
            log::info!(
                "chunk {} with no setup and teardown",
                next_chunk_index_with_no_setup_and_teardown
            );
            let message = SetupAndTeardownChunk {
                index: next_chunk_index_with_no_setup_and_teardown,
                chunk: None,
            };
            setup_and_teardown_chunks.send(message).unwrap();
            next_chunk_index_with_no_setup_and_teardown += 1;
        }
        if finished {
            let elapsed_ms = now.elapsed().as_secs_f64() * 1000.0;
            let cycles_count = chunks_traced_count * cycles_per_chunk;
            let speed = (cycles_count as f64) / (elapsed_ms * 1000.0);
            let touched_ram_cells_count = ram_tracing_data.get_touched_ram_cells_count();
            log::info!(
                "simulation ended at address 0x{:08x} and took {chunks_traced_count} chunks to finish execution",
                state.pc,
            );
            log::info!("simulator tracing touched RAM ran {chunks_traced_count}x(2^{log_domain_size}-1) cycles in {elapsed_ms:.3} ms @ {speed:.3} MHz");
            log::info!("simulator touched {touched_ram_cells_count} RAM cells");
            end_reached = true;
            break;
        }
        let new_timestamp =
            timestamp_from_chunk_cycle_and_sequence(0, cycles_per_chunk, chunks_traced_count);
        tracer.current_timestamp = new_timestamp;
    }
    assert!(end_reached, "end of the execution was never reached");
    let RamTracingData {
        register_last_live_timestamps,
        ram_words_last_live_timestamps,
        num_touched_ram_cells_in_pages,
        ..
    } = ram_tracing_data;
    let memory_final_state = memory.get_final_ram_state();
    let mut chunker = create_setup_and_teardown_chunker(
        &num_touched_ram_cells_in_pages,
        &memory_final_state,
        &ram_words_last_live_timestamps,
        cycles_per_chunk,
    );
    let setup_and_teardown_chunks_count = chunker.get_chunks_count();
    log::info!("{setup_and_teardown_chunks_count} lazy init/teardown chunk(s) are needed");
    assert_eq!(
        chunks_traced_count,
        setup_and_teardown_chunks_count + next_chunk_index_with_no_setup_and_teardown
    );
    let now = Instant::now();
    for index in next_chunk_index_with_no_setup_and_teardown..chunks_traced_count {
        let mut setup_and_teardown = free_setup_and_teardowns.recv().unwrap();
        chunker.populate_next_chunk(&mut setup_and_teardown.lazy_init_data);
        let chunk = Some(setup_and_teardown);
        let message = SetupAndTeardownChunk { index, chunk };
        setup_and_teardown_chunks.send(message).unwrap();
    }
    log::info!(
        "lazy init/teardown chunk(s) collected in {:.3} ms",
        now.elapsed().as_secs_f64() * 1000.0
    );
    let message = state
        .registers
        .into_iter()
        .zip(register_last_live_timestamps.into_iter())
        .map(|(value, last_access_timestamp)| FinalRegisterValue {
            value,
            last_access_timestamp,
        })
        .collect_array()
        .unwrap();
    final_register_values.send(message).unwrap();
    log::info!("tracing touched RAM finished");
}

fn trace_cycles<C: MachineConfig, A: GoodAllocator + 'static>(
    num_main_chunks_upper_bound: usize,
    binary: impl Deref<Target = impl Deref<Target = [u32]>> + Send + 'static,
    non_determinism: impl Deref<Target = impl NonDeterminism> + Send + 'static,
    split_count: usize,
    split_index: usize,
    free_cycle_data: Receiver<CycleData<C, A>>,
    chunks: Sender<CyclesChunk<C, A>>,
) {
    log::info!("worker for tracing cycles started");
    let domain_size = trace_len_for_machine::<C>();
    assert!(domain_size.is_power_of_two());
    let log_domain_size = domain_size.trailing_zeros();
    let mut non_determinism = non_determinism.clone();
    let mut memory = BoxedMemoryImplWithRom::<RAM_SIZE, LOG_ROM_SIZE>::new();
    for (idx, insn) in binary.iter().enumerate() {
        memory.populate(ENTRY_POINT + idx as u32 * 4, *insn);
    }
    let cycles_per_chunk = domain_size - 1;
    let mut state = RiscV32StateForUnrolledProver::<C>::initial(ENTRY_POINT);
    let mut custom_csr_processor = DelegationsCSRProcessor;
    let mut ram_tracing_data = RamTracingData::<RAM_SIZE, false>::new();
    let mut end_reached = false;
    let mut chunks_traced_count = 0;
    log::info!("starting simulation");
    let now = Instant::now();
    for chunk_index in 0..num_main_chunks_upper_bound {
        let delegation_tracing_data = DelegationTracingData::default();
        let delegation_swap_fn = |_, _| unreachable!();
        let initial_timestamp =
            timestamp_from_chunk_cycle_and_sequence(0, cycles_per_chunk, chunk_index);
        let mut finished = false;
        if chunk_index % split_count == split_index {
            let cycle_data = free_cycle_data.recv().unwrap();
            let mut tracer =
                YetAnotherTracer::<RAM_SIZE, LOG_ROM_SIZE, _, _, A, false, true, false>::new(
                    &mut ram_tracing_data,
                    cycle_data,
                    delegation_tracing_data,
                    delegation_swap_fn,
                    initial_timestamp,
                );
            let now = Instant::now();
            finished = state.run_cycles(
                &mut memory,
                &mut tracer,
                &mut non_determinism,
                &mut custom_csr_processor,
                cycles_per_chunk,
            );
            let elapsed_ms = now.elapsed().as_secs_f64() * 1000.0;
            let mhz = (cycles_per_chunk as f64) / (elapsed_ms * 1000.0);
            log::info!("tracing cycles for chunk {chunk_index} finished in {elapsed_ms:.3} ms @ {mhz:.3} MHz");
            let message = CyclesChunk {
                index: chunk_index,
                chunk: tracer.cycle_data,
            };
            chunks.send(message).unwrap();
        } else {
            // fast-forward the simulation
            let cycle_data = CycleData::dummy();
            let mut tracer =
                YetAnotherTracer::<RAM_SIZE, LOG_ROM_SIZE, _, _, A, false, false, false>::new(
                    &mut ram_tracing_data,
                    cycle_data,
                    delegation_tracing_data,
                    delegation_swap_fn,
                    initial_timestamp,
                );
            let now = Instant::now();
            finished = state.run_cycles(
                &mut memory,
                &mut tracer,
                &mut non_determinism,
                &mut custom_csr_processor,
                cycles_per_chunk,
            );
            let elapsed_ms = now.elapsed().as_secs_f64() * 1000.0;
            let mhz = (cycles_per_chunk as f64) / (elapsed_ms * 1000.0);
            log::info!(
                "fast-forwarding chunk {chunk_index} finished in {elapsed_ms:.3} ms @ {mhz:.3} MHz"
            );
        }
        chunks_traced_count += 1;
        if finished {
            let elapsed_ms = now.elapsed().as_secs_f64() * 1000.0;
            let cycles_count = chunks_traced_count * cycles_per_chunk;
            let speed = (cycles_count as f64) / (elapsed_ms * 1000.0);
            log::info!(
                "simulation ended at address 0x{:08x} and took {chunks_traced_count} chunks to finish execution",
                state.pc,
            );
            log::info!("simulator tracing 1/{split_count} cycles ran {chunks_traced_count}x(2^{log_domain_size}-1) cycles in {elapsed_ms:.3} ms @ {speed:.3} MHz");
            end_reached = true;
            break;
        }
    }
    assert!(end_reached, "end of the execution was never reached");
    log::info!("tracing cycles finished");
}

fn trace_delegations<C: MachineConfig, A: GoodAllocator + 'static>(
    num_main_chunks_upper_bound: usize,
    binary: impl Deref<Target = impl Deref<Target = [u32]>> + Send + 'static,
    non_determinism: impl Deref<Target = impl NonDeterminism> + Send + 'static,
    free_delegation_witnesses: HashMap<u16, Receiver<DelegationWitness<A>>>,
    delegation_witnesses: HashMap<u16, Sender<DelegationWitness<A>>>,
) {
    log::info!("worker for tracing delegations started");
    let domain_size = trace_len_for_machine::<C>();
    assert!(domain_size.is_power_of_two());
    let log_domain_size = domain_size.trailing_zeros();
    let mut non_determinism = non_determinism.clone();
    let mut memory = BoxedMemoryImplWithRom::<RAM_SIZE, LOG_ROM_SIZE>::new();
    for (idx, insn) in binary.iter().enumerate() {
        memory.populate(ENTRY_POINT + idx as u32 * 4, *insn);
    }
    let cycles_per_chunk = domain_size - 1;
    let mut state = RiscV32StateForUnrolledProver::<C>::initial(ENTRY_POINT);
    let mut custom_csr_processor = DelegationsCSRProcessor;
    let mut ram_tracing_data = RamTracingData::<RAM_SIZE, false>::new();
    let cycle_data = CycleData::dummy();
    let delegation_tracing_data = DelegationTracingData::default();
    let delegation_swap_fn = |delegation_id, witness| {
        if let Some(witness) = witness {
            log::info!("full delegation {delegation_id} witness produced");
            delegation_witnesses
                .get(&delegation_id)
                .unwrap()
                .send(witness)
                .unwrap();
        }
        free_delegation_witnesses
            .get(&delegation_id)
            .unwrap()
            .recv()
            .unwrap()
    };
    let initial_timestamp = timestamp_from_chunk_cycle_and_sequence(0, cycles_per_chunk, 0);
    let mut tracer = YetAnotherTracer::<RAM_SIZE, LOG_ROM_SIZE, _, _, A, false, false, true>::new(
        &mut ram_tracing_data,
        cycle_data,
        delegation_tracing_data,
        delegation_swap_fn,
        initial_timestamp,
    );
    let mut end_reached = false;
    let mut chunks_traced_count = 0;
    log::info!("starting simulation");
    let now = Instant::now();
    for _chunk_index in 0..num_main_chunks_upper_bound {
        let chunk_now = Instant::now();
        let finished = state.run_cycles(
            &mut memory,
            &mut tracer,
            &mut non_determinism,
            &mut custom_csr_processor,
            cycles_per_chunk,
        );
        let elapsed_ms = chunk_now.elapsed().as_secs_f64() * 1000.0;
        let mhz = (cycles_per_chunk as f64) / (elapsed_ms * 1000.0);
        log::info!("chunk {chunks_traced_count} finished in {elapsed_ms:.3} ms @ {mhz:.3} MHz)");
        chunks_traced_count += 1;
        if finished {
            let elapsed_ms = now.elapsed().as_secs_f64() * 1000.0;
            let cycles_count = chunks_traced_count * cycles_per_chunk;
            let speed = (cycles_count as f64) / (elapsed_ms * 1000.0);
            log::info!(
                "simulation ended at address 0x{:08x} and took {chunks_traced_count} chunks to finish execution",
                state.pc,
            );
            log::info!("simulator tracing delegations ran {chunks_traced_count}x(2^{log_domain_size}-1) cycles in {elapsed_ms:.3} ms @ {speed:.3} MHz");
            end_reached = true;
            break;
        }
        let new_timestamp =
            timestamp_from_chunk_cycle_and_sequence(0, cycles_per_chunk, chunks_traced_count);
        tracer.current_timestamp = new_timestamp;
    }
    assert!(end_reached, "end of the execution was never reached");
    for (delegation_id, witness) in tracer.delegation_tracing_data.witnesses.drain() {
        witness.assert_consistency();
        log::info!("delegation {delegation_id} witness with {} delegations produced", witness.write_timestamp.len());
        delegation_witnesses
            .get(&delegation_id)
            .unwrap()
            .send(witness)
            .unwrap();
    }
    log::info!("tracing delegations finished");
}

/*
fn trace_touched_ram<
    ND: NonDeterminismCSRSource<BoxedMemoryImplWithRom<RAM_SIZE, LOG_ROM_SIZE>>,
    C: MachineConfig,
    A: GoodAllocator + 'static,
>(
    num_cycles_upper_bound: usize,
    binary: impl Deref<Target = Box<[u32]>>,
    mut non_determinism: ND,
) {
    assert_eq!(
        setups::reduced_risc_v_machine::ROM_ADDRESS_SPACE_SECOND_WORD_BITS,
        crate::ROM_ADDRESS_SPACE_SECOND_WORD_BITS
    );
    assert_eq!(
        setups::final_reduced_risc_v_machine::ROM_ADDRESS_SPACE_SECOND_WORD_BITS,
        crate::ROM_ADDRESS_SPACE_SECOND_WORD_BITS
    );
    let domain_size = trace_len_for_machine::<C>();
    assert!(domain_size.is_power_of_two());
    let mut memory = BoxedMemoryImplWithRom::<RAM_SIZE, LOG_ROM_SIZE>::new();
    for (idx, insn) in binary.iter().enumerate() {
        memory.populate(ENTRY_POINT + idx as u32 * 4, *insn);
    }
    let cycles_per_chunk = domain_size - 1;
    let num_cycles_upper_bound = num_cycles_upper_bound.next_multiple_of(cycles_per_chunk);
    let num_circuits_upper_bound = num_cycles_upper_bound / cycles_per_chunk;
    let mut state = RiscV32StateForUnrolledProver::<C>::initial(ENTRY_POINT);
    let mut custom_csr_processor = DelegationsCSRProcessor;
    let ram_tracing_data = RamTracingData::<RAM_SIZE, TRACE_TOUCHED_RAM>::new();
    let cycle_data = if TRACE_CYCLES {
        CycleData::new_with_cycles_capacity(cycles_per_chunk)
    } else {
        CycleData::dummy()
    };
    let delegation_tracing_data = DelegationTracingData::default();
    let mut main_chunks = vec![];
    let delegation_chunks = RefCell::new(HashMap::new());
    let initial_timestamp = timestamp_from_chunk_cycle_and_sequence(0, cycles_per_chunk, 0);
    let delegation_tracing_data_factories = setups::delegation_factories_for_machine::<C, A>();
    let delegation_swap_fn = |delegation_id, witness| {
        if let Some(witness) = witness {
            println!("Delegation {} witness produced", delegation_id,);
            delegation_chunks
                .borrow_mut()
                .entry(delegation_id)
                .or_insert_with(Vec::new)
                .push(witness);
        }
        delegation_tracing_data_factories
            .get(&delegation_id)
            .unwrap()()
    };
    let tracer = YetAnotherTracer::<
        RAM_SIZE,
        LOG_ROM_SIZE,
        _,
        _,
        A,
        TRACE_TOUCHED_RAM,
        TRACE_CYCLES,
        TRACE_DELEGATIONS,
    >::new(
        ram_tracing_data,
        cycle_data,
        delegation_tracing_data,
        delegation_swap_fn,
        initial_timestamp,
    );
    let mut tracer = Some(tracer);
    let mut end_reached = false;
    let mut circuits_needed = 0;
    let now = std::time::Instant::now();
    for chunk_idx in 0..num_circuits_upper_bound {
        circuits_needed = chunk_idx + 1;

        let finished = state.run_cycles(
            &mut memory,
            tracer.as_mut().unwrap(),
            &mut non_determinism,
            &mut custom_csr_processor,
            cycles_per_chunk,
        );

        if finished {
            println!("Ended at address 0x{:08x}", state.pc);
            println!("Took {} circuits to finish execution", circuits_needed);
            end_reached = true;
            break;
        }
        let new_timestamp =
            timestamp_from_chunk_cycle_and_sequence(0, cycles_per_chunk, chunk_idx + 1);
        if TRACE_CYCLES {
            let new_cycle_data = CycleData::new_with_cycles_capacity(cycles_per_chunk);
            let old_tracer = tracer.take().unwrap();
            let (new_tracer, chunk) =
                old_tracer.prepare_for_next_chunk(new_cycle_data, new_timestamp);
            tracer = Some(new_tracer);
            main_chunks.push(chunk);
        } else {
            tracer.as_mut().unwrap().current_timestamp = new_timestamp;
        }
    }
    let elapsed = now.elapsed();
    assert!(end_reached, "end of the execution was never reached");
    let speed = (num_cycles_upper_bound as f64) / elapsed.as_secs_f64() / 1_000_000f64;
    println!(
        "Simulator running speed tracing {}TOUCHED_RAM | {}CYCLES | {}DELEGATIONS was {} MHz: ran {} cycles in {:?}",
        if TRACE_TOUCHED_RAM { "" } else { "!" },
        if TRACE_CYCLES { "" } else { "!" },
        if TRACE_DELEGATIONS { "" } else { "!" },
        speed, num_cycles_upper_bound, elapsed
    );
    let YetAnotherTracer {
        ram_tracing_data,
        cycle_data,
        mut delegation_tracing_data,
        ..
    } = tracer.unwrap();
    dbg!(delegation_tracing_data.witnesses.len());
    if TRACE_CYCLES {
        main_chunks.push(cycle_data);
        assert_eq!(main_chunks.len(), circuits_needed);
    }
    if TRACE_DELEGATIONS {
        delegation_tracing_data
            .witnesses
            .drain()
            .for_each(|(delegation_id, witness)| {
                delegation_chunks
                    .borrow_mut()
                    .entry(delegation_id)
                    .or_insert_with(Vec::new)
                    .push(witness);
            });
    }
    let touched_ram_cells_count = ram_tracing_data.get_touched_ram_cells_count();
    println!("{touched_ram_cells_count} touched RAM cells");
    let RamTracingData {
        register_last_live_timestamps,
        ram_words_last_live_timestamps,
        num_touched_ram_cells_in_pages,
        ..
    } = ram_tracing_data;
    let instant = std::time::Instant::now();
    let memory_final_state = memory.get_final_ram_state();
    let mut chunker = create_setup_and_teardown_chunker(
        &num_touched_ram_cells_in_pages,
        &memory_final_state,
        &ram_words_last_live_timestamps,
        cycles_per_chunk,
    );
    dbg!(instant.elapsed());
    dbg!(chunker.touched_ram_cells_count);
    dbg!(chunker.get_chunks_count());
    let mut teardown_chunks = Vec::with_capacity(chunker.get_chunks_count());
    for i in 0..chunker.get_chunks_count() {
        let mut lazy_init_data = Vec::with_capacity_in(cycles_per_chunk, A::default());
        unsafe {
            lazy_init_data.set_len(cycles_per_chunk);
        }
        chunker.populate_next_chunk(&mut lazy_init_data);
        dbg!(instant.elapsed());
        teardown_chunks.push(ShuffleRamSetupAndTeardown { lazy_init_data });
    }
    println!(
        "Lazy init/teardown chunks collected in {:?}",
        instant.elapsed()
    );

    let mut registers_final_states = Vec::with_capacity(32);
    for register_idx in 0..32 {
        let last_timestamp = register_last_live_timestamps[register_idx];
        let register_state = FinalRegisterValue {
            value: state.registers[register_idx],
            last_access_timestamp: last_timestamp,
        };
        registers_final_states.push(register_state);
    }
}

 */
