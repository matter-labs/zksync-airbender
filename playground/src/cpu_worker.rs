use crate::tracer::{
    create_setup_and_teardown_chunker, BoxedMemoryImplWithRom, DelegationTracingData,
    RamTracingData, YetAnotherTracer,
};
use crossbeam_channel::{Receiver, Sender};
use cs::definitions::timestamp_from_chunk_cycle_and_sequence;
use fft::GoodAllocator;
use itertools::Itertools;
use log::{Level, LevelFilter, Metadata, Record};
use prover::tracers::main_cycle_optimized::CycleData;
use prover::ShuffleRamSetupAndTeardown;
use risc_v_simulator::abstractions::non_determinism::NonDeterminismCSRSource;
use risc_v_simulator::cycle::state_new::RiscV32StateForUnrolledProver;
use risc_v_simulator::cycle::MachineConfig;
use risc_v_simulator::delegations::DelegationsCSRProcessor;
use std::cell::{Cell, RefCell};
use std::fmt::Display;
use std::ops::Deref;
use std::rc::Rc;
use std::time::Instant;
use trace_and_split::setups::trace_len_for_machine;
use trace_and_split::{setups, FinalRegisterValue, ENTRY_POINT};

const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize =
    setups::risc_v_cycles::ROM_ADDRESS_SPACE_SECOND_WORD_BITS;
const LOG_ROM_SIZE: u32 = 16 + crate::ROM_ADDRESS_SPACE_SECOND_WORD_BITS as u32;
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
        free_cycle_data: Receiver<CycleData<C, A>>,
        chunk_requests: Receiver<usize>,
        chunks: Sender<CyclesChunk<C, A>>,
    },
    TraceDelegations,
}

pub fn get_cpu_worker<
    ND: NonDeterminismCSRSource<BoxedMemoryImplWithRom<RAM_SIZE, LOG_ROM_SIZE>> + Send + 'static,
    C: MachineConfig,
    A: GoodAllocator + 'static,
>(
    worker_id: usize,
    timer: Instant,
    num_main_chunks_upper_bound: usize,
    binary: impl Deref<Target = impl Deref<Target = [u32]>> + Send + 'static,
    non_determinism: ND,
    mode: CpuWorkerMode<C, A>,
) -> impl FnOnce() + Send + 'static {
    let set_logger = move || {
        crate::logger::LOCAL_LOGGER.with_borrow_mut(|l| {
            l.name = format!("CPU[{worker_id}]");
            l.timer = timer;
        })
    };
    match mode {
        CpuWorkerMode::TraceTouchedRam {
            free_setup_and_teardowns,
            setup_and_teardown_chunks,
            final_register_values,
        } => move || {
            set_logger();
            trace_touched_ram::<ND, C, A>(
                num_main_chunks_upper_bound,
                binary,
                non_determinism,
                free_setup_and_teardowns,
                setup_and_teardown_chunks,
                final_register_values,
            )
        },
        CpuWorkerMode::TraceCycles { .. } => unimplemented!(),
        CpuWorkerMode::TraceDelegations => unimplemented!(),
    }
}

fn trace_touched_ram<
    ND: NonDeterminismCSRSource<BoxedMemoryImplWithRom<RAM_SIZE, LOG_ROM_SIZE>>,
    C: MachineConfig,
    A: GoodAllocator + 'static,
>(
    num_main_chunks_upper_bound: usize,
    binary: impl Deref<Target = impl Deref<Target = [u32]>> + Send + 'static,
    mut non_determinism: ND,
    free_setup_and_teardowns: Receiver<ShuffleRamSetupAndTeardown<A>>,
    setup_and_teardown_chunks: Sender<SetupAndTeardownChunk<A>>,
    final_register_values: Sender<[FinalRegisterValue; 32]>,
) {
    assert_eq!(
        setups::reduced_risc_v_machine::ROM_ADDRESS_SPACE_SECOND_WORD_BITS,
        ROM_ADDRESS_SPACE_SECOND_WORD_BITS
    );
    let domain_size = trace_len_for_machine::<C>();
    assert!(domain_size.is_power_of_two());
    let mut memory = BoxedMemoryImplWithRom::<RAM_SIZE, LOG_ROM_SIZE>::new();
    for (idx, insn) in binary.iter().enumerate() {
        memory.populate(ENTRY_POINT + idx as u32 * 4, *insn);
    }
    let cycles_per_chunk = domain_size - 1;
    let mut state = RiscV32StateForUnrolledProver::<C>::initial(ENTRY_POINT);
    let mut custom_csr_processor = DelegationsCSRProcessor;
    let ram_tracing_data = RamTracingData::<RAM_SIZE, true>::new();
    let cycle_data = CycleData::dummy();
    let delegation_tracing_data = DelegationTracingData::default();
    let delegation_swap_fn = |_, _| unreachable!();
    let initial_timestamp = timestamp_from_chunk_cycle_and_sequence(0, cycles_per_chunk, 0);
    let mut tracer = YetAnotherTracer::<RAM_SIZE, LOG_ROM_SIZE, _, _, A, true, false, false>::new(
        ram_tracing_data,
        cycle_data,
        delegation_tracing_data,
        delegation_swap_fn,
        initial_timestamp,
    );
    let mut end_reached = false;
    let mut chunks_created_count = 0;
    let mut next_chunk_index_with_no_setup_and_teardown = 0;
    log::info!("starting simulation");
    let now = Instant::now();
    for chunk_index in 0..num_main_chunks_upper_bound {
        let finished = state.run_cycles(
            &mut memory,
            &mut tracer,
            &mut non_determinism,
            &mut custom_csr_processor,
            cycles_per_chunk,
        );
        chunks_created_count += 1;
        let touched_ram_cells_count =
            tracer.ram_tracing_data.get_touched_ram_cells_count() as usize;
        let chunks_needed_for_setup_and_teardowns =
            touched_ram_cells_count.div_ceil(cycles_per_chunk);
        if chunks_needed_for_setup_and_teardowns
            < (chunks_created_count - next_chunk_index_with_no_setup_and_teardown)
        {
            log::info!("shard {} with no setup and teardown", next_chunk_index_with_no_setup_and_teardown);
            let message = SetupAndTeardownChunk {
                index: next_chunk_index_with_no_setup_and_teardown,
                chunk: None,
            };
            setup_and_teardown_chunks.send(message).unwrap();
            next_chunk_index_with_no_setup_and_teardown += 1;
        }
        if finished {
            log::info!(
                "Ended at address 0x{:08x}. Took {} circuits to finish execution",
                state.pc,
                chunks_created_count
            );
            end_reached = true;
            break;
        }
        let new_timestamp =
            timestamp_from_chunk_cycle_and_sequence(0, cycles_per_chunk, chunks_created_count);
        tracer.current_timestamp = new_timestamp;
    }
    let elapsed = now.elapsed();
    assert!(end_reached, "end of the execution was never reached");
    let cycles_count = chunks_created_count * cycles_per_chunk;
    let speed = (cycles_count as f64) / elapsed.as_secs_f64() / 1_000_000f64;
    log::info!(
        "Simulator running speed tracing touched RAM was {} MHz: ran {} cycles in {:?}",
        speed,
        cycles_count,
        elapsed
    );
    let YetAnotherTracer {
        ram_tracing_data, ..
    } = tracer;
    let touched_ram_cells_count = ram_tracing_data.get_touched_ram_cells_count();
    log::info!("Simulator touched {touched_ram_cells_count} RAM cells");
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
    assert_eq!(
        chunks_created_count,
        setup_and_teardown_chunks_count + next_chunk_index_with_no_setup_and_teardown
    );
    for index in next_chunk_index_with_no_setup_and_teardown..chunks_created_count {
        let mut setup_and_teardown = free_setup_and_teardowns.recv().unwrap();
        chunker.populate_next_chunk(&mut setup_and_teardown.lazy_init_data);
        let chunk = Some(setup_and_teardown);
        log::info!("shard {index} with setup and teardown");
        let message = SetupAndTeardownChunk { index, chunk };
        setup_and_teardown_chunks.send(message).unwrap();
    }
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
    final_register_values.send(message).unwrap()
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
