use super::messages::WorkerResult;
use super::tracer::{
    create_setup_and_teardown_chunker, BoxedMemoryImplWithRom, CycleTracingData, DelegationCounter,
    DelegationTracingData, DelegationTracingType, ExecutionTracer, RamTracingData,
};
use crate::circuit_type::{CircuitType, MainCircuitType};
use crossbeam_channel::{Receiver, Sender};
use crossbeam_utils::sync::WaitGroup;
use cs::definitions::timestamp_from_chunk_cycle_and_sequence;
use fft::GoodAllocator;
use itertools::Itertools;
use log::{debug, trace};
use prover::risc_v_simulator::abstractions::non_determinism::NonDeterminismCSRSource;
use prover::risc_v_simulator::cycle::state_new::RiscV32StateForUnrolledProver;
use prover::risc_v_simulator::cycle::MachineConfig;
use prover::risc_v_simulator::delegations::DelegationsCSRProcessor;
use prover::ShuffleRamSetupAndTeardown;
use std::alloc::Global;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::ops::Deref;
use std::time::Instant;
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

pub struct CyclesChunk<A: GoodAllocator> {
    pub index: usize,
    pub data: CycleTracingData<A>,
}

#[derive(Clone)]
pub enum CpuWorkerMode<A: GoodAllocator> {
    TraceTouchedRam {
        circuit_type: MainCircuitType,
        skip_set: HashSet<(CircuitType, usize)>,
        free_allocator: Receiver<A>,
    },
    TraceCycles {
        circuit_type: MainCircuitType,
        skip_set: HashSet<(CircuitType, usize)>,
        split_count: usize,
        split_index: usize,
        free_allocator: Receiver<A>,
    },
    TraceDelegations {
        circuit_type: MainCircuitType,
        skip_set: HashSet<(CircuitType, usize)>,
        free_allocator: Receiver<A>,
    },
}

pub fn get_cpu_worker_func<C: MachineConfig, A: GoodAllocator + 'static>(
    wait_group: WaitGroup,
    batch_id: u64,
    worker_id: usize,
    num_main_chunks_upper_bound: usize,
    binary: impl Deref<Target = impl Deref<Target = [u32]>> + Send + 'static,
    non_determinism: impl Deref<Target = impl NonDeterminism> + Send + 'static,
    mode: CpuWorkerMode<A>,
    results: Sender<WorkerResult<A>>,
) -> impl FnOnce() + Send + 'static {
    move || {
        match mode {
            CpuWorkerMode::TraceTouchedRam {
                circuit_type,
                skip_set,
                free_allocator,
            } => trace_touched_ram::<C, A>(
                batch_id,
                worker_id,
                num_main_chunks_upper_bound,
                circuit_type,
                binary,
                non_determinism,
                skip_set,
                free_allocator,
                results,
            ),
            CpuWorkerMode::TraceCycles {
                circuit_type,
                skip_set,
                split_count,
                split_index,
                free_allocator,
            } => trace_cycles::<C, A>(
                batch_id,
                worker_id,
                num_main_chunks_upper_bound,
                circuit_type,
                binary,
                non_determinism,
                skip_set,
                split_count,
                split_index,
                free_allocator,
                results,
            ),
            CpuWorkerMode::TraceDelegations {
                circuit_type,
                skip_set,
                free_allocator,
            } => trace_delegations::<C, A>(
                batch_id,
                worker_id,
                num_main_chunks_upper_bound,
                circuit_type,
                binary,
                non_determinism,
                skip_set,
                free_allocator,
                results,
            ),
        };
        drop(wait_group);
    }
}

fn trace_touched_ram<C: MachineConfig, A: GoodAllocator>(
    batch_id: u64,
    worker_id: usize,
    num_main_chunks_upper_bound: usize,
    circuit_type: MainCircuitType,
    binary: impl Deref<Target = impl Deref<Target = [u32]>>,
    non_determinism: impl Deref<Target = impl NonDeterminism>,
    skip_set: HashSet<(CircuitType, usize)>,
    free_allocator: Receiver<A>,
    results: Sender<WorkerResult<A>>,
) {
    trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] worker for tracing touched RAM started");
    let domain_size = circuit_type.get_domain_size();
    assert!(domain_size.is_power_of_two());
    let log_domain_size = domain_size.trailing_zeros();
    let mut non_determinism = non_determinism.clone();
    let mut memory = BoxedMemoryImplWithRom::<RAM_SIZE, LOG_ROM_SIZE>::new();
    for (idx, instruction) in binary.iter().enumerate() {
        memory.populate(ENTRY_POINT + idx as u32 * 4, *instruction);
    }
    let cycles_per_chunk = domain_size - 1;
    let mut state = RiscV32StateForUnrolledProver::<C>::initial(ENTRY_POINT);
    let mut custom_csr_processor = DelegationsCSRProcessor;
    let mut ram_tracing_data = RamTracingData::<RAM_SIZE, true>::new();
    let cycle_tracing_data = CycleTracingData::with_cycles_capacity(0);
    let delegation_tracing_data = DelegationTracingData::default();
    let delegation_swap_fn = |_, _| unreachable!();
    let initial_timestamp = timestamp_from_chunk_cycle_and_sequence(0, cycles_per_chunk, 0);
    let mut tracer =
        ExecutionTracer::<RAM_SIZE, LOG_ROM_SIZE, _, Global, Global, true, false, false>::new(
            &mut ram_tracing_data,
            cycle_tracing_data,
            delegation_tracing_data,
            delegation_swap_fn,
            initial_timestamp,
        );
    let mut end_reached = false;
    let mut chunks_traced_count = 0;
    let mut next_chunk_index_with_no_setup_and_teardown = 0;
    trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] starting simulation");
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
        trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] chunk {chunks_traced_count} finished in {elapsed_ms:.3} ms @ {mhz:.3} MHz");
        chunks_traced_count += 1;
        let touched_ram_cells_count =
            tracer.ram_tracing_data.get_touched_ram_cells_count() as usize;
        let chunks_needed_for_setup_and_teardowns =
            touched_ram_cells_count.div_ceil(cycles_per_chunk);
        let chunks_diff = chunks_traced_count - next_chunk_index_with_no_setup_and_teardown;
        if chunks_needed_for_setup_and_teardowns < chunks_diff {
            trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] chunk {next_chunk_index_with_no_setup_and_teardown} does not need setup and teardown");
            if skip_set.contains(&(
                CircuitType::Main(circuit_type),
                next_chunk_index_with_no_setup_and_teardown,
            )) {
                trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] chunk {next_chunk_index_with_no_setup_and_teardown} skipped");
            } else {
                let chunk = SetupAndTeardownChunk {
                    index: next_chunk_index_with_no_setup_and_teardown,
                    chunk: None,
                };
                let result = WorkerResult::SetupAndTeardownChunk(chunk);
                results.send(result).unwrap();
            }
            next_chunk_index_with_no_setup_and_teardown += 1;
        }
        if finished {
            let elapsed_ms = now.elapsed().as_secs_f64() * 1000.0;
            let cycles_count = chunks_traced_count * cycles_per_chunk;
            let speed = (cycles_count as f64) / (elapsed_ms * 1000.0);
            let touched_ram_cells_count = ram_tracing_data.get_touched_ram_cells_count();
            trace!(
                    "BATCH[{batch_id}] CPU_WORKER[{worker_id}] simulation ended at address 0x{:08x} and took {chunks_traced_count} chunks to finish execution",
                    state.observable.pc,
                );
            debug!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] simulator tracing touched RAM ran {chunks_traced_count}x(2^{log_domain_size}-1) cycles in {elapsed_ms:.3} ms @ {speed:.3} MHz");
            trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] simulator touched {touched_ram_cells_count} RAM cells");
            end_reached = true;
            break;
        }
        let new_timestamp =
            timestamp_from_chunk_cycle_and_sequence(0, cycles_per_chunk, chunks_traced_count);
        tracer.current_timestamp = new_timestamp;
    }
    assert!(
        end_reached,
        "BATCH[{batch_id}] CPU_WORKER[{worker_id}] end of execution was not reached after {num_main_chunks_upper_bound} chunks"
    );
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
    trace!(
        "BATCH[{batch_id}] CPU_WORKER[{worker_id}] {setup_and_teardown_chunks_count} setup and teardown chunk(s) are needed"
    );
    assert_eq!(
        chunks_traced_count,
        setup_and_teardown_chunks_count + next_chunk_index_with_no_setup_and_teardown
    );
    let now = Instant::now();
    for index in next_chunk_index_with_no_setup_and_teardown..chunks_traced_count {
        if skip_set.contains(&(CircuitType::Main(circuit_type), index)) {
            chunker.skip_next_chunk();
            trace!(
                "BATCH[{batch_id}] CPU_WORKER[{worker_id}] chunk {} skipped",
                index
            );
        } else {
            let allocator = free_allocator.recv().unwrap();
            let lazy_init_data = Vec::with_capacity_in(cycles_per_chunk, allocator);
            let mut setup_and_teardown = ShuffleRamSetupAndTeardown { lazy_init_data };
            unsafe { setup_and_teardown.lazy_init_data.set_len(cycles_per_chunk) };
            chunker.populate_next_chunk(&mut setup_and_teardown.lazy_init_data);
            let chunk = Some(setup_and_teardown);
            let chunk = SetupAndTeardownChunk { index, chunk };
            let result = WorkerResult::SetupAndTeardownChunk(chunk);
            results.send(result).unwrap();
        }
    }
    trace!(
        "BATCH[{batch_id}] CPU_WORKER[{worker_id}] setup and teardown chunk(s) collected in {:.3} ms",
        now.elapsed().as_secs_f64() * 1000.0
    );
    let final_register_values = state
        .observable
        .registers
        .into_iter()
        .zip(register_last_live_timestamps.into_iter())
        .map(|(value, last_access_timestamp)| FinalRegisterValue {
            value,
            last_access_timestamp,
        })
        .collect_array()
        .unwrap();
    let result = WorkerResult::RAMTracingResult {
        chunks_traced_count,
        final_register_values,
    };
    results.send(result).unwrap();
    trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] tracing touched RAM finished");
}

fn trace_cycles<C: MachineConfig, A: GoodAllocator + 'static>(
    batch_id: u64,
    worker_id: usize,
    num_main_chunks_upper_bound: usize,
    circuit_type: MainCircuitType,
    binary: impl Deref<Target = impl Deref<Target = [u32]>>,
    non_determinism: impl Deref<Target = impl NonDeterminism>,
    skip_set: HashSet<(CircuitType, usize)>,
    split_count: usize,
    split_index: usize,
    free_allocator: Receiver<A>,
    results: Sender<WorkerResult<A>>,
) {
    trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] worker for tracing cycles started");
    let domain_size = circuit_type.get_domain_size();
    assert!(domain_size.is_power_of_two());
    let log_domain_size = domain_size.trailing_zeros();
    let mut non_determinism = non_determinism.clone();
    let mut memory = BoxedMemoryImplWithRom::<RAM_SIZE, LOG_ROM_SIZE>::new();
    for (idx, instruction) in binary.iter().enumerate() {
        memory.populate(ENTRY_POINT + idx as u32 * 4, *instruction);
    }
    let cycles_per_chunk = domain_size - 1;
    let mut state = RiscV32StateForUnrolledProver::<C>::initial(ENTRY_POINT);
    let mut custom_csr_processor = DelegationsCSRProcessor;
    let mut ram_tracing_data = RamTracingData::<RAM_SIZE, false>::new();
    let mut end_reached = false;
    let mut chunks_traced_count = 0;
    trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] starting simulation");
    let now = Instant::now();
    for chunk_index in 0..num_main_chunks_upper_bound {
        let delegation_tracing_data = DelegationTracingData::default();
        let delegation_swap_fn = |_, _| unreachable!();
        let initial_timestamp =
            timestamp_from_chunk_cycle_and_sequence(0, cycles_per_chunk, chunk_index);
        let finished;
        if chunk_index % split_count == split_index
            && !skip_set.contains(&(CircuitType::Main(circuit_type), chunk_index))
        {
            let allocator = free_allocator.recv().unwrap();
            let per_cycle_data = Vec::with_capacity_in(cycles_per_chunk, allocator);
            let cycle_tracing_data = CycleTracingData { per_cycle_data };
            trace!(
                "BATCH[{batch_id}] CPU_WORKER[{worker_id}] tracing cycles for chunk {chunk_index}"
            );
            let mut tracer =
                ExecutionTracer::<RAM_SIZE, LOG_ROM_SIZE, _, A, Global, false, true, false>::new(
                    &mut ram_tracing_data,
                    cycle_tracing_data,
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
            trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] tracing cycles for chunk {chunk_index} finished in {elapsed_ms:.3} ms @ {mhz:.3} MHz");
            let chunk = CyclesChunk {
                index: chunk_index,
                data: tracer.cycle_tracing_data,
            };
            let result = WorkerResult::CyclesChunk(chunk);
            results.send(result).unwrap();
        } else {
            // fast-forward the simulation
            trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] fast-forwarding chunk {chunk_index}");
            let cycle_tracing_data = CycleTracingData::with_cycles_capacity(0);
            let mut tracer = ExecutionTracer::<
                RAM_SIZE,
                LOG_ROM_SIZE,
                _,
                Global,
                Global,
                false,
                false,
                false,
            >::new(
                &mut ram_tracing_data,
                cycle_tracing_data,
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
            trace!(
                "BATCH[{batch_id}] CPU_WORKER[{worker_id}] fast-forwarding chunk {chunk_index} finished in {elapsed_ms:.3} ms @ {mhz:.3} MHz"
            );
        }
        chunks_traced_count += 1;
        if finished {
            let elapsed_ms = now.elapsed().as_secs_f64() * 1000.0;
            let cycles_count = chunks_traced_count * cycles_per_chunk;
            let speed = (cycles_count as f64) / (elapsed_ms * 1000.0);
            trace!(
                "BATCH[{batch_id}] CPU_WORKER[{worker_id}] simulation ended at address 0x{:08x} and took {chunks_traced_count} chunks to finish execution",
                state.observable.pc,
            );
            debug!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] simulator tracing 1/{split_count} cycles ran {chunks_traced_count}x(2^{log_domain_size}-1) cycles in {elapsed_ms:.3} ms @ {speed:.3} MHz");
            end_reached = true;
            break;
        }
    }
    assert!(
        end_reached,
        "BATCH[{batch_id}] CPU_WORKER[{worker_id}] end of execution was not reached after {num_main_chunks_upper_bound} chunks"
    );
    let result = WorkerResult::CyclesTracingResult {
        chunks_traced_count,
    };
    results.send(result).unwrap();
    trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] tracing cycles finished");
}

fn trace_delegations<C: MachineConfig, A: GoodAllocator + 'static>(
    batch_id: u64,
    worker_id: usize,
    num_main_chunks_upper_bound: usize,
    circuit_type: MainCircuitType,
    binary: impl Deref<Target = impl Deref<Target = [u32]>>,
    non_determinism: impl Deref<Target = impl NonDeterminism>,
    skip_set: HashSet<(CircuitType, usize)>,
    free_allocator: Receiver<A>,
    results: Sender<WorkerResult<A>>,
) {
    trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] worker for tracing delegations started");
    let domain_size = circuit_type.get_domain_size();
    assert!(domain_size.is_power_of_two());
    let log_domain_size = domain_size.trailing_zeros();
    let mut non_determinism = non_determinism.clone();
    let mut memory = BoxedMemoryImplWithRom::<RAM_SIZE, LOG_ROM_SIZE>::new();
    for (idx, instruction) in binary.iter().enumerate() {
        memory.populate(ENTRY_POINT + idx as u32 * 4, *instruction);
    }
    let cycles_per_chunk = domain_size - 1;
    let mut state = RiscV32StateForUnrolledProver::<C>::initial(ENTRY_POINT);
    let mut custom_csr_processor = DelegationsCSRProcessor;
    let mut ram_tracing_data = RamTracingData::<RAM_SIZE, false>::new();
    let cycle_tracing_data = CycleTracingData::with_cycles_capacity(0);
    let delegation_tracing_data = DelegationTracingData::default();
    let delegation_chunks_counts = RefCell::new(HashMap::new());
    let delegation_swap_fn = |circuit_type, tracing_type: Option<DelegationTracingType<A>>| {
        if let Some(tracing_type) = tracing_type {
            let mut borrow = delegation_chunks_counts.borrow_mut();
            let value = borrow.entry(circuit_type).or_default();
            match tracing_type {
                DelegationTracingType::Counter(counter) => {
                    trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] full delegation {:?} chunk {value} counter with {} delegations counted", circuit_type, counter.num_requests);
                }
                DelegationTracingType::Witness(witness) => {
                    trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] full delegation {:?} chunk {value} witness with {} delegations produced", circuit_type, witness.num_requests);
                    let result = WorkerResult::DelegationWitness {
                        circuit_sequence: *value,
                        witness,
                    };
                    results.send(result).unwrap();
                }
            }
            *value += 1;
        }
        let current_count = delegation_chunks_counts
            .borrow()
            .get(&circuit_type)
            .copied()
            .unwrap_or_default();
        if skip_set.contains(&(CircuitType::Delegation(circuit_type), current_count)) {
            trace!(
                "BATCH[{batch_id}] CPU_WORKER[{worker_id}] skipping delegation {:?} chunk {current_count}",
                circuit_type
            );
            let counter = DelegationCounter {
                num_requests: circuit_type.get_num_delegation_cycles(),
                count: 0,
            };
            DelegationTracingType::Counter(counter)
        } else {
            let allocator = free_allocator.recv().unwrap();
            let factory = circuit_type.get_witness_factory_fn();
            let witness = factory(allocator);
            DelegationTracingType::Witness(witness)
        }
    };
    let initial_timestamp = timestamp_from_chunk_cycle_and_sequence(0, cycles_per_chunk, 0);
    let mut tracer =
        ExecutionTracer::<RAM_SIZE, LOG_ROM_SIZE, _, Global, A, false, false, true>::new(
            &mut ram_tracing_data,
            cycle_tracing_data,
            delegation_tracing_data,
            delegation_swap_fn,
            initial_timestamp,
        );
    let mut end_reached = false;
    let mut chunks_traced_count = 0;
    trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] starting simulation");
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
        trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] chunk {chunks_traced_count} finished in {elapsed_ms:.3} ms @ {mhz:.3} MHz");
        chunks_traced_count += 1;
        if finished {
            let elapsed_ms = now.elapsed().as_secs_f64() * 1000.0;
            let cycles_count = chunks_traced_count * cycles_per_chunk;
            let speed = (cycles_count as f64) / (elapsed_ms * 1000.0);
            trace!(
                "BATCH[{batch_id}] CPU_WORKER[{worker_id}] simulation ended at address 0x{:08x} and took {chunks_traced_count} chunks to finish execution",
                state.observable.pc,
            );
            debug!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] simulator tracing delegations ran {chunks_traced_count}x(2^{log_domain_size}-1) cycles in {elapsed_ms:.3} ms @ {speed:.3} MHz");
            end_reached = true;
            break;
        }
        let new_timestamp =
            timestamp_from_chunk_cycle_and_sequence(0, cycles_per_chunk, chunks_traced_count);
        tracer.current_timestamp = new_timestamp;
    }
    assert!(
        end_reached,
        "end of execution was not reached after {num_main_chunks_upper_bound} chunks"
    );
    let mut delegation_chunks_counts = delegation_chunks_counts.borrow().clone();
    for (circuit_type, tracing_type) in tracer.delegation_tracing_data.tracing_types.drain() {
        let value = delegation_chunks_counts.entry(circuit_type).or_default();
        match tracing_type {
            DelegationTracingType::Counter(counter) => {
                let count = counter.count;
                assert_ne!(count, 0);
                trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] delegation {circuit_type:?} chunk {value} counter with {count} delegations counted");
            }
            DelegationTracingType::Witness(witness) => {
                witness.assert_consistency();
                let is_empty = witness.write_timestamp.is_empty();
                trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] delegation {circuit_type:?} chunk {value} witness with {} delegations produced", witness.write_timestamp.len());
                let result = WorkerResult::DelegationWitness {
                    circuit_sequence: *value,
                    witness,
                };
                results.send(result).unwrap();
                if is_empty {
                    continue;
                }
            }
        }
        *value += 1;
    }
    let result = WorkerResult::DelegationTracingResult {
        delegation_chunks_counts,
    };
    results.send(result).unwrap();
    trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] tracing delegations finished");
}
