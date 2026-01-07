use super::A;
use crate::circuit_type::{CircuitType, UnrolledCircuitType};
use crate::execution::messages::SimulationResult;
use crate::execution::messages::{InitsAndTeardownsData, WorkerResult};
use crate::execution::simulation_runner::{
    LockedBoxedMemoryHolder, LockedBoxedTraceChunk, SimulationRunner, Snapshot,
};
use crate::execution::tracing::{Tracer, TracingType};
use crate::machine_type::MachineType;
use crate::witness::trace_unrolled::ShuffleRamInitsAndTeardownsHost;
use crossbeam_channel::{Receiver, Sender};
use cs::definitions::TimestampData;
use itertools::Itertools;
use log::{debug, trace};
use prover::common_constants;
use prover::definitions::LazyInitAndTeardown;
use prover::risc_v_simulator::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::common_constants::{TimestampScalar, INITIAL_TIMESTAMP, TIMESTAMP_STEP};
use riscv_transpiler::jit::{MemoryHolder, ReplayerMemChunks};
use riscv_transpiler::replayer::ReplayerVM;
use riscv_transpiler::vm::{InstructionTape, NonDeterminismCSRSource, State};
use std::cmp::min;
use std::ops::Deref;
use std::sync::atomic::AtomicBool;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use trace_and_split::FinalRegisterValue;
use type_map::concurrent::TypeMap;
use worker::Worker;

pub(crate) fn run_simulator<
    ND: NonDeterminismCSRSource + Send + 'static,
    T: TracingType + 'static,
>(
    batch_id: u64,
    machine_type: MachineType,
    binary_image: impl Deref<Target = impl Deref<Target = [u32]>>,
    text_section: impl Deref<Target = impl Deref<Target = [u32]>>,
    cycles_bound: Option<u32>,
    jit_cache: Arc<Mutex<TypeMap>>,
    memory_holder: &mut LockedBoxedMemoryHolder,
    non_determinism: Arc<Mutex<Option<ND>>>,
    free_trace_chunks_sender: Sender<LockedBoxedTraceChunk>,
    free_trace_chunks_receiver: Receiver<LockedBoxedTraceChunk>,
    snapshots: Sender<Snapshot<T::Ranges>>,
    results: Sender<WorkerResult<A>>,
    free_allocators: Receiver<A>,
    abort: Arc<AtomicBool>,
    worker: &Worker,
) {
    trace!("BATCH[{batch_id}] SIMULATOR started");
    let mut non_determinism_guard = non_determinism.lock().unwrap();
    let non_determinism_source = non_determinism_guard.take().unwrap();
    let runner = SimulationRunner::<_, T>::new(
        batch_id,
        machine_type,
        non_determinism_source,
        free_trace_chunks_sender,
        free_trace_chunks_receiver,
        snapshots,
        results,
        free_allocators.clone(),
        abort,
    );
    let runner = runner.run(
        binary_image,
        text_section,
        cycles_bound,
        jit_cache,
        memory_holder,
    );
    let SimulationRunner {
        batch_id,
        non_determinism_source,
        results,
        abort,
        state,
        is_aborted,
        ..
    } = runner;
    *non_determinism_guard = Some(non_determinism_source);
    let should_abort = abort.load(std::sync::atomic::Ordering::Relaxed);
    if !should_abort {
        assert!(!is_aborted);
        let results = results.unwrap();
        let instant = Instant::now();
        let inits_and_teardowns = collect_inits_and_teardowns(memory_holder, worker);
        let elapsed = instant.elapsed();
        let elapsed_ms = elapsed.as_secs_f64() * 1000.0;
        let count = inits_and_teardowns.iter().map(|v| v.len()).sum::<usize>();
        trace!("BATCH[{batch_id}] SIMULATOR collected INITS_AND_TEARDOWNS with {count} entries in {elapsed_ms:.3} ms");
        let mut instant = Instant::now();
        let (circuit_type, per_circuit_count, sequence_id_offset) = if T::IS_SPLIT {
            let per_circuit_count = setups::inits_and_teardowns::NUM_INIT_AND_TEARDOWN_SETS
                * setups::inits_and_teardowns::NUM_CYCLES;
            (UnrolledCircuitType::InitsAndTeardowns, per_circuit_count, 0)
        } else {
            let per_circuit_count = setups::unified_reduced_machine::NUM_CYCLES;
            let timestamp_diff = state.timestamp - INITIAL_TIMESTAMP;
            assert!(timestamp_diff.is_multiple_of(TIMESTAMP_STEP));
            let total_cycles = (timestamp_diff / TIMESTAMP_STEP) as usize;
            let empty_cycles = total_cycles - count;
            let empty_circuits = empty_cycles / per_circuit_count;
            for sequence_id in 0..empty_circuits {
                let data = InitsAndTeardownsData {
                    circuit_type: CircuitType::Unrolled(UnrolledCircuitType::Unified),
                    sequence_id,
                    inits_and_teardowns: None,
                };
                let result = WorkerResult::InitsAndTeardownsData(data);
                results.send(result).unwrap();
            }
            (
                UnrolledCircuitType::Unified,
                per_circuit_count,
                empty_circuits,
            )
        };
        let circuit_type = CircuitType::Unrolled(circuit_type);
        for (sequence_id, inits_and_teardowns_data) in
            get_inits_and_teardowns_chunks(inits_and_teardowns, per_circuit_count, free_allocators)
                .enumerate()
        {
            let sequence_id = sequence_id + sequence_id_offset;
            let count = inits_and_teardowns_data
                .chunks
                .iter()
                .map(|c| c.len())
                .sum::<usize>();
            let elapsed = instant.elapsed();
            let elapsed_ms = elapsed.as_secs_f64() * 1000.0;
            trace!("BATCH[{batch_id}] SIMULATOR produced INITS_AND_TEARDOWNS[{sequence_id}] with {count} entries in {elapsed_ms:.3} ms");
            let data = InitsAndTeardownsData {
                circuit_type,
                sequence_id,
                inits_and_teardowns: Some(inits_and_teardowns_data),
            };
            let result = WorkerResult::InitsAndTeardownsData(data);
            results.send(result).unwrap();
            instant = Instant::now();
        }
        let final_register_values = state
            .registers
            .into_iter()
            .zip(state.register_timestamps.into_iter())
            .map(|(value, last_access_timestamp)| FinalRegisterValue {
                value,
                last_access_timestamp,
            })
            .collect_array()
            .unwrap();
        let simulation_result = SimulationResult {
            final_register_values,
            final_pc: state.pc,
            final_timestamp: state.timestamp,
        };
        let result = WorkerResult::SimulationResult(simulation_result);
        results.send(result).unwrap();
    } else {
        trace!("BATCH[{batch_id}] SIMULATOR resetting memory due to abort");
        MemoryHolder::reset(&mut memory_holder.holder);
    }
    trace!("BATCH[{batch_id}] SIMULATOR finished");
}

pub(crate) fn run_replayer<T: TracingType>(
    batch_id: u64,
    worker_id: usize,
    tape: impl Deref<Target = impl InstructionTape>,
    snapshots: Receiver<Snapshot<T::Ranges>>,
    free_trace_chunks: Sender<LockedBoxedTraceChunk>,
    results: Sender<WorkerResult<A>>,
    abort: Arc<AtomicBool>,
) {
    trace!("BATCH[{batch_id}] REPLAYER[{worker_id}] started");
    let mut total_elapsed = Duration::default();
    let mut total_cycles = 0;
    let mut is_aborted = false;
    for snapshot in snapshots {
        if !is_aborted & abort.load(std::sync::atomic::Ordering::Relaxed) {
            debug!("BATCH[{batch_id}] REPLAYER[{worker_id}] aborting");
            is_aborted = true;
            if total_cycles != 0 {
                let elapsed_ms = total_elapsed.as_secs_f64() * 1000.0;
                let mhz = (total_cycles as f64) / (elapsed_ms * 1000.0);
                debug!("BATCH[{batch_id}] REPLAYER[{worker_id}] aborted replay after {total_cycles} cycles in {elapsed_ms:.3} ms @ {mhz:.3} MHz");
            }
        }
        let Snapshot {
            index,
            cycles_count,
            initial_state,
            trace,
            final_state,
            trace_ranges,
        } = snapshot;
        if is_aborted {
            free_trace_chunks.send(trace).unwrap();
            continue;
        }
        let trace_len = trace.len as usize;
        let mut state = initial_state.into();
        let final_state: State<T::Counters> = final_state.into();
        let mut ram = ReplayerMemChunks {
            chunks: &mut [(&trace.values[..trace_len], &trace.timestamps[..trace_len])],
        };
        let mut nd = QuasiUARTSource::new_with_reads(vec![]);
        let mut tracer = T::Tracer::new(trace_ranges);
        let instant = Instant::now();
        ReplayerVM::<T::Counters>::replay_basic_unrolled(
            &mut state,
            &mut ram,
            tape.deref(),
            &mut nd,
            cycles_count,
            &mut tracer,
        );
        let elapsed = instant.elapsed();
        free_trace_chunks.send(trace).unwrap();
        assert_eq!(state.pc, final_state.pc);
        assert_eq!(state.timestamp, final_state.timestamp);
        assert_eq!(state.registers, final_state.registers);
        total_elapsed += elapsed;
        total_cycles += cycles_count;
        let elapsed_ms = elapsed.as_secs_f64() * 1000.0;
        let mhz = (cycles_count as f64) / (elapsed_ms * 1000.0);
        trace!("BATCH[{batch_id}] REPLAYER[{worker_id}] processed SNAPSHOT[{index}] with {cycles_count} cycles in {elapsed_ms:.3} ms @ {mhz:.3} MHz");
        let result = WorkerResult::SnapshotReplayed(index);
        results.send(result).unwrap()
    }
    let elapsed_ms = total_elapsed.as_secs_f64() * 1000.0;
    let mhz = (total_cycles as f64) / (elapsed_ms * 1000.0);
    if !is_aborted && total_cycles != 0 {
        debug!("BATCH[{batch_id}] REPLAYER[{worker_id}] replayed {total_cycles} cycles in {elapsed_ms:.3} ms @ {mhz:.3} MHz");
    }
    trace!("BATCH[{batch_id}] REPLAYER[{worker_id}] finished");
}

fn collect_inits_and_teardowns(
    holder: &mut MemoryHolder,
    worker: &Worker,
) -> Vec<Vec<LazyInitAndTeardown>> {
    let mut chunks = vec![vec![]; worker.get_num_cores()];
    let mut dst = &mut chunks[..];
    worker.scope(holder.memory.len(), |scope, geometry| {
        for thread_idx in 0..geometry.len() {
            let chunk_size = geometry.get_chunk_size(thread_idx);
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
            let range = chunk_start..(chunk_start + chunk_size);
            let (el, rest) = dst.split_at_mut(1);
            dst = rest;
            let values = &holder.memory[range.clone()];
            let timestamps = &holder.timestamps[range];
            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                let values_ptr = values.as_ptr() as *mut u32;
                let timestamps_ptr = timestamps.as_ptr() as *mut TimestampScalar;
                let el = &mut el[0];
                for idx in 0..chunk_size {
                    let timestamp_ptr = timestamps_ptr.add(idx);
                    let timestamp = *timestamp_ptr;
                    if timestamp != 0 {
                        *timestamp_ptr = 0;
                        let value_ptr = values_ptr.add(idx);
                        let mut teardown_value = *value_ptr;
                        *value_ptr = 0;
                        let address = (chunk_start + idx) << 2;
                        if address < common_constants::rom::ROM_BYTE_SIZE {
                            teardown_value = 0;
                        }
                        let teardown_timestamp = TimestampData::from_scalar(timestamp);
                        let value = LazyInitAndTeardown {
                            address: address as u32,
                            teardown_value,
                            teardown_timestamp,
                        };
                        el.push(value);
                    }
                }
            });
        }
    });

    chunks
}

fn get_inits_and_teardowns_chunks(
    values: Vec<Vec<LazyInitAndTeardown>>,
    partition_size: usize,
    free_allocators: Receiver<A>,
) -> impl Iterator<Item = ShuffleRamInitsAndTeardownsHost<A>> {
    let inits_and_teardowns_count = values.iter().map(|v| v.len()).sum::<usize>();
    let mut iterator = values.into_iter().flat_map(|v| v.into_iter());
    let partitions_count = inits_and_teardowns_count.div_ceil(partition_size);
    (0..partitions_count).into_iter().map(move |index| {
        let mut values_count = if index == 0 {
            inits_and_teardowns_count - (partitions_count - 1) * partition_size
        } else {
            partition_size
        };
        let mut chunks = vec![];
        while values_count != 0 {
            let allocator = free_allocators.recv().unwrap();
            let capacity = allocator.capacity() / size_of::<LazyInitAndTeardown>();
            let count = min(capacity, values_count);
            let mut chunk = Vec::with_capacity_in(count, allocator);
            unsafe {
                chunk.set_len(count);
                for i in 0..count {
                    *chunk.get_unchecked_mut(i) = iterator.next().unwrap_unchecked();
                }
            };
            chunks.push(Arc::new(chunk));
            values_count -= count;
        }
        ShuffleRamInitsAndTeardownsHost { chunks }
    })
}
