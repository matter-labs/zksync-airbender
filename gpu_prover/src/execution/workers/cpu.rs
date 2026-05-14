use crate::execution::messages::{InitsAndTeardownsData, SimulationResult, WorkerResult};
use crate::execution::tracing::{Tracer, TracingType};
use crate::execution::workers::simulation_runner::{
    LockedBoxedMemoryHolder, LockedBoxedTraceChunk, SimulationRunner, Snapshot,
};
use crate::execution::A;
use crate::primitives::circuit_type::{CircuitType, UnrolledCircuitType};
use crate::primitives::machine_type::MachineType;
use crate::upstream::FinalRegisterValue;
use crate::witness::trace::ChunkedTraceHolder;
use crate::witness::trace_unrolled::{InitsAndTeardownsTraceHost, PAGE_SIZE_LOG2};
use common_constants::{TimestampScalar, INITIAL_TIMESTAMP, TIMESTAMP_STEP};
use crossbeam_channel::{Receiver, Sender};
use itertools::Itertools;
use log::{debug, trace};
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::jit::{MemoryHolder, ReplayerMemChunks};
use riscv_transpiler::replayer::ReplayerVM;
use riscv_transpiler::vm::{InstructionTape, NonDeterminismCSRSource, State};
use std::cmp::min;
use std::collections::BTreeMap;
use std::ops::Deref;
use std::sync::atomic::AtomicBool;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use type_map::concurrent::TypeMap;
use worker::Worker;

/// Sparse init-and-teardown record produced by the memory-holder traversal.
#[derive(Clone, Copy, Debug)]
pub(crate) struct InitAndTeardownRecord {
    pub address: u32,
    pub teardown_value: u32,
    pub teardown_timestamp: TimestampScalar,
}

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
        let trace_len_log2 = CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns)
            .get_domain_size()
            .trailing_zeros() as usize;
        let num_sets = setups::inits_and_teardowns::NUM_INIT_AND_TEARDOWN_SETS;
        let pages_per_set_log2 = trace_len_log2 - PAGE_SIZE_LOG2 as usize;
        let pages_per_partition: usize = num_sets << pages_per_set_log2;
        let (circuit_type, sequence_id_offset) = if T::IS_SPLIT {
            (UnrolledCircuitType::InitsAndTeardowns, 0usize)
        } else {
            // Unified mode: emit empty-circuit markers up-front so
            // sequence_ids span the full circuit count. The orchestrator
            // and replayer assume `sequence_id` runs `0..total_circuits`
            // even for circuits that have no I&T data; without these
            // prefill markers, sequence_ids would skip and the replayer's
            // tracing results would not pair up.
            // Under the `2^N`-row convention each unified circuit covers
            // `domain_size` cycles (one cycle per usable row).
            let per_circuit_count = UnrolledCircuitType::Unified.get_domain_size();
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
            (UnrolledCircuitType::Unified, empty_circuits)
        };
        let circuit_type = CircuitType::Unrolled(circuit_type);
        for (sequence_id, inits_and_teardowns_data) in get_inits_and_teardowns_chunks(
            inits_and_teardowns,
            pages_per_partition,
            free_allocators,
        )
        .enumerate()
        {
            let sequence_id = sequence_id + sequence_id_offset;
            let count = inits_and_teardowns_data.page_indices.len();
            let elapsed = instant.elapsed();
            let elapsed_ms = elapsed.as_secs_f64() * 1000.0;
            trace!("BATCH[{batch_id}] SIMULATOR produced INITS_AND_TEARDOWNS[{sequence_id}] with {count} pages in {elapsed_ms:.3} ms");
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
        ReplayerVM::<T::Counters>::replay_basic_unrolled::<_, _, crate::primitives::field::BF>(
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
) -> Vec<Vec<InitAndTeardownRecord>> {
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
                        let value = InitAndTeardownRecord {
                            address: address as u32,
                            teardown_value,
                            teardown_timestamp: timestamp as TimestampScalar,
                        };
                        el.push(value);
                    }
                }
            });
        }
    });

    chunks
}

/// Group sparse init-and-teardown records by page and produce one
/// `InitsAndTeardownsTraceHost` per circuit-sized partition.
///
/// Each partition holds up to `pages_per_partition` touched pages. Touched
/// pages are filled to `1 << PAGE_SIZE_LOG2` slots of `values_packed` and
/// `timestamps_packed`, with untouched cells zero-padded (the GPU kernel
/// relies on this contract). The three series are kept in lockstep at
/// page granularity by allocating chunks aligned to the page boundary on the
/// `values_packed` and `timestamps_packed` sides; `page_indices` carries one
/// `u32` per page.
///
/// Pool allocators are pulled from `free_allocators` whenever the current
/// chunk for a given series is full; the chunk's `Arc` is what eventually
/// returns the allocator to the pool when the orchestrator drops the host
/// after H2D has been scheduled.
fn get_inits_and_teardowns_chunks(
    values: Vec<Vec<InitAndTeardownRecord>>,
    pages_per_partition: usize,
    free_allocators: Receiver<A>,
) -> impl Iterator<Item = InitsAndTeardownsTraceHost> {
    assert!(pages_per_partition > 0);
    let page_size = 1usize << PAGE_SIZE_LOG2;
    // Aggregate sparse records into dense pages keyed by `page_idx`. The
    // `BTreeMap` iteration order matches the test reference's ordering; the
    // GPU kernel does not require sorted page indices but emitting them in a
    // canonical order keeps debugging deterministic.
    let mut pages: BTreeMap<u32, (Vec<u32>, Vec<TimestampScalar>)> = BTreeMap::new();
    for chunk in values {
        for record in chunk {
            let word_idx = record.address >> 2;
            let page_idx = word_idx >> PAGE_SIZE_LOG2;
            let word_in_page = (word_idx & ((1u32 << PAGE_SIZE_LOG2) - 1)) as usize;
            let entry = pages
                .entry(page_idx)
                .or_insert_with(|| (vec![0u32; page_size], vec![0u64; page_size]));
            entry.0[word_in_page] = record.teardown_value;
            entry.1[word_in_page] = record.teardown_timestamp;
        }
    }
    let total_pages = pages.len();
    let partitions_count = total_pages.div_ceil(pages_per_partition).max(1);
    // Drain pages from the BTreeMap partition by partition. The *first*
    // partition absorbs the remainder and later partitions are full-sized;
    // keeps sequence_id assignment stable.
    let mut pages_iter = pages.into_iter();
    (0..partitions_count).map(move |index| {
        let take = if index == 0 {
            total_pages - (partitions_count - 1) * pages_per_partition
        } else {
            pages_per_partition
        };
        let mut page_indices_flat: Vec<u32> = Vec::with_capacity(take);
        let mut values_flat: Vec<u32> = Vec::with_capacity(take * page_size);
        let mut timestamps_flat: Vec<TimestampScalar> = Vec::with_capacity(take * page_size);
        for _ in 0..take {
            let (idx, (vals, ts)) = pages_iter.next().unwrap();
            page_indices_flat.push(idx);
            values_flat.extend_from_slice(&vals);
            timestamps_flat.extend_from_slice(&ts);
        }
        let page_indices = chunk_into_pinned::<u32>(&page_indices_flat, &free_allocators, 1);
        let values_packed = chunk_into_pinned::<u32>(&values_flat, &free_allocators, page_size);
        let timestamps_packed =
            chunk_into_pinned::<TimestampScalar>(&timestamps_flat, &free_allocators, page_size);
        InitsAndTeardownsTraceHost {
            page_indices,
            values_packed,
            timestamps_packed,
        }
    })
}

/// Pack a flat slice of `T` into pinned-allocator chunks of size at most
/// `allocator.capacity() / size_of::<T>()` items, with each chunk's length
/// rounded down to a multiple of `alignment_in_items`. The final chunk may
/// be shorter than the others but is still aligned.
///
/// Each chunk is allocated from a fresh pool allocator pulled from
/// `free_allocators`. The Arc keeps the allocator alive until the orchestrator
/// drops the host post-H2D-schedule.
fn chunk_into_pinned<T: Copy + 'static>(
    src: &[T],
    free_allocators: &Receiver<A>,
    alignment_in_items: usize,
) -> ChunkedTraceHolder<T, A> {
    assert!(alignment_in_items > 0);
    let mut chunks = Vec::new();
    if src.is_empty() {
        // Producer contract: an empty trace means an empty `Vec` of chunks; the
        // device-side total is zero and `schedule_multiple` packs nothing.
        return ChunkedTraceHolder { chunks };
    }
    let mut written = 0usize;
    while written < src.len() {
        let allocator = free_allocators.recv().unwrap();
        let elem_capacity = allocator.capacity() / size_of::<T>();
        // Round down to alignment so chunk lengths stay page-aligned.
        let aligned_capacity = (elem_capacity / alignment_in_items) * alignment_in_items;
        let aligned_capacity = aligned_capacity.max(alignment_in_items);
        let remaining = src.len() - written;
        let take = min(aligned_capacity, remaining);
        debug_assert_eq!(take % alignment_in_items, 0);
        let mut chunk = Vec::with_capacity_in(take, allocator);
        chunk.extend_from_slice(&src[written..written + take]);
        chunks.push(Arc::new(chunk));
        written += take;
    }
    ChunkedTraceHolder { chunks }
}
