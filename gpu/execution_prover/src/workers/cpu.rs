use crate::messages::{InitsAndTeardownsData, SimulationResult, WorkerResult};
use crate::tracing::{Tracer, TracingType};
use crate::upstream::FinalRegisterValue;
use crate::workers::simulation_runner::{
    LockedBoxedMemoryHolder, LockedBoxedTraceChunk, SimulationRunner, Snapshot,
};
use crate::A;
use common_constants::{TimestampScalar, INITIAL_TIMESTAMP, TIMESTAMP_STEP};
use crossbeam_channel::{Receiver, Sender};
use gpu_core::primitives::machine_type::MachineType;
use gpu_trace::witness::circuit_type::{CircuitType, UnrolledCircuitType};
use gpu_trace::witness::trace::ChunkedTraceHolder;
use gpu_trace::witness::trace_unrolled::{InitsAndTeardownsTraceHost, PAGE_SIZE_LOG2};
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
    let mut non_determinism_guard = non_determinism
        .lock()
        .expect("simulation worker non-determinism mutex poisoned");
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
        let ram_words = memory_holder.memory.len();
        let inits_and_teardowns = collect_inits_and_teardowns(memory_holder, worker);
        let elapsed = instant.elapsed();
        let elapsed_ms = elapsed.as_secs_f64() * 1000.0;
        let count = inits_and_teardowns.iter().map(|v| v.len()).sum::<usize>();
        trace!("BATCH[{batch_id}] SIMULATOR collected INITS_AND_TEARDOWNS with {count} entries in {elapsed_ms:.3} ms");
        let mut instant = Instant::now();
        let carrier = if T::IS_SPLIT {
            UnrolledCircuitType::InitsAndTeardowns
        } else {
            UnrolledCircuitType::Unified
        };
        let geometry = InitsAndTeardownsGeometry::new(carrier, ram_words);
        let partitioning = InitsAndTeardownsPartitioning::new(inits_and_teardowns, geometry);
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
            // `domain_size` cycles (one cycle per usable row), which is also
            // where the tracing producer slices its circuits
            // (`cycles_per_circuit_for`), so both sides agree on the count.
            let per_circuit_count = UnrolledCircuitType::Unified.get_domain_size();
            let timestamp_diff = state.timestamp - INITIAL_TIMESTAMP;
            assert!(timestamp_diff.is_multiple_of(TIMESTAMP_STEP));
            let total_cycles = (timestamp_diff / TIMESTAMP_STEP) as usize;
            let total_circuits = total_cycles.div_ceil(per_circuit_count);
            // The i&t-carrying instances are the TRAILING ones, so the markers
            // take the leading sequence_ids.
            let it_circuits = partitioning.instances_count();
            assert!(
                it_circuits <= total_circuits,
                "inits-and-teardowns needs {it_circuits} unified instances but the execution \
                 only spans {total_circuits} ({total_cycles} cycles)"
            );
            let empty_circuits = total_circuits - it_circuits;
            for sequence_id in 0..empty_circuits {
                let data = InitsAndTeardownsData {
                    circuit_type: CircuitType::Unrolled(UnrolledCircuitType::Unified),
                    sequence_id,
                    inits_and_teardowns: None,
                };
                let result = WorkerResult::InitsAndTeardownsData(data);
                results.send(result).expect(
                    "CPU worker results channel closed while sending empty init/teardown data",
                );
            }
            (UnrolledCircuitType::Unified, empty_circuits)
        };
        let circuit_type = CircuitType::Unrolled(circuit_type);
        for (sequence_id, inits_and_teardowns_data) in
            partitioning.into_chunks(free_allocators).enumerate()
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
            results
                .send(result)
                .expect("CPU worker results channel closed while sending init/teardown data");
            instant = Instant::now();
        }
        let register_timestamps = state.register_timestamps_array();
        let final_register_values = state
            .materialized_registers()
            .into_iter()
            .zip(register_timestamps)
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
        results
            .send(result)
            .expect("CPU worker results channel closed while sending simulation result");
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
            free_trace_chunks
                .send(trace)
                .expect("CPU replayer trace-return channel closed while aborting");
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
        ReplayerVM::<T::Counters>::replay_basic_unrolled::<_, _, gpu_core::primitives::field::BF>(
            &mut state,
            &mut ram,
            tape.deref(),
            &mut nd,
            cycles_count,
            &mut tracer,
        );
        let elapsed = instant.elapsed();
        free_trace_chunks
            .send(trace)
            .expect("CPU replayer trace-return channel closed after replay");
        assert_eq!(state.pc, final_state.pc);
        assert_eq!(state.timestamp, final_state.timestamp);
        assert_eq!(state.registers, final_state.registers);
        total_elapsed += elapsed;
        total_cycles += cycles_count;
        let elapsed_ms = elapsed.as_secs_f64() * 1000.0;
        let mhz = (cycles_count as f64) / (elapsed_ms * 1000.0);
        trace!("BATCH[{batch_id}] REPLAYER[{worker_id}] processed SNAPSHOT[{index}] with {cycles_count} cycles in {elapsed_ms:.3} ms @ {mhz:.3} MHz");
        let result = WorkerResult::SnapshotReplayed(index);
        results
            .send(result)
            .expect("CPU replayer results channel closed while sending replay result")
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
                        // Documents the 32-bit RAM-word bound: `holder.memory`
                        // is sized to `NUM_RAM_WORDS = RAM_SIZE / 4` words
                        // with `RAM_SIZE == 1 << 30` bytes, so word indices
                        // stay well under `1 << 30` and `<< 2` cannot
                        // overflow into the address's u32 range today; this
                        // just guards/documents that architectural bound.
                        debug_assert!(
                            chunk_start + idx < (1usize << 30),
                            "RAM word index {} exceeds 32-bit word-address bound",
                            chunk_start + idx
                        );
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

/// Address geometry of the circuit carrying the inits-and-teardowns data: each
/// of its `num_sets` sets covers one *window* of `1 << trace_len_log2`
/// consecutive RAM words, named in the proof by its global window index
/// (`top_bits`).
#[derive(Clone, Copy)]
struct InitsAndTeardownsGeometry {
    pages_per_set_log2: u32,
    num_sets: usize,
    windows_in_ram: u32,
}

impl InitsAndTeardownsGeometry {
    fn new(carrier: UnrolledCircuitType, ram_words: usize) -> Self {
        let trace_len_log2 = carrier.get_domain_size_log2();
        assert!(
            trace_len_log2 >= PAGE_SIZE_LOG2,
            "inits-and-teardowns trace_len_log2 {trace_len_log2} below page size log2 {PAGE_SIZE_LOG2}"
        );
        Self {
            pages_per_set_log2: trace_len_log2 - PAGE_SIZE_LOG2,
            num_sets: carrier.get_num_inits_and_teardowns_sets(),
            windows_in_ram: ram_words.div_ceil(1usize << trace_len_log2) as u32,
        }
    }
}

/// Rebase a global page index onto the local geometry the kernel decodes: set
/// index in the high bits, page within that set's window in the low ones (see
/// `process_inits_and_teardowns_pages` in `memory_unrolled.cu`). `slots` is one
/// instance's slice of the window schedule.
#[inline]
fn local_page_index(page_idx: u32, slots: &[(u32, usize)], pages_per_set_log2: u32) -> u32 {
    let window = page_idx >> pages_per_set_log2;
    let set_idx = slots
        .iter()
        .position(|(w, _)| *w == window)
        .expect("page window must be scheduled in its own instance");
    ((set_idx as u32) << pages_per_set_log2) | (page_idx & ((1u32 << pages_per_set_log2) - 1))
}

/// Sparse init-and-teardown records aggregated into dense pages, plus the
/// window schedule that assigns those pages to circuit instances.
struct InitsAndTeardownsPartitioning {
    pages: BTreeMap<u32, (Vec<u32>, Vec<TimestampScalar>)>,
    /// `(global window index, touched pages in that window)` per set slot,
    /// ascending, `num_sets` slots per instance. The counts let `into_chunks`
    /// pre-size its payload buffers exactly.
    window_schedule: Vec<(u32, usize)>,
    geometry: InitsAndTeardownsGeometry,
}

impl InitsAndTeardownsPartitioning {
    fn new(values: Vec<Vec<InitAndTeardownRecord>>, geometry: InitsAndTeardownsGeometry) -> Self {
        let InitsAndTeardownsGeometry {
            pages_per_set_log2,
            num_sets,
            windows_in_ram,
        } = geometry;
        let page_size = 1usize << PAGE_SIZE_LOG2;
        // Keyed by GLOBAL page index: that order is also window-major, which is
        // what lets `into_chunks` group by window in one streaming pass without
        // re-scanning or sorting the page payloads.
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
        let mut touched: Vec<(u32, usize)> = Vec::new();
        for &page_idx in pages.keys() {
            let window = page_idx >> pages_per_set_log2;
            match touched.last_mut() {
                Some((last, count)) if *last == window => *count += 1,
                _ => touched.push((window, 1)),
            }
        }
        let window_schedule = if num_sets as u32 >= windows_in_ram {
            // The sets already span the whole address space (split mode), and
            // `full_statement_verifier::unrolled_proof_statement` asserts
            // `top_bits[i] == i`, so every window is present touched or not.
            (0..num_sets as u32)
                .map(|window| {
                    let count = touched
                        .binary_search_by_key(&window, |(w, _)| *w)
                        .map_or(0, |i| touched[i].1);
                    (window, count)
                })
                .collect()
        } else {
            // Pad to whole instances, and to at least one since the unified
            // verifier requires `num_it_circuits >= 1`. A padded set's rows are
            // all zero, so its init and teardown contributions cancel and its
            // window only has to keep the concatenated `top_bits` strictly
            // increasing; the choice of which mirrors the CPU reference.
            let instances = (touched.len().max(1)).div_ceil(num_sets);
            let missing = instances * num_sets - touched.len();
            if missing > 0 {
                let below = min(missing, touched.first().map_or(0, |(w, _)| *w) as usize);
                let mut padded = Vec::with_capacity(touched.len() + missing);
                padded.extend((0..below as u32).map(|w| (w, 0)));
                padded.append(&mut touched);
                padded.extend((0..(missing - below) as u32).map(|i| (windows_in_ram + i, 0)));
                touched = padded;
            }
            touched
        };
        Self {
            pages,
            window_schedule,
            geometry,
        }
    }

    fn instances_count(&self) -> usize {
        self.window_schedule.len() / self.geometry.num_sets
    }

    /// One `InitsAndTeardownsTraceHost` per instance, in ascending window order.
    /// Touched pages are filled to `1 << PAGE_SIZE_LOG2` slots of
    /// `values_packed` / `timestamps_packed` with untouched cells zero-padded
    /// (the GPU kernel relies on this), which is why the chunks handed to
    /// `chunk_into_pinned` are page-aligned.
    ///
    /// Pool allocators are pulled from `free_allocators` whenever the current
    /// chunk for a given series is full; the chunk's `Arc` is what eventually
    /// returns the allocator to the pool when the orchestrator drops the host
    /// after H2D has been scheduled.
    fn into_chunks(
        self,
        free_allocators: Receiver<A>,
    ) -> impl Iterator<Item = InitsAndTeardownsTraceHost> {
        let Self {
            pages,
            window_schedule,
            geometry:
                InitsAndTeardownsGeometry {
                    pages_per_set_log2,
                    num_sets,
                    ..
                },
        } = self;
        let page_size = 1usize << PAGE_SIZE_LOG2;
        let instances_count = window_schedule.len() / num_sets;
        let mut pages_iter = pages.into_iter();
        (0..instances_count).map(move |instance_idx| {
            let slots = &window_schedule[instance_idx * num_sets..][..num_sets];
            let take: usize = slots.iter().map(|(_, count)| *count).sum();
            let mut page_indices_flat: Vec<u32> = Vec::with_capacity(take);
            let mut values_flat: Vec<u32> = Vec::with_capacity(take * page_size);
            let mut timestamps_flat: Vec<TimestampScalar> = Vec::with_capacity(take * page_size);
            // Page and schedule order agree, so this instance's pages are
            // exactly the next `take` at the front of the iterator.
            for _ in 0..take {
                let (page_idx, (vals, ts)) = pages_iter.next().unwrap();
                page_indices_flat.push(local_page_index(page_idx, slots, pages_per_set_log2));
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
                top_bits: slots.iter().map(|(w, _)| *w).collect(),
            }
        })
    }
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
        let allocator = free_allocators
            .recv()
            .expect("CPU worker allocator channel closed while building tracing data");
        let elem_capacity = allocator.capacity() / size_of::<T>();
        // The pool allocator backs a fixed-size pinned buffer (currently
        // 64 MiB, see `host_allocator_backing_allocation_size`); the
        // `.max()` below assumes `elem_capacity` already covers one
        // alignment unit. If it didn't, `.max()` would silently force the
        // chunk length ABOVE the allocator's real capacity, over-allocating
        // against a fixed pool.
        assert!(
            elem_capacity >= alignment_in_items,
            "pool allocator elem capacity {elem_capacity} < alignment unit {alignment_in_items}"
        );
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

#[cfg(test)]
mod cpu_partitioning_tests {
    use super::*;

    const UNIFIED_RAM_WORDS: usize = (1usize << 30) / 4;

    fn unified_geometry() -> InitsAndTeardownsGeometry {
        InitsAndTeardownsGeometry::new(UnrolledCircuitType::Unified, UNIFIED_RAM_WORDS)
    }

    /// One record in `window`, at `page_in_window`, word 0 of that page.
    fn record_in(
        geometry: &InitsAndTeardownsGeometry,
        window: u32,
        page_in_window: u32,
    ) -> InitAndTeardownRecord {
        let page_idx = (window << geometry.pages_per_set_log2) | page_in_window;
        InitAndTeardownRecord {
            address: (page_idx << PAGE_SIZE_LOG2) << 2,
            teardown_value: 7,
            teardown_timestamp: 11,
        }
    }

    fn partition(
        geometry: InitsAndTeardownsGeometry,
        records: Vec<InitAndTeardownRecord>,
    ) -> InitsAndTeardownsPartitioning {
        InitsAndTeardownsPartitioning::new(vec![records], geometry)
    }

    fn windows_of(p: &InitsAndTeardownsPartitioning) -> Vec<u32> {
        p.window_schedule.iter().map(|(w, _)| *w).collect()
    }

    #[test]
    fn cpu_unified_geometry_comes_from_the_unified_circuit() {
        let geometry = unified_geometry();
        // The dedicated i&t circuit's 16 sets x 2^24 words must not leak in.
        assert_eq!(geometry.num_sets, 2);
        assert_eq!(geometry.pages_per_set_log2, 23 - PAGE_SIZE_LOG2);
        assert_eq!(geometry.windows_in_ram, 32);
    }

    #[test]
    fn cpu_unified_carries_touched_windows_and_rebases_pages() {
        let geometry = unified_geometry();
        let p = partition(
            geometry,
            vec![record_in(&geometry, 0, 3), record_in(&geometry, 2, 5)],
        );
        assert_eq!(windows_of(&p), vec![0, 2]);
        assert_eq!(p.instances_count(), 1);

        let slots = p.window_schedule.clone();
        let pages_per_set = 1u32 << geometry.pages_per_set_log2;
        assert_eq!(local_page_index(3, &slots, geometry.pages_per_set_log2), 3);
        assert_eq!(
            local_page_index(
                (2 << geometry.pages_per_set_log2) | 5,
                &slots,
                geometry.pages_per_set_log2
            ),
            pages_per_set | 5
        );
    }

    #[test]
    fn cpu_unified_pads_and_groups_into_whole_instances() {
        let geometry = unified_geometry();
        let beyond = geometry.windows_in_ram;

        // Window 0 free -> pad below it; window 0 taken -> pad past RAM.
        assert_eq!(
            windows_of(&partition(geometry, vec![record_in(&geometry, 3, 0)])),
            vec![0, 3]
        );
        assert_eq!(
            windows_of(&partition(geometry, vec![record_in(&geometry, 0, 0)])),
            vec![0, beyond]
        );
        // No dirtied word still needs one instance.
        assert_eq!(
            windows_of(&partition(geometry, vec![])),
            vec![beyond, beyond + 1]
        );

        let many = partition(
            geometry,
            vec![
                record_in(&geometry, 5, 0),
                record_in(&geometry, 1, 0),
                record_in(&geometry, 9, 0),
                record_in(&geometry, 4, 0),
            ],
        );
        assert_eq!(windows_of(&many), vec![1, 4, 5, 9]);
        assert_eq!(many.instances_count(), 2);
    }

    #[test]
    fn cpu_split_keeps_canonical_windows_and_page_indices() {
        let geometry = InitsAndTeardownsGeometry::new(
            UnrolledCircuitType::InitsAndTeardowns,
            UNIFIED_RAM_WORDS,
        );
        let p = partition(
            geometry,
            vec![record_in(&geometry, 0, 1), record_in(&geometry, 7, 2)],
        );
        assert_eq!(windows_of(&p), (0..16).collect::<Vec<_>>());
        assert_eq!(p.instances_count(), 1);
        // Set index == window, so the rebase is the identity.
        let global = (7 << geometry.pages_per_set_log2) | 2;
        assert_eq!(
            local_page_index(global, &p.window_schedule, geometry.pages_per_set_log2),
            global
        );
    }
}
