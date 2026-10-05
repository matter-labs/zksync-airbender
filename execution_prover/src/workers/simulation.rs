use crate::messages::{InitsAndTeardownsData, SimulationResult, WorkerResult};
use crate::tracing::{Tracer, TracingType};
use crate::upstream::FinalRegisterValue;
use crate::workers::simulation_runner::{
    EmptyInitsAndTeardownsStreamer, SimulationRunner, Snapshot,
};
use common_constants::{TimestampScalar, INITIAL_TIMESTAMP, TIMESTAMP_STEP};
use crossbeam_channel::{Receiver, Sender};
use execution_prover_model::allocator::HostTraceAllocator;
use execution_prover_model::circuit_type::{CircuitType, UnrolledCircuitType};
use execution_prover_model::trace::ChunkedTraceHolder;
use execution_prover_model::trace::{InitsAndTeardownsTraceHost, PAGE_SIZE_LOG2};
use execution_prover_model::MachineType;
use itertools::Itertools;
use log::{debug, trace};
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::jit::{JitRunnerRam, MemoryHolder, ReplayerMemChunks, TraceChunk};
use riscv_transpiler::replayer::ReplayerVM;
use riscv_transpiler::vm::{InstructionTape, NonDeterminismCSRSource, State};
use std::cmp::min;
use std::ops::{Deref, DerefMut};
use std::sync::atomic::AtomicBool;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use type_map::concurrent::TypeMap;
use worker::Worker;

const PAGE_SIZE_WORDS: usize = 1 << PAGE_SIZE_LOG2;
const ROM_PAGES: usize = common_constants::rom::ROM_BYTE_SIZE / 4 / PAGE_SIZE_WORDS;
const _: () = assert!(common_constants::rom::ROM_BYTE_SIZE.is_multiple_of(4 * PAGE_SIZE_WORDS));

pub(crate) fn run_simulator<
    ND: NonDeterminismCSRSource + Send + 'static,
    T: TracingType<A> + 'static,
    A: HostTraceAllocator + 'static,
    M: DerefMut<Target = MemoryHolder>,
    S: DerefMut<Target = TraceChunk> + Send + 'static,
>(
    batch_id: u64,
    machine_type: MachineType,
    unified_circuit: CircuitType,
    binary_image: impl Deref<Target = impl Deref<Target = [u32]>>,
    text_section: impl Deref<Target = impl Deref<Target = [u32]>>,
    cycles_bound: Option<u32>,
    jit_cache: Arc<Mutex<TypeMap>>,
    memory_holder: &mut M,
    non_determinism: Arc<Mutex<Option<ND>>>,
    free_trace_chunks_sender: Sender<S>,
    free_trace_chunks_receiver: Receiver<S>,
    snapshots: Sender<Snapshot<T::Ranges, S>>,
    results: Sender<WorkerResult<A>>,
    free_allocators: Receiver<A>,
    abort: Arc<AtomicBool>,
    worker: &Worker,
    ram_config: JitRunnerRam,
    assume_canonical_mop_inputs: bool,
) {
    assert_ne!(ram_config, JitRunnerRam::UninitPlaceholder);
    assert_eq!(ram_config.ram_size(), memory_holder.ram_size());

    trace!("BATCH[{batch_id}] SIMULATOR started");
    let mut non_determinism_guard = non_determinism
        .lock()
        .expect("simulation worker non-determinism mutex poisoned");
    let non_determinism_source = non_determinism_guard.take().unwrap();
    let ram_words = memory_holder.memory().len();
    let carrier = if T::IS_SPLIT {
        CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns)
    } else {
        unified_circuit
    };
    let geometry = InitsAndTeardownsGeometry::new(carrier, ram_words);
    let empty_it_streamer = (!T::IS_SPLIT).then(|| EmptyInitsAndTeardownsStreamer {
        circuit_type: unified_circuit,
        cycles_per_circuit: unified_circuit.get_domain_size(),
        max_it_instances: geometry.max_instances(),
        next_sequence_id: 0,
    });
    let runner = SimulationRunner::<_, T, _, _>::new(
        batch_id,
        machine_type,
        unified_circuit,
        non_determinism_source,
        free_trace_chunks_sender,
        free_trace_chunks_receiver,
        snapshots,
        results,
        free_allocators.clone(),
        abort,
        empty_it_streamer,
        ram_config,
        assume_canonical_mop_inputs,
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
        empty_it_streamer,
        ..
    } = runner;
    *non_determinism_guard = Some(non_determinism_source);
    let should_abort = abort.load(std::sync::atomic::Ordering::Relaxed);
    if !should_abort {
        assert!(!is_aborted);
        let results = results.unwrap();
        let instant = Instant::now();
        let (memory, timestamps) = memory_holder.memory_and_timestamps_mut();
        let touched_pages = find_touched_pages(timestamps, worker);
        let elapsed = instant.elapsed();
        let elapsed_ms = elapsed.as_secs_f64() * 1000.0;
        let count = touched_pages.len();
        trace!("BATCH[{batch_id}] SIMULATOR collected INITS_AND_TEARDOWNS with {count} pages in {elapsed_ms:.3} ms");
        let mut instant = Instant::now();
        let partitioning = InitsAndTeardownsPartitioning::new(touched_pages, geometry);
        let (circuit_type, sequence_id_offset) = if T::IS_SPLIT {
            (
                CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns),
                0usize,
            )
        } else {
            // Unified mode: sequence_ids must span the full circuit count even
            // for circuits with no I&T data, or the replayer's tracing results
            // would not pair up. Each unified circuit covers `domain_size`
            // cycles, matching where the tracing producer slices
            // (`cycles_per_circuit_for`).
            let per_circuit_count = unified_circuit.get_domain_size();
            let timestamp_diff = state.timestamp - INITIAL_TIMESTAMP;
            assert!(timestamp_diff.is_multiple_of(TIMESTAMP_STEP));
            let total_cycles = (timestamp_diff / TIMESTAMP_STEP) as usize;
            let total_circuits = total_cycles.div_ceil(per_circuit_count);
            // The i&t-carrying instances are the TRAILING ones, so the markers
            // take the leading sequence_ids.
            let it_circuits = partitioning.instances_count();
            if unified_circuit == CircuitType::L1Wrap {
                assert_l1_wrap_geometry(total_circuits, it_circuits);
            }
            assert!(
                it_circuits <= total_circuits,
                "inits-and-teardowns needs {it_circuits} unified instances but the execution \
                 only spans {total_circuits} ({total_cycles} cycles)"
            );
            let empty_circuits = total_circuits - it_circuits;
            let streamed = empty_it_streamer.map_or(0, |s| s.next_sequence_id);
            for sequence_id in streamed..empty_circuits {
                let data = InitsAndTeardownsData {
                    circuit_type: unified_circuit,
                    sequence_id,
                    inits_and_teardowns: None,
                };
                let result = WorkerResult::InitsAndTeardownsData(data);
                results.send(result).expect(
                    "CPU worker results channel closed while sending empty init/teardown data",
                );
            }
            (unified_circuit, empty_circuits)
        };
        for (sequence_id, inits_and_teardowns_data) in partitioning
            .into_chunks(memory, timestamps, worker, free_allocators)
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
        memory_holder.reset_buffer();
    }
    trace!("BATCH[{batch_id}] SIMULATOR finished");
}

pub(crate) fn run_replayer<
    T: TracingType<A>,
    A: HostTraceAllocator,
    S: DerefMut<Target = TraceChunk> + Send,
>(
    batch_id: u64,
    worker_id: usize,
    tape: impl Deref<Target = impl InstructionTape>,
    snapshots: Receiver<Snapshot<T::Ranges, S>>,
    free_trace_chunks: Sender<S>,
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
        ReplayerVM::<T::Counters>::replay_basic_unrolled::<_, _, crate::upstream::BF>(
            &mut state,
            &mut ram,
            tape.deref(),
            &mut nd,
            cycles_count,
            &mut tracer,
        );
        let elapsed = instant.elapsed();
        // SnapshotReplayed allows the consumer to recycle cached trace data
        // immediately. Release every PtrRange's chunk Arc before publishing it.
        drop(tracer);
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

/// Global indices of the pages holding at least one timestamped word, ascending.
fn find_touched_pages(timestamps: &[TimestampScalar], worker: &Worker) -> Vec<u32> {
    assert!(timestamps.len().is_multiple_of(PAGE_SIZE_WORDS));
    let num_pages = timestamps.len() / PAGE_SIZE_WORDS;
    assert!(u32::try_from(num_pages).is_ok());
    let mut touched = vec![vec![]; worker.get_num_cores()];
    let mut dst = &mut touched[..];
    worker.scope(num_pages, |scope, geometry| {
        for thread_idx in 0..geometry.len() {
            let chunk_size = geometry.get_chunk_size(thread_idx);
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
            let (el, rest) = dst.split_at_mut(1);
            dst = rest;
            let src = &timestamps[chunk_start * PAGE_SIZE_WORDS..][..chunk_size * PAGE_SIZE_WORDS];
            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                for (idx, page) in src.as_chunks::<PAGE_SIZE_WORDS>().0.iter().enumerate() {
                    if page.iter().fold(0, |acc, &timestamp| acc | timestamp) != 0 {
                        el[0].push((chunk_start + idx) as u32);
                    }
                }
            });
        }
    });
    touched.concat()
}

pub(crate) fn assert_l1_wrap_geometry(chunks: usize, it_instances: usize) {
    assert_eq!(
        it_instances, 1,
        "L1Wrap touched more than one inits/teardowns instance"
    );
    assert_eq!(chunks, 1, "L1Wrap needs exactly one unified chunk");
}

/// Address geometry of the circuit carrying the inits-and-teardowns data: each
/// of its `num_sets` sets covers one *window* of `1 << trace_len_log2`
/// consecutive RAM words, named in the proof by its global window index
/// (`top_bits`).
#[derive(Clone, Copy, Debug)]
struct InitsAndTeardownsGeometry {
    pages_per_set_log2: u32,
    num_sets: usize,
    windows_in_ram: u32,
}

impl InitsAndTeardownsGeometry {
    /// Upper bound on `instances_count()` of any partitioning: every window touched.
    fn max_instances(&self) -> usize {
        (self.windows_in_ram as usize).div_ceil(self.num_sets)
    }

    fn new(carrier: CircuitType, ram_words: usize) -> Self {
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

/// Touched pages plus the window schedule that assigns them to circuit
/// instances.
struct InitsAndTeardownsPartitioning {
    /// Global page indices, ascending: that order is also window-major, which
    /// is what lets `into_chunks` group by window in one streaming pass.
    pages: Vec<u32>,
    /// `(global window index, touched pages in that window)` per set slot,
    /// ascending, `num_sets` slots per instance. The counts let `into_chunks`
    /// size its payload buffers exactly.
    window_schedule: Vec<(u32, usize)>,
    geometry: InitsAndTeardownsGeometry,
}

impl InitsAndTeardownsPartitioning {
    fn new(pages: Vec<u32>, geometry: InitsAndTeardownsGeometry) -> Self {
        let InitsAndTeardownsGeometry {
            pages_per_set_log2,
            num_sets,
            windows_in_ram: _,
        } = geometry;
        let mut touched: Vec<(u32, usize)> = Vec::new();
        for &page_idx in pages.iter() {
            let window = page_idx >> pages_per_set_log2;
            match touched.last_mut() {
                Some((last, count)) if *last == window => *count += 1,
                _ => touched.push((window, 1)),
            }
        }
        // Pad to whole instances with the lowest untouched windows, as
        // `RamWithRomRegion::collect_inits_and_teardowns_sets` does; the padding
        // windows enter the transcript.
        let missing = touched.len().max(1).div_ceil(num_sets) * num_sets - touched.len();
        let padding: Vec<(u32, usize)> = (0..)
            .filter(|window| touched.binary_search_by_key(window, |(w, _)| *w).is_err())
            .take(missing)
            .map(|window| (window, 0))
            .collect();
        let mut window_schedule = touched;
        window_schedule.extend(padding);
        window_schedule.sort_unstable();
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
    /// Each touched page fills `1 << PAGE_SIZE_LOG2` slots of `values_packed` /
    /// `timestamps_packed` with untouched cells zero-padded (the GPU kernel
    /// relies on this), and the holder's timestamped words are cleared on the
    /// way.
    ///
    /// Pool allocators are pulled from `free_allocators` whenever the current
    /// chunk for a given series is full; the chunk's `Arc` is what eventually
    /// returns the allocator to the pool when the orchestrator drops the host
    /// after the backend has consumed it.
    fn into_chunks<'a, A: HostTraceAllocator + 'a>(
        self,
        memory: &'a mut [u32],
        timestamps: &'a mut [TimestampScalar],
        worker: &'a Worker,
        free_allocators: Receiver<A>,
    ) -> impl Iterator<Item = InitsAndTeardownsTraceHost<A>> + 'a {
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
        let instances_count = window_schedule.len() / num_sets;
        let mut next_page = 0;
        (0..instances_count).map(move |instance_idx| {
            let slots = &window_schedule[instance_idx * num_sets..][..num_sets];
            let take: usize = slots.iter().map(|(_, count)| *count).sum();
            // Page and schedule order agree, so this instance's pages are
            // exactly the next `take` ones.
            let instance_pages = &pages[next_page..next_page + take];
            next_page += take;
            let page_indices_flat: Vec<u32> = instance_pages
                .iter()
                .map(|&page_idx| local_page_index(page_idx, slots, pages_per_set_log2))
                .collect();
            let page_indices = chunk_into_blocks(&page_indices_flat, &free_allocators);
            let (values_packed, timestamps_packed) =
                pack_pages(instance_pages, memory, timestamps, &free_allocators, worker);
            InitsAndTeardownsTraceHost {
                page_indices,
                values_packed,
                timestamps_packed,
                top_bits: slots.iter().map(|(w, _)| *w).collect(),
            }
        })
    }
}

/// Pool chunks with room for `num_pages` whole pages of `T`, each paired with
/// its page count: as many pages as its allocator holds. The chunks are empty.
fn alloc_page_chunks<T, A: HostTraceAllocator>(
    num_pages: usize,
    free_allocators: &Receiver<A>,
) -> Vec<(Vec<T, A>, usize)> {
    let mut chunks = Vec::new();
    let mut remaining = num_pages;
    while remaining > 0 {
        let allocator = free_allocators
            .recv()
            .expect("CPU worker allocator channel closed while building tracing data");
        let pages_per_chunk = allocator.capacity() / size_of::<T>() / PAGE_SIZE_WORDS;
        assert!(
            pages_per_chunk > 0,
            "pool allocator capacity {} < one page of {} bytes",
            allocator.capacity(),
            PAGE_SIZE_WORDS * size_of::<T>()
        );
        let count = min(pages_per_chunk, remaining);
        chunks.push((
            Vec::with_capacity_in(count * PAGE_SIZE_WORDS, allocator),
            count,
        ));
        remaining -= count;
    }
    chunks
}

/// Dense values and timestamps of `pages` in pool chunks, one page after the
/// other. A page's untouched words and all ROM values come out zero; the
/// holder's timestamped words are zeroed, leaving it clean for reuse.
fn pack_pages<A: HostTraceAllocator>(
    pages: &[u32],
    memory: &mut [u32],
    timestamps: &mut [TimestampScalar],
    free_allocators: &Receiver<A>,
    worker: &Worker,
) -> (
    ChunkedTraceHolder<u32, A>,
    ChunkedTraceHolder<TimestampScalar, A>,
) {
    let mut values = alloc_page_chunks::<u32, A>(pages.len(), free_allocators);
    let mut stamps = alloc_page_chunks::<TimestampScalar, A>(pages.len(), free_allocators);
    let mut src = Vec::with_capacity(pages.len());
    let (mut values_rest, mut stamps_rest) = (memory, timestamps);
    let mut next_page = 0;
    for &page_idx in pages {
        let skip = (page_idx as usize - next_page) * PAGE_SIZE_WORDS;
        let (page_values, rest) = std::mem::take(&mut values_rest)[skip..]
            .split_first_chunk_mut::<PAGE_SIZE_WORDS>()
            .unwrap();
        values_rest = rest;
        let (page_stamps, rest) = std::mem::take(&mut stamps_rest)[skip..]
            .split_first_chunk_mut::<PAGE_SIZE_WORDS>()
            .unwrap();
        stamps_rest = rest;
        src.push((page_idx as usize, page_values, page_stamps));
        next_page = page_idx as usize + 1;
    }
    let dst_values = values.iter_mut().flat_map(|(chunk, count)| {
        chunk.spare_capacity_mut()[..*count * PAGE_SIZE_WORDS]
            .as_chunks_mut::<PAGE_SIZE_WORDS>()
            .0
    });
    let dst_stamps = stamps.iter_mut().flat_map(|(chunk, count)| {
        chunk.spare_capacity_mut()[..*count * PAGE_SIZE_WORDS]
            .as_chunks_mut::<PAGE_SIZE_WORDS>()
            .0
    });
    let mut work: Vec<_> = src.into_iter().zip(dst_values.zip(dst_stamps)).collect();
    assert_eq!(work.len(), pages.len());
    let mut rest = &mut work[..];
    worker.scope(pages.len(), |scope, geometry| {
        for thread_idx in 0..geometry.len() {
            let (items, tail) = rest.split_at_mut(geometry.get_chunk_size(thread_idx));
            rest = tail;
            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                for ((page_idx, src_values, src_stamps), (dst_values, dst_stamps)) in items {
                    let keep_values = *page_idx >= ROM_PAGES;
                    for idx in 0..PAGE_SIZE_WORDS {
                        let timestamp = src_stamps[idx];
                        let value = src_values[idx];
                        let touched = timestamp != 0;
                        dst_stamps[idx].write(timestamp);
                        dst_values[idx].write(if touched && keep_values { value } else { 0 });
                        src_values[idx] = if touched { 0 } else { value };
                        src_stamps[idx] = 0;
                    }
                }
            });
        }
    });
    drop(work);
    // SAFETY: the scope above wrote every page of every chunk.
    unsafe { (finish_page_chunks(values), finish_page_chunks(stamps)) }
}

/// # Safety
/// Each chunk's first `count * PAGE_SIZE_WORDS` slots must be initialized.
unsafe fn finish_page_chunks<T, A: HostTraceAllocator>(
    chunks: Vec<(Vec<T, A>, usize)>,
) -> ChunkedTraceHolder<T, A> {
    let chunks = chunks
        .into_iter()
        .map(|(mut chunk, count)| {
            unsafe { chunk.set_len(count * PAGE_SIZE_WORDS) };
            Arc::new(chunk)
        })
        .collect();
    ChunkedTraceHolder { chunks }
}

/// Pack `src` into pool-allocator chunks of at most `allocator.capacity()`
/// bytes; an empty `src` gives no chunks. Each chunk's `Arc` keeps its
/// allocator alive until the orchestrator drops the host once the backend has
/// consumed it.
fn chunk_into_blocks<A: HostTraceAllocator>(
    src: &[u32],
    free_allocators: &Receiver<A>,
) -> ChunkedTraceHolder<u32, A> {
    let mut chunks = Vec::new();
    let mut rest = src;
    while !rest.is_empty() {
        let allocator = free_allocators
            .recv()
            .expect("CPU worker allocator channel closed while building tracing data");
        let capacity = allocator.capacity() / size_of::<u32>();
        assert!(capacity > 0, "pool allocator cannot hold a single u32");
        let (head, tail) = rest.split_at(min(capacity, rest.len()));
        let mut chunk = Vec::with_capacity_in(head.len(), allocator);
        chunk.extend_from_slice(head);
        chunks.push(Arc::new(chunk));
        rest = tail;
    }
    ChunkedTraceHolder { chunks }
}

#[cfg(test)]
mod cpu_partitioning_tests {
    use super::*;

    #[test]
    fn cpu_l1_wrap_uses_log22_windows_and_two_sets() {
        let geometry = InitsAndTeardownsGeometry::new(CircuitType::L1Wrap, 1 << 28);
        assert_eq!(geometry.pages_per_set_log2, 22 - PAGE_SIZE_LOG2);
        assert_eq!(geometry.num_sets, 2);
        let pages = vec![
            0,
            (1 << (22 - PAGE_SIZE_LOG2)) - 1,
            1 << (22 - PAGE_SIZE_LOG2),
        ];
        let partition = InitsAndTeardownsPartitioning::new(pages, geometry);
        assert_eq!(partition.instances_count(), 1);
        assert_eq!(windows_of(&partition), [0, 1]);
        let partition = InitsAndTeardownsPartitioning::new(
            vec![0, 1 << (22 - PAGE_SIZE_LOG2), 2 << (22 - PAGE_SIZE_LOG2)],
            geometry,
        );
        assert_eq!(partition.instances_count(), 2);
        assert_eq!(windows_of(&partition), [0, 1, 2, 3]);
    }

    #[test]
    #[should_panic(expected = "L1Wrap touched more than one inits/teardowns instance")]
    fn cpu_l1_wrap_it_overflow_is_rejected_before_generic_geometry_check() {
        assert_l1_wrap_geometry(1, 2);
    }

    #[test]
    #[should_panic(expected = "L1Wrap needs exactly one unified chunk")]
    fn cpu_l1_wrap_cycle_overflow_is_rejected() {
        assert_l1_wrap_geometry(2, 1);
    }

    const UNIFIED_RAM_WORDS: usize = (1usize << 30) / 4;

    fn unified_geometry() -> InitsAndTeardownsGeometry {
        InitsAndTeardownsGeometry::new(
            CircuitType::Unrolled(UnrolledCircuitType::Unified),
            UNIFIED_RAM_WORDS,
        )
    }

    /// Global index of page `page_in_window` in `window`.
    fn page_in(geometry: &InitsAndTeardownsGeometry, window: u32, page_in_window: u32) -> u32 {
        (window << geometry.pages_per_set_log2) | page_in_window
    }

    fn windows_of(p: &InitsAndTeardownsPartitioning) -> Vec<u32> {
        p.window_schedule.iter().map(|(w, _)| *w).collect()
    }

    #[test]
    fn cpu_unified_geometry_max_instances_bounds_any_partitioning() {
        let geometry = unified_geometry();
        assert_eq!(geometry.max_instances(), 16);
        let pages: Vec<_> = (0..geometry.windows_in_ram)
            .map(|w| page_in(&geometry, w, 0))
            .collect();
        let all_windows_touched = InitsAndTeardownsPartitioning::new(pages, geometry);
        assert_eq!(
            all_windows_touched.instances_count(),
            geometry.max_instances()
        );
    }

    #[test]
    fn cpu_unified_geometry_comes_from_the_unified_circuit() {
        let geometry = unified_geometry();
        // Standalone i&t geometry must not leak into unified execution.
        assert_eq!(geometry.num_sets, 2);
        assert_eq!(geometry.pages_per_set_log2, 23 - PAGE_SIZE_LOG2);
        assert_eq!(geometry.windows_in_ram, 32);
    }

    #[test]
    fn cpu_unified_carries_touched_windows_and_rebases_pages() {
        let geometry = unified_geometry();
        let p = InitsAndTeardownsPartitioning::new(
            vec![page_in(&geometry, 0, 3), page_in(&geometry, 2, 5)],
            geometry,
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
        // Window 0 free -> pad below the touched window; window 0 taken -> pad right above it.
        assert_eq!(
            windows_of(&InitsAndTeardownsPartitioning::new(
                vec![page_in(&geometry, 3, 0)],
                geometry
            )),
            vec![0, 3]
        );
        assert_eq!(
            windows_of(&InitsAndTeardownsPartitioning::new(
                vec![page_in(&geometry, 0, 0)],
                geometry
            )),
            vec![0, 1]
        );
        // No dirtied word still needs one instance.
        assert_eq!(
            windows_of(&InitsAndTeardownsPartitioning::new(vec![], geometry)),
            vec![0, 1]
        );

        let many = InitsAndTeardownsPartitioning::new(
            vec![
                page_in(&geometry, 1, 0),
                page_in(&geometry, 4, 0),
                page_in(&geometry, 5, 0),
                page_in(&geometry, 9, 0),
            ],
            geometry,
        );
        assert_eq!(windows_of(&many), vec![1, 4, 5, 9]);
        assert_eq!(many.instances_count(), 2);
    }

    /// The independent oracle: mark RAM words, let the transpiler's own
    /// collector group them into sets, and require our window schedule to
    /// reproduce its `top_bits` exactly.
    fn oracle_windows(
        words_per_chunk_log2: u32,
        num_sets: usize,
        touched_windows: &[u32],
    ) -> (Vec<u32>, Vec<u32>) {
        use field::baby_bear::base::BabyBearField;
        use riscv_transpiler::vm::{RamWithRomRegion, RAM};
        use std::alloc::Global;

        const ROM_BOUND_SECOND_WORD_BITS: usize = 1;
        const TOTAL_SIZE_BYTES: usize = 1 << 21;
        let ram_words = TOTAL_SIZE_BYTES / 4;

        let mut ram =
            RamWithRomRegion::<ROM_BOUND_SECOND_WORD_BITS>::from_rom_content(&[], TOTAL_SIZE_BYTES);
        // `read_word` rather than `write_word`: it also stamps the slot, and it
        // is legal inside the ROM range, so window 0 can be touched too.
        for (index, window) in touched_windows.iter().enumerate() {
            let word = (*window as usize) << words_per_chunk_log2;
            assert!(word < ram_words);
            ram.read_word((word * 4) as u32, ((index as TimestampScalar) + 1) << 4);
        }
        let legacy: Vec<u32> = ram
            .collect_inits_and_teardowns_sets::<BabyBearField, Global>(
                &worker::Worker::new_with_num_threads(2),
                words_per_chunk_log2 as usize,
                num_sets,
                None,
            )
            .into_iter()
            .flat_map(|(top_bits, _)| top_bits)
            .collect();

        let geometry = InitsAndTeardownsGeometry {
            pages_per_set_log2: words_per_chunk_log2 - PAGE_SIZE_LOG2,
            num_sets,
            windows_in_ram: (ram_words >> words_per_chunk_log2) as u32,
        };
        let pages = touched_windows
            .iter()
            .map(|window| page_in(&geometry, *window, 0))
            .collect();
        (
            legacy,
            windows_of(&InitsAndTeardownsPartitioning::new(pages, geometry)),
        )
    }

    #[test]
    fn cpu_schedule_matches_the_transpiler_collector_on_a_single_instance() {
        // Four windows of RAM, eight sets: the reference fills the hole between
        // the two touched windows and then pads PAST the RAM range.
        let (legacy, ours) = oracle_windows(17, 8, &[0, 3]);
        assert_eq!(legacy, vec![0, 1, 2, 3, 4, 5, 6, 7]);
        assert_eq!(ours, legacy);
    }

    #[test]
    fn cpu_schedule_matches_the_transpiler_collector_across_instances() {
        let (legacy, ours) = oracle_windows(14, 8, &[0, 3, 20, 21, 22, 23, 24, 25, 30]);
        assert_eq!(
            legacy,
            vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 20, 21, 22, 23, 24, 25, 30]
        );
        assert_eq!(ours, legacy);
    }

    #[test]
    fn cpu_standalone_carries_touched_windows_and_rebases_pages() {
        let geometry = InitsAndTeardownsGeometry::new(
            CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns),
            UNIFIED_RAM_WORDS,
        );
        let p = InitsAndTeardownsPartitioning::new(
            vec![page_in(&geometry, 0, 1), page_in(&geometry, 13, 2)],
            geometry,
        );
        assert_eq!(geometry.num_sets, 8);
        assert_eq!(windows_of(&p), vec![0, 1, 2, 3, 4, 5, 6, 13]);
        assert_eq!(p.instances_count(), 1);
        let global = (13 << geometry.pages_per_set_log2) | 2;
        assert_eq!(
            local_page_index(global, &p.window_schedule, geometry.pages_per_set_log2),
            (7 << geometry.pages_per_set_log2) | 2
        );
    }

    /// `into_chunks` against a word-by-word reference: dense pages with
    /// untouched words and ROM values zero, page-aligned chunks, and a holder
    /// with every timestamped word cleared and everything else intact.
    #[test]
    fn cpu_page_scan_packs_touched_pages_and_cleans_the_holder() {
        use execution_prover_model::allocator::CpuTraceAllocator;

        const RAM_WORDS: usize = 4 * ROM_PAGES * PAGE_SIZE_WORDS;
        const TOUCHED: [usize; 8] = [3, 1023, 1024, 1500, 1501, 2047, 3000, 4095];
        let geometry = InitsAndTeardownsGeometry {
            pages_per_set_log2: 7,
            num_sets: 2,
            windows_in_ram: (RAM_WORDS >> (7 + PAGE_SIZE_LOG2)) as u32,
        };
        let mut memory = vec![0u32; RAM_WORDS];
        let mut timestamps = vec![0 as TimestampScalar; RAM_WORDS];
        // The binary image sits in ROM without timestamps.
        for (idx, word) in memory[..ROM_PAGES * PAGE_SIZE_WORDS].iter_mut().enumerate() {
            *word = idx as u32 | 1;
        }
        for page in TOUCHED {
            for offset in [0, 1, 500, PAGE_SIZE_WORDS - 1] {
                let word = page * PAGE_SIZE_WORDS + offset;
                timestamps[word] = (word as TimestampScalar + 1) << 2;
                if page >= ROM_PAGES {
                    memory[word] = word as u32 ^ 0xA5A5_A5A5;
                }
            }
        }
        let (memory_before, timestamps_before) = (memory.clone(), timestamps.clone());

        let worker = Worker::new_with_num_threads(3);
        let pages = find_touched_pages(&timestamps, &worker);
        assert_eq!(pages, TOUCHED.map(|p| p as u32));
        // 16 KiB blocks: 4 pages of values or 2 pages of timestamps per chunk.
        let (sender, receiver) = crossbeam_channel::unbounded();
        for _ in 0..64 {
            sender.send(CpuTraceAllocator::new(16 << 10)).unwrap();
        }
        let hosts: Vec<_> = InitsAndTeardownsPartitioning::new(pages, geometry)
            .into_chunks(&mut memory, &mut timestamps, &worker, receiver)
            .collect();

        let mut values = vec![];
        let mut stamps = vec![];
        for host in &hosts {
            for chunk in &host.values_packed.chunks {
                assert!(chunk.len() % PAGE_SIZE_WORDS == 0 && chunk.len() <= 4 * PAGE_SIZE_WORDS);
                values.extend_from_slice(chunk);
            }
            for chunk in &host.timestamps_packed.chunks {
                assert!(chunk.len() % PAGE_SIZE_WORDS == 0 && chunk.len() <= 2 * PAGE_SIZE_WORDS);
                stamps.extend_from_slice(chunk);
            }
        }
        let mut expected_values = vec![];
        let mut expected_stamps = vec![];
        for page in TOUCHED {
            for word in page * PAGE_SIZE_WORDS..(page + 1) * PAGE_SIZE_WORDS {
                let timestamp = timestamps_before[word];
                let in_ram = word >= ROM_PAGES * PAGE_SIZE_WORDS;
                expected_stamps.push(timestamp);
                expected_values.push(if timestamp != 0 && in_ram {
                    memory_before[word]
                } else {
                    0
                });
            }
        }
        assert_eq!(values, expected_values);
        assert_eq!(stamps, expected_stamps);
        assert!(timestamps.iter().all(|&timestamp| timestamp == 0));
        for word in 0..RAM_WORDS {
            let kept = if timestamps_before[word] != 0 {
                0
            } else {
                memory_before[word]
            };
            assert_eq!(memory[word], kept, "word {word}");
        }
    }
}
