use crate::execution::messages::WorkerResult;
use crate::execution::tracing::{DataTraceRanges, TracingDataProducers, TracingType};
use crate::execution::A;
use crate::machine_type::MachineType;
use crate::sync_profiling::{self, SyncMetric};
use crossbeam_channel::{Receiver, Sender};
use cs::definitions::{TimestampScalar, INITIAL_TIMESTAMP, TIMESTAMP_STEP};
use era_cudart::memory::{CudaHostAllocFlags, CudaHostRegisterFlags, HostAllocation};
use era_cudart::result::CudaResultWrap;
use era_cudart_sys::{cudaHostRegister, cudaHostUnregister};
use itertools::Itertools;
use log::{debug, trace};
use riscv_transpiler::common_constants::ROM_WORD_SIZE;
use riscv_transpiler::jit::{
    ContextImpl, MachineState, MemoryHolder, TraceChunk, MAX_NUM_COUNTERS, RAM_SIZE,
    TRACE_CHUNK_LEN,
};
use riscv_transpiler::vm::NonDeterminismCSRSource;
use std::mem::replace;
use std::ops::{Deref, DerefMut};
use std::os::raw::c_void;
use std::ptr::NonNull;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use type_map::concurrent::TypeMap;

#[cfg(not(target_arch = "x86_64"))]
use self::compat::{Context, JittedCode};
#[cfg(target_arch = "x86_64")]
use riscv_transpiler::jit::{Context, JittedCode};

// We're depending on JIT unconditionally, so it can fail compilation on some platforms,
// since some of the exported paths are platform-dependent. So, we provide panicking
// replacements to allow compilation on the platforms, e.g. with
// `ZKSYNC_USE_CUDA_STUBS`.
#[cfg(not(target_arch = "x86_64"))]
mod compat {
    use super::{ContextImpl, MemoryHolder, TraceChunk};
    use std::marker::PhantomData;
    use std::ptr::NonNull;

    pub(super) struct Context<I: ContextImpl> {
        pub(super) implementation: I,
    }

    impl<I: ContextImpl> Context<I> {
        pub(super) fn new(implementation: I) -> Self {
            Self { implementation }
        }

        pub(super) fn into_implementation(self) -> I {
            self.implementation
        }
    }

    pub(super) struct JittedCode<I: ContextImpl> {
        _marker: PhantomData<I>,
    }

    unsafe impl<I: ContextImpl> Send for JittedCode<I> {}

    unsafe impl<I: ContextImpl> Sync for JittedCode<I> {}

    impl<I: ContextImpl> JittedCode<I> {
        pub(super) fn preprocess_bytecode(_program: &[u32], _cycles_bound: Option<u32>) -> Self {
            Self {
                _marker: PhantomData,
            }
        }

        pub(super) fn run_over_prepared_memory(
            &self,
            _context: &mut Context<I>,
            _memory: &mut MemoryHolder,
            _initial_trace_chunk: NonNull<TraceChunk>,
        ) {
            panic!("gpu_prover simulation requires the x86_64 JIT backend");
        }
    }
}

fn replay_segment_timestamp_bound(
    replay_segment_cycle_limit: Option<usize>,
    timestamp: TimestampScalar,
) -> TimestampScalar {
    replay_segment_cycle_limit
        .map(|cycle_limit| timestamp + (cycle_limit as TimestampScalar) * TIMESTAMP_STEP)
        .unwrap_or(TimestampScalar::MAX)
}

pub(crate) struct LockedBoxedMemoryHolder {
    pub holder: Box<MemoryHolder>,
}

impl LockedBoxedMemoryHolder {
    pub fn new() -> Self {
        unsafe {
            let mut holder = Box::<MemoryHolder>::new_zeroed().assume_init();
            cudaHostRegister(
                holder.as_mut() as *mut MemoryHolder as *mut c_void,
                size_of::<MemoryHolder>(),
                CudaHostRegisterFlags::DEFAULT.bits(),
            )
            .wrap()
            .unwrap();
            Self { holder }
        }
    }
}

impl Deref for LockedBoxedMemoryHolder {
    type Target = MemoryHolder;

    fn deref(&self) -> &Self::Target {
        &self.holder
    }
}

impl DerefMut for LockedBoxedMemoryHolder {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.holder
    }
}

impl Drop for LockedBoxedMemoryHolder {
    fn drop(&mut self) {
        unsafe {
            cudaHostUnregister(self.holder.as_mut() as *mut MemoryHolder as *mut c_void)
                .wrap()
                .unwrap();
        }
    }
}

pub(crate) struct LockedBoxedTraceChunk {
    pub chunk: Box<TraceChunk, A>,
}

impl LockedBoxedTraceChunk {
    pub fn new() -> Self {
        const LOG_CHUNK_SIZE: u32 = 20;
        let size = size_of::<TraceChunk>().next_multiple_of(1 << LOG_CHUNK_SIZE);
        let allocation = HostAllocation::alloc(size, CudaHostAllocFlags::DEFAULT).unwrap();
        let allocator = A::new(vec![allocation], LOG_CHUNK_SIZE);
        let chunk = unsafe { Box::<TraceChunk, _>::new_uninit_in(allocator).assume_init() };
        Self { chunk }
    }
}

impl Deref for LockedBoxedTraceChunk {
    type Target = TraceChunk;

    fn deref(&self) -> &Self::Target {
        &self.chunk
    }
}

impl DerefMut for LockedBoxedTraceChunk {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.chunk
    }
}

pub(crate) struct SharedTraceChunk {
    trace: LockedBoxedTraceChunk,
    remaining_segments: AtomicUsize,
}

// Segmented replay publishes immutable views into one completed trace chunk to multiple replay
// workers. The simulator never mutates a chunk after wrapping it here, and the last segment moves
// the chunk back into the free pool.
unsafe impl Send for SharedTraceChunk {}
unsafe impl Sync for SharedTraceChunk {}

impl SharedTraceChunk {
    fn new(trace: LockedBoxedTraceChunk, segments_count: usize) -> Self {
        assert_ne!(segments_count, 0);
        Self {
            trace,
            remaining_segments: AtomicUsize::new(segments_count),
        }
    }
}

pub(crate) enum SnapshotTrace {
    Owned(LockedBoxedTraceChunk),
    Shared {
        parent: Arc<SharedTraceChunk>,
        start: usize,
        end: usize,
        segment_index: usize,
        segments_count: usize,
    },
}

impl SnapshotTrace {
    pub fn range(&self) -> (&[u32], &[TimestampScalar]) {
        match self {
            Self::Owned(trace) => {
                let end = trace.len as usize;
                (&trace.values[..end], &trace.timestamps[..end])
            }
            Self::Shared {
                parent, start, end, ..
            } => {
                debug_assert!(*start <= *end);
                debug_assert!(*end <= parent.trace.len as usize);
                (
                    &parent.trace.values[*start..*end],
                    &parent.trace.timestamps[*start..*end],
                )
            }
        }
    }

    pub fn segment_index(&self) -> usize {
        match self {
            Self::Owned(_) => 0,
            Self::Shared { segment_index, .. } => *segment_index,
        }
    }

    pub fn segments_count(&self) -> usize {
        match self {
            Self::Owned(_) => 1,
            Self::Shared { segments_count, .. } => *segments_count,
        }
    }

    pub fn recycle(self, free_trace_chunks: &Sender<LockedBoxedTraceChunk>) -> bool {
        match self {
            Self::Owned(trace) => {
                sync_profiling::measure(SyncMetric::FreeTraceChunksSend, || {
                    free_trace_chunks.send(trace)
                })
                .unwrap();
                true
            }
            Self::Shared { parent, .. } => {
                if parent.remaining_segments.fetch_sub(1, Ordering::AcqRel) != 1 {
                    return false;
                }
                let shared = match Arc::try_unwrap(parent) {
                    Ok(shared) => shared,
                    Err(_) => panic!("last replay segment should own the final trace chunk handle"),
                };
                sync_profiling::measure(SyncMetric::FreeTraceChunksSend, || {
                    free_trace_chunks.send(shared.trace)
                })
                .unwrap();
                true
            }
        }
    }
}

pub(crate) struct PendingReplaySegment<R: DataTraceRanges> {
    pub cycles_count: usize,
    pub initial_state: MachineState,
    pub final_state: MachineState,
    pub trace_start: usize,
    pub trace_end: usize,
    pub trace_ranges: R,
}

pub(crate) struct Snapshot<R: DataTraceRanges> {
    pub index: usize,
    pub cycles_count: usize,
    pub initial_state: MachineState,
    pub trace: SnapshotTrace,
    pub final_state: MachineState,
    pub trace_ranges: R,
}

unsafe impl<R: DataTraceRanges> Send for Snapshot<R> {}

pub(crate) struct SimulationRunner<
    ND: NonDeterminismCSRSource + Send + 'static,
    T: TracingType + 'static,
    const SEGMENTED_REPLAY: bool = false,
> {
    pub batch_id: u64,
    pub non_determinism_source: ND,
    pub free_trace_chunks_sender: Sender<LockedBoxedTraceChunk>,
    pub free_trace_chunks_receiver: Receiver<LockedBoxedTraceChunk>,
    pub snapshots: Option<Sender<Snapshot<T::Ranges>>>,
    pub results: Option<Sender<WorkerResult<A>>>,
    pub abort: Arc<AtomicBool>,
    pub state: MachineState,
    pub trace: Option<LockedBoxedTraceChunk>,
    pub snapshot_index: usize,
    pub replay_segment_cycle_limit: Option<usize>,
    pub next_replay_segment_timestamp_bound: TimestampScalar,
    pub segment_trace_start: usize,
    pub pending_segments: Vec<PendingReplaySegment<T::Ranges>>,
    pub tracing_data_producers: Option<T::Producers>,
    pub instant: Option<Instant>,
    pub total_elapsed: Duration,
    pub is_aborted: bool,
}

impl<
        ND: NonDeterminismCSRSource + Send + 'static,
        T: TracingType + 'static,
        const SEGMENTED_REPLAY: bool,
    > SimulationRunner<ND, T, SEGMENTED_REPLAY>
{
    pub fn new(
        batch_id: u64,
        machine_type: MachineType,
        non_determinism_source: ND,
        free_trace_chunks_sender: Sender<LockedBoxedTraceChunk>,
        free_trace_chunks_receiver: Receiver<LockedBoxedTraceChunk>,
        snapshots: Sender<Snapshot<T::Ranges>>,
        results: Sender<WorkerResult<A>>,
        free_allocators: Receiver<A>,
        abort: Arc<AtomicBool>,
    ) -> Self {
        Self::new_with_replay_segment_cycle_limit(
            batch_id,
            machine_type,
            non_determinism_source,
            free_trace_chunks_sender,
            free_trace_chunks_receiver,
            snapshots,
            results,
            free_allocators,
            abort,
            None,
        )
    }

    pub fn new_with_replay_segment_cycle_limit(
        batch_id: u64,
        machine_type: MachineType,
        non_determinism_source: ND,
        free_trace_chunks_sender: Sender<LockedBoxedTraceChunk>,
        free_trace_chunks_receiver: Receiver<LockedBoxedTraceChunk>,
        snapshots: Sender<Snapshot<T::Ranges>>,
        results: Sender<WorkerResult<A>>,
        free_allocators: Receiver<A>,
        abort: Arc<AtomicBool>,
        replay_segment_cycle_limit: Option<usize>,
    ) -> Self {
        assert_eq!(
            SEGMENTED_REPLAY,
            replay_segment_cycle_limit.is_some(),
            "segmented replay JIT and runtime configuration must agree"
        );
        if let Some(replay_segment_cycle_limit) = replay_segment_cycle_limit {
            assert_ne!(replay_segment_cycle_limit, 0);
        }
        let tracing_data_producers =
            T::Producers::new(machine_type, free_allocators, results.clone());
        let tracing_data_producers = Some(tracing_data_producers);
        let next_replay_segment_timestamp_bound =
            replay_segment_timestamp_bound(replay_segment_cycle_limit, INITIAL_TIMESTAMP);
        Self {
            batch_id,
            non_determinism_source,
            free_trace_chunks_sender,
            free_trace_chunks_receiver,
            snapshots: Some(snapshots),
            results: Some(results),
            abort,
            state: MachineState::initial(),
            trace: None,
            snapshot_index: 0,
            replay_segment_cycle_limit,
            next_replay_segment_timestamp_bound,
            segment_trace_start: 0,
            pending_segments: Vec::new(),
            tracing_data_producers,
            instant: None,
            total_elapsed: Default::default(),
            is_aborted: false,
        }
    }

    pub fn run(
        mut self,
        binary_image: impl Deref<Target = impl Deref<Target = [u32]>>,
        text_section: impl Deref<Target = impl Deref<Target = [u32]>>,
        cycles_bound: Option<u32>,
        jit_cache: Arc<Mutex<TypeMap>>,
        memory_holder: &mut MemoryHolder,
    ) -> Self {
        let batch_id = self.batch_id;
        let jitted_code = {
            let mut guard = sync_profiling::lock(
                jit_cache.as_ref(),
                SyncMetric::JitCacheLockWait,
                SyncMetric::JitCacheLockHold,
            );
            let entry = guard.get::<Arc<JittedCode<Self>>>();
            if let Some(entry) = entry {
                entry.clone()
            } else {
                trace!("BATCH[{batch_id}] SIMULATOR JIT compiling bytecode");
                let jitted_code = JittedCode::preprocess_bytecode(&text_section, cycles_bound);
                trace!("BATCH[{batch_id}] SIMULATOR JIT compiled bytecode");
                let jitted_code = Arc::new(jitted_code);
                guard.insert(jitted_code.clone());
                jitted_code
            }
        };
        let binary_image_len = binary_image.len();
        memory_holder.memory[..binary_image_len].copy_from_slice(&binary_image);
        memory_holder.memory[binary_image_len..ROM_WORD_SIZE].fill(0);
        let mut trace = sync_profiling::measure(SyncMetric::FreeTraceChunksRecv, || {
            self.free_trace_chunks_receiver.recv()
        })
        .expect("must receive a trace chunk for simulation");
        trace.chunk.len = 0;
        let trace_ref = unsafe { NonNull::new_unchecked(trace.chunk.as_mut()) };
        self.trace = Some(trace);
        self.instant = Some(Instant::now());
        let mut context = Context::new(self);
        jitted_code.run_over_prepared_memory(&mut context, memory_holder, trace_ref);
        let mut runner = context.into_implementation();
        if let Some(trace) = runner.trace.take() {
            sync_profiling::measure(SyncMetric::FreeTraceChunksSend, || {
                runner.free_trace_chunks_sender.send(trace)
            })
            .unwrap();
        }
        if !runner.is_aborted {
            let final_timestamp = runner.state.timestamp;
            let timestamp_diff = final_timestamp - INITIAL_TIMESTAMP;
            assert!(timestamp_diff.is_multiple_of(TIMESTAMP_STEP));
            let cycles_count = (timestamp_diff / TIMESTAMP_STEP) as usize;
            let elapsed_ms = runner.total_elapsed.as_secs_f64() * 1000.0;
            let mhz = (cycles_count as f64) / (elapsed_ms * 1000.0);
            debug!("BATCH[{batch_id}] SIMULATOR finished execution with {cycles_count} cycles in {elapsed_ms:.3} ms @ {mhz:.3} MHz");
        }
        runner
    }

    fn process_trace(
        &mut self,
        machine_state: &MachineState,
        elapsed: Duration,
        final_trace_piece: bool,
    ) {
        sync_profiling::record(SyncMetric::SimulatorExecuteTraceChunk, elapsed);
        if self.is_aborted {
            return;
        }
        let batch_id = self.batch_id;
        let snapshot_index = self.snapshot_index;
        let mut machine_state = *machine_state;
        let timestamp = machine_state.timestamp.next_multiple_of(TIMESTAMP_STEP); // align timestamp, needs to be fixed in the VM
        machine_state.timestamp = timestamp;
        let final_state = machine_state;
        let initial_state = replace(&mut self.state, machine_state);
        let timestamp_diff = timestamp - initial_state.timestamp;
        assert!(timestamp_diff.is_multiple_of(TIMESTAMP_STEP));
        let cycles_count = (timestamp_diff / TIMESTAMP_STEP) as usize;
        let elapsed_ms = elapsed.as_secs_f64() * 1000.0;
        let mhz = (cycles_count as f64) / (elapsed_ms * 1000.0);
        let trace_end = self.trace.as_ref().unwrap().len as usize;
        let trace_start = self.segment_trace_start;
        let physical_trace_boundary = final_trace_piece || trace_end >= TRACE_CHUNK_LEN;
        trace!("BATCH[{batch_id}] SIMULATOR produced SNAPSHOT[{snapshot_index}] SEGMENT[{}] with {cycles_count} cycles and {} trace rows in {elapsed_ms:.3} ms @ {mhz:.3} MHz",
            self.pending_segments.len(),
            trace_end - trace_start,
        );
        if self.abort.load(std::sync::atomic::Ordering::Relaxed) {
            sync_profiling::measure_exclusive(SyncMetric::SimulatorFinalizeTracingData, || {
                self.tracing_data_producers.take().unwrap().finalize();
            });
            assert!(self.snapshots.take().is_some());
            assert!(self.results.take().is_some());
            let timestamp_diff = timestamp - INITIAL_TIMESTAMP;
            assert!(timestamp_diff.is_multiple_of(TIMESTAMP_STEP));
            let cycles_count = (timestamp_diff / TIMESTAMP_STEP) as usize;
            let elapsed_ms = self.total_elapsed.as_secs_f64() * 1000.0;
            let mhz = (cycles_count as f64) / (elapsed_ms * 1000.0);
            debug!("BATCH[{batch_id}] SIMULATOR stopping snapshot production due to abort signal after {cycles_count} cycles in {elapsed_ms:.3} ms @ {mhz:.3} MHz");
            self.is_aborted = true;
            return;
        }

        let pending_segment =
            sync_profiling::measure_exclusive(SyncMetric::SimulatorPrepareSnapshot, || {
                self.prepare_replay_segment(
                    snapshot_index,
                    cycles_count,
                    initial_state,
                    final_state,
                    trace_start,
                    trace_end,
                )
            });

        if SEGMENTED_REPLAY {
            self.pending_segments.push(pending_segment);
            self.segment_trace_start = trace_end;
            self.advance_replay_segment_timestamp_bound(timestamp);
            if physical_trace_boundary {
                self.publish_pending_segments(snapshot_index);
            }
        } else {
            assert!(physical_trace_boundary);
            self.publish_owned_snapshot(snapshot_index, pending_segment);
        }
    }

    fn prepare_replay_segment(
        &mut self,
        snapshot_index: usize,
        cycles_count: usize,
        initial_state: MachineState,
        final_state: MachineState,
        trace_start: usize,
        trace_end: usize,
    ) -> PendingReplaySegment<T::Ranges> {
        let counters_diff = final_state
            .counters
            .iter()
            .zip_eq(initial_state.counters.iter())
            .map(|(a, b)| a - b)
            .collect_array::<MAX_NUM_COUNTERS>()
            .unwrap();
        let expected_cycles = counters_diff.iter().take(6).sum::<u64>() as usize;
        assert_eq!(expected_cycles, cycles_count);
        let trace_ranges = self
            .tracing_data_producers
            .as_mut()
            .unwrap()
            .process_snapshot(
                snapshot_index,
                &initial_state.counters,
                &final_state.counters,
            );
        PendingReplaySegment {
            cycles_count,
            initial_state,
            final_state,
            trace_start,
            trace_end,
            trace_ranges,
        }
    }

    fn advance_replay_segment_timestamp_bound(&mut self, timestamp: TimestampScalar) {
        let Some(replay_segment_cycle_limit) = self.replay_segment_cycle_limit else {
            self.next_replay_segment_timestamp_bound = TimestampScalar::MAX;
            return;
        };
        let step = (replay_segment_cycle_limit as TimestampScalar) * TIMESTAMP_STEP;
        while self.next_replay_segment_timestamp_bound <= timestamp {
            self.next_replay_segment_timestamp_bound += step;
        }
    }

    fn publish_owned_snapshot(
        &mut self,
        snapshot_index: usize,
        pending_segment: PendingReplaySegment<T::Ranges>,
    ) {
        let trace = self.trace.take().unwrap();
        self.publish_snapshot_produced();
        let snapshot = Snapshot {
            index: snapshot_index,
            cycles_count: pending_segment.cycles_count,
            initial_state: pending_segment.initial_state,
            trace: SnapshotTrace::Owned(trace),
            final_state: pending_segment.final_state,
            trace_ranges: pending_segment.trace_ranges,
        };
        sync_profiling::measure(SyncMetric::SnapshotsSend, || {
            self.snapshots.as_ref().unwrap().send(snapshot)
        })
        .unwrap();
        self.snapshot_index += 1;
        self.segment_trace_start = 0;
    }

    fn publish_pending_segments(&mut self, snapshot_index: usize) {
        let trace = self.trace.take().unwrap();
        let pending_segments = replace(&mut self.pending_segments, Vec::new());
        let segments_count = pending_segments.len();
        assert_ne!(segments_count, 0);
        self.publish_snapshot_produced();
        let mut parent = Some(Arc::new(SharedTraceChunk::new(trace, segments_count)));
        for (segment_index, pending_segment) in pending_segments.into_iter().enumerate() {
            let parent = if segment_index + 1 == segments_count {
                parent.take().unwrap()
            } else {
                parent.as_ref().unwrap().clone()
            };
            let snapshot = Snapshot {
                index: snapshot_index,
                cycles_count: pending_segment.cycles_count,
                initial_state: pending_segment.initial_state,
                trace: SnapshotTrace::Shared {
                    parent,
                    start: pending_segment.trace_start,
                    end: pending_segment.trace_end,
                    segment_index,
                    segments_count,
                },
                final_state: pending_segment.final_state,
                trace_ranges: pending_segment.trace_ranges,
            };
            sync_profiling::measure(SyncMetric::SnapshotsSend, || {
                self.snapshots.as_ref().unwrap().send(snapshot)
            })
            .unwrap();
        }
        debug_assert!(parent.is_none());
        self.snapshot_index += 1;
        self.segment_trace_start = 0;
    }

    fn publish_snapshot_produced(&self) {
        let result = WorkerResult::SnapshotProduced;
        sync_profiling::measure(SyncMetric::WorkResultsSend, || {
            self.results.as_ref().unwrap().send(result)
        })
        .unwrap();
    }
}

impl<
        ND: NonDeterminismCSRSource + Send + 'static,
        T: TracingType,
        const SEGMENTED_REPLAY: bool,
    > ContextImpl for SimulationRunner<ND, T, SEGMENTED_REPLAY>
{
    const ENABLE_REPLAY_SEGMENT_CHECKS: bool = SEGMENTED_REPLAY;

    fn replay_segment_timestamp_bound(&self) -> TimestampScalar {
        self.next_replay_segment_timestamp_bound
    }

    #[inline(always)]
    fn read_nondeterminism(&mut self) -> u32 {
        self.non_determinism_source.read()
    }

    #[inline(always)]
    fn write_nondeterminism(&mut self, value: u32, memory: &[u32; RAM_SIZE]) {
        self.non_determinism_source
            .write_with_memory_access(memory, value);
    }

    fn receive_trace(
        &mut self,
        trace_piece: NonNull<TraceChunk>,
        machine_state: &MachineState,
    ) -> NonNull<TraceChunk> {
        let elapsed = self.instant.take().unwrap().elapsed();
        self.total_elapsed += elapsed;
        let argument_ptr = trace_piece.as_ptr();
        let current_ptr = self.trace.as_mut().unwrap().deref_mut() as *mut TraceChunk;
        assert_eq!(argument_ptr, current_ptr);
        self.process_trace(machine_state, elapsed, false);
        if self.trace.is_none() {
            let trace = sync_profiling::measure(SyncMetric::FreeTraceChunksRecv, || {
                self.free_trace_chunks_receiver.recv()
            })
            .unwrap();
            self.trace = Some(trace);
            self.trace.as_mut().unwrap().chunk.len = 0;
        }
        let ptr = self.trace.as_mut().unwrap().deref_mut() as *mut TraceChunk;
        self.instant = Some(Instant::now());
        NonNull::new(ptr).unwrap()
    }

    fn receive_final_trace_piece(
        &mut self,
        trace_piece: NonNull<TraceChunk>,
        machine_state: &MachineState,
    ) {
        let elapsed = self.instant.take().unwrap().elapsed();
        self.total_elapsed += elapsed;
        debug_assert!(
            (machine_state as *const MachineState).is_aligned_to(align_of::<MachineState>())
        );
        let argument_ptr = trace_piece.as_ptr();
        let current_ptr = self.trace.as_mut().unwrap().deref_mut() as *mut TraceChunk;
        assert_eq!(argument_ptr, current_ptr);
        self.process_trace(machine_state, elapsed, true);
        if !self.is_aborted {
            sync_profiling::measure_exclusive(SyncMetric::SimulatorFinalizeTracingData, || {
                self.tracing_data_producers.take().unwrap().finalize();
            });
        }
    }

    fn take_final_state(&mut self) -> Option<MachineState> {
        unreachable!()
    }

    fn final_state_ref(&'_ self) -> Option<&'_ MachineState> {
        unreachable!()
    }
}
