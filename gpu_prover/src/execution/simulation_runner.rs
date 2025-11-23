use crate::execution::cpu_worker::LockedBoxedTraceChunk;
use crate::execution::messages::WorkerResult;
use crate::execution::snapshotter::Snapshot;
use crate::execution::tracing_data_producers::TracingDataProducers;
use crate::execution::A;
use crate::machine_type::MachineType;
use crossbeam_channel::{Receiver, Sender};
use cs::definitions::{INITIAL_TIMESTAMP, TIMESTAMP_STEP};
use itertools::Itertools;
use log::{debug, trace};
use riscv_transpiler::jit::{
    Context, ContextImpl, JittedCode, MachineState, MemoryHolder, TraceChunk, MAX_NUM_COUNTERS,
    MAX_TRACE_CHUNK_LEN, RAM_SIZE, TRACE_CHUNK_LEN,
};
use riscv_transpiler::vm::NonDeterminismCSRSource;
use std::mem::{replace, transmute};
use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;
use std::sync::atomic::AtomicBool;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use type_map::concurrent::TypeMap;

pub(crate) struct SimulationRunner<
    ND: NonDeterminismCSRSource + Send + 'static,
    P: TracingDataProducers + Send + 'static,
> {
    batch_id: u64,
    non_determinism_source: ND,
    free_trace_chunks: Receiver<LockedBoxedTraceChunk>,
    snapshots: Sender<Snapshot<P::Ranges>>,
    results: Sender<WorkerResult<A>>,
    abort: Arc<AtomicBool>,
    state: MachineState,
    final_state: Option<MachineState>,
    trace: Option<LockedBoxedTraceChunk>,
    snapshot_index: usize,
    tracing_data_producers: Option<P>,
    instant: Option<Instant>,
    total_elapsed: Duration,
    is_aborted: bool,
}

impl<ND: NonDeterminismCSRSource + Send + 'static, P: TracingDataProducers + Send + 'static>
    SimulationRunner<ND, P>
{
    fn new(
        machine_type: MachineType,
        batch_id: u64,
        non_determinism_source: ND,
        free_trace_chunks: Receiver<LockedBoxedTraceChunk>,
        snapshots: Sender<Snapshot<P::Ranges>>,
        results: Sender<WorkerResult<A>>,
        free_allocators: Receiver<A>,
        abort: Arc<AtomicBool>,
    ) -> Self {
        let tracing_data_producers = Some(P::new(machine_type, free_allocators, results.clone()));
        Self {
            batch_id,
            non_determinism_source,
            free_trace_chunks,
            snapshots,
            results,
            abort,
            state: MachineState::initial(),
            final_state: None,
            trace: None,
            snapshot_index: 0,
            tracing_data_producers,
            instant: None,
            total_elapsed: Default::default(),
            is_aborted: false,
        }
    }

    pub fn run(
        batch_id: u64,
        machine_type: MachineType,
        binary_image: impl Deref<Target = impl Deref<Target = [u32]>>,
        text_section: impl Deref<Target = impl Deref<Target = [u32]>>,
        cycles_bound: Option<u32>,
        jit_cache: Arc<Mutex<TypeMap>>,
        non_determinism_source: Arc<Mutex<Option<ND>>>,
        free_trace_chunks_sender: Sender<LockedBoxedTraceChunk>,
        free_trace_chunks_receiver: Receiver<LockedBoxedTraceChunk>,
        snapshots: Sender<Snapshot<P::Ranges>>,
        results: Sender<WorkerResult<A>>,
        free_allocators: Receiver<A>,
        abort: Arc<AtomicBool>,
    ) -> (MachineState, Box<MemoryHolder>) {
        trace!("getting jit code from cache or compiling new one");
        let jitted_code = {
            let mut guard = jit_cache.lock().unwrap();
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
        trace!("allocating memory holder for simulation");
        let mut memory_holder = unsafe { Box::<MemoryHolder>::new_uninit().assume_init() };
        trace!("zeroing memory holder memory");
        memory_holder.memory.fill(0);
        trace!("zeroing memory holder timestamps");
        memory_holder.timestamps.fill(0);
        trace!("copying binary image into memory holder");
        memory_holder.memory[..binary_image.len()].copy_from_slice(&binary_image);
        trace!("receiving free trace");
        let mut trace = free_trace_chunks_receiver
            .recv()
            .expect("must receive a trace chunk for simulation");
        trace.chunk.len = 0;
        let trace_ref = unsafe { NonNull::new_unchecked(trace.chunk.as_mut()) };
        trace!("getting ND");
        let mut nd_guard = non_determinism_source.lock().unwrap();
        let nd = nd_guard
            .take()
            .expect("Non-determinism source must be provided for simulation");
        trace!("creating simulation runner");
        let mut runner = Self::new(
            machine_type,
            batch_id,
            nd,
            free_trace_chunks_receiver,
            snapshots,
            results,
            free_allocators,
            abort,
        );
        runner.trace = Some(trace);
        runner.instant = Some(Instant::now());
        let mut context = Context {
            implementation: runner,
        };
        trace!("running");
        jitted_code.run_over_prepared_memory(&mut context, &mut memory_holder, trace_ref);
        let Context {
            implementation: mut runner,
        } = context;
        trace!("getting final state");
        let final_state = runner.take_final_state().expect("must finish execution");
        *nd_guard = Some(runner.non_determinism_source);
        if let Some(trace) = runner.trace.take() {
            free_trace_chunks_sender.send(trace).unwrap();
        }
        let timestamp_diff = final_state.timestamp - INITIAL_TIMESTAMP;
        assert!(timestamp_diff.is_multiple_of(TIMESTAMP_STEP));
        let cycles_count = (timestamp_diff / TIMESTAMP_STEP) as usize;
        let elapsed_ms = runner.total_elapsed.as_secs_f64() * 1000.0;
        let mhz = (cycles_count as f64) / (elapsed_ms * 1000.0);
        debug!("BATCH[{batch_id}] SIMULATOR finished execution with {cycles_count} cycles in {elapsed_ms:.3} ms @ {mhz:.3} MHz");
        (final_state, memory_holder)
    }

    fn process_trace(&mut self, machine_state: &MachineState, elapsed: Duration) {
        if self.is_aborted {
            return;
        }
        let batch_id = self.batch_id;
        if self.abort.load(std::sync::atomic::Ordering::Relaxed) {
            self.tracing_data_producers.take().unwrap().finalize();
            debug!("BATCH[{batch_id}] SIMULATOR stopping snapshot production due to abort signal");
            self.is_aborted = true;
            return;
        }
        let trace = self.trace.take().unwrap();
        let snapshot_index = self.snapshot_index;
        self.snapshot_index += 1;
        let result = WorkerResult::SnapshotProduced(snapshot_index);
        self.results.send(result).unwrap();
        let mut machine_state = *machine_state;
        machine_state.timestamp = machine_state.timestamp.next_multiple_of(TIMESTAMP_STEP); // align timestamp, needs to be fixed in the VM
        let final_state = machine_state;
        let initial_state = replace(&mut self.state, machine_state);
        let timestamp_diff = machine_state.timestamp - initial_state.timestamp;
        assert!(timestamp_diff.is_multiple_of(TIMESTAMP_STEP));
        let cycles_count = (timestamp_diff / TIMESTAMP_STEP) as usize;
        let elapsed_ms = elapsed.as_secs_f64() * 1000.0;
        let mhz = (cycles_count as f64) / (elapsed_ms * 1000.0);
        trace!("BATCH[{batch_id}] SIMULATOR produced SNAPSHOT[{snapshot_index}] with {cycles_count} cycles in {elapsed_ms:.3} ms @ {mhz:.3} MHz");
        let counters_diff = machine_state
            .counters
            .iter()
            .zip_eq(initial_state.counters.iter())
            .map(|(a, b)| a - b)
            .collect_array::<MAX_NUM_COUNTERS>()
            .unwrap();
        let expected_cycles = counters_diff.iter().take(6).sum::<u32>() as usize;
        assert_eq!(expected_cycles, cycles_count,);
        let trace_ranges = self
            .tracing_data_producers
            .as_mut()
            .unwrap()
            .process_snapshot(
                snapshot_index,
                &initial_state.counters,
                &machine_state.counters,
            );
        let snapshot = Snapshot {
            index: snapshot_index,
            cycles_count,
            initial_state,
            trace,
            final_state,
            trace_ranges,
        };
        self.snapshots.send(snapshot).unwrap();
    }
}

impl<ND: NonDeterminismCSRSource + Send + 'static, P: TracingDataProducers + Send + 'static>
    ContextImpl for SimulationRunner<ND, P>
{
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
        self.process_trace(machine_state, elapsed);
        if self.trace.is_none() {
            let trace = self.free_trace_chunks.recv().unwrap();
            self.trace = Some(trace);
        }
        self.trace.as_mut().unwrap().chunk.len = 0;
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
        self.process_trace(machine_state, elapsed);
        if !self.is_aborted {
            self.tracing_data_producers.take().unwrap().finalize();
        }
        self.final_state = Some(*machine_state);
    }

    fn take_final_state(&mut self) -> Option<MachineState> {
        self.final_state.take()
    }

    fn final_state_ref(&'_ self) -> Option<&'_ MachineState> {
        self.final_state.as_ref()
    }
}
