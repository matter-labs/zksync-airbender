use crate::execution::messages::WorkerResult;
use crate::execution::snapshotter::Snapshot;
use crate::execution::tracing_data_producers::TracingDataProducers;
use crate::execution::A;
use crate::machine_type::MachineType;
use crossbeam_channel::{Receiver, Sender};
use cs::definitions::{INITIAL_TIMESTAMP, TIMESTAMP_STEP};
use log::{debug, trace};
use riscv_transpiler::jit::{
    Context, ContextImpl, JittedCode, MachineState, MemoryHolder, TraceChunk, MAX_TRACE_CHUNK_LEN,
    RAM_SIZE, TRACE_CHUNK_LEN,
};
use riscv_transpiler::vm::NonDeterminismCSRSource;
use std::mem::{replace, transmute};
use std::ops::{Deref, DerefMut};
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
    snapshots: Sender<Snapshot<P::Ranges>>,
    results: Sender<WorkerResult<A>>,
    abort: Arc<AtomicBool>,
    state: MachineState,
    final_state: Option<MachineState>,
    trace: Option<Box<TraceChunk>>,
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
        snapshots: Sender<Snapshot<P::Ranges>>,
        results: Sender<WorkerResult<A>>,
        free_allocators: Receiver<A>,
        abort: Arc<AtomicBool>,
    ) -> Self {
        let tracing_data_producers = Some(P::new(machine_type, free_allocators, results.clone()));
        Self {
            batch_id,
            non_determinism_source,
            snapshots,
            results,
            abort,
            state: Default::default(),
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
        snapshots: Sender<Snapshot<P::Ranges>>,
        results: Sender<WorkerResult<A>>,
        free_allocators: Receiver<A>,
        abort: Arc<AtomicBool>,
    ) -> (MachineState, Box<MemoryHolder>) {
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
        let mut memory = unsafe { Box::new_zeroed().assume_init() };
        let mut guard = non_determinism_source.lock().unwrap();
        let nd = guard
            .take()
            .expect("Non-determinism source must be provided for simulation");
        let mut runner = Self::new(
            machine_type,
            batch_id,
            nd,
            snapshots,
            results,
            free_allocators,
            abort,
        );
        let mut trace: Box<TraceChunk> = unsafe { Box::new_uninit().assume_init() };
        trace.len = 0;
        let trace_ref = unsafe { transmute(trace.as_mut()) };
        runner.trace = Some(trace);
        runner.instant = Some(Instant::now());
        let mut context = Context {
            implementation: runner,
        };
        JittedCode::run(
            &jitted_code,
            &mut context,
            &mut memory,
            trace_ref,
            &binary_image,
        );
        let Context {
            implementation: mut runner,
        } = context;
        let final_state = runner.take_final_state().expect("must finish execution");
        *guard = Some(runner.non_determinism_source);
        let timestamp_diff = final_state.timestamp - INITIAL_TIMESTAMP;
        assert!(timestamp_diff.is_multiple_of(TIMESTAMP_STEP));
        let cycles_count = (timestamp_diff / TIMESTAMP_STEP) as usize;
        let elapsed_ms = runner.total_elapsed.as_secs_f64() * 1000.0;
        let mhz = (cycles_count as f64) / (elapsed_ms * 1000.0);
        debug!("BATCH[{batch_id}] SIMULATOR finished execution with {cycles_count} cycles in {elapsed_ms:.3} ms @ {mhz:.3} MHz");
        (final_state, memory)
    }

    fn process_trace(&mut self, machine_state: &MachineState) {
        let elapsed = self.instant.take().unwrap().elapsed();
        self.total_elapsed += elapsed;
        if self.is_aborted {
            return;
        }
        let batch_id = self.batch_id;
        if self.abort.load(std::sync::atomic::Ordering::Relaxed) {
            self.tracing_data_producers.take().unwrap().finalize();
            trace!("BATCH[{batch_id}] SIMULATOR stopping snapshot production due to abort signal");
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
        let initial_state = replace(&mut self.state, machine_state);
        let timestamp_diff = machine_state.timestamp - initial_state.timestamp;
        assert!(timestamp_diff.is_multiple_of(TIMESTAMP_STEP));
        let cycles_count = (timestamp_diff / TIMESTAMP_STEP) as usize;
        let elapsed_ms = elapsed.as_secs_f64() * 1000.0;
        let mhz = (cycles_count as f64) / (elapsed_ms * 1000.0);
        trace!("BATCH[{batch_id}] SIMULATOR produced SNAPSHOT[{snapshot_index}] with {cycles_count} cycles in {elapsed_ms:.3} ms @ {mhz:.3} MHz");
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
        trace_piece: &mut TraceChunk,
        machine_state: &MachineState,
    ) -> *mut TraceChunk {
        assert!((trace_piece.len as usize) >= TRACE_CHUNK_LEN);
        assert!((trace_piece.len as usize) <= MAX_TRACE_CHUNK_LEN);
        let argument_ptr = trace_piece as *mut TraceChunk;
        let current_ptr = self.trace.as_mut().unwrap().deref_mut() as *mut TraceChunk;
        assert_eq!(argument_ptr, current_ptr);
        self.process_trace(machine_state);
        let mut trace: Box<TraceChunk> = unsafe { Box::new_uninit().assume_init() };
        trace.len = 0;
        let ptr = trace.deref_mut() as *mut TraceChunk;
        self.trace = Some(trace);
        ptr
    }

    fn receive_final_trace_piece(
        &mut self,
        trace_piece: &mut TraceChunk,
        machine_state: &MachineState,
    ) {
        debug_assert!(
            (machine_state as *const MachineState).is_aligned_to(align_of::<MachineState>())
        );
        debug_assert!((trace_piece as *const TraceChunk).is_aligned_to(align_of::<TraceChunk>()));
        assert!((trace_piece.len as usize) <= MAX_TRACE_CHUNK_LEN);
        let argument_ptr = trace_piece as *mut TraceChunk;
        let current_ptr = self.trace.as_mut().unwrap().deref_mut() as *mut TraceChunk;
        assert_eq!(argument_ptr, current_ptr);
        self.process_trace(machine_state);
        self.tracing_data_producers.take().unwrap().finalize();
        self.final_state = Some(*machine_state);
    }

    fn take_final_state(&mut self) -> Option<MachineState> {
        self.final_state.take()
    }

    fn final_state_ref(&'_ self) -> Option<&'_ MachineState> {
        self.final_state.as_ref()
    }
}
