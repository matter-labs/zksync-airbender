use crate::execution::messages::WorkerResult;
use crate::execution::tracing::{DataTraceRanges, TracingDataProducers, TracingType};
use crate::execution::A;
use crate::machine_type::MachineType;
use crossbeam_channel::{Receiver, Sender};
use cs::definitions::{INITIAL_TIMESTAMP, TIMESTAMP_STEP};
use era_cudart::memory::{CudaHostAllocFlags, CudaHostRegisterFlags, HostAllocation};
use era_cudart::result::CudaResultWrap;
use era_cudart_sys::{cudaHostRegister, cudaHostUnregister};
use itertools::Itertools;
use log::{debug, trace};
use riscv_transpiler::common_constants::ROM_WORD_SIZE;
use riscv_transpiler::jit::{
    Context, ContextImpl, JittedCode, MachineState, MemoryHolder, TraceChunk, MAX_NUM_COUNTERS,
    RAM_SIZE,
};
use riscv_transpiler::vm::NonDeterminismCSRSource;
use std::mem::replace;
use std::ops::{Deref, DerefMut};
use std::os::raw::c_void;
use std::ptr::NonNull;
use std::sync::atomic::AtomicBool;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use type_map::concurrent::TypeMap;

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

pub(crate) struct Snapshot<R: DataTraceRanges> {
    pub index: usize,
    pub cycles_count: usize,
    pub initial_state: MachineState,
    pub trace: LockedBoxedTraceChunk,
    pub final_state: MachineState,
    pub trace_ranges: R,
}

unsafe impl<R: DataTraceRanges> Send for Snapshot<R> {}

pub(crate) struct SimulationRunner<
    ND: NonDeterminismCSRSource + Send + 'static,
    T: TracingType + 'static,
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
    pub tracing_data_producers: Option<T::Producers>,
    pub instant: Option<Instant>,
    pub total_elapsed: Duration,
    pub is_aborted: bool,
}

impl<ND: NonDeterminismCSRSource + Send + 'static, T: TracingType + 'static>
    SimulationRunner<ND, T>
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
        let tracing_data_producers =
            T::Producers::new(machine_type, free_allocators, results.clone());
        let tracing_data_producers = Some(tracing_data_producers);
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
        let binary_image_len = binary_image.len();
        memory_holder.memory[..binary_image_len].copy_from_slice(&binary_image);
        memory_holder.memory[binary_image_len..ROM_WORD_SIZE].fill(0);
        let mut trace = self
            .free_trace_chunks_receiver
            .recv()
            .expect("must receive a trace chunk for simulation");
        trace.chunk.len = 0;
        let trace_ref = unsafe { NonNull::new_unchecked(trace.chunk.as_mut()) };
        self.trace = Some(trace);
        self.instant = Some(Instant::now());
        let mut context = Context {
            implementation: self,
        };
        jitted_code.run_over_prepared_memory(&mut context, memory_holder, trace_ref);
        let Context {
            implementation: mut runner,
        } = context;
        if let Some(trace) = runner.trace.take() {
            runner.free_trace_chunks_sender.send(trace).unwrap();
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

    fn process_trace(&mut self, machine_state: &MachineState, elapsed: Duration) {
        if self.is_aborted {
            return;
        }
        let batch_id = self.batch_id;
        let snapshot_index = self.snapshot_index;
        self.snapshot_index += 1;
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
        trace!("BATCH[{batch_id}] SIMULATOR produced SNAPSHOT[{snapshot_index}] with {cycles_count} cycles in {elapsed_ms:.3} ms @ {mhz:.3} MHz");
        if self.abort.load(std::sync::atomic::Ordering::Relaxed) {
            self.tracing_data_producers.take().unwrap().finalize();
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
        let trace = self.trace.take().unwrap();
        let result = WorkerResult::SnapshotProduced;
        self.results.as_ref().unwrap().send(result).unwrap();
        let counters_diff = machine_state
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
        self.snapshots.as_ref().unwrap().send(snapshot).unwrap();
    }
}

impl<ND: NonDeterminismCSRSource + Send + 'static, T: TracingType> ContextImpl
    for SimulationRunner<ND, T>
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
            let trace = self.free_trace_chunks_receiver.recv().unwrap();
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
    }

    fn take_final_state(&mut self) -> Option<MachineState> {
        unreachable!()
    }

    fn final_state_ref(&'_ self) -> Option<&'_ MachineState> {
        unreachable!()
    }
}
