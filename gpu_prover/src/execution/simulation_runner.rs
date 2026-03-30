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
#[cfg(not(target_arch = "x86_64"))]
use riscv_transpiler::ir::{
    preprocess_bytecode, FullMachineDecoderConfig, FullUnsignedMachineDecoderConfig,
    ReducedMachineDecoderConfig,
};
#[cfg(not(target_arch = "x86_64"))]
use riscv_transpiler::jit::TRACE_CHUNK_LEN;
#[cfg(target_arch = "x86_64")]
use riscv_transpiler::jit::{Context, JittedCode};
use riscv_transpiler::jit::{
    ContextImpl, MachineState, MemoryHolder, TraceChunk, MAX_NUM_COUNTERS, RAM_SIZE,
};
use riscv_transpiler::vm::{
    DelegationsAndFamiliesCounters, DelegationsAndUnifiedCounters, NonDeterminismCSRSource, State,
};
#[cfg(not(target_arch = "x86_64"))]
use riscv_transpiler::vm::{RamPeek, SimpleTape, Snapshotter, RAM, VM};
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

#[cfg_attr(target_arch = "x86_64", allow(dead_code))]
pub(crate) trait VmCounters {
    fn into_machine_counters(self) -> [u64; MAX_NUM_COUNTERS];
}

impl VmCounters for DelegationsAndFamiliesCounters {
    fn into_machine_counters(self) -> [u64; MAX_NUM_COUNTERS] {
        let mut counters = [0; MAX_NUM_COUNTERS];
        counters[0] = self.add_sub_family as u64;
        counters[1] = self.slt_branch_family as u64;
        counters[2] = self.binary_shift_csr_family as u64;
        counters[3] = self.mul_div_family as u64;
        counters[4] = self.word_size_mem_family as u64;
        counters[5] = self.subword_size_mem_family as u64;
        counters[6] = self.blake_calls as u64;
        counters[7] = self.bigint_calls as u64;
        counters[8] = self.keccak_calls as u64;
        counters
    }
}

impl VmCounters for DelegationsAndUnifiedCounters {
    fn into_machine_counters(self) -> [u64; MAX_NUM_COUNTERS] {
        let mut counters = [0; MAX_NUM_COUNTERS];
        counters[0] = self.cycles as u64;
        counters[6] = self.blake_calls as u64;
        counters[7] = self.bigint_calls as u64;
        counters[8] = self.keccak_calls as u64;
        counters
    }
}

#[cfg_attr(target_arch = "x86_64", allow(dead_code))]
fn machine_state_from_vm_state<C: VmCounters + riscv_transpiler::vm::Counters>(
    state: &State<C>,
) -> MachineState {
    let mut machine_state = MachineState::initial();
    machine_state.registers = std::array::from_fn(|i| state.registers[i].value);
    machine_state.register_timestamps = std::array::from_fn(|i| state.registers[i].timestamp);
    machine_state.counters = state.counters.into_machine_counters();
    machine_state.pc = state.pc;
    machine_state.timestamp = state.timestamp;
    machine_state
}

fn process_trace_chunk<T: TracingType>(
    batch_id: u64,
    snapshot_index: &mut usize,
    abort: &Arc<AtomicBool>,
    state: &mut MachineState,
    trace: &mut Option<LockedBoxedTraceChunk>,
    tracing_data_producers: &mut Option<T::Producers>,
    snapshots: &mut Option<Sender<Snapshot<T::Ranges>>>,
    results: &mut Option<Sender<WorkerResult<A>>>,
    total_elapsed: Duration,
    is_aborted: &mut bool,
    machine_state: &MachineState,
    elapsed: Duration,
) {
    if *is_aborted {
        return;
    }
    let current_snapshot_index = *snapshot_index;
    *snapshot_index += 1;
    let mut machine_state = *machine_state;
    let timestamp = machine_state.timestamp.next_multiple_of(TIMESTAMP_STEP);
    machine_state.timestamp = timestamp;
    let final_state = machine_state;
    let initial_state = replace(state, machine_state);
    let timestamp_diff = timestamp - initial_state.timestamp;
    assert!(timestamp_diff.is_multiple_of(TIMESTAMP_STEP));
    let cycles_count = (timestamp_diff / TIMESTAMP_STEP) as usize;
    let elapsed_ms = elapsed.as_secs_f64() * 1000.0;
    let mhz = (cycles_count as f64) / (elapsed_ms * 1000.0);
    trace!("BATCH[{batch_id}] SIMULATOR produced SNAPSHOT[{current_snapshot_index}] with {cycles_count} cycles in {elapsed_ms:.3} ms @ {mhz:.3} MHz");
    if abort.load(std::sync::atomic::Ordering::Relaxed) {
        tracing_data_producers.take().unwrap().finalize();
        assert!(snapshots.take().is_some());
        assert!(results.take().is_some());
        let timestamp_diff = timestamp - INITIAL_TIMESTAMP;
        assert!(timestamp_diff.is_multiple_of(TIMESTAMP_STEP));
        let cycles_count = (timestamp_diff / TIMESTAMP_STEP) as usize;
        let elapsed_ms = total_elapsed.as_secs_f64() * 1000.0;
        let mhz = (cycles_count as f64) / (elapsed_ms * 1000.0);
        debug!("BATCH[{batch_id}] SIMULATOR stopping snapshot production due to abort signal after {cycles_count} cycles in {elapsed_ms:.3} ms @ {mhz:.3} MHz");
        *is_aborted = true;
        return;
    }
    let trace = trace.take().unwrap();
    let result = WorkerResult::SnapshotProduced;
    results.as_ref().unwrap().send(result).unwrap();
    let counters_diff = machine_state
        .counters
        .iter()
        .zip_eq(initial_state.counters.iter())
        .map(|(a, b)| a - b)
        .collect_array::<MAX_NUM_COUNTERS>()
        .unwrap();
    let expected_cycles = counters_diff.iter().take(6).sum::<u64>() as usize;
    assert_eq!(expected_cycles, cycles_count);
    let trace_ranges = tracing_data_producers.as_mut().unwrap().process_snapshot(
        current_snapshot_index,
        &initial_state.counters,
        &machine_state.counters,
    );
    let snapshot = Snapshot {
        index: current_snapshot_index,
        cycles_count,
        initial_state,
        trace,
        final_state,
        trace_ranges,
    };
    snapshots.as_ref().unwrap().send(snapshot).unwrap();
}

#[cfg(not(target_arch = "x86_64"))]
struct PreparedMemory<'a> {
    holder: &'a mut MemoryHolder,
}

#[cfg(not(target_arch = "x86_64"))]
impl<'a> PreparedMemory<'a> {
    fn new(holder: &'a mut MemoryHolder) -> Self {
        Self { holder }
    }
}

#[cfg(not(target_arch = "x86_64"))]
impl RamPeek for PreparedMemory<'_> {
    #[inline(always)]
    fn peek_word(&self, address: u32) -> u32 {
        debug_assert_eq!(address % 4, 0);
        let word_idx = (address / 4) as usize;
        debug_assert!(word_idx < self.holder.memory.len());
        unsafe { *self.holder.memory.get_unchecked(word_idx) }
    }
}

#[cfg(not(target_arch = "x86_64"))]
impl RAM for PreparedMemory<'_> {
    #[inline(always)]
    fn mask_read_for_witness(&self, address: &mut u32, value: &mut u32) {
        debug_assert_eq!(*address % 4, 0);
        if (*address as usize) < riscv_transpiler::common_constants::rom::ROM_BYTE_SIZE {
            *value = 0;
        }
    }

    #[inline(always)]
    fn read_word(
        &mut self,
        address: u32,
        timestamp: riscv_transpiler::common_constants::TimestampScalar,
    ) -> (riscv_transpiler::common_constants::TimestampScalar, u32) {
        debug_assert_eq!(address % 4, 0);
        let word_idx = (address / 4) as usize;
        debug_assert!(word_idx < self.holder.memory.len());
        unsafe {
            let value = *self.holder.memory.get_unchecked(word_idx);
            let read_timestamp = *self.holder.timestamps.get_unchecked(word_idx);
            *self.holder.timestamps.get_unchecked_mut(word_idx) = timestamp | 1;
            debug_assert!(read_timestamp < (timestamp | 1));
            (read_timestamp, value)
        }
    }

    #[inline(always)]
    fn write_word(
        &mut self,
        address: u32,
        word: u32,
        timestamp: riscv_transpiler::common_constants::TimestampScalar,
    ) -> (riscv_transpiler::common_constants::TimestampScalar, u32) {
        debug_assert_eq!(address % 4, 0);
        let word_idx = (address / 4) as usize;
        debug_assert!(word_idx < self.holder.memory.len());
        assert!(
            address as usize >= riscv_transpiler::common_constants::rom::ROM_BYTE_SIZE,
            "attempt to write into ROM range"
        );
        unsafe {
            let old_value = *self.holder.memory.get_unchecked(word_idx);
            let read_timestamp = *self.holder.timestamps.get_unchecked(word_idx);
            debug_assert!(read_timestamp < (timestamp | 2));
            *self.holder.memory.get_unchecked_mut(word_idx) = word;
            *self.holder.timestamps.get_unchecked_mut(word_idx) = timestamp | 2;
            (read_timestamp, old_value)
        }
    }

    #[inline(always)]
    fn skip_if_replaying(&mut self, _num_snapshots: usize) {
        panic!("must not be used in replay mode");
    }
}

#[cfg(not(target_arch = "x86_64"))]
struct VmTraceRunner<'a, T: TracingType> {
    batch_id: u64,
    free_trace_chunks_receiver: &'a Receiver<LockedBoxedTraceChunk>,
    snapshots: &'a mut Option<Sender<Snapshot<T::Ranges>>>,
    results: &'a mut Option<Sender<WorkerResult<A>>>,
    abort: &'a Arc<AtomicBool>,
    state: &'a mut MachineState,
    trace: &'a mut Option<LockedBoxedTraceChunk>,
    snapshot_index: &'a mut usize,
    tracing_data_producers: &'a mut Option<T::Producers>,
    instant: &'a mut Option<Instant>,
    total_elapsed: &'a mut Duration,
    is_aborted: &'a mut bool,
}

#[cfg(not(target_arch = "x86_64"))]
impl<T: TracingType> VmTraceRunner<'_, T> {
    fn current_trace(&mut self) -> &mut TraceChunk {
        &mut self.trace.as_mut().unwrap().chunk
    }

    fn finish_snapshot<C: VmCounters + riscv_transpiler::vm::Counters>(
        &mut self,
        state: &State<C>,
        is_final: bool,
    ) {
        let elapsed = self.instant.take().unwrap().elapsed();
        *self.total_elapsed += elapsed;
        let machine_state = machine_state_from_vm_state(state);
        process_trace_chunk::<T>(
            self.batch_id,
            self.snapshot_index,
            self.abort,
            self.state,
            self.trace,
            self.tracing_data_producers,
            self.snapshots,
            self.results,
            *self.total_elapsed,
            self.is_aborted,
            &machine_state,
            elapsed,
        );
        if *self.is_aborted {
            return;
        }
        if is_final {
            self.tracing_data_producers.take().unwrap().finalize();
        } else {
            let trace = self.free_trace_chunks_receiver.recv().unwrap();
            *self.trace = Some(trace);
            self.current_trace().len = 0;
            *self.instant = Some(Instant::now());
        }
    }
}

#[cfg(not(target_arch = "x86_64"))]
impl<T, C> Snapshotter<C> for VmTraceRunner<'_, T>
where
    T: TracingType,
    C: VmCounters + riscv_transpiler::vm::Counters,
{
    #[inline(always)]
    fn take_snapshot_if_needed(&mut self, state: &State<C>) -> bool {
        if self.current_trace().len as usize >= TRACE_CHUNK_LEN {
            self.finish_snapshot(state, false);
        }
        *self.is_aborted
    }

    #[inline(always)]
    fn take_final_snapshot(&mut self, state: &State<C>) {
        self.finish_snapshot(state, true);
    }

    #[inline(always)]
    fn append_arbitrary_value(&mut self, value: u32) {
        self.current_trace().append_arbitrary_value(value);
    }

    #[inline(always)]
    fn append_memory_read(
        &mut self,
        _address: u32,
        read_value: u32,
        read_timestamp: riscv_transpiler::common_constants::TimestampScalar,
        _write_timestamp: riscv_transpiler::common_constants::TimestampScalar,
    ) {
        self.current_trace().add_element(read_value, read_timestamp);
    }
}

pub(crate) struct SimulationRunner<
    ND: NonDeterminismCSRSource + Send + 'static,
    T: TracingType + 'static,
> {
    pub batch_id: u64,
    #[cfg_attr(target_arch = "x86_64", allow(dead_code))]
    pub machine_type: MachineType,
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
            machine_type,
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
        self,
        binary_image: impl Deref<Target = impl Deref<Target = [u32]>>,
        text_section: impl Deref<Target = impl Deref<Target = [u32]>>,
        cycles_bound: Option<u32>,
        jit_cache: Arc<Mutex<TypeMap>>,
        memory_holder: &mut MemoryHolder,
    ) -> Self
    where
        T::Counters: Default + VmCounters,
    {
        self.run_with_selected_backend(
            binary_image,
            text_section,
            cycles_bound,
            jit_cache,
            memory_holder,
        )
    }

    #[cfg(target_arch = "x86_64")]
    fn run_with_selected_backend(
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

    #[cfg(not(target_arch = "x86_64"))]
    fn run_with_selected_backend(
        mut self,
        binary_image: impl Deref<Target = impl Deref<Target = [u32]>>,
        text_section: impl Deref<Target = impl Deref<Target = [u32]>>,
        cycles_bound: Option<u32>,
        _jit_cache: Arc<Mutex<TypeMap>>,
        memory_holder: &mut MemoryHolder,
    ) -> Self
    where
        T::Counters: Default + VmCounters,
    {
        let batch_id = self.batch_id;
        let machine_type = self.machine_type;
        trace!("BATCH[{batch_id}] SIMULATOR using interpreter fallback on non-x86_64 target");
        let binary_image_len = binary_image.len();
        memory_holder.memory[..binary_image_len].copy_from_slice(&binary_image);
        memory_holder.memory[binary_image_len..ROM_WORD_SIZE].fill(0);
        let mut trace = self
            .free_trace_chunks_receiver
            .recv()
            .expect("must receive a trace chunk for simulation");
        trace.chunk.len = 0;
        self.trace = Some(trace);
        self.instant = Some(Instant::now());

        let instructions = match machine_type {
            MachineType::Full => preprocess_bytecode::<FullMachineDecoderConfig>(&text_section),
            MachineType::FullUnsigned => {
                preprocess_bytecode::<FullUnsignedMachineDecoderConfig>(&text_section)
            }
            MachineType::Reduced => {
                preprocess_bytecode::<ReducedMachineDecoderConfig>(&text_section)
            }
        };
        let tape = SimpleTape::new(&instructions);
        let mut prepared_memory = PreparedMemory::new(memory_holder);
        let mut state = State::initial_with_counters(T::Counters::default());
        let timestamp_bound =
            cycles_bound.map(|bound| INITIAL_TIMESTAMP + (bound as u64) * TIMESTAMP_STEP);

        {
            let SimulationRunner {
                batch_id,
                machine_type: _,
                non_determinism_source,
                free_trace_chunks_sender: _,
                free_trace_chunks_receiver,
                snapshots,
                results,
                abort,
                state: runner_state,
                trace,
                snapshot_index,
                tracing_data_producers,
                instant,
                total_elapsed,
                is_aborted,
            } = &mut self;
            let mut trace_runner = VmTraceRunner::<T> {
                batch_id: *batch_id,
                free_trace_chunks_receiver,
                snapshots,
                results,
                abort,
                state: runner_state,
                trace,
                snapshot_index,
                tracing_data_producers,
                instant,
                total_elapsed,
                is_aborted,
            };

            loop {
                if timestamp_bound.is_some_and(|bound| state.timestamp >= bound) {
                    trace_runner.take_final_snapshot(&state);
                    break;
                }

                let pc = state.pc;
                VM::<T::Counters>::run_step(
                    &mut state,
                    &mut prepared_memory,
                    &mut trace_runner,
                    &tape,
                    non_determinism_source,
                );
                state.timestamp += TIMESTAMP_STEP;

                if state.pc == pc {
                    trace_runner.take_final_snapshot(&state);
                    break;
                }

                if trace_runner.take_snapshot_if_needed(&state) {
                    break;
                }
            }
        }

        if let Some(trace) = self.trace.take() {
            self.free_trace_chunks_sender.send(trace).unwrap();
        }
        if !self.is_aborted {
            let final_timestamp = self.state.timestamp;
            let timestamp_diff = final_timestamp - INITIAL_TIMESTAMP;
            assert!(timestamp_diff.is_multiple_of(TIMESTAMP_STEP));
            let cycles_count = (timestamp_diff / TIMESTAMP_STEP) as usize;
            let elapsed_ms = self.total_elapsed.as_secs_f64() * 1000.0;
            let mhz = (cycles_count as f64) / (elapsed_ms * 1000.0);
            debug!("BATCH[{batch_id}] SIMULATOR finished execution with {cycles_count} cycles in {elapsed_ms:.3} ms @ {mhz:.3} MHz");
        }
        self
    }

    fn process_trace(&mut self, machine_state: &MachineState, elapsed: Duration) {
        process_trace_chunk::<T>(
            self.batch_id,
            &mut self.snapshot_index,
            &self.abort,
            &mut self.state,
            &mut self.trace,
            &mut self.tracing_data_producers,
            &mut self.snapshots,
            &mut self.results,
            self.total_elapsed,
            &mut self.is_aborted,
            machine_state,
            elapsed,
        );
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
