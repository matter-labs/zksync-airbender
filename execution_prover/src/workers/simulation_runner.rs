use crate::messages::{InitsAndTeardownsData, WorkerResult};
use crate::tracing::{DataTraceRanges, TracingDataProducers, TracingType};
use common_constants::{INITIAL_TIMESTAMP, TIMESTAMP_STEP};
use crossbeam_channel::{Receiver, Sender};
use execution_prover_model::allocator::HostTraceAllocator;
use execution_prover_model::circuit_type::{CircuitType, UnrolledCircuitType};
use execution_prover_model::MachineType;
use itertools::Itertools;
use log::{debug, trace};
use riscv_transpiler::common_constants::ROM_WORD_SIZE;
use riscv_transpiler::ir::simple_instruction_set::{preprocess_bytecode, Instruction};
use riscv_transpiler::ir::{
    FullMachineDecoderConfig, FullUnsignedMachineDecoderConfig, ReducedMachineDecoderConfig,
};
use riscv_transpiler::jit::{
    Context, ContextImpl, JitRunnerRam, JittedCode, MachineState, MemoryHolder, TraceChunk,
    MAX_NUM_COUNTERS,
};
use riscv_transpiler::vm::NonDeterminismCSRSource;
use std::mem::replace;
use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;
use std::sync::atomic::AtomicBool;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use type_map::concurrent::TypeMap;

pub(crate) struct Snapshot<R: DataTraceRanges, S> {
    pub index: usize,
    pub cycles_count: usize,
    pub initial_state: MachineState,
    pub trace: S,
    pub final_state: MachineState,
    pub trace_ranges: R,
}

// SAFETY: a `Snapshot` moves from the simulation worker to a replay worker via
// a channel. `S` owns its trace chunk allocation, so the trace pointers stay
// valid on the receiver thread. The `R: DataTraceRanges` payload may carry
// `PtrRange<T, A>` ranges; their Send guarantee is documented on those types.
unsafe impl<R: DataTraceRanges, S: Send> Send for Snapshot<R, S> {}

/// Streams the leading empty unified i&t markers during the run so tracing
/// data can pair and dispatch instead of pinning host allocators until
/// simulation ends. Sound without a guard: the i&t instances are the trailing
/// `it_final <= max_it_instances` — an architectural bound no cycle or
/// delegation burst can violate — so anything `max_it_instances` circuits
/// behind the run front is provably empty.
pub(crate) struct EmptyInitsAndTeardownsStreamer {
    pub cycles_per_circuit: usize,
    pub max_it_instances: usize,
    pub next_sequence_id: usize,
}

impl EmptyInitsAndTeardownsStreamer {
    fn release<A: HostTraceAllocator>(
        &mut self,
        cycles_so_far: usize,
        results: &Sender<WorkerResult<A>>,
    ) {
        let completed_circuits = cycles_so_far / self.cycles_per_circuit;
        let frontier = completed_circuits.saturating_sub(self.max_it_instances);
        while self.next_sequence_id < frontier {
            let data = InitsAndTeardownsData {
                circuit_type: CircuitType::Unrolled(UnrolledCircuitType::Unified),
                sequence_id: self.next_sequence_id,
                inits_and_teardowns: None,
            };
            results
                .send(WorkerResult::InitsAndTeardownsData(data))
                .expect(
                    "simulation runner results channel closed while streaming empty init/teardown markers",
                );
            self.next_sequence_id += 1;
        }
    }
}

pub(crate) struct SimulationRunner<
    ND: NonDeterminismCSRSource + Send + 'static,
    T: TracingType<A> + 'static,
    A: HostTraceAllocator + 'static,
    S: DerefMut<Target = TraceChunk> + Send + 'static,
> {
    pub batch_id: u64,
    pub machine_type: MachineType,
    pub non_determinism_source: ND,
    pub free_trace_chunks_sender: Sender<S>,
    pub free_trace_chunks_receiver: Receiver<S>,
    pub snapshots: Option<Sender<Snapshot<T::Ranges, S>>>,
    pub results: Option<Sender<WorkerResult<A>>>,
    pub abort: Arc<AtomicBool>,
    pub state: MachineState,
    pub trace: Option<S>,
    pub snapshot_index: usize,
    pub tracing_data_producers: Option<T::Producers>,
    pub empty_it_streamer: Option<EmptyInitsAndTeardownsStreamer>,
    pub instant: Option<Instant>,
    pub total_elapsed: Duration,
    pub is_aborted: bool,
    pub ram_config: JitRunnerRam,
}

impl<
        ND: NonDeterminismCSRSource + Send + 'static,
        T: TracingType<A> + 'static,
        A: HostTraceAllocator + 'static,
        S: DerefMut<Target = TraceChunk> + Send + 'static,
    > SimulationRunner<ND, T, A, S>
{
    pub fn new(
        batch_id: u64,
        machine_type: MachineType,
        non_determinism_source: ND,
        free_trace_chunks_sender: Sender<S>,
        free_trace_chunks_receiver: Receiver<S>,
        snapshots: Sender<Snapshot<T::Ranges, S>>,
        results: Sender<WorkerResult<A>>,
        free_allocators: Receiver<A>,
        abort: Arc<AtomicBool>,
        empty_it_streamer: Option<EmptyInitsAndTeardownsStreamer>,
        ram_config: JitRunnerRam,
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
            empty_it_streamer,
            instant: None,
            total_elapsed: Default::default(),
            is_aborted: false,
            ram_config,
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
            let mut guard = jit_cache
                .lock()
                .expect("simulation runner JIT cache mutex poisoned");
            let entry = guard.get::<Arc<JittedCode<Self>>>();
            if let Some(entry) = entry {
                entry.clone()
            } else {
                trace!("BATCH[{batch_id}] SIMULATOR JIT compiling bytecode");
                // JittedCode::preprocess_bytecode takes pre-decoded
                // `&[Instruction]`. The JIT's delegation lowering recovers a
                // delegated call's length by scanning the run of identical
                // delegation instructions (jit/impls.rs, `Op::ZicsrDelegation`),
                // so it requires the UNPROTECTED tape layout
                // (`PROTECT_AGAINST_MID_DELEGATION_JUMPS=false`, which fills
                // every slot of the run). The protected layout keeps only the
                // run head and loses the 7-vs-10 blake round count, aborting
                // the JIT on any delegation-bearing binary.
                let instructions: Vec<Instruction> = match self.machine_type {
                    MachineType::Full => {
                        preprocess_bytecode::<FullMachineDecoderConfig, false>(&text_section)
                    }
                    MachineType::FullUnsigned => preprocess_bytecode::<
                        FullUnsignedMachineDecoderConfig,
                        false,
                    >(&text_section),
                    MachineType::Reduced => {
                        preprocess_bytecode::<ReducedMachineDecoderConfig, false>(&text_section)
                    }
                };
                // This prover stack is BabyBear end to end: the replay worker
                // replays with `crate::upstream::BF` and the GKR circuits' MOP
                // tables are BabyBear, so the JIT must simulate MOP (Zimop)
                // opcodes over the same field.
                let jitted_code = JittedCode::preprocess_bytecode(
                    &instructions,
                    cycles_bound,
                    riscv_transpiler::jit::MopField::BabyBear,
                    self.ram_config,
                );
                trace!("BATCH[{batch_id}] SIMULATOR JIT compiled bytecode");
                let jitted_code = Arc::new(jitted_code);
                guard.insert(jitted_code.clone());
                jitted_code
            }
        };
        let binary_image_len = binary_image.len();
        assert!(binary_image_len <= ROM_WORD_SIZE);
        // NOTE: on reuse the holder is already clean outside the ROM region: every RAM word
        // the JIT writes is timestamped, and `collect_inits_and_teardowns` zeroes both the
        // value and the timestamp of every timestamped word (the abort path resets the whole
        // buffer). The binary image is the exception: it is copied in without timestamps, so
        // ROM words the program never loads survive collection. Only the ROM tail beyond the
        // current image needs an explicit clear, in case the previous image was longer.
        memory_holder.memory_mut()[..binary_image_len].copy_from_slice(&binary_image);
        memory_holder.memory_mut()[binary_image_len..ROM_WORD_SIZE].fill(0);
        let mut trace = self
            .free_trace_chunks_receiver
            .recv()
            .expect("must receive a trace chunk for simulation");
        trace.len = 0;
        // SAFETY: `DerefMut::deref_mut` yields a live, non-null `TraceChunk`.
        let trace_ref = unsafe { NonNull::new_unchecked(trace.deref_mut() as *mut TraceChunk) };
        self.trace = Some(trace);
        self.instant = Some(Instant::now());
        let ram_config = self.ram_config;
        let mut context = Context::new(self, ram_config);
        jitted_code.run_over_prepared_memory(&mut context, memory_holder, trace_ref);
        let mut runner = context.into_implementation();
        if let Some(trace) = runner.trace.take() {
            runner
                .free_trace_chunks_sender
                .send(trace)
                .expect("simulation runner trace-return channel closed during teardown");
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
        let timestamp = machine_state.timestamp.next_multiple_of(TIMESTAMP_STEP);
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
        if let (Some(streamer), Some(results)) =
            (self.empty_it_streamer.as_mut(), self.results.as_ref())
        {
            let cycles_so_far = ((timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP) as usize;
            streamer.release(cycles_so_far, results);
        }
        let trace = self.trace.take().unwrap();
        let result = WorkerResult::SnapshotProduced;
        self.results
            .as_ref()
            .expect("simulation runner results sender must exist while producing snapshots")
            .send(result)
            .expect("simulation runner results channel closed during snapshot production");
        let counters_diff = machine_state
            .counters
            .values
            .iter()
            .zip_eq(initial_state.counters.values.iter())
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
                &initial_state.counters.values,
                &machine_state.counters.values,
            );
        let snapshot = Snapshot {
            index: snapshot_index,
            cycles_count,
            initial_state,
            trace,
            final_state,
            trace_ranges,
        };
        self.snapshots
            .as_ref()
            .expect("simulation runner snapshots sender must exist while producing snapshots")
            .send(snapshot)
            .expect("simulation runner snapshots channel closed during snapshot production");
    }
}

impl<
        ND: NonDeterminismCSRSource + Send + 'static,
        T: TracingType<A> + 'static,
        A: HostTraceAllocator + 'static,
        S: DerefMut<Target = TraceChunk> + Send + 'static,
    > ContextImpl for SimulationRunner<ND, T, A, S>
{
    #[inline(always)]
    fn read_nondeterminism(&mut self) -> u32 {
        self.non_determinism_source.read()
    }

    #[inline(always)]
    fn write_nondeterminism(&mut self, value: u32, memory: &[u32]) {
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
            let trace = self.free_trace_chunks_receiver.recv().expect(
                "simulation runner trace pool channel closed while requesting a trace chunk",
            );
            self.trace = Some(trace);
        }
        self.trace.as_mut().unwrap().len = 0;
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

#[cfg(test)]
mod cpu_streamer_tests {
    use super::*;
    use execution_prover_model::allocator::CpuTraceAllocator;

    #[test]
    fn cpu_streamer_releases_only_provably_empty_markers() {
        let (tx, rx) = crossbeam_channel::unbounded::<WorkerResult<CpuTraceAllocator>>();
        let mut streamer = EmptyInitsAndTeardownsStreamer {
            cycles_per_circuit: 1000,
            max_it_instances: 3,
            next_sequence_id: 0,
        };
        streamer.release(2999, &tx);
        assert_eq!(streamer.next_sequence_id, 0);
        streamer.release(4000, &tx);
        assert_eq!(streamer.next_sequence_id, 1);
        streamer.release(4000, &tx);
        assert_eq!(streamer.next_sequence_id, 1);
        streamer.release(10500, &tx);
        assert_eq!(streamer.next_sequence_id, 7);
        drop(tx);
        let ids: Vec<usize> = rx
            .iter()
            .map(|result| match result {
                WorkerResult::InitsAndTeardownsData(data) => {
                    assert_eq!(
                        data.circuit_type,
                        CircuitType::Unrolled(UnrolledCircuitType::Unified)
                    );
                    assert!(data.inits_and_teardowns.is_none());
                    data.sequence_id
                }
                _ => panic!("streamer sent an unexpected worker result"),
            })
            .collect();
        assert_eq!(ids, (0..7).collect::<Vec<_>>());
    }
}
