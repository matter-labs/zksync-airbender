use super::cpu_worker::{collect_inits_and_teardowns, get_inits_and_teardowns_chunks};
use super::messages::{InitsAndTeardownsData, SimulationResult, TracingData, WorkerResult};
use super::simulation_runner::{
    LockedBoxedMemoryHolder, LockedBoxedTraceChunk, SimulationRunner, Snapshot,
};
use super::tracing::{SplitTracingType, Tracer, TracingType, UnifiedTracingType};
use super::A;
use crate::circuit_type::{CircuitType, UnrolledCircuitType};
use crate::execution::prover::ExecutionKind;
use crate::machine_type::MachineType;
use crate::prover::tracing_data::{
    DelegationTracingDataHost, TracingDataHost, UnrolledTracingDataHost,
};
use crate::witness::trace_unrolled::ShuffleRamInitsAndTeardownsHost;
use crossbeam_channel::{unbounded, Receiver, Sender};
use cs::definitions::TimestampScalar;
use era_cudart::memory::{CudaHostAllocFlags, HostAllocation};
use itertools::Itertools;
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::ir::{
    preprocess_bytecode, FullMachineDecoderConfig, FullUnsignedMachineDecoderConfig,
    ReducedMachineDecoderConfig,
};
use riscv_transpiler::jit::{MemoryHolder, ReplayerMemChunks};
use riscv_transpiler::replayer::ReplayerVM;
use riscv_transpiler::vm::{InstructionTape, SimpleTape, State};
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Deref;
use std::sync::atomic::AtomicBool;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use type_map::concurrent::TypeMap;
use worker::Worker;

/// Selects how much of the CPU-side proving pipeline the model should execute.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CpuPipelineMode {
    /// Run JIT simulation, snapshot production, trace-range allocation, and init/teardown
    /// collection. Snapshots are recycled without replaying instructions.
    SimulationOnly,
    /// Run the full CPU producer side used by GPU proving: simulation, replay, trace-row
    /// materialization, and init/teardown collection. GPU work is replaced by a null sink.
    Full,
}

impl Default for CpuPipelineMode {
    fn default() -> Self {
        Self::Full
    }
}

/// Static configuration for the CPU-only model.
#[derive(Clone, Copy, Debug)]
pub struct CpuPipelineModelConfig {
    pub execution_kind: ExecutionKind,
    pub machine_type: MachineType,
    pub mode: CpuPipelineMode,
    pub max_thread_pool_threads: Option<usize>,
    pub replay_worker_threads_count: usize,
    pub cycles_bound: Option<u32>,
    pub host_allocator_backing_allocation_size: usize,
    pub host_allocators_count: usize,
    pub memory_holders_count: usize,
}

impl Default for CpuPipelineModelConfig {
    fn default() -> Self {
        Self {
            execution_kind: ExecutionKind::Unrolled,
            machine_type: MachineType::FullUnsigned,
            mode: CpuPipelineMode::Full,
            max_thread_pool_threads: None,
            replay_worker_threads_count: 8,
            cycles_bound: None,
            host_allocator_backing_allocation_size: 1 << 26,
            host_allocators_count: 128,
            memory_holders_count: 1,
        }
    }
}

/// Binary input that is stable across benchmark iterations.
pub struct CpuPipelineModelInput {
    pub binary_image: Vec<u32>,
    pub text_section: Vec<u32>,
}

/// Timings collected by the CPU-only model.
#[derive(Clone, Debug, Default)]
pub struct CpuPipelineTimings {
    pub total_wall: Duration,
    pub simulator_wall: Duration,
    pub init_teardown_scan: Duration,
    pub init_teardown_partition: Duration,
    /// Sum of per-worker replay execution time. This intentionally excludes channel wait time.
    pub replay_cpu: Duration,
    pub replayed_cycles: u64,
}

/// Observable work performed by a CPU-only pipeline run.
#[derive(Clone, Debug, Default)]
pub struct CpuPipelineModelReport {
    pub mode: CpuPipelineMode,
    pub cycles: u64,
    pub final_pc: u32,
    pub final_timestamp: TimestampScalar,
    pub snapshots_produced: usize,
    /// Snapshots that are no longer holding trace-range references. In `Full` mode these were
    /// replayed; in `SimulationOnly` mode they were recycled by the model.
    pub snapshots_finalized: usize,
    pub tracing_rows_by_circuit: BTreeMap<CircuitType, usize>,
    pub inits_and_teardowns: usize,
    pub host_payloads_produced: usize,
    pub replayed_cycles: u64,
    pub timings: CpuPipelineTimings,
}

/// Reusable CPU-only model for benchmarking the host work required by GPU proving.
pub struct CpuPipelineModel {
    config: CpuPipelineModelConfig,
    worker: Arc<Worker>,
    binary_image: Arc<Box<[u32]>>,
    text_section: Arc<Box<[u32]>>,
    instruction_tape: Arc<SimpleTape>,
    jit_cache: Arc<Mutex<TypeMap>>,
    memory_holders_cache: Arc<Mutex<Vec<LockedBoxedMemoryHolder>>>,
    trace_chunks_cache: Arc<Mutex<Vec<Vec<LockedBoxedTraceChunk>>>>,
    free_allocators_sender: Sender<A>,
    free_allocators_receiver: Receiver<A>,
}

impl CpuPipelineModel {
    pub fn new(config: CpuPipelineModelConfig, input: CpuPipelineModelInput) -> Self {
        validate_config(config);

        let worker = if let Some(num_threads) = config.max_thread_pool_threads {
            Worker::new_with_num_threads(num_threads)
        } else {
            Worker::new()
        };
        let worker = Arc::new(worker);

        let preprocess_bytecode_fn = match config.machine_type {
            MachineType::Full => preprocess_bytecode::<FullMachineDecoderConfig>,
            MachineType::FullUnsigned => preprocess_bytecode::<FullUnsignedMachineDecoderConfig>,
            MachineType::Reduced => preprocess_bytecode::<ReducedMachineDecoderConfig>,
        };
        let preprocessed_bytecode = preprocess_bytecode_fn(&input.text_section);
        let instruction_tape = Arc::new(SimpleTape::new(&preprocessed_bytecode));

        let mut memory_holders = Vec::with_capacity(config.memory_holders_count);
        for _ in 0..config.memory_holders_count {
            memory_holders.push(LockedBoxedMemoryHolder::new());
        }

        let trace_chunks_count = trace_chunks_count(&config);
        let mut trace_chunks_cache = Vec::with_capacity(config.memory_holders_count);
        for _ in 0..config.memory_holders_count {
            let mut chunks = Vec::with_capacity(trace_chunks_count);
            for _ in 0..trace_chunks_count {
                chunks.push(LockedBoxedTraceChunk::new());
            }
            trace_chunks_cache.push(chunks);
        }

        let (free_allocators_sender, free_allocators_receiver) = unbounded();
        let host_allocation_log_chunk_size = config
            .host_allocator_backing_allocation_size
            .trailing_zeros();
        for _ in 0..config.host_allocators_count {
            let allocation = HostAllocation::alloc(
                config.host_allocator_backing_allocation_size,
                CudaHostAllocFlags::DEFAULT,
            )
            .expect("host allocator allocation should succeed");
            let allocator = A::new([allocation], host_allocation_log_chunk_size);
            free_allocators_sender.send(allocator).unwrap();
        }

        Self {
            config,
            worker,
            binary_image: Arc::new(input.binary_image.into_boxed_slice()),
            text_section: Arc::new(input.text_section.into_boxed_slice()),
            instruction_tape,
            jit_cache: Arc::new(Mutex::new(TypeMap::new())),
            memory_holders_cache: Arc::new(Mutex::new(memory_holders)),
            trace_chunks_cache: Arc::new(Mutex::new(trace_chunks_cache)),
            free_allocators_sender,
            free_allocators_receiver,
        }
    }

    /// Run one benchmark iteration with the supplied nondeterminism tape.
    pub fn run(&self, nondeterminism: Vec<u32>) -> CpuPipelineModelReport {
        let timer = Instant::now();
        let mut report = match self.config.execution_kind {
            ExecutionKind::Unrolled => {
                self.run_for_tracing_type::<SplitTracingType>(nondeterminism)
            }
            ExecutionKind::Unified => {
                self.run_for_tracing_type::<UnifiedTracingType>(nondeterminism)
            }
        };
        report.timings.total_wall = timer.elapsed();
        report
    }

    fn run_for_tracing_type<T: TracingType + 'static>(
        &self,
        nondeterminism: Vec<u32>,
    ) -> CpuPipelineModelReport {
        let (work_results_sender, work_results_receiver) = unbounded();
        let (snapshot_sender, snapshot_receiver) = unbounded();
        let (free_trace_chunks_sender, free_trace_chunks_receiver) = unbounded();
        let abort = Arc::new(AtomicBool::new(false));
        let timings = Arc::new(Mutex::new(CpuPipelineTimings::default()));
        let batch_id = 0;

        {
            let machine_type = self.config.machine_type;
            let cycles_bound = self.config.cycles_bound;
            let trace_chunks_count = trace_chunks_count(&self.config);
            let memory_holders_cache = self.memory_holders_cache.clone();
            let trace_chunks_cache = self.trace_chunks_cache.clone();
            let free_trace_chunks_sender = free_trace_chunks_sender.clone();
            let free_allocators_receiver = self.free_allocators_receiver.clone();
            let binary_image = self.binary_image.clone();
            let text_section = self.text_section.clone();
            let jit_cache = self.jit_cache.clone();
            let work_results_sender = work_results_sender.clone();
            let abort = abort.clone();
            let worker = self.worker.clone();
            let timings = timings.clone();
            let source = QuasiUARTSource::new_with_reads(nondeterminism);

            self.worker.pool.spawn(move || {
                // The benchmark reuses the same model across tight Criterion iterations.
                // Keep the result channel open until the simulator-owned caches are restored,
                // otherwise `run()` can return while the next iteration still sees empty caches.
                let cache_restoration_barrier = work_results_sender.clone();
                let mut memory_holder = {
                    let mut cache = memory_holders_cache.lock().unwrap();
                    cache
                        .pop()
                        .expect("CPU pipeline model should have a cached memory holder")
                };
                {
                    let mut cache = trace_chunks_cache.lock().unwrap();
                    let chunks = cache
                        .pop()
                        .expect("CPU pipeline model should have cached trace chunks");
                    assert_eq!(chunks.len(), trace_chunks_count);
                    for chunk in chunks {
                        free_trace_chunks_sender.send(chunk).unwrap();
                    }
                }
                let free_trace_chunks_receiver_clone = free_trace_chunks_receiver.clone();
                run_simulator_for_model::<T>(
                    batch_id,
                    machine_type,
                    binary_image,
                    text_section,
                    cycles_bound,
                    jit_cache,
                    &mut memory_holder,
                    source,
                    free_trace_chunks_sender,
                    free_trace_chunks_receiver,
                    snapshot_sender,
                    work_results_sender,
                    free_allocators_receiver,
                    abort,
                    &worker,
                    timings,
                );
                memory_holders_cache.lock().unwrap().push(memory_holder);
                let trace_chunks = free_trace_chunks_receiver_clone.iter().collect_vec();
                assert_eq!(trace_chunks.len(), trace_chunks_count);
                trace_chunks_cache.lock().unwrap().push(trace_chunks);
                drop(cache_restoration_barrier);
            });
        }

        match self.config.mode {
            CpuPipelineMode::SimulationOnly => {
                let snapshot_receiver = snapshot_receiver.clone();
                let free_trace_chunks_sender = free_trace_chunks_sender.clone();
                let work_results_sender = work_results_sender.clone();
                self.worker.pool.spawn(move || {
                    recycle_snapshots::<T>(
                        snapshot_receiver,
                        free_trace_chunks_sender,
                        work_results_sender,
                    )
                });
            }
            CpuPipelineMode::Full => {
                for worker_id in 0..self.config.replay_worker_threads_count {
                    let instruction_tape = self.instruction_tape.clone();
                    let snapshot_receiver = snapshot_receiver.clone();
                    let free_trace_chunks_sender = free_trace_chunks_sender.clone();
                    let work_results_sender = work_results_sender.clone();
                    let abort = abort.clone();
                    let timings = timings.clone();
                    self.worker.pool.spawn(move || {
                        run_replayer_for_model::<T>(
                            batch_id,
                            worker_id,
                            instruction_tape,
                            snapshot_receiver,
                            free_trace_chunks_sender,
                            work_results_sender,
                            abort,
                            timings,
                        )
                    });
                }
            }
        }

        drop(snapshot_receiver);
        drop(free_trace_chunks_sender);
        drop(work_results_sender);

        let mut report = CpuPipelineModelReport {
            mode: self.config.mode,
            ..Default::default()
        };
        let mut processed_snapshots = BTreeSet::new();
        let mut pending_tracing_data = BTreeMap::new();
        let mut tracing_data_keys_by_snapshot =
            BTreeMap::<usize, BTreeSet<(CircuitType, usize)>>::new();

        for result in work_results_receiver {
            match result {
                WorkerResult::SnapshotProduced => {
                    report.snapshots_produced += 1;
                }
                WorkerResult::InitsAndTeardownsData(data) => {
                    report.host_payloads_produced += 1;
                    consume_inits_and_teardowns(data, &self.free_allocators_sender, &mut report);
                }
                WorkerResult::TracingData(data) => {
                    report.host_payloads_produced += 1;
                    record_tracing_data_metrics(&data, &mut report);
                    hold_or_release_tracing_data(
                        data,
                        &processed_snapshots,
                        &mut pending_tracing_data,
                        &mut tracing_data_keys_by_snapshot,
                        &self.free_allocators_sender,
                    );
                }
                WorkerResult::SimulationResult(result) => {
                    consume_simulation_result(result, &mut report);
                }
                WorkerResult::SnapshotReplayed(index) => {
                    report.snapshots_finalized += 1;
                    processed_snapshots.insert(index);
                    release_ready_tracing_data(
                        index,
                        &processed_snapshots,
                        &mut pending_tracing_data,
                        &mut tracing_data_keys_by_snapshot,
                        &self.free_allocators_sender,
                    );
                }
                WorkerResult::GpuWorkResult(_) => {
                    panic!("CPU pipeline model should not receive GPU work results")
                }
            }
        }

        assert!(
            pending_tracing_data.is_empty(),
            "all tracing data should be releasable once snapshots are finalized"
        );

        report.timings = timings.lock().unwrap().clone();
        report.replayed_cycles = report.timings.replayed_cycles;
        report
    }
}

fn validate_config(config: CpuPipelineModelConfig) {
    assert!(
        config
            .host_allocator_backing_allocation_size
            .is_power_of_two(),
        "host allocator backing allocation size must be a power of two"
    );
    assert!(
        config.host_allocators_count > 0,
        "CPU pipeline model needs at least one host allocator"
    );
    assert!(
        config.memory_holders_count > 0,
        "CPU pipeline model needs at least one memory holder"
    );
    if config.mode == CpuPipelineMode::Full {
        assert!(
            config.replay_worker_threads_count > 0,
            "full CPU pipeline mode needs at least one replay worker"
        );
    }
    if config.execution_kind == ExecutionKind::Unified {
        assert_eq!(
            config.machine_type,
            MachineType::Reduced,
            "unified execution is only supported for the reduced machine"
        );
    }
}

fn trace_chunks_count(config: &CpuPipelineModelConfig) -> usize {
    (config.replay_worker_threads_count * 2).max(2)
}

fn run_simulator_for_model<T: TracingType + 'static>(
    batch_id: u64,
    machine_type: MachineType,
    binary_image: impl Deref<Target = impl Deref<Target = [u32]>>,
    text_section: impl Deref<Target = impl Deref<Target = [u32]>>,
    cycles_bound: Option<u32>,
    jit_cache: Arc<Mutex<TypeMap>>,
    memory_holder: &mut LockedBoxedMemoryHolder,
    non_determinism_source: QuasiUARTSource,
    free_trace_chunks_sender: Sender<LockedBoxedTraceChunk>,
    free_trace_chunks_receiver: Receiver<LockedBoxedTraceChunk>,
    snapshots: Sender<Snapshot<T::Ranges>>,
    results: Sender<WorkerResult<A>>,
    free_allocators: Receiver<A>,
    abort: Arc<AtomicBool>,
    worker: &Worker,
    timings: Arc<Mutex<CpuPipelineTimings>>,
) {
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

    let instant = Instant::now();
    let runner = runner.run(
        binary_image,
        text_section,
        cycles_bound,
        jit_cache,
        memory_holder,
    );
    timings.lock().unwrap().simulator_wall += instant.elapsed();

    let SimulationRunner {
        batch_id: _,
        results,
        abort,
        state,
        is_aborted,
        ..
    } = runner;
    let should_abort = abort.load(std::sync::atomic::Ordering::Relaxed);
    if should_abort {
        MemoryHolder::reset(&mut memory_holder.holder);
        return;
    }

    assert!(!is_aborted);
    let results = results.unwrap();
    let instant = Instant::now();
    let inits_and_teardowns = collect_inits_and_teardowns(memory_holder, worker);
    timings.lock().unwrap().init_teardown_scan += instant.elapsed();

    let instant = Instant::now();
    let (circuit_type, per_circuit_count, sequence_id_offset) = if T::IS_SPLIT {
        let per_circuit_count = setups::inits_and_teardowns::NUM_INIT_AND_TEARDOWN_SETS
            * setups::inits_and_teardowns::NUM_CYCLES;
        (UnrolledCircuitType::InitsAndTeardowns, per_circuit_count, 0)
    } else {
        let per_circuit_count = setups::unified_reduced_machine::NUM_CYCLES;
        let timestamp_diff =
            state.timestamp - riscv_transpiler::common_constants::INITIAL_TIMESTAMP;
        assert!(timestamp_diff.is_multiple_of(riscv_transpiler::common_constants::TIMESTAMP_STEP));
        let total_cycles =
            (timestamp_diff / riscv_transpiler::common_constants::TIMESTAMP_STEP) as usize;
        let count = inits_and_teardowns.iter().map(|v| v.len()).sum::<usize>();
        let empty_cycles = total_cycles - count;
        let empty_circuits = empty_cycles / per_circuit_count;
        for sequence_id in 0..empty_circuits {
            let data = InitsAndTeardownsData {
                circuit_type: CircuitType::Unrolled(UnrolledCircuitType::Unified),
                sequence_id,
                inits_and_teardowns: None,
            };
            results
                .send(WorkerResult::InitsAndTeardownsData(data))
                .unwrap();
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
        let data = InitsAndTeardownsData {
            circuit_type,
            sequence_id: sequence_id + sequence_id_offset,
            inits_and_teardowns: Some(inits_and_teardowns_data),
        };
        results
            .send(WorkerResult::InitsAndTeardownsData(data))
            .unwrap();
    }
    timings.lock().unwrap().init_teardown_partition += instant.elapsed();

    let final_register_values = state
        .registers
        .into_iter()
        .zip(state.register_timestamps)
        .map(
            |(value, last_access_timestamp)| trace_and_split::FinalRegisterValue {
                value,
                last_access_timestamp,
            },
        )
        .collect_array()
        .unwrap();
    let simulation_result = SimulationResult {
        final_register_values,
        final_pc: state.pc,
        final_timestamp: state.timestamp,
    };
    results
        .send(WorkerResult::SimulationResult(simulation_result))
        .unwrap();
}

fn run_replayer_for_model<T: TracingType>(
    _batch_id: u64,
    _worker_id: usize,
    tape: impl Deref<Target = impl InstructionTape>,
    snapshots: Receiver<Snapshot<T::Ranges>>,
    free_trace_chunks: Sender<LockedBoxedTraceChunk>,
    results: Sender<WorkerResult<A>>,
    abort: Arc<AtomicBool>,
    timings: Arc<Mutex<CpuPipelineTimings>>,
) {
    let mut total_elapsed = Duration::default();
    let mut total_cycles = 0usize;
    let mut is_aborted = false;
    for snapshot in snapshots {
        if !is_aborted && abort.load(std::sync::atomic::Ordering::Relaxed) {
            is_aborted = true;
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
        drop(tracer);
        free_trace_chunks.send(trace).unwrap();
        assert_eq!(state.pc, final_state.pc);
        assert_eq!(state.timestamp, final_state.timestamp);
        assert_eq!(state.registers, final_state.registers);
        total_elapsed += elapsed;
        total_cycles += cycles_count;
        results.send(WorkerResult::SnapshotReplayed(index)).unwrap();
    }
    let mut timings = timings.lock().unwrap();
    timings.replay_cpu += total_elapsed;
    timings.replayed_cycles += total_cycles as u64;
}

fn recycle_snapshots<T: TracingType>(
    snapshots: Receiver<Snapshot<T::Ranges>>,
    free_trace_chunks: Sender<LockedBoxedTraceChunk>,
    results: Sender<WorkerResult<A>>,
) {
    for snapshot in snapshots {
        let Snapshot {
            index,
            trace,
            trace_ranges,
            ..
        } = snapshot;
        free_trace_chunks.send(trace).unwrap();
        drop(trace_ranges);
        results.send(WorkerResult::SnapshotReplayed(index)).unwrap();
    }
}

fn consume_inits_and_teardowns(
    data: InitsAndTeardownsData<A>,
    free_allocators: &Sender<A>,
    report: &mut CpuPipelineModelReport,
) {
    if let Some(inits_and_teardowns) = data.inits_and_teardowns {
        report.inits_and_teardowns += inits_and_teardowns.len();
        free_inits_and_teardowns(inits_and_teardowns, free_allocators);
    }
}

fn hold_or_release_tracing_data(
    data: TracingData<A>,
    processed_snapshots: &BTreeSet<usize>,
    pending_tracing_data: &mut BTreeMap<(CircuitType, usize), TracingData<A>>,
    tracing_data_keys_by_snapshot: &mut BTreeMap<usize, BTreeSet<(CircuitType, usize)>>,
    free_allocators: &Sender<A>,
) {
    if data
        .participating_snapshot_indexes
        .is_subset(processed_snapshots)
    {
        free_tracing_data(data.tracing_data, free_allocators);
        return;
    }

    let key = (data.circuit_type, data.sequence_id);
    for snapshot_index in data.participating_snapshot_indexes.iter().copied() {
        tracing_data_keys_by_snapshot
            .entry(snapshot_index)
            .or_default()
            .insert(key);
    }
    assert!(pending_tracing_data.insert(key, data).is_none());
}

fn release_ready_tracing_data(
    snapshot_index: usize,
    processed_snapshots: &BTreeSet<usize>,
    pending_tracing_data: &mut BTreeMap<(CircuitType, usize), TracingData<A>>,
    tracing_data_keys_by_snapshot: &mut BTreeMap<usize, BTreeSet<(CircuitType, usize)>>,
    free_allocators: &Sender<A>,
) {
    let Some(keys) = tracing_data_keys_by_snapshot.remove(&snapshot_index) else {
        return;
    };
    for key in keys {
        let Some(data) = pending_tracing_data.get(&key) else {
            continue;
        };
        if data
            .participating_snapshot_indexes
            .is_subset(processed_snapshots)
        {
            let data = pending_tracing_data.remove(&key).unwrap();
            free_tracing_data(data.tracing_data, free_allocators);
        }
    }
}

fn consume_simulation_result(result: SimulationResult, report: &mut CpuPipelineModelReport) {
    report.final_pc = result.final_pc;
    report.final_timestamp = result.final_timestamp;
    let timestamp_diff =
        result.final_timestamp - riscv_transpiler::common_constants::INITIAL_TIMESTAMP;
    assert!(timestamp_diff.is_multiple_of(riscv_transpiler::common_constants::TIMESTAMP_STEP));
    report.cycles = timestamp_diff / riscv_transpiler::common_constants::TIMESTAMP_STEP;
}

fn record_tracing_data_metrics(data: &TracingData<A>, report: &mut CpuPipelineModelReport) {
    let len = tracing_data_len(&data.tracing_data);
    *report
        .tracing_rows_by_circuit
        .entry(data.circuit_type)
        .or_default() += len;
}

fn tracing_data_len(data: &TracingDataHost<A>) -> usize {
    match data {
        TracingDataHost::Delegation(data) => match data {
            DelegationTracingDataHost::BigIntWithControl(data) => data.len(),
            DelegationTracingDataHost::Blake2WithCompression(data) => data.len(),
            DelegationTracingDataHost::KeccakSpecial5(data) => data.len(),
        },
        TracingDataHost::Unrolled(data) => match data {
            UnrolledTracingDataHost::Memory(data) => data.len(),
            UnrolledTracingDataHost::NonMemory(data) => data.len(),
            UnrolledTracingDataHost::Unified(data) => data.len(),
        },
    }
}

fn free_inits_and_teardowns(
    inits_and_teardowns: ShuffleRamInitsAndTeardownsHost<A>,
    free_allocators: &Sender<A>,
) {
    for allocator in inits_and_teardowns.into_allocators() {
        free_allocators.send(allocator).unwrap();
    }
}

fn free_tracing_data(tracing_data: TracingDataHost<A>, free_allocators: &Sender<A>) {
    for allocator in tracing_data.into_allocators() {
        free_allocators.send(allocator).unwrap();
    }
}
