use crate::allocator::host::ConcurrentStaticHostAllocator;
use crate::circuit_type::{
    CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
    UnrolledNonMemoryCircuitType,
};
use crate::execution::messages::WorkerResult::SimulationResult;
use crate::execution::messages::{InitsAndTeardownsData, TracingData, WorkerResult};
use crate::execution::ram::RamWithRomRegion;
use crate::execution::snapshotter::{
    DelegationsAndFamiliesDataTraceRanges, OnceSnapshotter, PtrRange, SplitSnapshot,
};
use crate::execution::tracer::SplitTracer;
use crate::machine_type::MachineType;
use crate::prover::tracing_data::{
    DelegationTracingDataHostSource, TracingDataHost, UnrolledTracingDataHost,
};
use crate::witness::trace::ChunkedTraceHolder;
use crate::witness::trace_unrolled::ShuffleRamInitsAndTeardownsHost;
use crossbeam_channel::{Receiver, Sender};
use cs::definitions::{INITIAL_TIMESTAMP, TIMESTAMP_STEP};
use era_cudart::slice::CudaSlice;
use itertools::Itertools;
use log::{debug, trace};
use prover::common_constants;
use prover::definitions::LazyInitAndTeardown;
use prover::risc_v_simulator::machine_mode_only_unrolled::{
    MemoryOpcodeTracingDataWithTimestamp, NonMemoryOpcodeTracingDataWithTimestamp,
    UnifiedOpcodeTracingDataWithTimestamp,
};
use riscv_transpiler::replayer::{ReplayerNonDeterminism, ReplayerRam, ReplayerVM};
use riscv_transpiler::vm::{
    DelegationsAndFamiliesCounters, InstructionTape, NonDeterminismCSRSource, State, VM,
};
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;
use std::cmp::min;
use std::collections::{HashSet, VecDeque};
use std::mem::replace;
use std::ops::Deref;
use std::sync::Arc;
use std::time::Instant;
use trace_and_split::FinalRegisterValue;

const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize = common_constants::rom::ROM_SECOND_WORD_BITS;

const ROM_LOG_SIZE: u32 = 16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS as u32;
const RAM_LOG_SIZE: u32 = 30;

type A = ConcurrentStaticHostAllocator;
type Ram = RamWithRomRegion<RAM_LOG_SIZE, ROM_LOG_SIZE, true>;

pub trait NonDeterminism: NonDeterminismCSRSource<Ram> + Clone {}

impl<T> NonDeterminism for T where T: NonDeterminismCSRSource<Ram> + Clone {}

const SNAPSHOT_PERIOD: usize = 1 << 20;

pub(crate) fn run_split_simulator(
    batch_id: u64,
    machine_type: MachineType,
    binary_image: impl Deref<Target = impl Deref<Target = [u32]>>,
    tape: impl Deref<Target = impl InstructionTape>,
    mut non_determinism: impl NonDeterminism,
    cycles_limit: usize,
    snapshots: Sender<SplitSnapshot>,
    results: Sender<WorkerResult<A>>,
    free_allocators: Receiver<A>,
) {
    debug!("BATCH[{batch_id}] SIMULATOR started");
    let mut ram = Ram::new(&binary_image);
    let mut state = State::initial_with_counters(DelegationsAndFamiliesCounters::default());
    let mut snapshot_index = 0usize;
    let mut tracing_data_producers =
        SplitTracingDataProducers::new(machine_type, free_allocators.clone(), results.clone());
    let instant = Instant::now();
    loop {
        let initial_state = state.clone();
        let mut snapshotter = OnceSnapshotter::new_for_period(SNAPSHOT_PERIOD);
        let instant = Instant::now();
        let is_program_finished = VM::run_basic_unrolled(
            &mut state,
            1,
            &mut ram,
            &mut snapshotter,
            tape.deref(),
            SNAPSHOT_PERIOD,
            &mut non_determinism,
        );
        let elapsed = instant.elapsed();
        let final_state = state.clone();
        let timestamp_diff = final_state.timestamp - initial_state.timestamp;
        assert!(timestamp_diff.is_multiple_of(TIMESTAMP_STEP));
        let cycles_count = (timestamp_diff / TIMESTAMP_STEP) as usize;
        let elapsed_ms = elapsed.as_secs_f64() * 1000.0;
        let mhz = (cycles_count as f64) / (elapsed_ms * 1000.0);
        trace!("BATCH[{batch_id}] SIMULATOR produced SNAPSHOT[{snapshot_index}] with {cycles_count} cycles in {elapsed_ms:.3} ms @ {mhz:.3} MHz");
        let trace_ranges = tracing_data_producers.process_snapshot(
            snapshot_index,
            &initial_state.counters,
            &final_state.counters,
        );
        let OnceSnapshotter {
            non_determinism_reads,
            memory_reads,
            ..
        } = snapshotter;
        let snapshot = SplitSnapshot {
            index: snapshot_index,
            cycles_count,
            initial_state,
            non_determinism_reads,
            memory_reads,
            trace_ranges,
        };
        snapshots.send(snapshot).unwrap();
        snapshot_index += 1;
        if is_program_finished {
            break;
        }
        if cycles_count >= cycles_limit {
            panic!("BATCH[{batch_id}] SIMULATOR end of execution was not reached after {cycles_limit} cycles");
        }
    }
    drop(snapshots);
    tracing_data_producers.finalize();
    let elapsed = instant.elapsed();
    let timestamp_diff = state.timestamp - INITIAL_TIMESTAMP;
    assert!(timestamp_diff.is_multiple_of(TIMESTAMP_STEP));
    let cycles_count = (timestamp_diff / TIMESTAMP_STEP) as usize;
    let elapsed_ms = elapsed.as_secs_f64() * 1000.0;
    let mhz = (cycles_count as f64) / (elapsed_ms * 1000.0);
    trace!("BATCH[{batch_id}] SIMULATOR finished execution with {cycles_count} cycles in {elapsed_ms:.3} ms @ {mhz:.3} MHz");
    const PER_CIRCUIT_COUNT: usize = setups::inits_and_teardowns::NUM_INIT_AND_TEARDOWN_SETS
        * setups::inits_and_teardowns::NUM_CYCLES;
    let mut instant = Instant::now();
    for (sequence_id, inits_and_teardowns_data) in
        get_inits_and_teardowns(&ram, PER_CIRCUIT_COUNT, free_allocators).enumerate()
    {
        let circuit_type = CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns);
        let count = inits_and_teardowns_data
            .chunks
            .iter()
            .map(|c| c.len())
            .sum::<usize>();
        let elapsed = instant.elapsed();
        let elapsed_ms = elapsed.as_secs_f64() * 1000.0;
        trace!("BATCH[{batch_id}] SIMULATOR produced INITS_AND_TEARDOWNS[{sequence_id}] with {count} entries in {elapsed_ms:.3} ms");
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
        .map(|register| FinalRegisterValue {
            value: register.value,
            last_access_timestamp: register.timestamp,
        })
        .collect_array()
        .unwrap();
    let simulation_result = SimulationResult {
        cycles_count,
        final_register_values,
    };
    results.send(simulation_result).unwrap();
    debug!("BATCH[{batch_id}] SIMULATOR finished");
}

pub(crate) fn run_split_replayer(
    batch_id: u64,
    worker_id: usize,
    tape: impl Deref<Target = impl InstructionTape>,
    snapshots: Receiver<SplitSnapshot>,
    results: Sender<WorkerResult<A>>,
) {
    debug!("BATCH[{batch_id}] REPLAYER[{worker_id}] started");
    for snapshot in snapshots {
        let SplitSnapshot {
            index,
            cycles_count,
            initial_state,
            non_determinism_reads,
            memory_reads,
            trace_ranges,
        } = snapshot;
        let mut state = initial_state;
        let mut ram_log = vec![memory_reads.as_slice()];
        let mut ram = ReplayerRam::<ROM_ADDRESS_SPACE_SECOND_WORD_BITS> {
            ram_log: &mut ram_log,
        };
        let mut non_determinism_reads = vec![non_determinism_reads.as_slice()];
        let mut nd = ReplayerNonDeterminism {
            non_determinism_reads_log: &mut non_determinism_reads,
        };
        let mut tracer = SplitTracer::new(trace_ranges);
        let instant = Instant::now();
        ReplayerVM::replay_basic_unrolled(
            &mut state,
            1,
            &mut ram,
            tape.deref(),
            SNAPSHOT_PERIOD,
            &mut nd,
            &mut tracer,
        );
        let elapsed = instant.elapsed();
        let elapsed_ms = elapsed.as_secs_f64() * 1000.0;
        let mhz = (cycles_count as f64) / (elapsed_ms * 1000.0);
        trace!("BATCH[{batch_id}] REPLAYER[{worker_id}] processed SNAPSHOT[{index}] with {cycles_count} cycles in {elapsed_ms:.3} ms @ {mhz:.3} MHz");
        let result = WorkerResult::SnapshotReplayed(index);
        results.send(result).unwrap()
    }
    debug!("BATCH[{batch_id}] REPLAYER[{worker_id}] finished");
}

trait TracingDataProducerType: Sized {
    fn produce_tracing_data(holder: ChunkedTraceHolder<Self, A>) -> TracingDataHost<A>;
}

impl<T: DelegationTracingDataHostSource> TracingDataProducerType for T {
    fn produce_tracing_data(holder: ChunkedTraceHolder<Self, A>) -> TracingDataHost<A> {
        TracingDataHost::Delegation(T::get(holder))
    }
}

impl TracingDataProducerType for MemoryOpcodeTracingDataWithTimestamp {
    fn produce_tracing_data(holder: ChunkedTraceHolder<Self, A>) -> TracingDataHost<A> {
        TracingDataHost::Unrolled(UnrolledTracingDataHost::Memory(holder))
    }
}

impl TracingDataProducerType for NonMemoryOpcodeTracingDataWithTimestamp {
    fn produce_tracing_data(holder: ChunkedTraceHolder<Self, A>) -> TracingDataHost<A> {
        TracingDataHost::Unrolled(UnrolledTracingDataHost::NonMemory(holder))
    }
}

impl TracingDataProducerType for UnifiedOpcodeTracingDataWithTimestamp {
    fn produce_tracing_data(holder: ChunkedTraceHolder<Self, A>) -> TracingDataHost<A> {
        TracingDataHost::Unrolled(UnrolledTracingDataHost::Unified(holder))
    }
}

struct TracingDataProducer<T: TracingDataProducerType> {
    circuit_type: CircuitType,
    free_allocators: Receiver<A>,
    results: Sender<WorkerResult<A>>,
    current_circuit_index: usize,
    chunks: VecDeque<Arc<Vec<T, A>>>,
    participating_snapshot_indexes: HashSet<usize>,
}

impl<T: TracingDataProducerType> TracingDataProducer<T> {
    pub fn new(
        circuit_type: CircuitType,
        free_allocators: Receiver<A>,
        results: Sender<WorkerResult<A>>,
    ) -> Self {
        Self {
            circuit_type,
            free_allocators,
            results,
            current_circuit_index: 0,
            chunks: VecDeque::new(),
            participating_snapshot_indexes: HashSet::new(),
        }
    }

    pub fn process_snapshot(
        &mut self,
        snapshot_index: usize,
        mut start: usize,
        end: usize,
        trace_ranges: &mut VecDeque<PtrRange<T>>,
    ) {
        while start != end {
            let cycles_per_circuit = self.circuit_type.get_num_cycles();
            let next_circuit_boundary = (start + 1).next_multiple_of(cycles_per_circuit);
            let next_circuit_index = next_circuit_boundary / cycles_per_circuit;
            assert_eq!(next_circuit_index, self.current_circuit_index + 1);
            if self.chunks.back().map_or(true, |v| v.len() == v.capacity()) {
                let allocator = self.free_allocators.recv().unwrap();
                let capacity = allocator.capacity() / size_of::<T>();
                let chunk = Arc::new(Vec::with_capacity_in(capacity, allocator));
                self.chunks.push_back(chunk)
            };
            let chunk = self.chunks.back_mut().unwrap();
            let chunk_mut = unsafe { Arc::get_mut_unchecked(chunk) };
            let spare_capacity = chunk_mut.spare_capacity_mut();
            let end = min(end, next_circuit_boundary);
            let diff = min(spare_capacity.len(), end - start);
            assert_ne!(diff, 0);
            let ptr_range = unsafe {
                let start_ptr = spare_capacity.as_mut_ptr() as *mut T;
                let end_ptr = start_ptr.add(diff);
                chunk_mut.set_len(chunk_mut.len() + diff);
                PtrRange {
                    start: start_ptr,
                    end: end_ptr,
                    chunk: Some(chunk.clone()),
                }
            };
            trace_ranges.push_back(ptr_range);
            self.participating_snapshot_indexes.insert(snapshot_index);
            start += diff;
            if start.is_multiple_of(cycles_per_circuit) {
                assert_eq!(start / cycles_per_circuit, next_circuit_index);
                self.produce_and_send_result();
                self.current_circuit_index = next_circuit_index;
            }
        }
    }

    fn produce_and_send_result(&mut self) {
        let chunks = self.chunks.drain(..).collect_vec();
        let holder = ChunkedTraceHolder { chunks };
        let tracing_data = T::produce_tracing_data(holder);
        let participating_snapshot_indexes =
            replace(&mut self.participating_snapshot_indexes, HashSet::new());
        let data = TracingData {
            circuit_type: self.circuit_type,
            sequence_id: self.current_circuit_index,
            tracing_data,
            participating_snapshot_indexes,
        };
        let result = WorkerResult::TracingData(data);
        self.results.send(result).unwrap();
    }

    pub fn finalize(mut self) {
        if !self.chunks.is_empty() {
            self.produce_and_send_result()
        }
    }
}

struct SplitTracingDataProducers {
    blake_producer: TracingDataProducer<Blake2sRoundFunctionDelegationWitness>,
    bigint_producer: TracingDataProducer<BigintDelegationWitness>,
    keccak_producer: TracingDataProducer<KeccakSpecial5DelegationWitness>,
    add_sub_family_producer: TracingDataProducer<NonMemoryOpcodeTracingDataWithTimestamp>,
    binary_shift_csr_family_producer: TracingDataProducer<NonMemoryOpcodeTracingDataWithTimestamp>,
    slt_branch_family_producer: TracingDataProducer<NonMemoryOpcodeTracingDataWithTimestamp>,
    mul_div_family_producer: TracingDataProducer<NonMemoryOpcodeTracingDataWithTimestamp>,
    word_size_mem_family_producer: TracingDataProducer<MemoryOpcodeTracingDataWithTimestamp>,
    subword_size_mem_family_producer: TracingDataProducer<MemoryOpcodeTracingDataWithTimestamp>,
}

impl SplitTracingDataProducers {
    fn new(
        machine_type: MachineType,
        free_allocators: Receiver<A>,
        results: Sender<WorkerResult<A>>,
    ) -> Self {
        let blake_producer = TracingDataProducer::<Blake2sRoundFunctionDelegationWitness>::new(
            CircuitType::Delegation(DelegationCircuitType::Blake2WithCompression),
            free_allocators.clone(),
            results.clone(),
        );
        let bigint_producer = TracingDataProducer::<BigintDelegationWitness>::new(
            CircuitType::Delegation(DelegationCircuitType::BigIntWithControl),
            free_allocators.clone(),
            results.clone(),
        );
        let keccak_producer = TracingDataProducer::<KeccakSpecial5DelegationWitness>::new(
            CircuitType::Delegation(DelegationCircuitType::KeccakSpecial5),
            free_allocators.clone(),
            results.clone(),
        );
        let add_sub_family_producer =
            TracingDataProducer::<NonMemoryOpcodeTracingDataWithTimestamp>::new(
                CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
                    UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
                )),
                free_allocators.clone(),
                results.clone(),
            );
        let binary_shift_csr_family_producer =
            TracingDataProducer::<NonMemoryOpcodeTracingDataWithTimestamp>::new(
                CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
                    UnrolledNonMemoryCircuitType::ShiftBinaryCsr,
                )),
                free_allocators.clone(),
                results.clone(),
            );
        let slt_branch_family_producer =
            TracingDataProducer::<NonMemoryOpcodeTracingDataWithTimestamp>::new(
                CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
                    UnrolledNonMemoryCircuitType::JumpBranchSlt,
                )),
                free_allocators.clone(),
                results.clone(),
            );
        let mul_div_family_producer =
            TracingDataProducer::<NonMemoryOpcodeTracingDataWithTimestamp>::new(
                CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
                    if machine_type == MachineType::Full {
                        UnrolledNonMemoryCircuitType::MulDiv
                    } else {
                        UnrolledNonMemoryCircuitType::MulDivUnsigned
                    },
                )),
                free_allocators.clone(),
                results.clone(),
            );
        let word_size_mem_family_producer =
            TracingDataProducer::<MemoryOpcodeTracingDataWithTimestamp>::new(
                CircuitType::Unrolled(UnrolledCircuitType::Memory(
                    UnrolledMemoryCircuitType::LoadStoreWordOnly,
                )),
                free_allocators.clone(),
                results.clone(),
            );
        let subword_size_mem_family_producer =
            TracingDataProducer::<MemoryOpcodeTracingDataWithTimestamp>::new(
                CircuitType::Unrolled(UnrolledCircuitType::Memory(
                    UnrolledMemoryCircuitType::LoadStoreSubwordOnly,
                )),
                free_allocators,
                results,
            );
        Self {
            blake_producer,
            bigint_producer,
            keccak_producer,
            add_sub_family_producer,
            binary_shift_csr_family_producer,
            slt_branch_family_producer,
            mul_div_family_producer,
            word_size_mem_family_producer,
            subword_size_mem_family_producer,
        }
    }

    pub fn process_snapshot(
        &mut self,
        snapshot_index: usize,
        initial_counters: &DelegationsAndFamiliesCounters,
        final_counters: &DelegationsAndFamiliesCounters,
    ) -> DelegationsAndFamiliesDataTraceRanges {
        let mut trace_ranges = DelegationsAndFamiliesDataTraceRanges::default();
        self.blake_producer.process_snapshot(
            snapshot_index,
            initial_counters.blake_calls,
            final_counters.blake_calls,
            &mut trace_ranges.blake_calls,
        );
        self.bigint_producer.process_snapshot(
            snapshot_index,
            initial_counters.bigint_calls,
            final_counters.bigint_calls,
            &mut trace_ranges.bigint_calls,
        );
        self.keccak_producer.process_snapshot(
            snapshot_index,
            initial_counters.keccak_calls,
            final_counters.keccak_calls,
            &mut trace_ranges.keccak_calls,
        );
        self.add_sub_family_producer.process_snapshot(
            snapshot_index,
            initial_counters.add_sub_family,
            final_counters.add_sub_family,
            &mut trace_ranges.add_sub_family,
        );
        self.binary_shift_csr_family_producer.process_snapshot(
            snapshot_index,
            initial_counters.binary_shift_csr_family,
            final_counters.binary_shift_csr_family,
            &mut trace_ranges.binary_shift_csr_family,
        );
        self.slt_branch_family_producer.process_snapshot(
            snapshot_index,
            initial_counters.slt_branch_family,
            final_counters.slt_branch_family,
            &mut trace_ranges.slt_branch_family,
        );
        self.mul_div_family_producer.process_snapshot(
            snapshot_index,
            initial_counters.mul_div_family,
            final_counters.mul_div_family,
            &mut trace_ranges.mul_div_family,
        );
        self.word_size_mem_family_producer.process_snapshot(
            snapshot_index,
            initial_counters.word_size_mem_family,
            final_counters.word_size_mem_family,
            &mut trace_ranges.word_size_mem_family,
        );
        self.subword_size_mem_family_producer.process_snapshot(
            snapshot_index,
            initial_counters.subword_size_mem_family,
            final_counters.subword_size_mem_family,
            &mut trace_ranges.subword_size_mem_family,
        );
        trace_ranges
    }

    pub fn finalize(self) {
        self.blake_producer.finalize();
        self.bigint_producer.finalize();
        self.keccak_producer.finalize();
        self.add_sub_family_producer.finalize();
        self.binary_shift_csr_family_producer.finalize();
        self.slt_branch_family_producer.finalize();
        self.mul_div_family_producer.finalize();
        self.word_size_mem_family_producer.finalize();
        self.subword_size_mem_family_producer.finalize();
    }
}

fn get_inits_and_teardowns(
    ram: &Ram,
    partition_size: usize,
    free_allocators: Receiver<A>,
) -> impl Iterator<Item = ShuffleRamInitsAndTeardownsHost<A>> + '_ {
    let inits_and_teardowns_count = ram.get_touched_words_count() as usize;
    let mut iterator = ram.get_inits_and_teardowns_iterator();
    let partitions_count = inits_and_teardowns_count.div_ceil(partition_size);
    (0..partitions_count).into_iter().map(move |index| {
        let mut values_count = if index == 0 {
            inits_and_teardowns_count - (partitions_count - 1) * partition_size
        } else {
            partition_size
        };
        let mut chunks = vec![];
        while values_count != 0 {
            let allocator = free_allocators.recv().unwrap();
            let capacity = allocator.capacity() / size_of::<LazyInitAndTeardown>();
            let count = min(capacity, values_count);
            let mut chunk = Vec::with_capacity_in(count, allocator);
            unsafe {
                chunk.set_len(count);
                for i in 0..count {
                    *chunk.get_unchecked_mut(i) = iterator.next().unwrap_unchecked();
                }
            };
            chunks.push(Arc::new(chunk));
            values_count -= count;
        }
        ShuffleRamInitsAndTeardownsHost { chunks }
    })
}

#[cfg(test)]
mod tests {
    use crate::allocator::host::ConcurrentStaticHostAllocator;
    use crate::execution::cpu_worker::{run_split_replayer, run_split_simulator};
    use crate::machine_type::MachineType;
    use crate::tests::{init_logger, read_binary};
    use crossbeam_channel::unbounded;
    use era_cudart::memory::{CudaHostAllocFlags, HostAllocation};
    use itertools::Itertools;
    use log::info;
    use prover::risc_v_simulator::abstractions::non_determinism::QuasiUARTSource;
    use rayon::iter::IntoParallelIterator;
    use rayon::iter::ParallelIterator;
    use riscv_transpiler::ir::{decode, FullMachineDecoderConfig};
    use riscv_transpiler::vm::SimpleTape;
    use std::path::Path;
    use std::sync::Arc;
    use worker::Worker;

    #[test]
    fn test_simulator() {
        init_logger();
        let worker = Worker::new();
        let (free_allocators_sender, free_allocators_receiver) = unbounded();
        let free_allocators_sender_ref = &free_allocators_sender;
        let instant = std::time::Instant::now();
        info!("Starting allocator preparation");
        (0..256).into_par_iter().for_each(|_| {
            let allocation = HostAllocation::alloc(1 << 25, CudaHostAllocFlags::DEFAULT).unwrap();
            let allocator = ConcurrentStaticHostAllocator::new([allocation], 24);
            free_allocators_sender_ref.send(allocator).unwrap();
        });
        let elapsed = instant.elapsed();
        info!(
            "Allocator preparation finished in {:.3} seconds",
            elapsed.as_secs_f64()
        );
        let binary_image = read_binary(&Path::new("../examples/hashed_fibonacci/app.bin"));
        let binary_image = Arc::new(binary_image);
        let text_section = read_binary(&Path::new("../examples/hashed_fibonacci/app.text"));
        // let nd = vec![1 << 22, 0];
        let nd = vec![0, 1 << 16];
        let non_determinism_source = QuasiUARTSource::new_with_reads(nd.clone());
        let preprocessed_bytecode = text_section
            .iter()
            .copied()
            .map(decode::<FullMachineDecoderConfig>)
            .collect_vec();
        let tape = Arc::new(SimpleTape::new(&preprocessed_bytecode));
        let (snapshots_sender, snapshots_receiver) = unbounded();
        let (results_sender, results_receiver) = unbounded();
        for worker_id in 0..4 {
            let tape = tape.clone();
            let snapshots_receiver = snapshots_receiver.clone();
            let results_sender = results_sender.clone();
            worker.pool.spawn(move || {
                run_split_replayer(0, worker_id, tape, snapshots_receiver, results_sender)
            });
        }
        drop(snapshots_receiver);
        run_split_simulator(
            0,
            MachineType::Full,
            binary_image.clone(),
            tape.clone(),
            non_determinism_source,
            1 << 30,
            snapshots_sender,
            results_sender,
            free_allocators_receiver.clone(),
        );
        results_receiver.iter().for_each(|_| {});
        drop(results_receiver);
        let non_determinism_source = QuasiUARTSource::new_with_reads(nd.clone());
        let preprocessed_bytecode = text_section
            .iter()
            .copied()
            .map(decode::<FullMachineDecoderConfig>)
            .collect_vec();
        let (snapshots_sender, snapshots_receiver) = unbounded();
        let (results_sender, results_receiver) = unbounded();
        for worker_id in 0..4 {
            let tape = SimpleTape::new(&preprocessed_bytecode);
            let snapshots_receiver = snapshots_receiver.clone();
            let results_sender = results_sender.clone();
            worker.pool.spawn(move || {
                run_split_replayer(0, worker_id, &tape, snapshots_receiver, results_sender);
            });
        }
        drop(snapshots_receiver);
        run_split_simulator(
            0,
            MachineType::Full,
            binary_image,
            tape,
            non_determinism_source,
            1 << 30,
            snapshots_sender,
            results_sender,
            free_allocators_receiver.clone(),
        );
        results_receiver.iter().for_each(|_| {});
        drop(results_receiver);
    }
}

// #[derive(Clone)]
// pub enum CpuWorkerMode<A: GoodAllocator> {
//     TraceTouchedRam {
//         circuit_type: MainCircuitType,
//         skip_set: HashSet<(CircuitType, usize)>,
//         free_allocator: Receiver<A>,
//     },
//     TraceCycles {
//         circuit_type: MainCircuitType,
//         skip_set: HashSet<(CircuitType, usize)>,
//         split_count: usize,
//         split_index: usize,
//         free_allocator: Receiver<A>,
//     },
//     TraceDelegations {
//         circuit_type: MainCircuitType,
//         skip_set: HashSet<(CircuitType, usize)>,
//         free_allocator: Receiver<A>,
//     },
// }
//
// pub fn get_cpu_worker_func<C: MachineConfig, A: GoodAllocator + 'static>(
//     wait_group: WaitGroup,
//     batch_id: u64,
//     worker_id: usize,
//     num_main_chunks_upper_bound: usize,
//     binary: impl Deref<Target = impl Deref<Target = [u32]>> + Send + 'static,
//     non_determinism: impl Deref<Target = impl NonDeterminism> + Send + 'static,
//     mode: CpuWorkerMode<A>,
//     results: Sender<WorkerResult<A>>,
// ) -> impl FnOnce() + Send + 'static {
//     move || {
//         match mode {
//             CpuWorkerMode::TraceTouchedRam {
//                 circuit_type,
//                 skip_set,
//                 free_allocator,
//             } => trace_touched_ram::<C, A>(
//                 batch_id,
//                 worker_id,
//                 num_main_chunks_upper_bound,
//                 circuit_type,
//                 binary,
//                 non_determinism,
//                 skip_set,
//                 free_allocator,
//                 results,
//             ),
//             CpuWorkerMode::TraceCycles {
//                 circuit_type,
//                 skip_set,
//                 split_count,
//                 split_index,
//                 free_allocator,
//             } => trace_cycles::<C, A>(
//                 batch_id,
//                 worker_id,
//                 num_main_chunks_upper_bound,
//                 circuit_type,
//                 binary,
//                 non_determinism,
//                 skip_set,
//                 split_count,
//                 split_index,
//                 free_allocator,
//                 results,
//             ),
//             CpuWorkerMode::TraceDelegations {
//                 circuit_type,
//                 skip_set,
//                 free_allocator,
//             } => trace_delegations::<C, A>(
//                 batch_id,
//                 worker_id,
//                 num_main_chunks_upper_bound,
//                 circuit_type,
//                 binary,
//                 non_determinism,
//                 skip_set,
//                 free_allocator,
//                 results,
//             ),
//         };
//         drop(wait_group);
//     }
// }
//
// fn trace_touched_ram<C: MachineConfig, A: GoodAllocator>(
//     batch_id: u64,
//     worker_id: usize,
//     num_main_chunks_upper_bound: usize,
//     circuit_type: MainCircuitType,
//     binary: impl Deref<Target = impl Deref<Target = [u32]>>,
//     non_determinism: impl Deref<Target = impl NonDeterminism>,
//     skip_set: HashSet<(CircuitType, usize)>,
//     free_allocator: Receiver<A>,
//     results: Sender<WorkerResult<A>>,
// ) {
//     trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] worker for tracing touched RAM started");
//     let domain_size = circuit_type.get_domain_size();
//     assert!(domain_size.is_power_of_two());
//     let log_domain_size = domain_size.trailing_zeros();
//     let mut non_determinism = non_determinism.clone();
//     let mut memory = BoxedMemoryImplWithRom::<RAM_SIZE, LOG_ROM_SIZE>::new();
//     for (idx, instruction) in binary.iter().enumerate() {
//         memory.populate(ENTRY_POINT + idx as u32 * 4, *instruction);
//     }
//     let cycles_per_chunk = domain_size - 1;
//     let mut state = RiscV32StateForUnrolledProver::<C>::initial(ENTRY_POINT);
//     let mut custom_csr_processor = DelegationsCSRProcessor;
//     let mut ram_tracing_data = RamTracingData::<RAM_SIZE, true>::new();
//     let cycle_tracing_data = CycleTracingData::with_cycles_capacity(0);
//     let delegation_tracing_data = DelegationTracingData::default();
//     let delegation_swap_fn = |_, _| unreachable!();
//     let initial_timestamp = timestamp_from_chunk_cycle_and_sequence(0, cycles_per_chunk, 0);
//     let mut tracer =
//         ExecutionTracer::<RAM_SIZE, LOG_ROM_SIZE, _, Global, Global, true, false, false>::new(
//             &mut ram_tracing_data,
//             cycle_tracing_data,
//             delegation_tracing_data,
//             delegation_swap_fn,
//             initial_timestamp,
//         );
//     let mut end_reached = false;
//     let mut chunks_traced_count = 0;
//     let mut next_chunk_index_with_no_inits_and_teardowns = 0;
//     trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] starting simulation");
//     let now = Instant::now();
//     for _chunk_index in 0..num_main_chunks_upper_bound {
//         let chunk_now = Instant::now();
//         let finished = state.run_cycles(
//             &mut memory,
//             &mut tracer,
//             &mut non_determinism,
//             &mut custom_csr_processor,
//             cycles_per_chunk,
//         );
//         let elapsed_ms = chunk_now.elapsed().as_secs_f64() * 1000.0;
//         let mhz = (cycles_per_chunk as f64) / (elapsed_ms * 1000.0);
//         trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] chunk {chunks_traced_count} finished in {elapsed_ms:.3} ms @ {mhz:.3} MHz");
//         chunks_traced_count += 1;
//         let touched_ram_cells_count =
//             tracer.ram_tracing_data.get_touched_ram_cells_count() as usize;
//         let chunks_needed_for_inits_and_teardowns =
//             touched_ram_cells_count.div_ceil(cycles_per_chunk);
//         let chunks_diff = chunks_traced_count - next_chunk_index_with_no_inits_and_teardowns;
//         if chunks_needed_for_inits_and_teardowns < chunks_diff {
//             trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] chunk {next_chunk_index_with_no_inits_and_teardowns} does not need setup and teardown");
//             if skip_set.contains(&(
//                 CircuitType::Main(circuit_type),
//                 next_chunk_index_with_no_inits_and_teardowns,
//             )) {
//                 trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] chunk {next_chunk_index_with_no_inits_and_teardowns} skipped");
//             } else {
//                 let chunk = InitsAndTeardownsChunk {
//                     index: next_chunk_index_with_no_inits_and_teardowns,
//                     chunk: None,
//                 };
//                 let result = WorkerResult::InitsAndTeardownsChunk(chunk);
//                 results.send(result).unwrap();
//             }
//             next_chunk_index_with_no_inits_and_teardowns += 1;
//         }
//         if finished {
//             let elapsed_ms = now.elapsed().as_secs_f64() * 1000.0;
//             let cycles_count = chunks_traced_count * cycles_per_chunk;
//             let speed = (cycles_count as f64) / (elapsed_ms * 1000.0);
//             let touched_ram_cells_count = ram_tracing_data.get_touched_ram_cells_count();
//             trace!(
//                     "BATCH[{batch_id}] CPU_WORKER[{worker_id}] simulation ended at address 0x{:08x} and took {chunks_traced_count} chunks to finish execution",
//                     state.observable.pc,
//                 );
//             debug!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] simulator tracing touched RAM ran {chunks_traced_count}x(2^{log_domain_size}-1) cycles in {elapsed_ms:.3} ms @ {speed:.3} MHz");
//             trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] simulator touched {touched_ram_cells_count} RAM cells");
//             end_reached = true;
//             break;
//         }
//         let new_timestamp =
//             timestamp_from_chunk_cycle_and_sequence(0, cycles_per_chunk, chunks_traced_count);
//         tracer.current_timestamp = new_timestamp;
//     }
//     assert!(
//         end_reached,
//         "BATCH[{batch_id}] CPU_WORKER[{worker_id}] end of execution was not reached after {num_main_chunks_upper_bound} chunks"
//     );
//     let RamTracingData {
//         register_last_live_timestamps,
//         ram_words_last_live_timestamps,
//         num_touched_ram_cells_in_pages,
//         ..
//     } = ram_tracing_data;
//     let memory_final_state = memory.get_final_ram_state();
//     let mut chunker = create_inits_and_teardowns_chunker(
//         &num_touched_ram_cells_in_pages,
//         &memory_final_state,
//         &ram_words_last_live_timestamps,
//         cycles_per_chunk,
//     );
//     let inits_and_teardowns_chunks_count = chunker.get_chunks_count();
//     trace!(
//         "BATCH[{batch_id}] CPU_WORKER[{worker_id}] {inits_and_teardowns_chunks_count} setup and teardown chunk(s) are needed"
//     );
//     assert_eq!(
//         chunks_traced_count,
//         inits_and_teardowns_chunks_count + next_chunk_index_with_no_inits_and_teardowns
//     );
//     let now = Instant::now();
//     for index in next_chunk_index_with_no_inits_and_teardowns..chunks_traced_count {
//         if skip_set.contains(&(CircuitType::Main(circuit_type), index)) {
//             chunker.skip_next_chunk();
//             trace!(
//                 "BATCH[{batch_id}] CPU_WORKER[{worker_id}] chunk {} skipped",
//                 index
//             );
//         } else {
//             let allocator = free_allocator.recv().unwrap();
//             let lazy_init_data = Vec::with_capacity_in(cycles_per_chunk, allocator);
//             let mut inits_and_teardowns = ShuffleRamSetupAndTeardown { lazy_init_data };
//             unsafe { inits_and_teardowns.lazy_init_data.set_len(cycles_per_chunk) };
//             chunker.populate_next_chunk(&mut inits_and_teardowns.lazy_init_data);
//             let chunk = Some(inits_and_teardowns);
//             let chunk = InitsAndTeardownsChunk { index, chunk };
//             let result = WorkerResult::InitsAndTeardownsChunk(chunk);
//             results.send(result).unwrap();
//         }
//     }
//     trace!(
//         "BATCH[{batch_id}] CPU_WORKER[{worker_id}] setup and teardown chunk(s) collected in {:.3} ms",
//         now.elapsed().as_secs_f64() * 1000.0
//     );
//     let final_register_values = state
//         .observable
//         .registers
//         .into_iter()
//         .zip(register_last_live_timestamps.into_iter())
//         .map(|(value, last_access_timestamp)| FinalRegisterValue {
//             value,
//             last_access_timestamp,
//         })
//         .collect_array()
//         .unwrap();
//     let result = WorkerResult::RAMTracingResult {
//         chunks_traced_count,
//         final_register_values,
//     };
//     results.send(result).unwrap();
//     trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] tracing touched RAM finished");
// }
//
// fn trace_cycles<C: MachineConfig, A: GoodAllocator + 'static>(
//     batch_id: u64,
//     worker_id: usize,
//     num_main_chunks_upper_bound: usize,
//     circuit_type: MainCircuitType,
//     binary: impl Deref<Target = impl Deref<Target = [u32]>>,
//     non_determinism: impl Deref<Target = impl NonDeterminism>,
//     skip_set: HashSet<(CircuitType, usize)>,
//     split_count: usize,
//     split_index: usize,
//     free_allocator: Receiver<A>,
//     results: Sender<WorkerResult<A>>,
// ) {
//     trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] worker for tracing cycles started");
//     let domain_size = circuit_type.get_domain_size();
//     assert!(domain_size.is_power_of_two());
//     let log_domain_size = domain_size.trailing_zeros();
//     let mut non_determinism = non_determinism.clone();
//     let mut memory = BoxedMemoryImplWithRom::<RAM_SIZE, LOG_ROM_SIZE>::new();
//     for (idx, instruction) in binary.iter().enumerate() {
//         memory.populate(ENTRY_POINT + idx as u32 * 4, *instruction);
//     }
//     let cycles_per_chunk = domain_size - 1;
//     let mut state = RiscV32StateForUnrolledProver::<C>::initial(ENTRY_POINT);
//     let mut custom_csr_processor = DelegationsCSRProcessor;
//     let mut ram_tracing_data = RamTracingData::<RAM_SIZE, false>::new();
//     let mut end_reached = false;
//     let mut chunks_traced_count = 0;
//     trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] starting simulation");
//     let now = Instant::now();
//     for chunk_index in 0..num_main_chunks_upper_bound {
//         let delegation_tracing_data = DelegationTracingData::default();
//         let delegation_swap_fn = |_, _| unreachable!();
//         let initial_timestamp =
//             timestamp_from_chunk_cycle_and_sequence(0, cycles_per_chunk, chunk_index);
//         let finished;
//         if chunk_index % split_count == split_index
//             && !skip_set.contains(&(CircuitType::Main(circuit_type), chunk_index))
//         {
//             let allocator = free_allocator.recv().unwrap();
//             let per_cycle_data = Vec::with_capacity_in(cycles_per_chunk, allocator);
//             let cycle_tracing_data = CycleTracingData { per_cycle_data };
//             trace!(
//                 "BATCH[{batch_id}] CPU_WORKER[{worker_id}] tracing cycles for chunk {chunk_index}"
//             );
//             let mut tracer =
//                 ExecutionTracer::<RAM_SIZE, LOG_ROM_SIZE, _, A, Global, false, true, false>::new(
//                     &mut ram_tracing_data,
//                     cycle_tracing_data,
//                     delegation_tracing_data,
//                     delegation_swap_fn,
//                     initial_timestamp,
//                 );
//             let now = Instant::now();
//             finished = state.run_cycles(
//                 &mut memory,
//                 &mut tracer,
//                 &mut non_determinism,
//                 &mut custom_csr_processor,
//                 cycles_per_chunk,
//             );
//             let elapsed_ms = now.elapsed().as_secs_f64() * 1000.0;
//             let mhz = (cycles_per_chunk as f64) / (elapsed_ms * 1000.0);
//             trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] tracing cycles for chunk {chunk_index} finished in {elapsed_ms:.3} ms @ {mhz:.3} MHz");
//             let chunk = CyclesChunk {
//                 index: chunk_index,
//                 data: tracer.cycle_tracing_data,
//             };
//             let result = WorkerResult::CyclesChunk(chunk);
//             results.send(result).unwrap();
//         } else {
//             // fast-forward the simulation
//             trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] fast-forwarding chunk {chunk_index}");
//             let cycle_tracing_data = CycleTracingData::with_cycles_capacity(0);
//             let mut tracer = ExecutionTracer::<
//                 RAM_SIZE,
//                 LOG_ROM_SIZE,
//                 _,
//                 Global,
//                 Global,
//                 false,
//                 false,
//                 false,
//             >::new(
//                 &mut ram_tracing_data,
//                 cycle_tracing_data,
//                 delegation_tracing_data,
//                 delegation_swap_fn,
//                 initial_timestamp,
//             );
//             let now = Instant::now();
//             finished = state.run_cycles(
//                 &mut memory,
//                 &mut tracer,
//                 &mut non_determinism,
//                 &mut custom_csr_processor,
//                 cycles_per_chunk,
//             );
//             let elapsed_ms = now.elapsed().as_secs_f64() * 1000.0;
//             let mhz = (cycles_per_chunk as f64) / (elapsed_ms * 1000.0);
//             trace!(
//                 "BATCH[{batch_id}] CPU_WORKER[{worker_id}] fast-forwarding chunk {chunk_index} finished in {elapsed_ms:.3} ms @ {mhz:.3} MHz"
//             );
//         }
//         chunks_traced_count += 1;
//         if finished {
//             let elapsed_ms = now.elapsed().as_secs_f64() * 1000.0;
//             let cycles_count = chunks_traced_count * cycles_per_chunk;
//             let speed = (cycles_count as f64) / (elapsed_ms * 1000.0);
//             trace!(
//                 "BATCH[{batch_id}] CPU_WORKER[{worker_id}] simulation ended at address 0x{:08x} and took {chunks_traced_count} chunks to finish execution",
//                 state.observable.pc,
//             );
//             debug!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] simulator tracing 1/{split_count} cycles ran {chunks_traced_count}x(2^{log_domain_size}-1) cycles in {elapsed_ms:.3} ms @ {speed:.3} MHz");
//             end_reached = true;
//             break;
//         }
//     }
//     assert!(
//         end_reached,
//         "BATCH[{batch_id}] CPU_WORKER[{worker_id}] end of execution was not reached after {num_main_chunks_upper_bound} chunks"
//     );
//     let result = WorkerResult::CyclesTracingResult {
//         chunks_traced_count,
//     };
//     results.send(result).unwrap();
//     trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] tracing cycles finished");
// }
//
// fn trace_delegations<C: MachineConfig, A: GoodAllocator + 'static>(
//     batch_id: u64,
//     worker_id: usize,
//     num_main_chunks_upper_bound: usize,
//     circuit_type: MainCircuitType,
//     binary: impl Deref<Target = impl Deref<Target = [u32]>>,
//     non_determinism: impl Deref<Target = impl NonDeterminism>,
//     skip_set: HashSet<(CircuitType, usize)>,
//     free_allocator: Receiver<A>,
//     results: Sender<WorkerResult<A>>,
// ) {
//     trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] worker for tracing delegations started");
//     let domain_size = circuit_type.get_domain_size();
//     assert!(domain_size.is_power_of_two());
//     let log_domain_size = domain_size.trailing_zeros();
//     let mut non_determinism = non_determinism.clone();
//     let mut memory = BoxedMemoryImplWithRom::<RAM_SIZE, LOG_ROM_SIZE>::new();
//     for (idx, instruction) in binary.iter().enumerate() {
//         memory.populate(ENTRY_POINT + idx as u32 * 4, *instruction);
//     }
//     let cycles_per_chunk = domain_size - 1;
//     let mut state = RiscV32StateForUnrolledProver::<C>::initial(ENTRY_POINT);
//     let mut custom_csr_processor = DelegationsCSRProcessor;
//     let mut ram_tracing_data = RamTracingData::<RAM_SIZE, false>::new();
//     let cycle_tracing_data = CycleTracingData::with_cycles_capacity(0);
//     let delegation_tracing_data = DelegationTracingData::default();
//     let delegation_chunks_counts = RefCell::new(HashMap::new());
//     let delegation_swap_fn = |circuit_type, tracing_type: Option<DelegationTracingType<A>>| {
//         if let Some(tracing_type) = tracing_type {
//             let mut borrow = delegation_chunks_counts.borrow_mut();
//             let value = borrow.entry(circuit_type).or_default();
//             match tracing_type {
//                 DelegationTracingType::Counter(counter) => {
//                     trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] full delegation {:?} chunk {value} counter with {} delegations counted", circuit_type, counter.num_requests);
//                 }
//                 DelegationTracingType::Witness(witness) => {
//                     trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] full delegation {:?} chunk {value} witness with {} delegations produced", circuit_type, witness.num_requests);
//                     let result = WorkerResult::DelegationWitness {
//                         circuit_sequence: *value,
//                         witness,
//                     };
//                     results.send(result).unwrap();
//                 }
//             }
//             *value += 1;
//         }
//         let current_count = delegation_chunks_counts
//             .borrow()
//             .get(&circuit_type)
//             .copied()
//             .unwrap_or_default();
//         if skip_set.contains(&(CircuitType::Delegation(circuit_type), current_count)) {
//             trace!(
//                 "BATCH[{batch_id}] CPU_WORKER[{worker_id}] skipping delegation {:?} chunk {current_count}",
//                 circuit_type
//             );
//             let counter = DelegationCounter {
//                 num_requests: circuit_type.get_num_delegation_cycles(),
//                 count: 0,
//             };
//             DelegationTracingType::Counter(counter)
//         } else {
//             let allocator = free_allocator.recv().unwrap();
//             let factory = circuit_type.get_witness_factory_fn();
//             let witness = factory(allocator);
//             DelegationTracingType::Witness(witness)
//         }
//     };
//     let initial_timestamp = timestamp_from_chunk_cycle_and_sequence(0, cycles_per_chunk, 0);
//     let mut tracer =
//         ExecutionTracer::<RAM_SIZE, LOG_ROM_SIZE, _, Global, A, false, false, true>::new(
//             &mut ram_tracing_data,
//             cycle_tracing_data,
//             delegation_tracing_data,
//             delegation_swap_fn,
//             initial_timestamp,
//         );
//     let mut end_reached = false;
//     let mut chunks_traced_count = 0;
//     trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] starting simulation");
//     let now = Instant::now();
//     for _chunk_index in 0..num_main_chunks_upper_bound {
//         let chunk_now = Instant::now();
//         let finished = state.run_cycles(
//             &mut memory,
//             &mut tracer,
//             &mut non_determinism,
//             &mut custom_csr_processor,
//             cycles_per_chunk,
//         );
//         let elapsed_ms = chunk_now.elapsed().as_secs_f64() * 1000.0;
//         let mhz = (cycles_per_chunk as f64) / (elapsed_ms * 1000.0);
//         trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] chunk {chunks_traced_count} finished in {elapsed_ms:.3} ms @ {mhz:.3} MHz");
//         chunks_traced_count += 1;
//         if finished {
//             let elapsed_ms = now.elapsed().as_secs_f64() * 1000.0;
//             let cycles_count = chunks_traced_count * cycles_per_chunk;
//             let speed = (cycles_count as f64) / (elapsed_ms * 1000.0);
//             trace!(
//                 "BATCH[{batch_id}] CPU_WORKER[{worker_id}] simulation ended at address 0x{:08x} and took {chunks_traced_count} chunks to finish execution",
//                 state.observable.pc,
//             );
//             debug!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] simulator tracing delegations ran {chunks_traced_count}x(2^{log_domain_size}-1) cycles in {elapsed_ms:.3} ms @ {speed:.3} MHz");
//             end_reached = true;
//             break;
//         }
//         let new_timestamp =
//             timestamp_from_chunk_cycle_and_sequence(0, cycles_per_chunk, chunks_traced_count);
//         tracer.current_timestamp = new_timestamp;
//     }
//     assert!(
//         end_reached,
//         "end of execution was not reached after {num_main_chunks_upper_bound} chunks"
//     );
//     let mut delegation_chunks_counts = delegation_chunks_counts.borrow().clone();
//     for (circuit_type, tracing_type) in tracer.delegation_tracing_data.tracing_types.drain() {
//         let value = delegation_chunks_counts.entry(circuit_type).or_default();
//         match tracing_type {
//             DelegationTracingType::Counter(counter) => {
//                 let count = counter.count;
//                 assert_ne!(count, 0);
//                 trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] delegation {circuit_type:?} chunk {value} counter with {count} delegations counted");
//             }
//             DelegationTracingType::Witness(witness) => {
//                 witness.assert_consistency();
//                 let is_empty = witness.write_timestamp.is_empty();
//                 trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] delegation {circuit_type:?} chunk {value} witness with {} delegations produced", witness.write_timestamp.len());
//                 let result = WorkerResult::DelegationWitness {
//                     circuit_sequence: *value,
//                     witness,
//                 };
//                 results.send(result).unwrap();
//                 if is_empty {
//                     continue;
//                 }
//             }
//         }
//         *value += 1;
//     }
//     let result = WorkerResult::DelegationTracingResult {
//         delegation_chunks_counts,
//     };
//     results.send(result).unwrap();
//     trace!("BATCH[{batch_id}] CPU_WORKER[{worker_id}] tracing delegations finished");
// }
