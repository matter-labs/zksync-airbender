use super::A;
use crate::circuit_type::{
    CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
    UnrolledNonMemoryCircuitType,
};
use crate::execution::messages::{TracingData, WorkerResult};
use crate::execution::snapshotter::{
    DataTraceRanges, PtrRange, SplitDataTraceRanges, UnifiedDataTraceRanges,
};
use crate::machine_type::MachineType;
use crate::prover::tracing_data::{
    DelegationTracingDataHostSource, TracingDataHost, UnrolledTracingDataHost,
};
use crate::witness::trace::ChunkedTraceHolder;
use crossbeam_channel::{Receiver, Sender};
use itertools::Itertools;
use prover::risc_v_simulator::machine_mode_only_unrolled::{
    MemoryOpcodeTracingDataWithTimestamp, NonMemoryOpcodeTracingDataWithTimestamp,
    UnifiedOpcodeTracingDataWithTimestamp,
};
use riscv_transpiler::jit::{CounterType, MAX_NUM_COUNTERS};
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;
use std::cmp::min;
use std::collections::{BTreeSet, VecDeque};
use std::mem::{replace, transmute};
use std::sync::Arc;

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
    participating_snapshot_indexes: BTreeSet<usize>,
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
            participating_snapshot_indexes: BTreeSet::new(),
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
                    _chunk: Some(chunk.clone()),
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
            replace(&mut self.participating_snapshot_indexes, BTreeSet::new());
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

pub(crate) trait TracingDataProducers {
    type Ranges: DataTraceRanges + Send;

    fn new(
        machine_type: MachineType,
        free_allocators: Receiver<A>,
        results: Sender<WorkerResult<A>>,
    ) -> Self;

    fn process_snapshot(
        &mut self,
        snapshot_index: usize,
        initial_counters: &[u32; MAX_NUM_COUNTERS],
        final_counters: &[u32; MAX_NUM_COUNTERS],
    ) -> Self::Ranges;

    fn finalize(self);
}

pub(super) struct SplitTracingDataProducers {
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

impl TracingDataProducers for SplitTracingDataProducers {
    type Ranges = SplitDataTraceRanges;

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

    fn process_snapshot(
        &mut self,
        snapshot_index: usize,
        initial_counters: &[u32; MAX_NUM_COUNTERS],
        final_counters: &[u32; MAX_NUM_COUNTERS],
    ) -> Self::Ranges {
        let mut trace_ranges = SplitDataTraceRanges::default();
        for i in 0..CounterType::FormalEnd as u8 {
            let counter_type = unsafe { transmute(i) };
            let index = i as usize;
            let initial_count = initial_counters[index] as usize;
            let final_count = final_counters[index] as usize;
            match counter_type {
                CounterType::AddSubLui => self.add_sub_family_producer.process_snapshot(
                    snapshot_index,
                    initial_count,
                    final_count,
                    &mut trace_ranges.add_sub_family,
                ),
                CounterType::BranchSlt => self.slt_branch_family_producer.process_snapshot(
                    snapshot_index,
                    initial_count,
                    final_count,
                    &mut trace_ranges.slt_branch_family,
                ),
                CounterType::ShiftBinaryCsr => {
                    self.binary_shift_csr_family_producer.process_snapshot(
                        snapshot_index,
                        initial_count,
                        final_count,
                        &mut trace_ranges.binary_shift_csr_family,
                    )
                }
                CounterType::MulDiv => self.mul_div_family_producer.process_snapshot(
                    snapshot_index,
                    initial_count,
                    final_count,
                    &mut trace_ranges.mul_div_family,
                ),
                CounterType::MemWord => self.word_size_mem_family_producer.process_snapshot(
                    snapshot_index,
                    initial_count,
                    final_count,
                    &mut trace_ranges.word_size_mem_family,
                ),
                CounterType::MemSubword => self.subword_size_mem_family_producer.process_snapshot(
                    snapshot_index,
                    initial_count,
                    final_count,
                    &mut trace_ranges.subword_size_mem_family,
                ),
                CounterType::BlakeDelegation => self.blake_producer.process_snapshot(
                    snapshot_index,
                    initial_count,
                    final_count,
                    &mut trace_ranges.blake_calls,
                ),
                CounterType::BigintDelegation => self.bigint_producer.process_snapshot(
                    snapshot_index,
                    initial_count,
                    final_count,
                    &mut trace_ranges.bigint_calls,
                ),
                CounterType::KeccakDelegation => self.keccak_producer.process_snapshot(
                    snapshot_index,
                    initial_count,
                    final_count,
                    &mut trace_ranges.keccak_calls,
                ),
                _ => unreachable!(),
            }
        }
        trace_ranges
    }

    fn finalize(self) {
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

pub(super) struct UnifiedTracingDataProducers {
    blake_producer: TracingDataProducer<Blake2sRoundFunctionDelegationWitness>,
    bigint_producer: TracingDataProducer<BigintDelegationWitness>,
    keccak_producer: TracingDataProducer<KeccakSpecial5DelegationWitness>,
    cycles_producer: TracingDataProducer<UnifiedOpcodeTracingDataWithTimestamp>,
}

impl TracingDataProducers for UnifiedTracingDataProducers {
    type Ranges = UnifiedDataTraceRanges;

    fn new(
        machine_type: MachineType,
        free_allocators: Receiver<A>,
        results: Sender<WorkerResult<A>>,
    ) -> Self {
        assert_eq!(machine_type, MachineType::Reduced);
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
        let cycles_producer = TracingDataProducer::<UnifiedOpcodeTracingDataWithTimestamp>::new(
            CircuitType::Unrolled(UnrolledCircuitType::Unified),
            free_allocators.clone(),
            results.clone(),
        );
        Self {
            blake_producer,
            bigint_producer,
            keccak_producer,
            cycles_producer,
        }
    }

    fn process_snapshot(
        &mut self,
        snapshot_index: usize,
        initial_counters: &[u32; MAX_NUM_COUNTERS],
        final_counters: &[u32; MAX_NUM_COUNTERS],
    ) -> Self::Ranges {
        let mut trace_ranges = UnifiedDataTraceRanges::default();
        let mut cycles_initial_count = 0;
        let mut cycles_final_count = 0;
        for i in 0..CounterType::FormalEnd as u8 {
            let counter_type = unsafe { transmute(i) };
            let index = i as usize;
            let initial_count = initial_counters[index] as usize;
            let final_count = final_counters[index] as usize;
            match counter_type {
                CounterType::AddSubLui
                | CounterType::BranchSlt
                | CounterType::ShiftBinaryCsr
                | CounterType::MulDiv
                | CounterType::MemWord
                | CounterType::MemSubword => {
                    cycles_initial_count += initial_count;
                    cycles_final_count += final_count;
                }
                CounterType::BlakeDelegation => self.blake_producer.process_snapshot(
                    snapshot_index,
                    initial_count,
                    final_count,
                    &mut trace_ranges.blake_calls,
                ),
                CounterType::BigintDelegation => self.bigint_producer.process_snapshot(
                    snapshot_index,
                    initial_count,
                    final_count,
                    &mut trace_ranges.bigint_calls,
                ),
                CounterType::KeccakDelegation => self.keccak_producer.process_snapshot(
                    snapshot_index,
                    initial_count,
                    final_count,
                    &mut trace_ranges.keccak_calls,
                ),
                _ => unreachable!(),
            }
        }
        self.cycles_producer.process_snapshot(
            snapshot_index,
            cycles_initial_count,
            cycles_final_count,
            &mut trace_ranges.cycles,
        );
        trace_ranges
    }

    fn finalize(self) {
        self.blake_producer.finalize();
        self.bigint_producer.finalize();
        self.keccak_producer.finalize();
        self.cycles_producer.finalize();
    }
}
