use super::{DataTraceRanges, SplitDataTraceRanges, TracingDataProducer, UnifiedDataTraceRanges};
use crate::messages::WorkerResult;
use crate::workers::cancellation::Cancellation;
use crossbeam_channel::{Receiver, Sender};
use execution_prover_model::allocator::HostTraceAllocator;
use execution_prover_model::circuit_type::{
    CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
    UnrolledNonMemoryCircuitType,
};
use execution_prover_model::MachineType;
use riscv_transpiler::jit::{CounterType, MAX_NUM_COUNTERS};
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_g_function::Blake2sGFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;
use riscv_transpiler::witness::{
    MemoryOpcodeTracingDataWithTimestamp, NonMemoryOpcodeTracingDataWithTimestamp,
    UnifiedOpcodeTracingDataWithTimestamp,
};
use std::mem::transmute;

pub(crate) trait TracingDataProducers<A: HostTraceAllocator> {
    type Ranges: DataTraceRanges + Send;

    fn new(
        machine_type: MachineType,
        free_allocators: Receiver<A>,
        results: Sender<WorkerResult<A>>,
        cancellation: Cancellation,
    ) -> Self;

    /// `None` once cancellation (or a closed channel) has ended production;
    /// see [`super::TracingDataProducer::process_snapshot`] for why giving up
    /// cannot be a panic here.
    fn process_snapshot(
        &mut self,
        snapshot_index: usize,
        initial_counters: &[u64; MAX_NUM_COUNTERS],
        final_counters: &[u64; MAX_NUM_COUNTERS],
    ) -> Option<Self::Ranges>;

    fn finalize(self);
}

/// The four delegation producers, constructed and torn down identically by
/// both `TracingDataProducers` impls, which differ only in the per-family or
/// unified-cycle producers that accompany them.
struct DelegationProducers<A: HostTraceAllocator> {
    blake_producer: TracingDataProducer<Blake2sRoundFunctionDelegationWitness, A>,
    bigint_producer: TracingDataProducer<BigintDelegationWitness, A>,
    keccak_producer: TracingDataProducer<KeccakSpecial5DelegationWitness, A>,
    blake_g_function_producer: TracingDataProducer<Blake2sGFunctionDelegationWitness, A>,
}

/// Every producer is built from the same three channel handles; only the row
/// type and the circuit differ.
fn producer<T: super::TracingDataProducerType, A: HostTraceAllocator>(
    circuit_type: CircuitType,
    free_allocators: &Receiver<A>,
    results: &Sender<WorkerResult<A>>,
    cancellation: &Cancellation,
) -> TracingDataProducer<T, A> {
    TracingDataProducer::new(
        circuit_type,
        free_allocators.clone(),
        results.clone(),
        cancellation.clone(),
    )
}

fn delegation(circuit_type: DelegationCircuitType) -> CircuitType {
    CircuitType::Delegation(circuit_type)
}

fn non_memory(circuit_type: UnrolledNonMemoryCircuitType) -> CircuitType {
    CircuitType::Unrolled(UnrolledCircuitType::NonMemory(circuit_type))
}

fn memory(circuit_type: UnrolledMemoryCircuitType) -> CircuitType {
    CircuitType::Unrolled(UnrolledCircuitType::Memory(circuit_type))
}

impl<A: HostTraceAllocator> DelegationProducers<A> {
    fn new(
        free_allocators: &Receiver<A>,
        results: &Sender<WorkerResult<A>>,
        cancellation: &Cancellation,
    ) -> Self {
        Self {
            blake_producer: producer(
                delegation(DelegationCircuitType::Blake2WithCompression),
                free_allocators,
                results,
                cancellation,
            ),
            bigint_producer: producer(
                delegation(DelegationCircuitType::BigIntWithControl),
                free_allocators,
                results,
                cancellation,
            ),
            keccak_producer: producer(
                delegation(DelegationCircuitType::KeccakSpecial5),
                free_allocators,
                results,
                cancellation,
            ),
            blake_g_function_producer: producer(
                delegation(DelegationCircuitType::Blake2GFunction),
                free_allocators,
                results,
                cancellation,
            ),
        }
    }

    fn finalize(self) {
        self.blake_producer.finalize();
        self.bigint_producer.finalize();
        self.keccak_producer.finalize();
        self.blake_g_function_producer.finalize();
    }
}

pub(crate) struct SplitTracingDataProducers<A: HostTraceAllocator> {
    delegation: DelegationProducers<A>,
    add_sub_family_producer: TracingDataProducer<NonMemoryOpcodeTracingDataWithTimestamp, A>,
    binary_shift_csr_family_producer:
        TracingDataProducer<NonMemoryOpcodeTracingDataWithTimestamp, A>,
    slt_branch_family_producer: TracingDataProducer<NonMemoryOpcodeTracingDataWithTimestamp, A>,
    mul_div_family_producer: TracingDataProducer<NonMemoryOpcodeTracingDataWithTimestamp, A>,
    word_size_mem_family_producer: TracingDataProducer<MemoryOpcodeTracingDataWithTimestamp, A>,
    subword_size_mem_family_producer: TracingDataProducer<MemoryOpcodeTracingDataWithTimestamp, A>,
}

impl<A: HostTraceAllocator> TracingDataProducers<A> for SplitTracingDataProducers<A> {
    type Ranges = SplitDataTraceRanges<A>;

    fn new(
        _machine_type: MachineType,
        free_allocators: Receiver<A>,
        results: Sender<WorkerResult<A>>,
        cancellation: Cancellation,
    ) -> Self {
        let (free, res, cancel) = (&free_allocators, &results, &cancellation);
        Self {
            delegation: DelegationProducers::new(free, res, cancel),
            add_sub_family_producer: producer(
                non_memory(UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop),
                free,
                res,
                cancel,
            ),
            binary_shift_csr_family_producer: producer(
                non_memory(UnrolledNonMemoryCircuitType::ShiftBinary),
                free,
                res,
                cancel,
            ),
            slt_branch_family_producer: producer(
                non_memory(UnrolledNonMemoryCircuitType::JumpBranchSlt),
                free,
                res,
                cancel,
            ),
            mul_div_family_producer: producer(
                non_memory(UnrolledNonMemoryCircuitType::MulDivUnsigned),
                free,
                res,
                cancel,
            ),
            word_size_mem_family_producer: producer(
                memory(UnrolledMemoryCircuitType::LoadStoreWordOnly),
                free,
                res,
                cancel,
            ),
            subword_size_mem_family_producer: producer(
                memory(UnrolledMemoryCircuitType::LoadStoreSubwordOnly),
                free,
                res,
                cancel,
            ),
        }
    }

    fn process_snapshot(
        &mut self,
        snapshot_index: usize,
        initial_counters: &[u64; MAX_NUM_COUNTERS],
        final_counters: &[u64; MAX_NUM_COUNTERS],
    ) -> Option<Self::Ranges> {
        let mut trace_ranges = SplitDataTraceRanges::default();
        for i in 0..CounterType::FormalEnd as u8 {
            // SAFETY: loop bound `0..CounterType::FormalEnd as u8` keeps `i`
            // within the enum's defined `#[repr(u8)]` discriminants.
            let counter_type = unsafe { transmute::<u8, CounterType>(i) };
            let index = i as usize;
            let initial_count = initial_counters[index] as usize;
            let final_count = final_counters[index] as usize;
            match counter_type {
                CounterType::AddSubLui => self.add_sub_family_producer.process_snapshot(
                    snapshot_index,
                    initial_count,
                    final_count,
                    &mut trace_ranges.add_sub_family,
                )?,
                CounterType::BranchSlt => self.slt_branch_family_producer.process_snapshot(
                    snapshot_index,
                    initial_count,
                    final_count,
                    &mut trace_ranges.slt_branch_family,
                )?,
                CounterType::ShiftBinary => {
                    self.binary_shift_csr_family_producer.process_snapshot(
                        snapshot_index,
                        initial_count,
                        final_count,
                        &mut trace_ranges.binary_shift_csr_family,
                    )?
                }
                CounterType::MulDiv => self.mul_div_family_producer.process_snapshot(
                    snapshot_index,
                    initial_count,
                    final_count,
                    &mut trace_ranges.mul_div_family,
                )?,
                CounterType::MemWord => self.word_size_mem_family_producer.process_snapshot(
                    snapshot_index,
                    initial_count,
                    final_count,
                    &mut trace_ranges.word_size_mem_family,
                )?,
                CounterType::MemSubword => self.subword_size_mem_family_producer.process_snapshot(
                    snapshot_index,
                    initial_count,
                    final_count,
                    &mut trace_ranges.subword_size_mem_family,
                )?,
                CounterType::BlakeDelegation => self.delegation.blake_producer.process_snapshot(
                    snapshot_index,
                    initial_count,
                    final_count,
                    &mut trace_ranges.blake_calls,
                )?,
                CounterType::BigintDelegation => self.delegation.bigint_producer.process_snapshot(
                    snapshot_index,
                    initial_count,
                    final_count,
                    &mut trace_ranges.bigint_calls,
                )?,
                CounterType::KeccakDelegation => self.delegation.keccak_producer.process_snapshot(
                    snapshot_index,
                    initial_count,
                    final_count,
                    &mut trace_ranges.keccak_calls,
                )?,
                CounterType::BlakeGFunctionDelegation => {
                    self.delegation.blake_g_function_producer.process_snapshot(
                        snapshot_index,
                        initial_count,
                        final_count,
                        &mut trace_ranges.blake_g_function_calls,
                    )?
                }
                _ => unreachable!(),
            }
        }
        Some(trace_ranges)
    }

    fn finalize(self) {
        self.delegation.finalize();
        self.add_sub_family_producer.finalize();
        self.binary_shift_csr_family_producer.finalize();
        self.slt_branch_family_producer.finalize();
        self.mul_div_family_producer.finalize();
        self.word_size_mem_family_producer.finalize();
        self.subword_size_mem_family_producer.finalize();
    }
}

pub(crate) struct UnifiedTracingDataProducers<A: HostTraceAllocator> {
    delegation: DelegationProducers<A>,
    cycles_producer: TracingDataProducer<UnifiedOpcodeTracingDataWithTimestamp, A>,
}

impl<A: HostTraceAllocator> TracingDataProducers<A> for UnifiedTracingDataProducers<A> {
    type Ranges = UnifiedDataTraceRanges<A>;

    fn new(
        machine_type: MachineType,
        free_allocators: Receiver<A>,
        results: Sender<WorkerResult<A>>,
        cancellation: Cancellation,
    ) -> Self {
        assert_eq!(machine_type, MachineType::Reduced);
        let (free, res, cancel) = (&free_allocators, &results, &cancellation);
        Self {
            delegation: DelegationProducers::new(free, res, cancel),
            cycles_producer: producer(
                CircuitType::Unrolled(UnrolledCircuitType::Unified),
                free,
                res,
                cancel,
            ),
        }
    }

    fn process_snapshot(
        &mut self,
        snapshot_index: usize,
        initial_counters: &[u64; MAX_NUM_COUNTERS],
        final_counters: &[u64; MAX_NUM_COUNTERS],
    ) -> Option<Self::Ranges> {
        let mut trace_ranges = UnifiedDataTraceRanges::default();
        let mut cycles_initial_count = 0;
        let mut cycles_final_count = 0;
        for i in 0..CounterType::FormalEnd as u8 {
            // SAFETY: loop bound `0..CounterType::FormalEnd as u8` keeps `i`
            // within the enum's defined `#[repr(u8)]` discriminants.
            let counter_type = unsafe { transmute::<u8, CounterType>(i) };
            let index = i as usize;
            let initial_count = initial_counters[index] as usize;
            let final_count = final_counters[index] as usize;
            match counter_type {
                CounterType::AddSubLui
                | CounterType::BranchSlt
                | CounterType::ShiftBinary
                | CounterType::MulDiv
                | CounterType::MemWord
                | CounterType::MemSubword => {
                    cycles_initial_count += initial_count;
                    cycles_final_count += final_count;
                }
                CounterType::BlakeDelegation => self.delegation.blake_producer.process_snapshot(
                    snapshot_index,
                    initial_count,
                    final_count,
                    &mut trace_ranges.blake_calls,
                )?,
                CounterType::BigintDelegation => self.delegation.bigint_producer.process_snapshot(
                    snapshot_index,
                    initial_count,
                    final_count,
                    &mut trace_ranges.bigint_calls,
                )?,
                CounterType::KeccakDelegation => self.delegation.keccak_producer.process_snapshot(
                    snapshot_index,
                    initial_count,
                    final_count,
                    &mut trace_ranges.keccak_calls,
                )?,
                CounterType::BlakeGFunctionDelegation => {
                    self.delegation.blake_g_function_producer.process_snapshot(
                        snapshot_index,
                        initial_count,
                        final_count,
                        &mut trace_ranges.blake_g_function_calls,
                    )?
                }
                _ => unreachable!(),
            }
        }
        self.cycles_producer.process_snapshot(
            snapshot_index,
            cycles_initial_count,
            cycles_final_count,
            &mut trace_ranges.cycles,
        )?;
        Some(trace_ranges)
    }

    fn finalize(self) {
        self.delegation.finalize();
        self.cycles_producer.finalize();
    }
}
