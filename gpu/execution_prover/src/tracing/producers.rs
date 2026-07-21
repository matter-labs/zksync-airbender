use super::{DataTraceRanges, SplitDataTraceRanges, TracingDataProducer, UnifiedDataTraceRanges};
use crate::messages::WorkerResult;
use crate::A;
use crossbeam_channel::{Receiver, Sender};
use gpu_circuit_prover::witness::circuit_type::{
    CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
    UnrolledNonMemoryCircuitType,
};
use gpu_core::primitives::machine_type::MachineType;
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
        initial_counters: &[u64; MAX_NUM_COUNTERS],
        final_counters: &[u64; MAX_NUM_COUNTERS],
    ) -> Self::Ranges;

    fn finalize(self);
}

/// The four delegation producers (blake / bigint / keccak /
/// blake_g_function), constructed and torn down identically by
/// `SplitTracingDataProducers` and `UnifiedTracingDataProducers` — the two
/// differ only in which additional (per-family or unified-cycle) producers
/// accompany this shared set.
struct DelegationProducers {
    blake_producer: TracingDataProducer<Blake2sRoundFunctionDelegationWitness>,
    bigint_producer: TracingDataProducer<BigintDelegationWitness>,
    keccak_producer: TracingDataProducer<KeccakSpecial5DelegationWitness>,
    blake_g_function_producer: TracingDataProducer<Blake2sGFunctionDelegationWitness>,
}

impl DelegationProducers {
    fn new(free_allocators: &Receiver<A>, results: &Sender<WorkerResult<A>>) -> Self {
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
        let blake_g_function_producer =
            TracingDataProducer::<Blake2sGFunctionDelegationWitness>::new(
                CircuitType::Delegation(DelegationCircuitType::Blake2GFunction),
                free_allocators.clone(),
                results.clone(),
            );
        Self {
            blake_producer,
            bigint_producer,
            keccak_producer,
            blake_g_function_producer,
        }
    }

    fn finalize(self) {
        self.blake_producer.finalize();
        self.bigint_producer.finalize();
        self.keccak_producer.finalize();
        self.blake_g_function_producer.finalize();
    }
}

pub(crate) struct SplitTracingDataProducers {
    delegation: DelegationProducers,
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
        _machine_type: MachineType,
        free_allocators: Receiver<A>,
        results: Sender<WorkerResult<A>>,
    ) -> Self {
        let delegation = DelegationProducers::new(&free_allocators, &results);
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
                    UnrolledNonMemoryCircuitType::MulDivUnsigned,
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
            delegation,
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
        initial_counters: &[u64; MAX_NUM_COUNTERS],
        final_counters: &[u64; MAX_NUM_COUNTERS],
    ) -> Self::Ranges {
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
                ),
                CounterType::BranchSlt => self.slt_branch_family_producer.process_snapshot(
                    snapshot_index,
                    initial_count,
                    final_count,
                    &mut trace_ranges.slt_branch_family,
                ),
                CounterType::ShiftBinary => self.binary_shift_csr_family_producer.process_snapshot(
                    snapshot_index,
                    initial_count,
                    final_count,
                    &mut trace_ranges.binary_shift_csr_family,
                ),
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
                CounterType::BlakeDelegation => self.delegation.blake_producer.process_snapshot(
                    snapshot_index,
                    initial_count,
                    final_count,
                    &mut trace_ranges.blake_calls,
                ),
                CounterType::BigintDelegation => self.delegation.bigint_producer.process_snapshot(
                    snapshot_index,
                    initial_count,
                    final_count,
                    &mut trace_ranges.bigint_calls,
                ),
                CounterType::KeccakDelegation => self.delegation.keccak_producer.process_snapshot(
                    snapshot_index,
                    initial_count,
                    final_count,
                    &mut trace_ranges.keccak_calls,
                ),
                CounterType::BlakeGFunctionDelegation => {
                    self.delegation.blake_g_function_producer.process_snapshot(
                        snapshot_index,
                        initial_count,
                        final_count,
                        &mut trace_ranges.blake_g_function_calls,
                    )
                }
                _ => unreachable!(),
            }
        }
        trace_ranges
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

pub(crate) struct UnifiedTracingDataProducers {
    delegation: DelegationProducers,
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
        let delegation = DelegationProducers::new(&free_allocators, &results);
        let cycles_producer = TracingDataProducer::<UnifiedOpcodeTracingDataWithTimestamp>::new(
            CircuitType::Unrolled(UnrolledCircuitType::Unified),
            free_allocators.clone(),
            results.clone(),
        );
        Self {
            delegation,
            cycles_producer,
        }
    }

    fn process_snapshot(
        &mut self,
        snapshot_index: usize,
        initial_counters: &[u64; MAX_NUM_COUNTERS],
        final_counters: &[u64; MAX_NUM_COUNTERS],
    ) -> Self::Ranges {
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
                ),
                CounterType::BigintDelegation => self.delegation.bigint_producer.process_snapshot(
                    snapshot_index,
                    initial_count,
                    final_count,
                    &mut trace_ranges.bigint_calls,
                ),
                CounterType::KeccakDelegation => self.delegation.keccak_producer.process_snapshot(
                    snapshot_index,
                    initial_count,
                    final_count,
                    &mut trace_ranges.keccak_calls,
                ),
                CounterType::BlakeGFunctionDelegation => {
                    self.delegation.blake_g_function_producer.process_snapshot(
                        snapshot_index,
                        initial_count,
                        final_count,
                        &mut trace_ranges.blake_g_function_calls,
                    )
                }
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
        self.delegation.finalize();
        self.cycles_producer.finalize();
    }
}
