use super::{DataTraceRanges, SplitDataTraceRanges, TracingDataProducer, UnifiedDataTraceRanges};
use crate::messages::WorkerResult;
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
use riscv_transpiler::witness::delegation::keccak_k2::{
    KeccakChi5DelegationWitness, KeccakColumnParityDelegationWitness,
    KeccakThetaRhoDelegationWitness,
};
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
    ) -> Self;

    fn process_snapshot(
        &mut self,
        snapshot_index: usize,
        initial_counters: &[u64; MAX_NUM_COUNTERS],
        final_counters: &[u64; MAX_NUM_COUNTERS],
    ) -> Self::Ranges;

    fn finalize(self);
}

/// Delegation producers, constructed and torn down identically by
/// `SplitTracingDataProducers` and `UnifiedTracingDataProducers` — the two
/// differ only in which additional (per-family or unified-cycle) producers
/// accompany this shared set.
struct DelegationProducers<A: HostTraceAllocator> {
    blake_producer: TracingDataProducer<Blake2sRoundFunctionDelegationWitness, A>,
    bigint_producer: TracingDataProducer<BigintDelegationWitness, A>,
    keccak_producer: TracingDataProducer<KeccakSpecial5DelegationWitness, A>,
    keccak_column_parity_producer: TracingDataProducer<KeccakColumnParityDelegationWitness, A>,
    keccak_theta_rho_producer: TracingDataProducer<KeccakThetaRhoDelegationWitness, A>,
    keccak_chi5_producer: TracingDataProducer<KeccakChi5DelegationWitness, A>,
    blake_g_function_producer: TracingDataProducer<Blake2sGFunctionDelegationWitness, A>,
}

impl<A: HostTraceAllocator> DelegationProducers<A> {
    fn new(free_allocators: &Receiver<A>, results: &Sender<WorkerResult<A>>) -> Self {
        let blake_producer = TracingDataProducer::<Blake2sRoundFunctionDelegationWitness, _>::new(
            CircuitType::Delegation(DelegationCircuitType::Blake2WithCompression),
            free_allocators.clone(),
            results.clone(),
        );
        let bigint_producer = TracingDataProducer::<BigintDelegationWitness, _>::new(
            CircuitType::Delegation(DelegationCircuitType::BigIntWithControl),
            free_allocators.clone(),
            results.clone(),
        );
        let keccak_producer = TracingDataProducer::<KeccakSpecial5DelegationWitness, _>::new(
            CircuitType::Delegation(DelegationCircuitType::KeccakSpecial5),
            free_allocators.clone(),
            results.clone(),
        );
        let keccak_column_parity_producer =
            TracingDataProducer::<KeccakColumnParityDelegationWitness, _>::new(
                CircuitType::Delegation(DelegationCircuitType::KeccakColumnParity),
                free_allocators.clone(),
                results.clone(),
            );
        let keccak_theta_rho_producer =
            TracingDataProducer::<KeccakThetaRhoDelegationWitness, _>::new(
                CircuitType::Delegation(DelegationCircuitType::KeccakThetaRho),
                free_allocators.clone(),
                results.clone(),
            );
        let keccak_chi5_producer = TracingDataProducer::<KeccakChi5DelegationWitness, _>::new(
            CircuitType::Delegation(DelegationCircuitType::KeccakChi5),
            free_allocators.clone(),
            results.clone(),
        );
        let blake_g_function_producer =
            TracingDataProducer::<Blake2sGFunctionDelegationWitness, _>::new(
                CircuitType::Delegation(DelegationCircuitType::Blake2GFunction),
                free_allocators.clone(),
                results.clone(),
            );
        Self {
            blake_producer,
            bigint_producer,
            keccak_producer,
            keccak_column_parity_producer,
            keccak_theta_rho_producer,
            keccak_chi5_producer,
            blake_g_function_producer,
        }
    }

    fn finalize(self) {
        self.blake_producer.finalize();
        self.bigint_producer.finalize();
        self.keccak_producer.finalize();
        self.keccak_column_parity_producer.finalize();
        self.keccak_theta_rho_producer.finalize();
        self.keccak_chi5_producer.finalize();
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
    ) -> Self {
        let delegation = DelegationProducers::new(&free_allocators, &results);
        let add_sub_family_producer =
            TracingDataProducer::<NonMemoryOpcodeTracingDataWithTimestamp, _>::new(
                CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
                    UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
                )),
                free_allocators.clone(),
                results.clone(),
            );
        let binary_shift_csr_family_producer =
            TracingDataProducer::<NonMemoryOpcodeTracingDataWithTimestamp, _>::new(
                CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
                    UnrolledNonMemoryCircuitType::ShiftBinary,
                )),
                free_allocators.clone(),
                results.clone(),
            );
        let slt_branch_family_producer =
            TracingDataProducer::<NonMemoryOpcodeTracingDataWithTimestamp, _>::new(
                CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
                    UnrolledNonMemoryCircuitType::JumpBranchSlt,
                )),
                free_allocators.clone(),
                results.clone(),
            );
        let mul_div_family_producer =
            TracingDataProducer::<NonMemoryOpcodeTracingDataWithTimestamp, _>::new(
                CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
                    UnrolledNonMemoryCircuitType::MulDivUnsigned,
                )),
                free_allocators.clone(),
                results.clone(),
            );
        let word_size_mem_family_producer =
            TracingDataProducer::<MemoryOpcodeTracingDataWithTimestamp, _>::new(
                CircuitType::Unrolled(UnrolledCircuitType::Memory(
                    UnrolledMemoryCircuitType::LoadStoreWordOnly,
                )),
                free_allocators.clone(),
                results.clone(),
            );
        let subword_size_mem_family_producer =
            TracingDataProducer::<MemoryOpcodeTracingDataWithTimestamp, _>::new(
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
                CounterType::KeccakK2Delegation => {
                    let (cp_start, tr_start, chi_start) = keccak_k2_rows_per_circuit(initial_count);
                    let (cp_end, tr_end, chi_end) = keccak_k2_rows_per_circuit(final_count);
                    self.delegation
                        .keccak_column_parity_producer
                        .process_snapshot(
                            snapshot_index,
                            cp_start,
                            cp_end,
                            &mut trace_ranges.keccak_column_parity_calls,
                        );
                    self.delegation.keccak_theta_rho_producer.process_snapshot(
                        snapshot_index,
                        tr_start,
                        tr_end,
                        &mut trace_ranges.keccak_theta_rho_calls,
                    );
                    self.delegation.keccak_chi5_producer.process_snapshot(
                        snapshot_index,
                        chi_start,
                        chi_end,
                        &mut trace_ranges.keccak_chi5_calls,
                    );
                }
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
    ) -> Self {
        assert_eq!(machine_type, MachineType::Reduced);
        let delegation = DelegationProducers::new(&free_allocators, &results);
        let cycles_producer = TracingDataProducer::<UnifiedOpcodeTracingDataWithTimestamp, _>::new(
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
                CounterType::KeccakK2Delegation => {
                    let (cp_start, tr_start, chi_start) = keccak_k2_rows_per_circuit(initial_count);
                    let (cp_end, tr_end, chi_end) = keccak_k2_rows_per_circuit(final_count);
                    self.delegation
                        .keccak_column_parity_producer
                        .process_snapshot(
                            snapshot_index,
                            cp_start,
                            cp_end,
                            &mut trace_ranges.keccak_column_parity_calls,
                        );
                    self.delegation.keccak_theta_rho_producer.process_snapshot(
                        snapshot_index,
                        tr_start,
                        tr_end,
                        &mut trace_ranges.keccak_theta_rho_calls,
                    );
                    self.delegation.keccak_chi5_producer.process_snapshot(
                        snapshot_index,
                        chi_start,
                        chi_end,
                        &mut trace_ranges.keccak_chi5_calls,
                    );
                }
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

// the ranges back unchecked tracer writes, so a partial permutation must not round down
fn keccak_k2_rows_per_circuit(calls: usize) -> (usize, usize, usize) {
    use common_constants::delegation_types::keccak_k2::*;
    assert_eq!(
        calls % NUM_DELEGATION_CALLS_FOR_KECCAK_K2_F1600,
        0,
        "Keccak snapshot counter must end on a full K2 permutation"
    );
    let permutations = calls / NUM_DELEGATION_CALLS_FOR_KECCAK_K2_F1600;
    (
        permutations * NUM_KECCAK_K2_COLUMN_PARITY_CALLS,
        permutations * NUM_KECCAK_K2_THETA_RHO_CALLS,
        permutations * NUM_KECCAK_K2_CHI5_CALLS,
    )
}
