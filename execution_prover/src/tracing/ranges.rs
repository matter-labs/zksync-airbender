use execution_prover_model::allocator::HostTraceAllocator;
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_g_function::Blake2sGFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;
use riscv_transpiler::witness::{
    MemoryOpcodeTracingDataWithTimestamp, NonMemoryOpcodeTracingDataWithTimestamp,
    UnifiedOpcodeTracingDataWithTimestamp,
};
use std::collections::VecDeque;
use std::sync::Arc;

pub(crate) struct PtrRange<T, A: HostTraceAllocator> {
    pub start: *mut T,
    pub end: *mut T,
    pub _chunk: Option<Arc<Vec<T, A>>>,
}

impl<T, A: HostTraceAllocator> Default for PtrRange<T, A> {
    fn default() -> Self {
        Self {
            start: std::ptr::null_mut(),
            end: std::ptr::null_mut(),
            _chunk: None,
        }
    }
}

// SAFETY: `PtrRange<T, A>` is a raw pointer pair into a host buffer owned by
// `_chunk`. The owning chunk is moved across threads alongside the range,
// so the lifetime of the pointed-to memory matches the receiver thread's
// access window. Concurrent mutation is controlled by the queue's pop/push
// discipline, not by the type itself.
unsafe impl<T, A: HostTraceAllocator> Send for PtrRange<T, A> {}

pub(crate) trait DataTraceRanges {}

#[derive(Default)]
pub(crate) struct SplitDataTraceRanges<A: HostTraceAllocator> {
    pub blake_calls: VecDeque<PtrRange<Blake2sRoundFunctionDelegationWitness, A>>,
    pub bigint_calls: VecDeque<PtrRange<BigintDelegationWitness, A>>,
    pub keccak_calls: VecDeque<PtrRange<KeccakSpecial5DelegationWitness, A>>,
    pub blake_g_function_calls: VecDeque<PtrRange<Blake2sGFunctionDelegationWitness, A>>,
    pub add_sub_family: VecDeque<PtrRange<NonMemoryOpcodeTracingDataWithTimestamp, A>>,
    pub binary_shift_csr_family: VecDeque<PtrRange<NonMemoryOpcodeTracingDataWithTimestamp, A>>,
    pub slt_branch_family: VecDeque<PtrRange<NonMemoryOpcodeTracingDataWithTimestamp, A>>,
    pub mul_div_family: VecDeque<PtrRange<NonMemoryOpcodeTracingDataWithTimestamp, A>>,
    pub word_size_mem_family: VecDeque<PtrRange<MemoryOpcodeTracingDataWithTimestamp, A>>,
    pub subword_size_mem_family: VecDeque<PtrRange<MemoryOpcodeTracingDataWithTimestamp, A>>,
}

impl<A: HostTraceAllocator> DataTraceRanges for SplitDataTraceRanges<A> {}

#[derive(Default)]
pub(crate) struct UnifiedDataTraceRanges<A: HostTraceAllocator> {
    pub blake_calls: VecDeque<PtrRange<Blake2sRoundFunctionDelegationWitness, A>>,
    pub bigint_calls: VecDeque<PtrRange<BigintDelegationWitness, A>>,
    pub keccak_calls: VecDeque<PtrRange<KeccakSpecial5DelegationWitness, A>>,
    pub blake_g_function_calls: VecDeque<PtrRange<Blake2sGFunctionDelegationWitness, A>>,
    pub cycles: VecDeque<PtrRange<UnifiedOpcodeTracingDataWithTimestamp, A>>,
}

impl<A: HostTraceAllocator> DataTraceRanges for UnifiedDataTraceRanges<A> {}
