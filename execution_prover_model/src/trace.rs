use crate::upstream::TimestampScalar;
use fft::GoodAllocator;
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_g_function::Blake2sGFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;
use riscv_transpiler::witness::{
    MemoryOpcodeTracingDataWithTimestamp, NonMemoryOpcodeTracingDataWithTimestamp,
    UnifiedOpcodeTracingDataWithTimestamp,
};
use std::sync::Arc;

/// Init/teardown page size in log2(words).
pub const PAGE_SIZE_LOG2: u32 = 10;

#[derive(Clone)]
pub struct ChunkedTraceHolder<T, A: GoodAllocator> {
    pub chunks: Vec<Arc<Vec<T, A>>>,
}

impl<T, A: GoodAllocator> ChunkedTraceHolder<T, A> {
    pub fn len(&self) -> usize {
        self.chunks.iter().map(|chunk| chunk.len()).sum()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn into_allocators(self) -> Vec<A> {
        self.chunks
            .into_iter()
            .map(|c| {
                Arc::into_inner(c)
                    .expect(
                        "ChunkedTraceHolder::into_allocators requires unique Arc ownership per chunk",
                    )
                    .allocator()
                    .clone()
            })
            .collect()
    }
}

pub type DelegationTraceHost<T, A> = ChunkedTraceHolder<T, A>;
pub type UnrolledMemoryTraceHost<A> = ChunkedTraceHolder<MemoryOpcodeTracingDataWithTimestamp, A>;
pub type UnrolledNonMemoryTraceHost<A> =
    ChunkedTraceHolder<NonMemoryOpcodeTracingDataWithTimestamp, A>;
pub type UnrolledUnifiedTraceHost<A> = ChunkedTraceHolder<UnifiedOpcodeTracingDataWithTimestamp, A>;

/// Sparse pages with matching values and timestamps. Page indices are local
/// to each set; `top_bits` gives each set's global window index.
#[derive(Clone)]
pub struct InitsAndTeardownsTraceHost<A: GoodAllocator> {
    pub page_indices: ChunkedTraceHolder<u32, A>,
    pub values_packed: ChunkedTraceHolder<u32, A>,
    pub timestamps_packed: ChunkedTraceHolder<TimestampScalar, A>,
    /// One global window index per set, ascending.
    pub top_bits: Vec<u32>,
}

impl<A: GoodAllocator> InitsAndTeardownsTraceHost<A> {
    pub fn into_allocators(self) -> Vec<A> {
        let Self {
            page_indices,
            values_packed,
            timestamps_packed,
            top_bits: _,
        } = self;
        let mut allocators = page_indices.into_allocators();
        allocators.extend(values_packed.into_allocators());
        allocators.extend(timestamps_packed.into_allocators());
        allocators
    }
}

#[derive(Clone)]
pub enum DelegationTracingDataHost<A: GoodAllocator> {
    BigIntWithControl(DelegationTraceHost<BigintDelegationWitness, A>),
    Blake2WithCompression(DelegationTraceHost<Blake2sRoundFunctionDelegationWitness, A>),
    Blake2GFunction(DelegationTraceHost<Blake2sGFunctionDelegationWitness, A>),
    KeccakSpecial5(DelegationTraceHost<KeccakSpecial5DelegationWitness, A>),
}

impl<A: GoodAllocator> DelegationTracingDataHost<A> {
    pub fn into_allocators(self) -> Vec<A> {
        match self {
            DelegationTracingDataHost::BigIntWithControl(trace) => trace.into_allocators(),
            DelegationTracingDataHost::Blake2WithCompression(trace) => trace.into_allocators(),
            DelegationTracingDataHost::Blake2GFunction(trace) => trace.into_allocators(),
            DelegationTracingDataHost::KeccakSpecial5(trace) => trace.into_allocators(),
        }
    }
}

pub trait DelegationTracingDataHostSource: Sized {
    fn get<A: GoodAllocator>(trace: DelegationTraceHost<Self, A>) -> DelegationTracingDataHost<A>;
}

impl DelegationTracingDataHostSource for BigintDelegationWitness {
    fn get<A: GoodAllocator>(trace: DelegationTraceHost<Self, A>) -> DelegationTracingDataHost<A> {
        DelegationTracingDataHost::BigIntWithControl(trace)
    }
}

impl DelegationTracingDataHostSource for Blake2sRoundFunctionDelegationWitness {
    fn get<A: GoodAllocator>(trace: DelegationTraceHost<Self, A>) -> DelegationTracingDataHost<A> {
        DelegationTracingDataHost::Blake2WithCompression(trace)
    }
}

impl DelegationTracingDataHostSource for Blake2sGFunctionDelegationWitness {
    fn get<A: GoodAllocator>(trace: DelegationTraceHost<Self, A>) -> DelegationTracingDataHost<A> {
        DelegationTracingDataHost::Blake2GFunction(trace)
    }
}

impl DelegationTracingDataHostSource for KeccakSpecial5DelegationWitness {
    fn get<A: GoodAllocator>(trace: DelegationTraceHost<Self, A>) -> DelegationTracingDataHost<A> {
        DelegationTracingDataHost::KeccakSpecial5(trace)
    }
}

#[derive(Clone)]
pub enum UnrolledTracingDataHost<A: GoodAllocator> {
    Memory(UnrolledMemoryTraceHost<A>),
    NonMemory(UnrolledNonMemoryTraceHost<A>),
    Unified(UnrolledUnifiedTraceHost<A>),
}

impl<A: GoodAllocator> UnrolledTracingDataHost<A> {
    pub fn into_allocators(self) -> Vec<A> {
        match self {
            UnrolledTracingDataHost::Memory(trace) => trace.into_allocators(),
            UnrolledTracingDataHost::NonMemory(trace) => trace.into_allocators(),
            UnrolledTracingDataHost::Unified(trace) => trace.into_allocators(),
        }
    }
}

#[derive(Clone)]
pub enum TracingDataHost<A: GoodAllocator> {
    Delegation(DelegationTracingDataHost<A>),
    Unrolled(UnrolledTracingDataHost<A>),
}

impl<A: GoodAllocator> TracingDataHost<A> {
    pub fn into_allocators(self) -> Vec<A> {
        match self {
            TracingDataHost::Delegation(trace) => trace.into_allocators(),
            TracingDataHost::Unrolled(trace) => trace.into_allocators(),
        }
    }
}
