use crate::circuit_type::DelegationCircuitType;
use crate::upstream::TimestampScalar;
use fft::GoodAllocator;
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_g_function::Blake2sGFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::keccak_f1600::{
    KeccakChi5DelegationWitness, KeccakColumnParityDelegationWitness,
    KeccakThetaRhoDelegationWitness,
};
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;
use riscv_transpiler::witness::{
    MemoryOpcodeTracingDataWithTimestamp, NonMemoryOpcodeTracingDataWithTimestamp,
    UnifiedOpcodeTracingDataWithTimestamp,
};

mod chunked;

pub use chunked::ChunkedTraceHolder;

/// Init/teardown page size in log2(words).
pub const PAGE_SIZE_LOG2: u32 = 10;

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
    KeccakChi5(DelegationTraceHost<KeccakChi5DelegationWitness, A>),
    KeccakThetaRho(DelegationTraceHost<KeccakThetaRhoDelegationWitness, A>),
    KeccakColumnParity(DelegationTraceHost<KeccakColumnParityDelegationWitness, A>),
}

impl<A: GoodAllocator> DelegationTracingDataHost<A> {
    pub fn into_allocators(self) -> Vec<A> {
        match self {
            DelegationTracingDataHost::BigIntWithControl(trace) => trace.into_allocators(),
            DelegationTracingDataHost::Blake2WithCompression(trace) => trace.into_allocators(),
            DelegationTracingDataHost::Blake2GFunction(trace) => trace.into_allocators(),
            DelegationTracingDataHost::KeccakSpecial5(trace) => trace.into_allocators(),
            DelegationTracingDataHost::KeccakChi5(trace) => trace.into_allocators(),
            DelegationTracingDataHost::KeccakThetaRho(trace) => trace.into_allocators(),
            DelegationTracingDataHost::KeccakColumnParity(trace) => trace.into_allocators(),
        }
    }
}

pub trait DelegationTracingDataHostSource: Sized {
    fn get<A: GoodAllocator>(
        circuit_type: DelegationCircuitType,
        trace: DelegationTraceHost<Self, A>,
    ) -> DelegationTracingDataHost<A>;
}

impl DelegationTracingDataHostSource for BigintDelegationWitness {
    fn get<A: GoodAllocator>(
        circuit_type: DelegationCircuitType,
        trace: DelegationTraceHost<Self, A>,
    ) -> DelegationTracingDataHost<A> {
        assert_eq!(circuit_type, DelegationCircuitType::BigIntWithControl);
        DelegationTracingDataHost::BigIntWithControl(trace)
    }
}

impl DelegationTracingDataHostSource for Blake2sRoundFunctionDelegationWitness {
    fn get<A: GoodAllocator>(
        circuit_type: DelegationCircuitType,
        trace: DelegationTraceHost<Self, A>,
    ) -> DelegationTracingDataHost<A> {
        assert_eq!(circuit_type, DelegationCircuitType::Blake2WithCompression);
        DelegationTracingDataHost::Blake2WithCompression(trace)
    }
}

impl DelegationTracingDataHostSource for Blake2sGFunctionDelegationWitness {
    fn get<A: GoodAllocator>(
        circuit_type: DelegationCircuitType,
        trace: DelegationTraceHost<Self, A>,
    ) -> DelegationTracingDataHost<A> {
        assert_eq!(circuit_type, DelegationCircuitType::Blake2GFunction);
        DelegationTracingDataHost::Blake2GFunction(trace)
    }
}

// column parity and special5 share DelegationWitness<2, 0, 12, 6>; the CSR picks the variant
impl DelegationTracingDataHostSource for KeccakColumnParityDelegationWitness {
    fn get<A: GoodAllocator>(
        circuit_type: DelegationCircuitType,
        trace: DelegationTraceHost<Self, A>,
    ) -> DelegationTracingDataHost<A> {
        match circuit_type {
            DelegationCircuitType::KeccakColumnParity => {
                DelegationTracingDataHost::KeccakColumnParity(trace)
            }
            DelegationCircuitType::KeccakSpecial5 => {
                DelegationTracingDataHost::KeccakSpecial5(trace)
            }
            _ => panic!("wrong circuit for column-parity/special5 witness shape"),
        }
    }
}

impl DelegationTracingDataHostSource for KeccakThetaRhoDelegationWitness {
    fn get<A: GoodAllocator>(
        circuit_type: DelegationCircuitType,
        trace: DelegationTraceHost<Self, A>,
    ) -> DelegationTracingDataHost<A> {
        assert_eq!(circuit_type, DelegationCircuitType::KeccakThetaRho);
        DelegationTracingDataHost::KeccakThetaRho(trace)
    }
}

impl DelegationTracingDataHostSource for KeccakChi5DelegationWitness {
    fn get<A: GoodAllocator>(
        circuit_type: DelegationCircuitType,
        trace: DelegationTraceHost<Self, A>,
    ) -> DelegationTracingDataHost<A> {
        assert_eq!(circuit_type, DelegationCircuitType::KeccakChi5);
        DelegationTracingDataHost::KeccakChi5(trace)
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
