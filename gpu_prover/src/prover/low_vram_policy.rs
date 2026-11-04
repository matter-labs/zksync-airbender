use super::memory_policy::MemoryPolicy;
use super::trace_holder::CosetsCacheMode;
use crate::circuit_type::{
    CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
    UnrolledNonMemoryCircuitType,
};

pub(crate) const fn low_vram_policy(circuit: CircuitType) -> MemoryPolicy {
    use CosetsCacheMode::{CacheFull as Full, CacheSingle as Single};

    match circuit {
        CircuitType::Delegation(DelegationCircuitType::BigIntWithControl) => {
            MemoryPolicy::new(Full, Full, Full, Full)
        }
        CircuitType::Delegation(DelegationCircuitType::Blake2WithCompression) => {
            MemoryPolicy::new(Full, Full, Full, Full)
        }
        CircuitType::Delegation(DelegationCircuitType::KeccakSpecial5) => {
            MemoryPolicy::new(Full, Full, Single, Full)
        }
        CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns) => {
            MemoryPolicy::new(Full, Single, Single, Full)
        }
        CircuitType::Unrolled(UnrolledCircuitType::Memory(
            UnrolledMemoryCircuitType::LoadStoreSubwordOnly,
        )) => MemoryPolicy::new(Single, Full, Full, Single),
        CircuitType::Unrolled(UnrolledCircuitType::Memory(
            UnrolledMemoryCircuitType::LoadStoreWordOnly,
        )) => MemoryPolicy::new(Full, Single, Single, Full),
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
        )) => MemoryPolicy::new(Full, Full, Single, Full),
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::JumpBranchSlt,
        )) => MemoryPolicy::new(Single, Single, Single, Full),
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::MulDiv,
        )) => MemoryPolicy::new(Full, Full, Full, Full),
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::MulDivUnsigned,
        )) => MemoryPolicy::new(Full, Full, Full, Full),
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::ShiftBinaryCsr,
        )) => MemoryPolicy::new(Single, Single, Single, Full),
        CircuitType::Unrolled(UnrolledCircuitType::Unified) => {
            MemoryPolicy::new(Single, Full, Full, Full)
        }
    }
}
