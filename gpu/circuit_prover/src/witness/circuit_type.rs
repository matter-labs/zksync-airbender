use crate::primitives::machine_type::MachineType;
use crate::upstream::{
    inits_and_teardowns, AddSubLuiAuipcMopCircuit, BabyBearField, BigIntDelegationCircuit,
    Blake2sGFunctionDelegationCircuit, Blake2sWithCompressionDelegationCircuit,
    JumpBranchSltCircuit, KeccakSpecial5DelegationCircuit, LoadStoreSubwordOnlyCircuit,
    LoadStoreWordOnlyCircuit, ShiftBinaryCircuit, UnsignedMulDivCircuit,
};
use circuit_common::{DelegationCircuit, RiscVCycleCircuit};
use common_constants::circuit_families::{
    ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX, INITS_AND_TEARDOWNS_FORMAL_CIRCUIT_FAMILY_IDX,
    JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX, LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX,
    LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX, MUL_DIV_CIRCUIT_FAMILY_IDX,
    REDUCED_MACHINE_CIRCUIT_FAMILY_IDX, SHIFT_BINARY_CIRCUIT_FAMILY_IDX,
};
use common_constants::delegation_types::{
    bigint_with_control::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER,
    blake2s_g_function::BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER,
    blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER,
    keccak_special5::KECCAK_SPECIAL5_CSR_REGISTER,
};

const BIGINT_DOMAIN_SIZE: usize =
    1 << <BigIntDelegationCircuit as DelegationCircuit<BabyBearField>>::DOMAIN_SIZE_LOG2;
const BLAKE_DOMAIN_SIZE: usize = 1 << <Blake2sWithCompressionDelegationCircuit as
    DelegationCircuit<BabyBearField>>::DOMAIN_SIZE_LOG2;
const BLAKE_G_FUNCTION_DOMAIN_SIZE: usize =
    1 << <Blake2sGFunctionDelegationCircuit as DelegationCircuit<BabyBearField>>::DOMAIN_SIZE_LOG2;
const KECCAK_DOMAIN_SIZE: usize =
    1 << <KeccakSpecial5DelegationCircuit as DelegationCircuit<BabyBearField>>::DOMAIN_SIZE_LOG2;

const ADD_SUB_DOMAIN_SIZE: usize =
    1 << <AddSubLuiAuipcMopCircuit as RiscVCycleCircuit<BabyBearField, false>>::DOMAIN_SIZE_LOG2;
// The unified reduced-machine circuit is compiled at trace_len_log2 = 24
// (cs/src/gkr_circuits/unified_reduced_machine/circuit.rs:604; layout JSON
// trace_len = 16777216 = 2^24). There is no live upstream DOMAIN_SIZE_LOG2 trait
// const to mirror here: the circuit_defs unified circuit type is commented out of
// `setups` and is stale at TRACE_LEN_LOG2 = 23, while the PR #305 CPU truth is 24.
const UNIFIED_REDUCED_MACHINE_DOMAIN_SIZE: usize = 1 << 24;
const JUMP_BRANCH_DOMAIN_SIZE: usize =
    1 << <JumpBranchSltCircuit as RiscVCycleCircuit<BabyBearField, false>>::DOMAIN_SIZE_LOG2;
const SHIFT_BINARY_DOMAIN_SIZE: usize =
    1 << <ShiftBinaryCircuit as RiscVCycleCircuit<BabyBearField, false>>::DOMAIN_SIZE_LOG2;
const LOAD_STORE_WORD_DOMAIN_SIZE: usize =
    1 << <LoadStoreWordOnlyCircuit as RiscVCycleCircuit<BabyBearField, true>>::DOMAIN_SIZE_LOG2;
const LOAD_STORE_SUBWORD_DOMAIN_SIZE: usize =
    1 << <LoadStoreSubwordOnlyCircuit as RiscVCycleCircuit<BabyBearField, true>>::DOMAIN_SIZE_LOG2;
const INITS_AND_TEARDOWNS_DOMAIN_SIZE: usize = 1 << inits_and_teardowns::TRACE_LEN_LOG2;
const MUL_DIV_UNSIGNED_DOMAIN_SIZE: usize =
    1 << <UnsignedMulDivCircuit as RiscVCycleCircuit<BabyBearField, false>>::DOMAIN_SIZE_LOG2;

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CircuitType {
    Delegation(DelegationCircuitType),
    Unrolled(UnrolledCircuitType),
}

impl CircuitType {
    #[inline(always)]
    pub const fn get_domain_size(&self) -> usize {
        match self {
            Self::Delegation(delegation_type) => delegation_type.get_domain_size(),
            Self::Unrolled(unrolled_type) => unrolled_type.get_domain_size(),
        }
    }

    #[inline(always)]
    pub const fn get_family_idx(&self) -> u8 {
        match self {
            Self::Delegation(_) => panic!("delegation circuits do not have a circuit family idx"),
            Self::Unrolled(unrolled_type) => unrolled_type.get_family_idx(),
        }
    }
}

#[repr(u32)]
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum DelegationCircuitType {
    BigIntWithControl = BIGINT_OPS_WITH_CONTROL_CSR_REGISTER,
    Blake2WithCompression = BLAKE2S_DELEGATION_CSR_REGISTER,
    Blake2GFunction = BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER,
    KeccakSpecial5 = KECCAK_SPECIAL5_CSR_REGISTER,
}

impl DelegationCircuitType {
    #[inline(always)]
    pub const fn get_delegation_type_id(&self) -> u16 {
        *self as u16
    }

    #[inline(always)]
    pub const fn get_domain_size(&self) -> usize {
        match self {
            Self::BigIntWithControl => BIGINT_DOMAIN_SIZE,
            Self::Blake2WithCompression => BLAKE_DOMAIN_SIZE,
            Self::Blake2GFunction => BLAKE_G_FUNCTION_DOMAIN_SIZE,
            Self::KeccakSpecial5 => KECCAK_DOMAIN_SIZE,
        }
    }

    pub fn get_all_delegation_types() -> &'static [DelegationCircuitType] {
        &[
            DelegationCircuitType::BigIntWithControl,
            DelegationCircuitType::Blake2WithCompression,
            DelegationCircuitType::Blake2GFunction,
            DelegationCircuitType::KeccakSpecial5,
        ]
    }

    pub fn get_delegation_types_for_machine_type(
        machine_type: MachineType,
    ) -> &'static [DelegationCircuitType] {
        match machine_type {
            MachineType::Full => Self::get_all_delegation_types(),
            MachineType::FullUnsigned => Self::get_all_delegation_types(),
            MachineType::Reduced => &[DelegationCircuitType::Blake2WithCompression],
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InvalidDelegationCircuitType {
    pub(crate) raw: u16,
}

impl std::fmt::Display for InvalidDelegationCircuitType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "unknown delegation type {}", self.raw)
    }
}

impl std::error::Error for InvalidDelegationCircuitType {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_unknown_delegation_type_ids() {
        let err = DelegationCircuitType::try_from(u16::MAX).unwrap_err();

        assert_eq!(err.raw, u16::MAX);
    }

    #[test]
    fn unified_domain_size_is_two_pow_24() {
        assert_eq!(
            UnrolledCircuitType::Unified.get_domain_size(),
            1 << 24,
            "unified reduced-machine domain size must match the CPU trace_len_log2 = 24"
        );
    }
}

impl TryFrom<u16> for DelegationCircuitType {
    type Error = InvalidDelegationCircuitType;

    #[inline(always)]
    fn try_from(delegation_type: u16) -> Result<Self, Self::Error> {
        match delegation_type as u32 {
            BIGINT_OPS_WITH_CONTROL_CSR_REGISTER => Ok(Self::BigIntWithControl),
            BLAKE2S_DELEGATION_CSR_REGISTER => Ok(Self::Blake2WithCompression),
            BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER => Ok(Self::Blake2GFunction),
            KECCAK_SPECIAL5_CSR_REGISTER => Ok(Self::KeccakSpecial5),
            _ => Err(InvalidDelegationCircuitType {
                raw: delegation_type,
            }),
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum UnrolledCircuitType {
    InitsAndTeardowns,
    Memory(UnrolledMemoryCircuitType),
    NonMemory(UnrolledNonMemoryCircuitType),
    Unified,
}

impl UnrolledCircuitType {
    #[inline(always)]
    pub const fn get_domain_size(&self) -> usize {
        match self {
            Self::InitsAndTeardowns => INITS_AND_TEARDOWNS_DOMAIN_SIZE,
            Self::Memory(circuit_type) => circuit_type.get_domain_size(),
            Self::NonMemory(circuit_type) => circuit_type.get_domain_size(),
            Self::Unified => UNIFIED_REDUCED_MACHINE_DOMAIN_SIZE,
        }
    }

    #[inline(always)]
    pub const fn get_family_idx(&self) -> u8 {
        match self {
            Self::InitsAndTeardowns => INITS_AND_TEARDOWNS_FORMAL_CIRCUIT_FAMILY_IDX,
            Self::Memory(circuit_type) => circuit_type.get_family_idx(),
            Self::NonMemory(circuit_type) => circuit_type.get_family_idx(),
            Self::Unified => REDUCED_MACHINE_CIRCUIT_FAMILY_IDX,
        }
    }
}

#[repr(u32)]
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum UnrolledMemoryCircuitType {
    LoadStoreSubwordOnly,
    LoadStoreWordOnly,
}

impl UnrolledMemoryCircuitType {
    #[inline(always)]
    pub const fn get_domain_size(&self) -> usize {
        match self {
            Self::LoadStoreSubwordOnly => LOAD_STORE_SUBWORD_DOMAIN_SIZE,
            Self::LoadStoreWordOnly => LOAD_STORE_WORD_DOMAIN_SIZE,
        }
    }

    #[inline(always)]
    pub const fn get_family_idx(&self) -> u8 {
        match self {
            Self::LoadStoreSubwordOnly => LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX,
            Self::LoadStoreWordOnly => LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX,
        }
    }

    pub fn get_circuit_types_for_machine_type(
        machine_type: MachineType,
    ) -> &'static [UnrolledMemoryCircuitType] {
        match machine_type {
            MachineType::Full => &[Self::LoadStoreSubwordOnly, Self::LoadStoreWordOnly],
            MachineType::FullUnsigned => &[Self::LoadStoreSubwordOnly, Self::LoadStoreWordOnly],
            MachineType::Reduced => &[Self::LoadStoreWordOnly],
        }
    }
}

#[repr(u32)]
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum UnrolledNonMemoryCircuitType {
    AddSubLuiAuipcMop,
    JumpBranchSlt,
    MulDivUnsigned,
    ShiftBinaryCsr,
}

impl UnrolledNonMemoryCircuitType {
    #[inline(always)]
    pub const fn get_domain_size(&self) -> usize {
        match self {
            Self::AddSubLuiAuipcMop => ADD_SUB_DOMAIN_SIZE,
            Self::JumpBranchSlt => JUMP_BRANCH_DOMAIN_SIZE,
            Self::MulDivUnsigned => MUL_DIV_UNSIGNED_DOMAIN_SIZE,
            Self::ShiftBinaryCsr => SHIFT_BINARY_DOMAIN_SIZE,
        }
    }

    #[inline(always)]
    pub const fn get_family_idx(&self) -> u8 {
        match self {
            Self::AddSubLuiAuipcMop => ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX,
            Self::JumpBranchSlt => JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX,
            Self::MulDivUnsigned => MUL_DIV_CIRCUIT_FAMILY_IDX,
            Self::ShiftBinaryCsr => SHIFT_BINARY_CIRCUIT_FAMILY_IDX,
        }
    }

    pub fn get_circuit_types_for_machine_type(
        machine_type: MachineType,
    ) -> &'static [UnrolledNonMemoryCircuitType] {
        match machine_type {
            MachineType::Full | MachineType::FullUnsigned => &[
                Self::AddSubLuiAuipcMop,
                Self::JumpBranchSlt,
                Self::MulDivUnsigned,
                Self::ShiftBinaryCsr,
            ],
            MachineType::Reduced => &[
                Self::AddSubLuiAuipcMop,
                Self::JumpBranchSlt,
                Self::ShiftBinaryCsr,
            ],
        }
    }

    #[inline(always)]
    pub const fn get_default_pc_value_in_padding(&self) -> u32 {
        match self {
            Self::AddSubLuiAuipcMop => 4,
            Self::JumpBranchSlt => 0,
            Self::MulDivUnsigned => 4,
            Self::ShiftBinaryCsr => 4,
        }
    }
}
