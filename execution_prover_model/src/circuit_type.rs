use crate::upstream::{
    inits_and_teardowns, AddSubLuiAuipcMopCircuit, BabyBearField, BigIntDelegationCircuit,
    Blake2sGFunctionDelegationCircuit, Blake2sWithCompressionDelegationCircuit,
    JumpBranchSltCircuit, KeccakChi5DelegationCircuit, KeccakColumnParityDelegationCircuit,
    KeccakSpecial5DelegationCircuit, KeccakThetaRhoDelegationCircuit, LoadStoreSubwordOnlyCircuit,
    LoadStoreWordOnlyCircuit, ProofProfile, ShiftBinaryCircuit, UnifiedReducedMachineCircuit,
    UnifiedReducedMachineCircuit2_22, UnsignedMulDivCircuit,
};
use crate::MachineType;
use circuit_common::{DelegationCircuit, ProverConfig, RiscVCycleCircuit, SecurityLevel};
use common_constants::circuit_families::{
    ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX, INITS_AND_TEARDOWNS_FORMAL_CIRCUIT_FAMILY_IDX,
    JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX, LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX,
    LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX, MUL_DIV_CIRCUIT_FAMILY_IDX,
    REDUCED_MACHINE_CIRCUIT_FAMILY_IDX, SHIFT_BINARY_CIRCUIT_FAMILY_IDX,
};
use common_constants::delegation_types::keccak_f1600::*;
use common_constants::delegation_types::{
    bigint_with_control::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER,
    blake2s_g_function::BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER,
    blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER,
    keccak_special5::KECCAK_SPECIAL5_CSR_REGISTER,
};
use common_constants::rom::{RomGeometry, L1_WRAP_ROM, REGULAR_ROM};

// log2 trace lengths of the circuits, usable in `const` contexts. The source of
// truth is each circuit's `prover_config` (`trace_len_log2`); the
// `trace_lengths_match_prover_configs` test below guards these literals
// against it.
const BIGINT_DOMAIN_SIZE_LOG2: u32 = 22;
const BLAKE_DOMAIN_SIZE_LOG2: u32 = 20;
const BLAKE_G_FUNCTION_DOMAIN_SIZE_LOG2: u32 = 22;
const KECCAK_DOMAIN_SIZE_LOG2: u32 = 22;

const ADD_SUB_DOMAIN_SIZE_LOG2: u32 = 24;
const UNIFIED_REDUCED_MACHINE_DOMAIN_SIZE_LOG2: u32 = 23;
const JUMP_BRANCH_DOMAIN_SIZE_LOG2: u32 = 24;
const SHIFT_BINARY_DOMAIN_SIZE_LOG2: u32 = 24;
const LOAD_STORE_WORD_DOMAIN_SIZE_LOG2: u32 = 24;
const LOAD_STORE_SUBWORD_DOMAIN_SIZE_LOG2: u32 = 24;
const UNIFIED_REDUCED_MACHINE_2_22_DOMAIN_SIZE_LOG2: u32 = 22;
const INITS_AND_TEARDOWNS_DOMAIN_SIZE_LOG2: u32 = inits_and_teardowns::TRACE_LEN_LOG2;
const INITS_AND_TEARDOWNS_NUM_SETS: usize = inits_and_teardowns::NUM_INIT_AND_TEARDOWN_SETS;
// One inline i&t "pair" allocates two sets (`allocate_inline_inits_and_teardowns_sets`).
const UNIFIED_REDUCED_MACHINE_NUM_INIT_AND_TEARDOWN_SETS: usize =
    2 * <UnifiedReducedMachineCircuit as RiscVCycleCircuit<BabyBearField, true>>::NUM_INIT_AND_TEARDOWN_PAIRS;
const MUL_DIV_UNSIGNED_DOMAIN_SIZE_LOG2: u32 = 23;
const UNIFIED_REDUCED_MACHINE_2_22_NUM_INIT_AND_TEARDOWN_SETS: usize =
    2 * <UnifiedReducedMachineCircuit2_22 as RiscVCycleCircuit<BabyBearField, true>>::NUM_INIT_AND_TEARDOWN_PAIRS;

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CircuitType {
    Delegation(DelegationCircuitType),
    Unrolled(UnrolledCircuitType),
    /// The 2^21 Proth120 L1 wrap over the 512 KiB wrap ROM.
    L1Wrap21,
}

impl CircuitType {
    /// The prover config of this circuit at `level`, straight from the circuit
    /// definition (`DelegationCircuit::prover_config` /
    /// `RiscVCycleCircuit::prover_config`): the single source of the proving
    /// and verification geometry (trace length, schedules, packing).
    pub fn prover_config(&self, level: SecurityLevel) -> ProverConfig {
        match self {
            Self::Delegation(delegation_type) => delegation_type.prover_config(level),
            Self::Unrolled(unrolled_type) => unrolled_type.prover_config(level),
            Self::L1Wrap21 => {
                ProofProfile::L1Wrap.prover_config(self.get_domain_size_log2() as usize, level)
            }
        }
    }

    #[inline(always)]
    pub const fn get_domain_size(&self) -> usize {
        1 << self.get_domain_size_log2()
    }

    #[inline(always)]
    pub const fn get_domain_size_log2(&self) -> u32 {
        match self {
            Self::Delegation(delegation_type) => delegation_type.get_domain_size_log2(),
            Self::Unrolled(unrolled_type) => unrolled_type.get_domain_size_log2(),
            Self::L1Wrap21 => 21,
        }
    }

    #[inline(always)]
    pub const fn get_family_idx(&self) -> u8 {
        match self {
            Self::Delegation(_) => panic!("delegation circuits do not have a circuit family idx"),
            Self::Unrolled(unrolled_type) => unrolled_type.get_family_idx(),
            Self::L1Wrap21 => REDUCED_MACHINE_CIRCUIT_FAMILY_IDX,
        }
    }

    pub const fn get_num_inits_and_teardowns_sets(&self) -> usize {
        match self {
            Self::Unrolled(circuit) => circuit.get_num_inits_and_teardowns_sets(),
            Self::L1Wrap21 => 2,
            Self::Delegation(_) => panic!("delegation circuits do not carry inits and teardowns"),
        }
    }

    pub const fn is_l1_wrap(&self) -> bool {
        matches!(self, Self::L1Wrap21)
    }

    /// The ROM geometry the circuit's load/store and decoder tables assume.
    pub const fn rom(&self) -> RomGeometry {
        match self {
            Self::L1Wrap21 => L1_WRAP_ROM,
            Self::Delegation(_) | Self::Unrolled(_) => REGULAR_ROM,
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
    KeccakColumnParity = KECCAK_COLUMN_PARITY_CSR_REGISTER,
    KeccakThetaRho = KECCAK_THETA_RHO_CSR_REGISTER,
    KeccakChi5 = KECCAK_CHI5_CSR_REGISTER,
}

impl DelegationCircuitType {
    #[inline(always)]
    pub const fn get_delegation_type_id(&self) -> u16 {
        *self as u16
    }

    #[inline(always)]
    pub const fn get_domain_size(&self) -> usize {
        1 << self.get_domain_size_log2()
    }

    #[inline(always)]
    pub const fn get_domain_size_log2(&self) -> u32 {
        match self {
            Self::BigIntWithControl => BIGINT_DOMAIN_SIZE_LOG2,
            Self::Blake2WithCompression => BLAKE_DOMAIN_SIZE_LOG2,
            Self::Blake2GFunction => BLAKE_G_FUNCTION_DOMAIN_SIZE_LOG2,
            Self::KeccakSpecial5 => KECCAK_DOMAIN_SIZE_LOG2,
            Self::KeccakColumnParity => 22,
            Self::KeccakThetaRho => 22,
            Self::KeccakChi5 => 22,
        }
    }

    /// See [`CircuitType::prover_config`].
    pub fn prover_config(&self, level: SecurityLevel) -> ProverConfig {
        match self {
            Self::BigIntWithControl => {
                <BigIntDelegationCircuit as DelegationCircuit<BabyBearField>>::prover_config(level)
            }
            Self::Blake2WithCompression => {
                <Blake2sWithCompressionDelegationCircuit as DelegationCircuit<BabyBearField>>::prover_config(level)
            }
            Self::Blake2GFunction => {
                <Blake2sGFunctionDelegationCircuit as DelegationCircuit<BabyBearField>>::prover_config(level)
            }
            Self::KeccakSpecial5 => {
                <KeccakSpecial5DelegationCircuit as DelegationCircuit<BabyBearField>>::prover_config(level)
            }
            Self::KeccakColumnParity => {
                <KeccakColumnParityDelegationCircuit as DelegationCircuit<BabyBearField>>::prover_config(level)
            }
            Self::KeccakThetaRho => {
                <KeccakThetaRhoDelegationCircuit as DelegationCircuit<BabyBearField>>::prover_config(level)
            }
            Self::KeccakChi5 => {
                <KeccakChi5DelegationCircuit as DelegationCircuit<BabyBearField>>::prover_config(level)
            }
        }
    }

    pub fn get_all_delegation_types() -> &'static [DelegationCircuitType] {
        &[
            DelegationCircuitType::Blake2WithCompression,
            DelegationCircuitType::BigIntWithControl,
            DelegationCircuitType::KeccakSpecial5,
            DelegationCircuitType::KeccakThetaRho,
            DelegationCircuitType::KeccakColumnParity,
            DelegationCircuitType::KeccakChi5,
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
    fn l1_wrap_identities_carry_their_domain_and_rom() {
        assert_eq!(CircuitType::L1Wrap21.get_domain_size_log2(), 21);
        assert_eq!(CircuitType::L1Wrap21.rom(), L1_WRAP_ROM);
        assert!(CircuitType::L1Wrap21.is_l1_wrap());
        assert_eq!(
            CircuitType::L1Wrap21.get_family_idx(),
            REDUCED_MACHINE_CIRCUIT_FAMILY_IDX
        );
        assert_eq!(CircuitType::L1Wrap21.get_num_inits_and_teardowns_sets(), 2);
        for circuit in [
            CircuitType::Unrolled(UnrolledCircuitType::Unified),
            CircuitType::Unrolled(UnrolledCircuitType::Unified22),
            CircuitType::Delegation(DelegationCircuitType::Blake2WithCompression),
        ] {
            assert!(!circuit.is_l1_wrap());
            assert_eq!(circuit.rom(), REGULAR_ROM);
        }
    }

    #[test]
    fn rejects_unknown_delegation_type_ids() {
        let err = DelegationCircuitType::try_from(u16::MAX).unwrap_err();

        assert_eq!(err.raw, u16::MAX);
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
            KECCAK_COLUMN_PARITY_CSR_REGISTER => Ok(Self::KeccakColumnParity),
            KECCAK_THETA_RHO_CSR_REGISTER => Ok(Self::KeccakThetaRho),
            KECCAK_CHI5_CSR_REGISTER => Ok(Self::KeccakChi5),
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
    /// The 2^23 unified reduced-machine circuit of regular recursion.
    Unified,
    /// The 2^22 unified reduced-machine circuit of the L1 feeder layers:
    /// same family and definition as [`Self::Unified`], distinct geometry
    /// (and so distinct setups, precomputations and proof shape).
    Unified22,
}

impl UnrolledCircuitType {
    /// See [`CircuitType::prover_config`].
    pub fn prover_config(&self, level: SecurityLevel) -> ProverConfig {
        match self {
            Self::InitsAndTeardowns => inits_and_teardowns::prover_config(level),
            Self::Memory(circuit_type) => circuit_type.prover_config(level),
            Self::NonMemory(circuit_type) => circuit_type.prover_config(level),
            Self::Unified => <UnifiedReducedMachineCircuit as RiscVCycleCircuit<
                BabyBearField,
                true,
            >>::prover_config(level),
            Self::Unified22 => <UnifiedReducedMachineCircuit2_22 as RiscVCycleCircuit<
                BabyBearField,
                true,
            >>::prover_config(level),
        }
    }

    #[inline(always)]
    pub const fn get_domain_size(&self) -> usize {
        1 << self.get_domain_size_log2()
    }

    #[inline(always)]
    pub const fn get_domain_size_log2(&self) -> u32 {
        match self {
            Self::InitsAndTeardowns => INITS_AND_TEARDOWNS_DOMAIN_SIZE_LOG2,
            Self::Memory(circuit_type) => circuit_type.get_domain_size_log2(),
            Self::NonMemory(circuit_type) => circuit_type.get_domain_size_log2(),
            Self::Unified => UNIFIED_REDUCED_MACHINE_DOMAIN_SIZE_LOG2,
            Self::Unified22 => UNIFIED_REDUCED_MACHINE_2_22_DOMAIN_SIZE_LOG2,
        }
    }

    #[inline(always)]
    pub const fn get_family_idx(&self) -> u8 {
        match self {
            Self::InitsAndTeardowns => INITS_AND_TEARDOWNS_FORMAL_CIRCUIT_FAMILY_IDX,
            Self::Memory(circuit_type) => circuit_type.get_family_idx(),
            Self::NonMemory(circuit_type) => circuit_type.get_family_idx(),
            Self::Unified | Self::Unified22 => REDUCED_MACHINE_CIRCUIT_FAMILY_IDX,
        }
    }

    /// Length of this circuit's `memory_layout.teardown_sets`. Each set covers
    /// one `get_domain_size()`-word address window.
    #[inline(always)]
    pub const fn get_num_inits_and_teardowns_sets(&self) -> usize {
        match self {
            Self::InitsAndTeardowns => INITS_AND_TEARDOWNS_NUM_SETS,
            Self::Memory(_) | Self::NonMemory(_) => 0,
            Self::Unified => UNIFIED_REDUCED_MACHINE_NUM_INIT_AND_TEARDOWN_SETS,
            Self::Unified22 => UNIFIED_REDUCED_MACHINE_2_22_NUM_INIT_AND_TEARDOWN_SETS,
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
    /// See [`CircuitType::prover_config`].
    pub fn prover_config(&self, level: SecurityLevel) -> ProverConfig {
        match self {
            Self::LoadStoreSubwordOnly => <LoadStoreSubwordOnlyCircuit as RiscVCycleCircuit<
                BabyBearField,
                true,
            >>::prover_config(level),
            Self::LoadStoreWordOnly => <LoadStoreWordOnlyCircuit as RiscVCycleCircuit<
                BabyBearField,
                true,
            >>::prover_config(level),
        }
    }

    #[inline(always)]
    pub const fn get_domain_size(&self) -> usize {
        1 << self.get_domain_size_log2()
    }

    #[inline(always)]
    pub const fn get_domain_size_log2(&self) -> u32 {
        match self {
            Self::LoadStoreSubwordOnly => LOAD_STORE_SUBWORD_DOMAIN_SIZE_LOG2,
            Self::LoadStoreWordOnly => LOAD_STORE_WORD_DOMAIN_SIZE_LOG2,
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
    ShiftBinary,
}

impl UnrolledNonMemoryCircuitType {
    /// See [`CircuitType::prover_config`].
    pub fn prover_config(&self, level: SecurityLevel) -> ProverConfig {
        match self {
            Self::AddSubLuiAuipcMop => <AddSubLuiAuipcMopCircuit as RiscVCycleCircuit<
                BabyBearField,
                false,
            >>::prover_config(level),
            Self::JumpBranchSlt => <JumpBranchSltCircuit as RiscVCycleCircuit<
                BabyBearField,
                false,
            >>::prover_config(level),
            Self::MulDivUnsigned => <UnsignedMulDivCircuit as RiscVCycleCircuit<
                BabyBearField,
                false,
            >>::prover_config(level),
            Self::ShiftBinary => {
                <ShiftBinaryCircuit as RiscVCycleCircuit<BabyBearField, false>>::prover_config(
                    level,
                )
            }
        }
    }

    #[inline(always)]
    pub const fn get_domain_size(&self) -> usize {
        1 << self.get_domain_size_log2()
    }

    #[inline(always)]
    pub const fn get_domain_size_log2(&self) -> u32 {
        match self {
            Self::AddSubLuiAuipcMop => ADD_SUB_DOMAIN_SIZE_LOG2,
            Self::JumpBranchSlt => JUMP_BRANCH_DOMAIN_SIZE_LOG2,
            Self::MulDivUnsigned => MUL_DIV_UNSIGNED_DOMAIN_SIZE_LOG2,
            Self::ShiftBinary => SHIFT_BINARY_DOMAIN_SIZE_LOG2,
        }
    }

    #[inline(always)]
    pub const fn get_family_idx(&self) -> u8 {
        match self {
            Self::AddSubLuiAuipcMop => ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX,
            Self::JumpBranchSlt => JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX,
            Self::MulDivUnsigned => MUL_DIV_CIRCUIT_FAMILY_IDX,
            Self::ShiftBinary => SHIFT_BINARY_CIRCUIT_FAMILY_IDX,
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
                Self::ShiftBinary,
            ],
            MachineType::Reduced => &[
                Self::AddSubLuiAuipcMop,
                Self::JumpBranchSlt,
                Self::ShiftBinary,
            ],
        }
    }

    /// Final-PC value substituted into padding rows of the memory columns.
    /// Must equal the `PC_STEP` the CPU setups pass to
    /// `make_setup_for_non_mem_circuit` for every family. The GPU test fixtures
    /// anchor their CPU oracles to `common_constants::PC_STEP` directly — NOT
    /// to this accessor — so a stale arm here diverges from the fixtures and
    /// the parity suite catches it. Keep that separation: threading this
    /// accessor into a CPU oracle makes the GPU-vs-CPU comparison tautological
    /// (fixtures once did exactly that, and a stale JumpBranchSlt value stayed
    /// invisible until the gpu_program_prover base-layer verify e2e caught it).
    #[inline(always)]
    pub const fn get_default_pc_value_in_padding(&self) -> u32 {
        match self {
            Self::AddSubLuiAuipcMop => common_constants::PC_STEP as u32,
            Self::JumpBranchSlt => common_constants::PC_STEP as u32,
            Self::MulDivUnsigned => common_constants::PC_STEP as u32,
            Self::ShiftBinary => common_constants::PC_STEP as u32,
        }
    }
}

#[cfg(test)]
mod prover_config_tests {
    use super::*;

    /// The `const` trace-length literals above must agree with every circuit's
    /// `prover_config` (the source of truth) at every security level.
    #[test]
    fn trace_lengths_match_prover_configs() {
        let all: Vec<CircuitType> = [
            DelegationCircuitType::BigIntWithControl,
            DelegationCircuitType::Blake2WithCompression,
            DelegationCircuitType::Blake2GFunction,
            DelegationCircuitType::KeccakSpecial5,
            DelegationCircuitType::KeccakColumnParity,
            DelegationCircuitType::KeccakThetaRho,
            DelegationCircuitType::KeccakChi5,
        ]
        .into_iter()
        .map(CircuitType::Delegation)
        .chain(
            [
                UnrolledCircuitType::InitsAndTeardowns,
                UnrolledCircuitType::Unified,
                UnrolledCircuitType::Unified22,
                UnrolledCircuitType::Memory(UnrolledMemoryCircuitType::LoadStoreSubwordOnly),
                UnrolledCircuitType::Memory(UnrolledMemoryCircuitType::LoadStoreWordOnly),
                UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop),
                UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::JumpBranchSlt),
                UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::MulDivUnsigned),
                UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::ShiftBinary),
            ]
            .into_iter()
            .map(CircuitType::Unrolled),
        )
        .collect();
        for circuit_type in all {
            for &level in SecurityLevel::ALL {
                assert_eq!(
                    circuit_type.get_domain_size_log2() as usize,
                    circuit_type.prover_config(level).trace_len_log2,
                    "{circuit_type:?} at {level:?}"
                );
            }
        }
    }
}
