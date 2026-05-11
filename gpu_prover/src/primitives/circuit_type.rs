use crate::primitives::machine_type::MachineType;
use circuit_common::{DelegationCircuit, RiscVCycleCircuit};
use common_constants::circuit_families::{
    ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX, INITS_AND_TEARDOWNS_FORMAL_CIRCUIT_FAMILY_IDX,
    JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX, LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX,
    LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX, MUL_DIV_CIRCUIT_FAMILY_IDX,
    REDUCED_MACHINE_CIRCUIT_FAMILY_IDX, SHIFT_BINARY_CIRCUIT_FAMILY_IDX,
};
use common_constants::delegation_types::{
    bigint_with_control::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER,
    blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER,
    keccak_special5::KECCAK_SPECIAL5_CSR_REGISTER,
};
use common_constants::NON_DETERMINISM_CSR;
use field::baby_bear::base::BabyBearField;
use prover::definitions::{SecurityLevel, OPTIMAL_FOLDING_PROPERTIES};
use prover::gkr::prover::WhirSchedule;
use prover::gkr::prover_config::ProverConfig;
use riscv_transpiler::cycle::{IMStandardIsaConfigUnsignedMulDivOnly, MachineConfig};
use setups::{
    inits_and_teardowns, AddSubLuiAuipcMopCircuit, BigIntDelegationCircuit,
    Blake2sWithCompressionDelegationCircuit, JumpBranchSltCircuit, KeccakSpecial5DelegationCircuit,
    LoadStoreSubwordOnlyCircuit, LoadStoreWordOnlyCircuit, ShiftBinaryCircuit,
    UnsignedMulDivCircuit,
};

const DEFAULT_LDE_FACTOR: usize = 2;
const DEFAULT_LDE_SOURCE_COSETS: &[usize] = &[0, 1];

const BIGINT_DOMAIN_SIZE: usize =
    1 << <BigIntDelegationCircuit as DelegationCircuit<BabyBearField>>::DOMAIN_SIZE_LOG2;
const BLAKE_DOMAIN_SIZE: usize = 1 << <Blake2sWithCompressionDelegationCircuit as
    DelegationCircuit<BabyBearField>>::DOMAIN_SIZE_LOG2;
const KECCAK_DOMAIN_SIZE: usize =
    1 << <KeccakSpecial5DelegationCircuit as DelegationCircuit<BabyBearField>>::DOMAIN_SIZE_LOG2;

const ADD_SUB_DOMAIN_SIZE: usize =
    1 << <AddSubLuiAuipcMopCircuit as RiscVCycleCircuit<BabyBearField, false>>::DOMAIN_SIZE_LOG2;
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

const SHIFT_BINARY_ALLOWED_DELEGATION_CSRS: &[u32] =
    IMStandardIsaConfigUnsignedMulDivOnly::ALLOWED_DELEGATION_CSRS;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct ProofSecurityConfig {
    pub lookup_pow_bits: u32,
    pub quotient_alpha_pow_bits: u32,
    pub quotient_z_pow_bits: u32,
    pub deep_poly_alpha_pow_bits: u32,
    pub foldings_pow_bits: Vec<u32>,
    pub fri_queries_pow_bits: u32,
    pub num_queries: usize,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CircuitType {
    Delegation(DelegationCircuitType),
    Unrolled(UnrolledCircuitType),
}

impl CircuitType {
    #[inline(always)]
    pub fn from_delegation_type(delegation_type: u16) -> Self {
        Self::Delegation(delegation_type.into())
    }

    #[inline(always)]
    pub const fn as_delegation(&self) -> Option<DelegationCircuitType> {
        match self {
            Self::Delegation(circuit_type) => Some(*circuit_type),
            _ => None,
        }
    }

    #[inline(always)]
    pub const fn as_unrolled(&self) -> Option<UnrolledCircuitType> {
        match self {
            Self::Unrolled(circuit_type) => Some(*circuit_type),
            _ => None,
        }
    }

    #[inline(always)]
    pub const fn get_domain_size(&self) -> usize {
        match self {
            Self::Delegation(delegation_type) => delegation_type.get_domain_size(),
            Self::Unrolled(unrolled_type) => unrolled_type.get_domain_size(),
        }
    }

    #[inline(always)]
    pub const fn get_lde_factor(&self) -> usize {
        match self {
            Self::Delegation(delegation_type) => delegation_type.get_lde_factor(),
            Self::Unrolled(unrolled_type) => unrolled_type.get_lde_factor(),
        }
    }

    #[inline(always)]
    pub const fn get_lde_source_cosets(&self) -> &'static [usize] {
        match self {
            Self::Delegation(delegation_type) => delegation_type.get_lde_source_cosets(),
            Self::Unrolled(unrolled_type) => unrolled_type.get_lde_source_cosets(),
        }
    }

    #[inline(always)]
    pub const fn get_tree_cap_size(&self) -> usize {
        let domain_size = self.get_domain_size();
        get_tree_cap_size_for_domain_size(domain_size)
        // match self {
        //     Self::Delegation(delegation_type) => delegation_type.get_tree_cap_size(),
        //     Self::Unrolled(unrolled_type) => unrolled_type.get_tree_cap_size(),
        // }
    }

    /// Canonical `ProverConfig` for this circuit at the requested security
    /// level. Mirrors CPU's `config_for_security_level_under_pessimistic_conjecture`
    /// for the schedule-independent fields, but uses the
    /// `default_for_tests_80_bits_*` schedules that GPU stage1 and WHIR are
    /// tuned for. Only `Sec80` is supported on GPU today.
    pub fn prover_config(&self, security_level: SecurityLevel) -> ProverConfig {
        match security_level {
            SecurityLevel::Sec80 => self.prover_config_sec80(),
            SecurityLevel::Sec100 => unimplemented!("Sec100 not supported on GPU yet"),
        }
    }

    fn prover_config_sec80(&self) -> ProverConfig {
        let domain_size_log_2 = self.get_domain_size().trailing_zeros();
        let whir_schedule = match domain_size_log_2 {
            20 => WhirSchedule::default_for_tests_80_bits_20(),
            22 => WhirSchedule::default_for_tests_80_bits_22(),
            23 | 24 => WhirSchedule::default_for_tests_80_bits_24(),
            other => panic!(
                "no Sec80 ProverConfig for circuit {self:?} (domain_size_log_2 = {other})"
            ),
        };
        ProverConfig {
            lde_factor: 2,
            cap_size: 16,
            base_oracles_values_per_leaf: 2,
            lookup_challenges_pow_bits: 0,
            sumcheck_explicit_output_size_log_2: 4,
            batched_proximity_check_challenge_pow_bits: 0,
            whir_schedule,
        }
    }

    #[inline(always)]
    pub const fn get_family_idx(&self) -> u8 {
        match self {
            Self::Delegation(_) => panic!("delegation circuits do not have a circuit family idx"),
            Self::Unrolled(unrolled_type) => unrolled_type.get_family_idx(),
        }
    }

    pub fn get_security_config(&self) -> ProofSecurityConfig {
        match self {
            Self::Delegation(delegation_type) => delegation_type.get_security_config(),
            Self::Unrolled(unrolled_type) => unrolled_type.get_security_config(),
        }
    }
}

#[repr(u32)]
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum DelegationCircuitType {
    BigIntWithControl = BIGINT_OPS_WITH_CONTROL_CSR_REGISTER,
    Blake2WithCompression = BLAKE2S_DELEGATION_CSR_REGISTER,
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
            Self::KeccakSpecial5 => KECCAK_DOMAIN_SIZE,
        }
    }

    #[inline(always)]
    pub const fn get_lde_factor(&self) -> usize {
        DEFAULT_LDE_FACTOR
    }

    #[inline(always)]
    pub const fn get_lde_source_cosets(&self) -> &'static [usize] {
        DEFAULT_LDE_SOURCE_COSETS
    }

    #[inline(always)]
    pub const fn get_tree_cap_size(&self) -> usize {
        let domain_size = self.get_domain_size();
        get_tree_cap_size_for_domain_size(domain_size)
        // match self {
        //     Self::BigIntWithControl => bigint_with_control::TREE_CAP_SIZE,
        //     Self::Blake2WithCompression => blake2_with_compression::TREE_CAP_SIZE,
        //     Self::KeccakSpecial5 => keccak_special5::TREE_CAP_SIZE,
        // }
    }

    pub fn get_all_delegation_types() -> &'static [DelegationCircuitType] {
        &[
            DelegationCircuitType::BigIntWithControl,
            DelegationCircuitType::Blake2WithCompression,
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

    pub fn get_security_config(&self) -> ProofSecurityConfig {
        match self {
            Self::BigIntWithControl => get_security_config::<BIGINT_DOMAIN_SIZE>(),
            Self::Blake2WithCompression => get_security_config::<BLAKE_DOMAIN_SIZE>(),
            Self::KeccakSpecial5 => get_security_config::<KECCAK_DOMAIN_SIZE>(),
        }
    }
}

impl From<u16> for DelegationCircuitType {
    #[inline(always)]
    fn from(delegation_type: u16) -> Self {
        match delegation_type as u32 {
            BIGINT_OPS_WITH_CONTROL_CSR_REGISTER => Self::BigIntWithControl,
            BLAKE2S_DELEGATION_CSR_REGISTER => Self::Blake2WithCompression,
            KECCAK_SPECIAL5_CSR_REGISTER => Self::KeccakSpecial5,
            _ => panic!("unknown delegation type {}", delegation_type),
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
    const fn unified_unimplemented() -> ! {
        panic!("Unified circuit metadata is unavailable because Unified execution is unimplemented")
    }

    #[inline(always)]
    pub fn as_memory(&self) -> Option<UnrolledMemoryCircuitType> {
        match self {
            Self::Memory(circuit_type) => Some(*circuit_type),
            _ => None,
        }
    }

    #[inline(always)]
    pub fn as_non_memory(&self) -> Option<UnrolledNonMemoryCircuitType> {
        match self {
            Self::NonMemory(circuit_type) => Some(*circuit_type),
            _ => None,
        }
    }

    #[inline(always)]
    pub const fn get_domain_size(&self) -> usize {
        match self {
            Self::InitsAndTeardowns => INITS_AND_TEARDOWNS_DOMAIN_SIZE,
            Self::Memory(circuit_type) => circuit_type.get_domain_size(),
            Self::NonMemory(circuit_type) => circuit_type.get_domain_size(),
            Self::Unified => Self::unified_unimplemented(),
        }
    }

    #[inline(always)]
    pub const fn get_lde_factor(&self) -> usize {
        match self {
            Self::InitsAndTeardowns => DEFAULT_LDE_FACTOR,
            Self::Memory(circuit_type) => circuit_type.get_lde_factor(),
            Self::NonMemory(circuit_type) => circuit_type.get_lde_factor(),
            Self::Unified => Self::unified_unimplemented(),
        }
    }

    #[inline(always)]
    pub const fn get_lde_source_cosets(&self) -> &'static [usize] {
        match self {
            Self::InitsAndTeardowns => DEFAULT_LDE_SOURCE_COSETS,
            Self::Memory(circuit_type) => circuit_type.get_lde_source_cosets(),
            Self::NonMemory(circuit_type) => circuit_type.get_lde_source_cosets(),
            Self::Unified => Self::unified_unimplemented(),
        }
    }

    #[inline(always)]
    pub const fn get_tree_cap_size(&self) -> usize {
        let domain_size = self.get_domain_size();
        get_tree_cap_size_for_domain_size(domain_size)
        // match self {
        //     Self::InitsAndTeardowns => inits_and_teardowns::TREE_CAP_SIZE,
        //     Self::Memory(circuit_type) => circuit_type.get_tree_cap_size(),
        //     Self::NonMemory(circuit_type) => circuit_type.get_tree_cap_size(),
        //     Self::Unified => unified_reduced_machine::TREE_CAP_SIZE,
        // }
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

    pub const fn get_allowed_delegation_csrs(&self) -> &'static [u32] {
        match self {
            Self::InitsAndTeardowns => &[],
            Self::Memory(_) => &[],
            Self::NonMemory(circuit_type) => circuit_type.get_allowed_delegation_csrs(),
            Self::Unified => Self::unified_unimplemented(),
        }
    }

    pub fn get_allowed_delegation_circuit_types(
        &self,
    ) -> impl Iterator<Item = DelegationCircuitType> {
        self.get_allowed_delegation_csrs()
            .iter()
            .map(|id| DelegationCircuitType::from(*id as u16))
    }

    pub fn get_security_config(&self) -> ProofSecurityConfig {
        match self {
            Self::InitsAndTeardowns => get_security_config::<INITS_AND_TEARDOWNS_DOMAIN_SIZE>(),
            Self::Memory(circuit_type) => circuit_type.get_security_config(),
            Self::NonMemory(circuit_type) => circuit_type.get_security_config(),
            Self::Unified => unimplemented!(
                "Unified security config is unavailable because Unified execution is unimplemented"
            ),
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
    pub const fn get_lde_factor(&self) -> usize {
        DEFAULT_LDE_FACTOR
    }

    #[inline(always)]
    pub const fn get_lde_source_cosets(&self) -> &'static [usize] {
        DEFAULT_LDE_SOURCE_COSETS
    }

    #[inline(always)]
    pub const fn get_tree_cap_size(&self) -> usize {
        match self {
            Self::LoadStoreSubwordOnly => {
                get_tree_cap_size_for_domain_size(LOAD_STORE_SUBWORD_DOMAIN_SIZE)
            }
            Self::LoadStoreWordOnly => {
                get_tree_cap_size_for_domain_size(LOAD_STORE_WORD_DOMAIN_SIZE)
            }
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

    pub fn from_family_idx(family_idx: u8, machine_type: MachineType) -> Self {
        let panic = || {
            panic!("unknown/unsupported unrolled memory family idx {family_idx} for machine type {machine_type:?}")
        };
        match machine_type {
            MachineType::Full => match family_idx {
                LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX => Self::LoadStoreSubwordOnly,
                LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX => Self::LoadStoreWordOnly,
                _ => panic(),
            },
            MachineType::FullUnsigned => match family_idx {
                LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX => Self::LoadStoreSubwordOnly,
                LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX => Self::LoadStoreWordOnly,
                _ => panic(),
            },
            MachineType::Reduced => match family_idx {
                LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX => Self::LoadStoreWordOnly,
                _ => panic(),
            },
        }
    }

    pub fn get_security_config(&self) -> ProofSecurityConfig {
        match self {
            Self::LoadStoreSubwordOnly => get_security_config::<LOAD_STORE_SUBWORD_DOMAIN_SIZE>(),
            Self::LoadStoreWordOnly => get_security_config::<LOAD_STORE_WORD_DOMAIN_SIZE>(),
        }
    }
}

#[repr(u32)]
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum UnrolledNonMemoryCircuitType {
    AddSubLuiAuipcMop,
    JumpBranchSlt,
    MulDiv,
    MulDivUnsigned,
    ShiftBinaryCsr,
}

impl UnrolledNonMemoryCircuitType {
    const fn signed_mul_div_unimplemented() -> ! {
        panic!("signed MulDiv metadata is unavailable because signed MulDiv execution is unimplemented")
    }

    #[inline(always)]
    pub const fn get_domain_size(&self) -> usize {
        match self {
            Self::AddSubLuiAuipcMop => ADD_SUB_DOMAIN_SIZE,
            Self::JumpBranchSlt => JUMP_BRANCH_DOMAIN_SIZE,
            Self::MulDiv => Self::signed_mul_div_unimplemented(),
            Self::MulDivUnsigned => MUL_DIV_UNSIGNED_DOMAIN_SIZE,
            Self::ShiftBinaryCsr => SHIFT_BINARY_DOMAIN_SIZE,
        }
    }

    #[inline(always)]
    pub const fn get_lde_factor(&self) -> usize {
        DEFAULT_LDE_FACTOR
    }

    #[inline(always)]
    pub const fn get_lde_source_cosets(&self) -> &'static [usize] {
        DEFAULT_LDE_SOURCE_COSETS
    }

    #[inline(always)]
    pub const fn get_tree_cap_size(&self) -> usize {
        match self {
            Self::AddSubLuiAuipcMop => get_tree_cap_size_for_domain_size(ADD_SUB_DOMAIN_SIZE),
            Self::JumpBranchSlt => get_tree_cap_size_for_domain_size(JUMP_BRANCH_DOMAIN_SIZE),
            Self::MulDiv => Self::signed_mul_div_unimplemented(),
            Self::MulDivUnsigned => get_tree_cap_size_for_domain_size(MUL_DIV_UNSIGNED_DOMAIN_SIZE),
            Self::ShiftBinaryCsr => get_tree_cap_size_for_domain_size(SHIFT_BINARY_DOMAIN_SIZE),
        }
    }

    #[inline(always)]
    pub const fn get_family_idx(&self) -> u8 {
        match self {
            Self::AddSubLuiAuipcMop => ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX,
            Self::JumpBranchSlt => JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX,
            Self::MulDiv => MUL_DIV_CIRCUIT_FAMILY_IDX,
            Self::MulDivUnsigned => MUL_DIV_CIRCUIT_FAMILY_IDX,
            Self::ShiftBinaryCsr => SHIFT_BINARY_CIRCUIT_FAMILY_IDX,
        }
    }

    pub const fn get_allowed_delegation_csrs(&self) -> &'static [u32] {
        match self {
            Self::AddSubLuiAuipcMop => &[],
            Self::JumpBranchSlt => &[],
            Self::MulDiv => &[],
            Self::MulDivUnsigned => &[],
            Self::ShiftBinaryCsr => SHIFT_BINARY_ALLOWED_DELEGATION_CSRS,
        }
    }

    pub const fn needs_delegation_challenge(&self) -> bool {
        !self.get_allowed_delegation_csrs().is_empty()
    }

    pub fn get_circuit_types_for_machine_type(
        machine_type: MachineType,
    ) -> &'static [UnrolledNonMemoryCircuitType] {
        match machine_type {
            MachineType::Full => &[
                Self::AddSubLuiAuipcMop,
                Self::JumpBranchSlt,
                Self::MulDiv,
                Self::ShiftBinaryCsr,
            ],
            MachineType::FullUnsigned => &[
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

    pub fn from_family_idx(family_idx: u8, machine_type: MachineType) -> Self {
        let panic = || {
            panic!("unknown/unsupported unrolled non-memory family idx {family_idx} for machine type {machine_type:?}")
        };
        match machine_type {
            MachineType::Full => match family_idx {
                ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX => Self::AddSubLuiAuipcMop,
                JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX => Self::JumpBranchSlt,
                MUL_DIV_CIRCUIT_FAMILY_IDX => Self::MulDiv,
                SHIFT_BINARY_CIRCUIT_FAMILY_IDX => Self::ShiftBinaryCsr,
                _ => panic(),
            },
            MachineType::FullUnsigned => match family_idx {
                ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX => Self::AddSubLuiAuipcMop,
                JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX => Self::JumpBranchSlt,
                MUL_DIV_CIRCUIT_FAMILY_IDX => Self::MulDivUnsigned,
                SHIFT_BINARY_CIRCUIT_FAMILY_IDX => Self::ShiftBinaryCsr,
                _ => panic(),
            },
            MachineType::Reduced => match family_idx {
                ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX => Self::AddSubLuiAuipcMop,
                JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX => Self::JumpBranchSlt,
                SHIFT_BINARY_CIRCUIT_FAMILY_IDX => Self::ShiftBinaryCsr,
                _ => panic(),
            },
        }
    }

    #[inline(always)]
    pub const fn get_default_pc_value_in_padding(&self) -> u32 {
        match self {
            Self::AddSubLuiAuipcMop => 4,
            Self::JumpBranchSlt => 0,
            Self::MulDiv => 4,
            Self::MulDivUnsigned => 4,
            Self::ShiftBinaryCsr => 4,
        }
    }

    pub fn get_security_config(&self) -> ProofSecurityConfig {
        match self {
            Self::AddSubLuiAuipcMop => get_security_config::<ADD_SUB_DOMAIN_SIZE>(),
            Self::JumpBranchSlt => get_security_config::<JUMP_BRANCH_DOMAIN_SIZE>(),
            Self::MulDiv => unimplemented!(
                "signed MulDiv security config is unavailable because signed MulDiv execution is unimplemented"
            ),
            Self::MulDivUnsigned => get_security_config::<MUL_DIV_UNSIGNED_DOMAIN_SIZE>(),
            Self::ShiftBinaryCsr => get_security_config::<SHIFT_BINARY_DOMAIN_SIZE>(),
        }
    }
}

#[inline(always)]
pub const fn get_tree_cap_size_for_domain_size(domain_size: usize) -> usize {
    assert!(domain_size.is_power_of_two());
    let log_domain_size = domain_size.trailing_zeros();
    get_tree_cap_size_for_log_domain_size(log_domain_size)
}

#[inline(always)]
pub const fn get_tree_cap_size_for_log_domain_size(log_domain_size: u32) -> usize {
    1 << get_log_tree_cap_size_for_log_domain_size(log_domain_size)
}

#[inline(always)]
pub const fn get_log_tree_cap_size_for_log_domain_size(log_domain_size: u32) -> usize {
    OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize].total_caps_size_log2
}

const fn get_num_foldings<const DOMAIN_SIZE: usize>() -> usize {
    assert!(DOMAIN_SIZE.is_power_of_two());
    OPTIMAL_FOLDING_PROPERTIES[DOMAIN_SIZE.trailing_zeros() as usize]
        .folding_sequence
        .len()
}

fn get_security_config<const DOMAIN_SIZE: usize>() -> ProofSecurityConfig
where
    [(); get_num_foldings::<DOMAIN_SIZE>()]:,
{
    assert!(DOMAIN_SIZE.is_power_of_two());
    let config = verifier_common::SizedProofSecurityConfig::<{
        get_num_foldings::<DOMAIN_SIZE>()
    }>::worst_case_config();
    ProofSecurityConfig {
        lookup_pow_bits: config.lookup_pow_bits,
        quotient_alpha_pow_bits: config.quotient_alpha_pow_bits,
        quotient_z_pow_bits: config.quotient_z_pow_bits,
        deep_poly_alpha_pow_bits: config.deep_poly_alpha_pow_bits,
        foldings_pow_bits: config.foldings_pow_bits.to_vec(),
        fri_queries_pow_bits: config.fri_queries_pow_bits,
        num_queries: config.num_queries,
    }
}
