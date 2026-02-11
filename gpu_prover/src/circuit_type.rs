use crate::machine_type::MachineType;
use prover::definitions::OPTIMAL_FOLDING_PROPERTIES;
use prover::prover_stages::ProofSecurityConfig;
use setups::{
    add_sub_lui_auipc_mop, bigint_with_control, blake2_with_compression, inits_and_teardowns,
    jump_branch_slt, keccak_special5, load_store_subword_only, load_store_word_only, mul_div,
    mul_div_unsigned, shift_binary_csr, unified_reduced_machine,
};

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
    pub const fn get_num_cycles(&self) -> usize {
        match self {
            CircuitType::Delegation(delegation) => delegation.get_num_cycles(),
            CircuitType::Unrolled(unrolled) => unrolled.get_num_cycles(),
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
    BigIntWithControl = bigint_with_control::DELEGATION_TYPE_ID,
    Blake2WithCompression = blake2_with_compression::DELEGATION_TYPE_ID,
    KeccakSpecial5 = keccak_special5::DELEGATION_TYPE_ID,
}

impl DelegationCircuitType {
    #[inline(always)]
    pub const fn get_delegation_type_id(&self) -> u16 {
        *self as u16
    }

    #[inline(always)]
    pub const fn get_num_cycles(&self) -> usize {
        match self {
            Self::BigIntWithControl => bigint_with_control::NUM_DELEGATION_CYCLES,
            Self::Blake2WithCompression => blake2_with_compression::NUM_DELEGATION_CYCLES,
            Self::KeccakSpecial5 => keccak_special5::NUM_DELEGATION_CYCLES,
        }
    }

    #[inline(always)]
    pub const fn get_domain_size(&self) -> usize {
        match self {
            Self::BigIntWithControl => bigint_with_control::DOMAIN_SIZE,
            Self::Blake2WithCompression => blake2_with_compression::DOMAIN_SIZE,
            Self::KeccakSpecial5 => keccak_special5::DOMAIN_SIZE,
        }
    }

    #[inline(always)]
    pub const fn get_lde_factor(&self) -> usize {
        match self {
            Self::BigIntWithControl => bigint_with_control::LDE_FACTOR,
            Self::Blake2WithCompression => blake2_with_compression::LDE_FACTOR,
            Self::KeccakSpecial5 => keccak_special5::LDE_FACTOR,
        }
    }

    #[inline(always)]
    pub const fn get_lde_source_cosets(&self) -> &'static [usize] {
        match self {
            Self::BigIntWithControl => bigint_with_control::LDE_SOURCE_COSETS,
            Self::Blake2WithCompression => blake2_with_compression::LDE_SOURCE_COSETS,
            Self::KeccakSpecial5 => keccak_special5::LDE_SOURCE_COSETS,
        }
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
            Self::BigIntWithControl => {
                get_security_config::<{ bigint_with_control::DOMAIN_SIZE }>()
            }
            Self::Blake2WithCompression => {
                get_security_config::<{ blake2_with_compression::DOMAIN_SIZE }>()
            }
            Self::KeccakSpecial5 => get_security_config::<{ keccak_special5::DOMAIN_SIZE }>(),
        }
    }
}

impl From<u16> for DelegationCircuitType {
    #[inline(always)]
    fn from(delegation_type: u16) -> Self {
        match delegation_type as u32 {
            bigint_with_control::DELEGATION_TYPE_ID => Self::BigIntWithControl,
            blake2_with_compression::DELEGATION_TYPE_ID => Self::Blake2WithCompression,
            keccak_special5::DELEGATION_TYPE_ID => Self::KeccakSpecial5,
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
    pub const fn get_num_cycles(&self) -> usize {
        match self {
            Self::InitsAndTeardowns => inits_and_teardowns::NUM_CYCLES,
            Self::Memory(circuit_type) => circuit_type.get_num_cycles(),
            Self::NonMemory(circuit_type) => circuit_type.get_num_cycles(),
            Self::Unified => unified_reduced_machine::NUM_CYCLES,
        }
    }

    #[inline(always)]
    pub const fn get_domain_size(&self) -> usize {
        match self {
            Self::InitsAndTeardowns => inits_and_teardowns::DOMAIN_SIZE,
            Self::Memory(circuit_type) => circuit_type.get_domain_size(),
            Self::NonMemory(circuit_type) => circuit_type.get_domain_size(),
            Self::Unified => unified_reduced_machine::DOMAIN_SIZE,
        }
    }

    #[inline(always)]
    pub const fn get_lde_factor(&self) -> usize {
        match self {
            Self::InitsAndTeardowns => inits_and_teardowns::LDE_FACTOR,
            Self::Memory(circuit_type) => circuit_type.get_lde_factor(),
            Self::NonMemory(circuit_type) => circuit_type.get_lde_factor(),
            Self::Unified => unified_reduced_machine::LDE_FACTOR,
        }
    }

    #[inline(always)]
    pub const fn get_lde_source_cosets(&self) -> &'static [usize] {
        match self {
            Self::InitsAndTeardowns => inits_and_teardowns::LDE_SOURCE_COSETS,
            Self::Memory(circuit_type) => circuit_type.get_lde_source_cosets(),
            Self::NonMemory(circuit_type) => circuit_type.get_lde_source_cosets(),
            Self::Unified => unified_reduced_machine::LDE_SOURCE_COSETS,
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
            Self::InitsAndTeardowns => inits_and_teardowns::FAMILY_IDX,
            Self::Memory(circuit_type) => circuit_type.get_family_idx(),
            Self::NonMemory(circuit_type) => circuit_type.get_family_idx(),
            Self::Unified => unified_reduced_machine::FAMILY_IDX,
        }
    }

    pub const fn get_allowed_delegation_csrs(&self) -> &'static [u32] {
        match self {
            Self::InitsAndTeardowns => &[],
            Self::Memory(_) => &[],
            Self::NonMemory(circuit_type) => circuit_type.get_allowed_delegation_csrs(),
            Self::Unified => unified_reduced_machine::ALLOWED_DELEGATION_CSRS,
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
            Self::InitsAndTeardowns => {
                get_security_config::<{ inits_and_teardowns::DOMAIN_SIZE }>()
            }
            Self::Memory(circuit_type) => circuit_type.get_security_config(),
            Self::NonMemory(circuit_type) => circuit_type.get_security_config(),
            Self::Unified => get_security_config::<{ unified_reduced_machine::DOMAIN_SIZE }>(),
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
    pub const fn get_num_cycles(&self) -> usize {
        match self {
            Self::LoadStoreSubwordOnly => load_store_subword_only::NUM_CYCLES,
            Self::LoadStoreWordOnly => load_store_word_only::NUM_CYCLES,
        }
    }

    #[inline(always)]
    pub const fn get_domain_size(&self) -> usize {
        match self {
            Self::LoadStoreSubwordOnly => load_store_subword_only::DOMAIN_SIZE,
            Self::LoadStoreWordOnly => load_store_word_only::DOMAIN_SIZE,
        }
    }

    #[inline(always)]
    pub const fn get_lde_factor(&self) -> usize {
        match self {
            Self::LoadStoreSubwordOnly => load_store_subword_only::LDE_FACTOR,
            Self::LoadStoreWordOnly => load_store_word_only::LDE_FACTOR,
        }
    }

    #[inline(always)]
    pub const fn get_lde_source_cosets(&self) -> &'static [usize] {
        match self {
            Self::LoadStoreSubwordOnly => load_store_subword_only::LDE_SOURCE_COSETS,
            Self::LoadStoreWordOnly => load_store_word_only::LDE_SOURCE_COSETS,
        }
    }

    #[inline(always)]
    pub const fn get_tree_cap_size(&self) -> usize {
        match self {
            Self::LoadStoreSubwordOnly => load_store_subword_only::TREE_CAP_SIZE,
            Self::LoadStoreWordOnly => load_store_word_only::TREE_CAP_SIZE,
        }
    }

    #[inline(always)]
    pub const fn get_family_idx(&self) -> u8 {
        match self {
            Self::LoadStoreSubwordOnly => load_store_subword_only::FAMILY_IDX,
            Self::LoadStoreWordOnly => load_store_word_only::FAMILY_IDX,
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
                load_store_subword_only::FAMILY_IDX => Self::LoadStoreSubwordOnly,
                load_store_word_only::FAMILY_IDX => Self::LoadStoreWordOnly,
                _ => panic(),
            },
            MachineType::FullUnsigned => match family_idx {
                load_store_subword_only::FAMILY_IDX => Self::LoadStoreSubwordOnly,
                load_store_word_only::FAMILY_IDX => Self::LoadStoreWordOnly,
                _ => panic(),
            },
            MachineType::Reduced => match family_idx {
                load_store_word_only::FAMILY_IDX => Self::LoadStoreWordOnly,
                _ => panic(),
            },
        }
    }

    pub fn get_security_config(&self) -> ProofSecurityConfig {
        match self {
            Self::LoadStoreSubwordOnly => {
                get_security_config::<{ load_store_subword_only::DOMAIN_SIZE }>()
            }
            Self::LoadStoreWordOnly => {
                get_security_config::<{ load_store_word_only::DOMAIN_SIZE }>()
            }
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
    #[inline(always)]
    pub const fn get_num_cycles(&self) -> usize {
        match self {
            Self::AddSubLuiAuipcMop => add_sub_lui_auipc_mop::NUM_CYCLES,
            Self::JumpBranchSlt => jump_branch_slt::NUM_CYCLES,
            Self::MulDiv => mul_div::NUM_CYCLES,
            Self::MulDivUnsigned => mul_div_unsigned::NUM_CYCLES,
            Self::ShiftBinaryCsr => shift_binary_csr::NUM_CYCLES,
        }
    }

    #[inline(always)]
    pub const fn get_domain_size(&self) -> usize {
        match self {
            Self::AddSubLuiAuipcMop => add_sub_lui_auipc_mop::DOMAIN_SIZE,
            Self::JumpBranchSlt => jump_branch_slt::DOMAIN_SIZE,
            Self::MulDiv => mul_div::DOMAIN_SIZE,
            Self::MulDivUnsigned => mul_div_unsigned::DOMAIN_SIZE,
            Self::ShiftBinaryCsr => shift_binary_csr::DOMAIN_SIZE,
        }
    }

    #[inline(always)]
    pub const fn get_lde_factor(&self) -> usize {
        match self {
            Self::AddSubLuiAuipcMop => add_sub_lui_auipc_mop::LDE_FACTOR,
            Self::JumpBranchSlt => jump_branch_slt::LDE_FACTOR,
            Self::MulDiv => mul_div::LDE_FACTOR,
            Self::MulDivUnsigned => mul_div_unsigned::LDE_FACTOR,
            Self::ShiftBinaryCsr => shift_binary_csr::LDE_FACTOR,
        }
    }

    #[inline(always)]
    pub const fn get_lde_source_cosets(&self) -> &'static [usize] {
        match self {
            Self::AddSubLuiAuipcMop => add_sub_lui_auipc_mop::LDE_SOURCE_COSETS,
            Self::JumpBranchSlt => jump_branch_slt::LDE_SOURCE_COSETS,
            Self::MulDiv => mul_div::LDE_SOURCE_COSETS,
            Self::MulDivUnsigned => mul_div_unsigned::LDE_SOURCE_COSETS,
            Self::ShiftBinaryCsr => shift_binary_csr::LDE_SOURCE_COSETS,
        }
    }

    #[inline(always)]
    pub const fn get_tree_cap_size(&self) -> usize {
        match self {
            Self::AddSubLuiAuipcMop => add_sub_lui_auipc_mop::TREE_CAP_SIZE,
            Self::JumpBranchSlt => jump_branch_slt::TREE_CAP_SIZE,
            Self::MulDiv => mul_div::TREE_CAP_SIZE,
            Self::MulDivUnsigned => mul_div_unsigned::TREE_CAP_SIZE,
            Self::ShiftBinaryCsr => shift_binary_csr::TREE_CAP_SIZE,
        }
    }

    #[inline(always)]
    pub const fn get_family_idx(&self) -> u8 {
        match self {
            Self::AddSubLuiAuipcMop => add_sub_lui_auipc_mop::FAMILY_IDX,
            Self::JumpBranchSlt => jump_branch_slt::FAMILY_IDX,
            Self::MulDiv => mul_div::FAMILY_IDX,
            Self::MulDivUnsigned => mul_div_unsigned::FAMILY_IDX,
            Self::ShiftBinaryCsr => shift_binary_csr::FAMILY_IDX,
        }
    }

    pub const fn get_allowed_delegation_csrs(&self) -> &'static [u32] {
        match self {
            Self::AddSubLuiAuipcMop => &[],
            Self::JumpBranchSlt => &[],
            Self::MulDiv => &[],
            Self::MulDivUnsigned => &[],
            Self::ShiftBinaryCsr => shift_binary_csr::ALLOWED_DELEGATION_CSRS,
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
                add_sub_lui_auipc_mop::FAMILY_IDX => Self::AddSubLuiAuipcMop,
                jump_branch_slt::FAMILY_IDX => Self::JumpBranchSlt,
                mul_div::FAMILY_IDX => Self::MulDiv,
                shift_binary_csr::FAMILY_IDX => Self::ShiftBinaryCsr,
                _ => panic(),
            },
            MachineType::FullUnsigned => match family_idx {
                add_sub_lui_auipc_mop::FAMILY_IDX => Self::AddSubLuiAuipcMop,
                jump_branch_slt::FAMILY_IDX => Self::JumpBranchSlt,
                mul_div_unsigned::FAMILY_IDX => Self::MulDivUnsigned,
                shift_binary_csr::FAMILY_IDX => Self::ShiftBinaryCsr,
                _ => panic(),
            },
            MachineType::Reduced => match family_idx {
                add_sub_lui_auipc_mop::FAMILY_IDX => Self::AddSubLuiAuipcMop,
                jump_branch_slt::FAMILY_IDX => Self::JumpBranchSlt,
                shift_binary_csr::FAMILY_IDX => Self::ShiftBinaryCsr,
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
            Self::AddSubLuiAuipcMop => {
                get_security_config::<{ add_sub_lui_auipc_mop::DOMAIN_SIZE }>()
            }
            Self::JumpBranchSlt => get_security_config::<{ jump_branch_slt::DOMAIN_SIZE }>(),
            Self::MulDiv => get_security_config::<{ mul_div::DOMAIN_SIZE }>(),
            Self::MulDivUnsigned => get_security_config::<{ mul_div_unsigned::DOMAIN_SIZE }>(),
            Self::ShiftBinaryCsr => get_security_config::<{ shift_binary_csr::DOMAIN_SIZE }>(),
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
    config.for_prover()
}
