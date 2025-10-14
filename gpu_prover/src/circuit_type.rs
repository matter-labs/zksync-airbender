use fft::GoodAllocator;
use prover::risc_v_simulator::cycle::MachineConfig;
use prover::tracers::delegation::{
    bigint_with_control_factory_fn, blake2_with_control_factory_fn, keccak_special5_factory_fn,
    DelegationWitness,
};
use setups::{
    add_sub_lui_auipc_mop, bigint_with_control, blake2_with_compression,
    final_reduced_risc_v_machine, inits_and_teardowns, is_default_machine_configuration,
    is_machine_without_signed_mul_div_configuration, is_reduced_machine_configuration,
    jump_branch_slt, keccak_special5, load_store_subword_only, load_store_word_only,
    machine_without_signed_mul_div, mul_div, mul_div_unsigned, reduced_risc_v_log_23_machine,
    reduced_risc_v_machine, risc_v_cycles, shift_binary_csr_all_delegations,
    shift_binary_csr_blake_only_delegation,
};

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum CircuitType {
    Main(MainCircuitType),
    Delegation(DelegationCircuitType),
    Unrolled(UnrolledCircuitType),
}

impl CircuitType {
    #[inline(always)]
    pub fn from_delegation_type(delegation_type: u16) -> Self {
        Self::Delegation(delegation_type.into())
    }

    #[inline(always)]
    pub const fn as_main(&self) -> Option<MainCircuitType> {
        match self {
            Self::Main(circuit_type) => Some(*circuit_type),
            _ => None,
        }
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

    pub const fn get_domain_size(&self) -> usize {
        match self {
            Self::Main(main_type) => main_type.get_domain_size(),
            Self::Delegation(delegation_type) => delegation_type.get_domain_size(),
            Self::Unrolled(unrolled_type) => unrolled_type.get_domain_size(),
        }
    }

    pub const fn get_lde_factor(&self) -> usize {
        match self {
            Self::Main(main_type) => main_type.get_lde_factor(),
            Self::Delegation(delegation_type) => delegation_type.get_lde_factor(),
            Self::Unrolled(unrolled_type) => unrolled_type.get_lde_factor(),
        }
    }

    pub const fn get_lde_source_cosets(&self) -> &'static [usize] {
        match self {
            Self::Main(main_type) => main_type.get_lde_source_cosets(),
            Self::Delegation(delegation_type) => delegation_type.get_lde_source_cosets(),
            Self::Unrolled(unrolled_type) => unrolled_type.get_lde_source_cosets(),
        }
    }

    pub const fn get_tree_cap_size(&self) -> usize {
        match self {
            Self::Main(main_type) => main_type.get_tree_cap_size(),
            Self::Delegation(delegation_type) => delegation_type.get_tree_cap_size(),
            Self::Unrolled(unrolled_type) => unrolled_type.get_tree_cap_size(),
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum MainCircuitType {
    FinalReducedRiscVMachine,
    MachineWithoutSignedMulDiv,
    ReducedRiscVLog23Machine,
    ReducedRiscVMachine,
    RiscVCycles,
}

impl MainCircuitType {
    pub const fn get_domain_size(&self) -> usize {
        match self {
            Self::FinalReducedRiscVMachine => final_reduced_risc_v_machine::DOMAIN_SIZE,
            Self::MachineWithoutSignedMulDiv => machine_without_signed_mul_div::DOMAIN_SIZE,
            Self::ReducedRiscVLog23Machine => reduced_risc_v_log_23_machine::DOMAIN_SIZE,
            Self::ReducedRiscVMachine => reduced_risc_v_machine::DOMAIN_SIZE,
            Self::RiscVCycles => risc_v_cycles::DOMAIN_SIZE,
        }
    }

    pub const fn get_lde_factor(&self) -> usize {
        match self {
            Self::FinalReducedRiscVMachine => final_reduced_risc_v_machine::LDE_FACTOR,
            Self::MachineWithoutSignedMulDiv => machine_without_signed_mul_div::LDE_FACTOR,
            Self::ReducedRiscVLog23Machine => reduced_risc_v_log_23_machine::LDE_FACTOR,
            Self::ReducedRiscVMachine => reduced_risc_v_machine::LDE_FACTOR,
            Self::RiscVCycles => risc_v_cycles::LDE_FACTOR,
        }
    }

    pub const fn get_lde_source_cosets(&self) -> &'static [usize] {
        match self {
            Self::FinalReducedRiscVMachine => final_reduced_risc_v_machine::LDE_SOURCE_COSETS,
            Self::MachineWithoutSignedMulDiv => machine_without_signed_mul_div::LDE_SOURCE_COSETS,
            Self::ReducedRiscVLog23Machine => reduced_risc_v_log_23_machine::LDE_SOURCE_COSETS,
            Self::ReducedRiscVMachine => reduced_risc_v_machine::LDE_SOURCE_COSETS,
            Self::RiscVCycles => risc_v_cycles::LDE_SOURCE_COSETS,
        }
    }

    pub const fn get_tree_cap_size(&self) -> usize {
        match self {
            Self::FinalReducedRiscVMachine => final_reduced_risc_v_machine::TREE_CAP_SIZE,
            Self::MachineWithoutSignedMulDiv => machine_without_signed_mul_div::TREE_CAP_SIZE,
            Self::ReducedRiscVLog23Machine => reduced_risc_v_log_23_machine::TREE_CAP_SIZE,
            Self::ReducedRiscVMachine => reduced_risc_v_machine::TREE_CAP_SIZE,
            Self::RiscVCycles => risc_v_cycles::TREE_CAP_SIZE,
        }
    }

    pub const fn get_num_cycles(&self) -> usize {
        match self {
            Self::FinalReducedRiscVMachine => final_reduced_risc_v_machine::NUM_CYCLES,
            Self::MachineWithoutSignedMulDiv => machine_without_signed_mul_div::NUM_CYCLES,
            Self::ReducedRiscVLog23Machine => reduced_risc_v_log_23_machine::NUM_CYCLES,
            Self::ReducedRiscVMachine => reduced_risc_v_machine::NUM_CYCLES,
            Self::RiscVCycles => risc_v_cycles::NUM_CYCLES,
        }
    }

    pub const fn get_allowed_delegation_csrs(&self) -> &'static [u32] {
        match self {
            Self::FinalReducedRiscVMachine => final_reduced_risc_v_machine::ALLOWED_DELEGATION_CSRS,
            Self::MachineWithoutSignedMulDiv => {
                machine_without_signed_mul_div::ALLOWED_DELEGATION_CSRS
            }
            Self::ReducedRiscVLog23Machine => {
                reduced_risc_v_log_23_machine::ALLOWED_DELEGATION_CSRS
            }
            Self::ReducedRiscVMachine => reduced_risc_v_machine::ALLOWED_DELEGATION_CSRS,
            Self::RiscVCycles => risc_v_cycles::ALLOWED_DELEGATION_CSRS,
        }
    }

    pub fn get_allowed_delegation_circuit_types(
        &self,
    ) -> impl Iterator<Item = DelegationCircuitType> {
        self.get_allowed_delegation_csrs()
            .iter()
            .map(|id| DelegationCircuitType::from(*id as u16))
    }

    pub const fn needs_delegation_challenge(&self) -> bool {
        !self.get_allowed_delegation_csrs().is_empty()
    }
}

#[repr(u32)]
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum DelegationCircuitType {
    BigIntWithControl = bigint_with_control::DELEGATION_TYPE_ID,
    Blake2WithCompression = blake2_with_compression::DELEGATION_TYPE_ID,
    KeccakSpecial5 = keccak_special5::DELEGATION_TYPE_ID,
}

pub type DelegationWitnessFactoryFn<A> =
    fn(delegation_type: u16, num_requests: usize, allocator: A) -> DelegationWitness<A>;

impl DelegationCircuitType {
    pub const fn get_delegation_type_id(&self) -> u16 {
        *self as u16
    }

    pub const fn get_num_delegation_cycles(&self) -> usize {
        match self {
            Self::BigIntWithControl => bigint_with_control::NUM_DELEGATION_CYCLES,
            Self::Blake2WithCompression => blake2_with_compression::NUM_DELEGATION_CYCLES,
            Self::KeccakSpecial5 => keccak_special5::NUM_DELEGATION_CYCLES,
        }
    }

    pub const fn get_domain_size(&self) -> usize {
        match self {
            Self::BigIntWithControl => bigint_with_control::DOMAIN_SIZE,
            Self::Blake2WithCompression => blake2_with_compression::DOMAIN_SIZE,
            Self::KeccakSpecial5 => keccak_special5::DOMAIN_SIZE,
        }
    }

    pub const fn get_lde_factor(&self) -> usize {
        match self {
            Self::BigIntWithControl => bigint_with_control::LDE_FACTOR,
            Self::Blake2WithCompression => blake2_with_compression::LDE_FACTOR,
            Self::KeccakSpecial5 => keccak_special5::LDE_FACTOR,
        }
    }

    pub const fn get_lde_source_cosets(&self) -> &'static [usize] {
        match self {
            Self::BigIntWithControl => bigint_with_control::LDE_SOURCE_COSETS,
            Self::Blake2WithCompression => blake2_with_compression::LDE_SOURCE_COSETS,
            Self::KeccakSpecial5 => keccak_special5::LDE_SOURCE_COSETS,
        }
    }

    pub const fn get_tree_cap_size(&self) -> usize {
        match self {
            Self::BigIntWithControl => bigint_with_control::TREE_CAP_SIZE,
            Self::Blake2WithCompression => blake2_with_compression::TREE_CAP_SIZE,
            Self::KeccakSpecial5 => keccak_special5::TREE_CAP_SIZE,
        }
    }

    const fn get_witness_factory<A: GoodAllocator>(&self) -> DelegationWitnessFactoryFn<A> {
        match self {
            Self::BigIntWithControl => bigint_with_control_factory_fn,
            Self::Blake2WithCompression => blake2_with_control_factory_fn,
            Self::KeccakSpecial5 => keccak_special5_factory_fn,
        }
    }

    pub const fn get_witness_factory_fn<A: GoodAllocator>(
        &self,
    ) -> impl Fn(A) -> DelegationWitness<A> {
        let f = self.get_witness_factory();
        let delegation_type_id = self.get_delegation_type_id();
        let num_delegation_cycles = self.get_num_delegation_cycles();
        move |allocator| f(delegation_type_id, num_delegation_cycles, allocator)
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

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum UnrolledCircuitType {
    InitsAndTeardowns,
    Memory(UnrolledMemoryCircuitType),
    NonMemory(UnrolledNonMemoryCircuitType),
}

impl UnrolledCircuitType {
    pub fn as_memory(&self) -> Option<UnrolledMemoryCircuitType> {
        match self {
            Self::Memory(circuit_type) => Some(*circuit_type),
            _ => None,
        }
    }

    pub fn as_non_memory(&self) -> Option<UnrolledNonMemoryCircuitType> {
        match self {
            Self::NonMemory(circuit_type) => Some(*circuit_type),
            _ => None,
        }
    }

    pub const fn get_domain_size(&self) -> usize {
        match self {
            Self::InitsAndTeardowns => inits_and_teardowns::DOMAIN_SIZE,
            Self::Memory(circuit_type) => circuit_type.get_domain_size(),
            Self::NonMemory(circuit_type) => circuit_type.get_domain_size(),
        }
    }

    pub const fn get_lde_factor(&self) -> usize {
        match self {
            Self::InitsAndTeardowns => inits_and_teardowns::LDE_FACTOR,
            Self::Memory(circuit_type) => circuit_type.get_lde_factor(),
            Self::NonMemory(circuit_type) => circuit_type.get_lde_factor(),
        }
    }

    pub const fn get_lde_source_cosets(&self) -> &'static [usize] {
        match self {
            Self::InitsAndTeardowns => inits_and_teardowns::LDE_SOURCE_COSETS,
            Self::Memory(circuit_type) => circuit_type.get_lde_source_cosets(),
            Self::NonMemory(circuit_type) => circuit_type.get_lde_source_cosets(),
        }
    }

    pub const fn get_tree_cap_size(&self) -> usize {
        match self {
            Self::InitsAndTeardowns => inits_and_teardowns::TREE_CAP_SIZE,
            Self::Memory(circuit_type) => circuit_type.get_tree_cap_size(),
            Self::NonMemory(circuit_type) => circuit_type.get_tree_cap_size(),
        }
    }

    pub const fn get_family_idx(&self) -> u8 {
        match self {
            Self::InitsAndTeardowns => inits_and_teardowns::FAMILY_IDX,
            Self::Memory(circuit_type) => circuit_type.get_family_idx(),
            Self::NonMemory(circuit_type) => circuit_type.get_family_idx(),
        }
    }

    pub const fn get_num_cycles(&self) -> usize {
        match self {
            Self::InitsAndTeardowns => inits_and_teardowns::NUM_CYCLES,
            Self::Memory(circuit_type) => circuit_type.get_num_cycles(),
            Self::NonMemory(circuit_type) => circuit_type.get_num_cycles(),
        }
    }

    pub const fn get_allowed_delegation_csrs(&self) -> &'static [u32] {
        match self {
            Self::InitsAndTeardowns => &[],
            Self::Memory(circuit_type) => circuit_type.get_allowed_delegation_csrs(),
            Self::NonMemory(circuit_type) => circuit_type.get_allowed_delegation_csrs(),
        }
    }

    pub fn get_allowed_delegation_circuit_types(
        &self,
    ) -> impl Iterator<Item = DelegationCircuitType> {
        self.get_allowed_delegation_csrs()
            .iter()
            .map(|id| DelegationCircuitType::from(*id as u16))
    }
}

#[repr(u32)]
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum UnrolledMemoryCircuitType {
    LoadStoreSubwordOnly,
    LoadStoreWordOnly,
}

impl UnrolledMemoryCircuitType {
    pub const fn get_domain_size(&self) -> usize {
        match self {
            Self::LoadStoreSubwordOnly => load_store_subword_only::DOMAIN_SIZE,
            Self::LoadStoreWordOnly => load_store_word_only::DOMAIN_SIZE,
        }
    }

    pub const fn get_lde_factor(&self) -> usize {
        match self {
            Self::LoadStoreSubwordOnly => load_store_subword_only::LDE_FACTOR,
            Self::LoadStoreWordOnly => load_store_word_only::LDE_FACTOR,
        }
    }

    pub const fn get_lde_source_cosets(&self) -> &'static [usize] {
        match self {
            Self::LoadStoreSubwordOnly => load_store_subword_only::LDE_SOURCE_COSETS,
            Self::LoadStoreWordOnly => load_store_word_only::LDE_SOURCE_COSETS,
        }
    }

    pub const fn get_tree_cap_size(&self) -> usize {
        match self {
            Self::LoadStoreSubwordOnly => load_store_subword_only::TREE_CAP_SIZE,
            Self::LoadStoreWordOnly => load_store_word_only::TREE_CAP_SIZE,
        }
    }

    pub const fn get_family_idx(&self) -> u8 {
        match self {
            Self::LoadStoreSubwordOnly => load_store_subword_only::FAMILY_IDX,
            Self::LoadStoreWordOnly => load_store_word_only::FAMILY_IDX,
        }
    }

    pub const fn get_num_cycles(&self) -> usize {
        match self {
            Self::LoadStoreSubwordOnly => load_store_subword_only::NUM_CYCLES,
            Self::LoadStoreWordOnly => load_store_word_only::NUM_CYCLES,
        }
    }

    pub const fn get_allowed_delegation_csrs(&self) -> &'static [u32] {
        match self {
            Self::LoadStoreSubwordOnly => &[],
            Self::LoadStoreWordOnly => &[],
        }
    }

    pub fn get_allowed_delegation_circuit_types(
        &self,
    ) -> impl Iterator<Item = DelegationCircuitType> {
        self.get_allowed_delegation_csrs()
            .iter()
            .map(|id| DelegationCircuitType::from(*id as u16))
    }

    pub fn from_family_idx<C: MachineConfig>(family_idx: u8) -> Self {
        if is_default_machine_configuration::<C>() {
            match family_idx {
                load_store_subword_only::FAMILY_IDX => Self::LoadStoreSubwordOnly,
                load_store_word_only::FAMILY_IDX => Self::LoadStoreWordOnly,
                _ => panic!(
                    "unknown/unsupported unrolled non-memory family idx {} for configuration {}",
                    family_idx,
                    std::any::type_name::<C>()
                ),
            }
        } else if is_machine_without_signed_mul_div_configuration::<C>() {
            match family_idx {
                load_store_subword_only::FAMILY_IDX => Self::LoadStoreSubwordOnly,
                load_store_word_only::FAMILY_IDX => Self::LoadStoreWordOnly,
                _ => panic!(
                    "unknown/unsupported unrolled non-memory family idx {} for configuration {}",
                    family_idx,
                    std::any::type_name::<C>()
                ),
            }
        } else if is_reduced_machine_configuration::<C>() {
            match family_idx {
                load_store_word_only::FAMILY_IDX => Self::LoadStoreWordOnly,
                _ => panic!(
                    "unknown/unsupported unrolled non-memory family idx {} for configuration {}",
                    family_idx,
                    std::any::type_name::<C>()
                ),
            }
        } else {
            panic!("unknown configuration {:?}", std::any::type_name::<C>());
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
    ShiftBinaryCsrAllDelegations,
    ShiftBinaryCsrBlakeOnlyDelegation,
}

impl UnrolledNonMemoryCircuitType {
    pub const fn get_domain_size(&self) -> usize {
        match self {
            Self::AddSubLuiAuipcMop => add_sub_lui_auipc_mop::DOMAIN_SIZE,
            Self::JumpBranchSlt => jump_branch_slt::DOMAIN_SIZE,
            Self::MulDiv => mul_div::DOMAIN_SIZE,
            Self::MulDivUnsigned => mul_div_unsigned::DOMAIN_SIZE,
            Self::ShiftBinaryCsrAllDelegations => shift_binary_csr_all_delegations::DOMAIN_SIZE,
            Self::ShiftBinaryCsrBlakeOnlyDelegation => {
                shift_binary_csr_blake_only_delegation::DOMAIN_SIZE
            }
        }
    }

    pub const fn get_lde_factor(&self) -> usize {
        match self {
            Self::AddSubLuiAuipcMop => add_sub_lui_auipc_mop::LDE_FACTOR,
            Self::JumpBranchSlt => jump_branch_slt::LDE_FACTOR,
            Self::MulDiv => mul_div::LDE_FACTOR,
            Self::MulDivUnsigned => mul_div_unsigned::LDE_FACTOR,
            Self::ShiftBinaryCsrAllDelegations => shift_binary_csr_all_delegations::LDE_FACTOR,
            Self::ShiftBinaryCsrBlakeOnlyDelegation => {
                shift_binary_csr_blake_only_delegation::LDE_FACTOR
            }
        }
    }

    pub const fn get_lde_source_cosets(&self) -> &'static [usize] {
        match self {
            Self::AddSubLuiAuipcMop => add_sub_lui_auipc_mop::LDE_SOURCE_COSETS,
            Self::JumpBranchSlt => jump_branch_slt::LDE_SOURCE_COSETS,
            Self::MulDiv => mul_div::LDE_SOURCE_COSETS,
            Self::MulDivUnsigned => mul_div_unsigned::LDE_SOURCE_COSETS,
            Self::ShiftBinaryCsrAllDelegations => {
                shift_binary_csr_all_delegations::LDE_SOURCE_COSETS
            }
            Self::ShiftBinaryCsrBlakeOnlyDelegation => {
                shift_binary_csr_blake_only_delegation::LDE_SOURCE_COSETS
            }
        }
    }

    pub const fn get_tree_cap_size(&self) -> usize {
        match self {
            Self::AddSubLuiAuipcMop => add_sub_lui_auipc_mop::TREE_CAP_SIZE,
            Self::JumpBranchSlt => jump_branch_slt::TREE_CAP_SIZE,
            Self::MulDiv => mul_div::TREE_CAP_SIZE,
            Self::MulDivUnsigned => mul_div_unsigned::TREE_CAP_SIZE,
            Self::ShiftBinaryCsrAllDelegations => shift_binary_csr_all_delegations::TREE_CAP_SIZE,
            Self::ShiftBinaryCsrBlakeOnlyDelegation => {
                shift_binary_csr_blake_only_delegation::TREE_CAP_SIZE
            }
        }
    }

    pub const fn get_family_idx(&self) -> u8 {
        match self {
            Self::AddSubLuiAuipcMop => add_sub_lui_auipc_mop::FAMILY_IDX,
            Self::JumpBranchSlt => jump_branch_slt::FAMILY_IDX,
            Self::MulDiv => mul_div::FAMILY_IDX,
            Self::MulDivUnsigned => mul_div_unsigned::FAMILY_IDX,
            Self::ShiftBinaryCsrAllDelegations => shift_binary_csr_all_delegations::FAMILY_IDX,
            Self::ShiftBinaryCsrBlakeOnlyDelegation => {
                shift_binary_csr_blake_only_delegation::FAMILY_IDX
            }
        }
    }

    pub const fn get_num_cycles(&self) -> usize {
        match self {
            Self::AddSubLuiAuipcMop => add_sub_lui_auipc_mop::NUM_CYCLES,
            Self::JumpBranchSlt => jump_branch_slt::NUM_CYCLES,
            Self::MulDiv => mul_div::NUM_CYCLES,
            Self::MulDivUnsigned => mul_div_unsigned::NUM_CYCLES,
            Self::ShiftBinaryCsrAllDelegations => shift_binary_csr_all_delegations::NUM_CYCLES,
            Self::ShiftBinaryCsrBlakeOnlyDelegation => {
                shift_binary_csr_blake_only_delegation::NUM_CYCLES
            }
        }
    }

    pub const fn get_allowed_delegation_csrs(&self) -> &'static [u32] {
        match self {
            Self::AddSubLuiAuipcMop => &[],
            Self::JumpBranchSlt => &[],
            Self::MulDiv => &[],
            Self::MulDivUnsigned => &[],
            Self::ShiftBinaryCsrAllDelegations => {
                shift_binary_csr_all_delegations::ALLOWED_DELEGATION_CSRS
            }
            Self::ShiftBinaryCsrBlakeOnlyDelegation => {
                shift_binary_csr_blake_only_delegation::ALLOWED_DELEGATION_CSRS
            }
        }
    }

    pub const fn needs_delegation_challenge(&self) -> bool {
        !self.get_allowed_delegation_csrs().is_empty()
    }

    pub fn from_family_idx<C: MachineConfig>(family_idx: u8) -> Self {
        if is_default_machine_configuration::<C>() {
            match family_idx {
                add_sub_lui_auipc_mop::FAMILY_IDX => Self::AddSubLuiAuipcMop,
                jump_branch_slt::FAMILY_IDX => Self::JumpBranchSlt,
                mul_div::FAMILY_IDX => Self::MulDiv,
                shift_binary_csr_all_delegations::FAMILY_IDX => Self::ShiftBinaryCsrAllDelegations,
                _ => panic!(
                    "unknown/unsupported unrolled non-memory family idx {} for configuration {}",
                    family_idx,
                    std::any::type_name::<C>()
                ),
            }
        } else if is_machine_without_signed_mul_div_configuration::<C>() {
            match family_idx {
                add_sub_lui_auipc_mop::FAMILY_IDX => Self::AddSubLuiAuipcMop,
                jump_branch_slt::FAMILY_IDX => Self::JumpBranchSlt,
                mul_div_unsigned::FAMILY_IDX => Self::MulDivUnsigned,
                shift_binary_csr_all_delegations::FAMILY_IDX => Self::ShiftBinaryCsrAllDelegations,
                _ => panic!(
                    "unknown/unsupported unrolled non-memory family idx {} for configuration {}",
                    family_idx,
                    std::any::type_name::<C>()
                ),
            }
        } else if is_reduced_machine_configuration::<C>() {
            match family_idx {
                add_sub_lui_auipc_mop::FAMILY_IDX => Self::AddSubLuiAuipcMop,
                jump_branch_slt::FAMILY_IDX => Self::JumpBranchSlt,
                shift_binary_csr_blake_only_delegation::FAMILY_IDX => {
                    Self::ShiftBinaryCsrBlakeOnlyDelegation
                }
                _ => panic!(
                    "unknown/unsupported unrolled non-memory family idx {} for configuration {}",
                    family_idx,
                    std::any::type_name::<C>()
                ),
            }
        } else {
            panic!("unknown configuration {:?}", std::any::type_name::<C>());
        }
    }
}
