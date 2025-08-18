use fft::GoodAllocator;
use prover::tracers::delegation::{
    bigint_with_control_factory_fn, blake2_with_control_factory_fn, DelegationWitness,
};
use setups::{
    bigint_with_control, blake2_with_compression, final_reduced_risc_v_machine,
    machine_without_signed_mul_div, reduced_risc_v_log_23_machine, reduced_risc_v_machine,
    risc_v_cycles,
};

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum CircuitType {
    Main(MainCircuitType),
    Delegation(DelegationCircuitType),
}

impl CircuitType {
    #[inline(always)]
    pub fn from_delegation_type(delegation_type: u16) -> Self {
        Self::Delegation(delegation_type.into())
    }

    #[inline(always)]
    pub fn as_main(&self) -> Option<MainCircuitType> {
        match self {
            CircuitType::Main(circuit_type) => Some(*circuit_type),
            _ => None,
        }
    }

    #[inline(always)]
    pub fn as_delegation(&self) -> Option<DelegationCircuitType> {
        match self {
            CircuitType::Delegation(circuit_type) => Some(*circuit_type),
            _ => None,
        }
    }

    pub fn get_domain_size(&self) -> usize {
        match self {
            CircuitType::Main(main_type) => main_type.get_domain_size(),
            CircuitType::Delegation(delegation_type) => delegation_type.get_domain_size(),
        }
    }

    pub fn get_lde_factor(&self) -> usize {
        match self {
            CircuitType::Main(main_type) => main_type.get_lde_factor(),
            CircuitType::Delegation(delegation_type) => delegation_type.get_lde_factor(),
        }
    }

    pub fn get_lde_source_cosets(&self) -> &'static [usize] {
        match self {
            CircuitType::Main(main_type) => main_type.get_lde_source_cosets(),
            CircuitType::Delegation(delegation_type) => delegation_type.get_lde_source_cosets(),
        }
    }

    pub fn get_tree_cap_size(&self) -> usize {
        match self {
            CircuitType::Main(main_type) => main_type.get_tree_cap_size(),
            CircuitType::Delegation(delegation_type) => delegation_type.get_tree_cap_size(),
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
    pub fn get_num_cycles(&self) -> usize {
        match self {
            MainCircuitType::FinalReducedRiscVMachine => final_reduced_risc_v_machine::NUM_CYCLES,
            MainCircuitType::MachineWithoutSignedMulDiv => {
                machine_without_signed_mul_div::NUM_CYCLES
            }
            MainCircuitType::ReducedRiscVLog23Machine => reduced_risc_v_log_23_machine::NUM_CYCLES,
            MainCircuitType::ReducedRiscVMachine => reduced_risc_v_machine::NUM_CYCLES,
            MainCircuitType::RiscVCycles => risc_v_cycles::NUM_CYCLES,
        }
    }

    pub fn get_domain_size(&self) -> usize {
        match self {
            MainCircuitType::FinalReducedRiscVMachine => final_reduced_risc_v_machine::DOMAIN_SIZE,
            MainCircuitType::MachineWithoutSignedMulDiv => {
                machine_without_signed_mul_div::DOMAIN_SIZE
            }
            MainCircuitType::ReducedRiscVLog23Machine => reduced_risc_v_log_23_machine::DOMAIN_SIZE,
            MainCircuitType::ReducedRiscVMachine => reduced_risc_v_machine::DOMAIN_SIZE,
            MainCircuitType::RiscVCycles => risc_v_cycles::DOMAIN_SIZE,
        }
    }

    pub fn get_lde_factor(&self) -> usize {
        match self {
            MainCircuitType::FinalReducedRiscVMachine => final_reduced_risc_v_machine::LDE_FACTOR,
            MainCircuitType::MachineWithoutSignedMulDiv => {
                machine_without_signed_mul_div::LDE_FACTOR
            }
            MainCircuitType::ReducedRiscVLog23Machine => reduced_risc_v_log_23_machine::LDE_FACTOR,
            MainCircuitType::ReducedRiscVMachine => reduced_risc_v_machine::LDE_FACTOR,
            MainCircuitType::RiscVCycles => risc_v_cycles::LDE_FACTOR,
        }
    }

    pub fn get_lde_source_cosets(&self) -> &'static [usize] {
        match self {
            MainCircuitType::FinalReducedRiscVMachine => {
                final_reduced_risc_v_machine::LDE_SOURCE_COSETS
            }
            MainCircuitType::MachineWithoutSignedMulDiv => {
                machine_without_signed_mul_div::LDE_SOURCE_COSETS
            }
            MainCircuitType::ReducedRiscVLog23Machine => {
                reduced_risc_v_log_23_machine::LDE_SOURCE_COSETS
            }
            MainCircuitType::ReducedRiscVMachine => reduced_risc_v_machine::LDE_SOURCE_COSETS,
            MainCircuitType::RiscVCycles => risc_v_cycles::LDE_SOURCE_COSETS,
        }
    }

    pub fn get_tree_cap_size(&self) -> usize {
        match self {
            MainCircuitType::FinalReducedRiscVMachine => {
                final_reduced_risc_v_machine::TREE_CAP_SIZE
            }
            MainCircuitType::MachineWithoutSignedMulDiv => {
                machine_without_signed_mul_div::TREE_CAP_SIZE
            }
            MainCircuitType::ReducedRiscVLog23Machine => {
                reduced_risc_v_log_23_machine::TREE_CAP_SIZE
            }
            MainCircuitType::ReducedRiscVMachine => reduced_risc_v_machine::TREE_CAP_SIZE,
            MainCircuitType::RiscVCycles => risc_v_cycles::TREE_CAP_SIZE,
        }
    }

    pub fn get_allowed_delegation_circuit_types(
        &self,
    ) -> impl Iterator<Item = DelegationCircuitType> {
        match self {
            MainCircuitType::FinalReducedRiscVMachine => {
                final_reduced_risc_v_machine::ALLOWED_DELEGATION_CSRS
            }
            MainCircuitType::MachineWithoutSignedMulDiv => {
                machine_without_signed_mul_div::ALLOWED_DELEGATION_CSRS
            }
            MainCircuitType::ReducedRiscVLog23Machine => {
                reduced_risc_v_log_23_machine::ALLOWED_DELEGATION_CSRS
            }
            MainCircuitType::ReducedRiscVMachine => reduced_risc_v_machine::ALLOWED_DELEGATION_CSRS,
            MainCircuitType::RiscVCycles => risc_v_cycles::ALLOWED_DELEGATION_CSRS,
        }
        .iter()
        .map(|id| DelegationCircuitType::from(*id as u16))
    }

    pub fn needs_delegation_challenge(&self) -> bool {
        match self {
            MainCircuitType::FinalReducedRiscVMachine => false,
            MainCircuitType::MachineWithoutSignedMulDiv => true,
            MainCircuitType::ReducedRiscVLog23Machine => true,
            MainCircuitType::ReducedRiscVMachine => true,
            MainCircuitType::RiscVCycles => true,
        }
    }
}

#[repr(u32)]
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum DelegationCircuitType {
    BigIntWithControl = bigint_with_control::DELEGATION_TYPE_ID,
    Blake2WithCompression = blake2_with_compression::DELEGATION_TYPE_ID,
}

impl DelegationCircuitType {
    pub fn get_delegation_type_id(&self) -> u16 {
        *self as u16
    }

    pub fn get_num_delegation_cycles(&self) -> usize {
        match self {
            DelegationCircuitType::BigIntWithControl => bigint_with_control::NUM_DELEGATION_CYCLES,
            DelegationCircuitType::Blake2WithCompression => {
                blake2_with_compression::NUM_DELEGATION_CYCLES
            }
        }
    }

    pub fn get_domain_size(&self) -> usize {
        match self {
            DelegationCircuitType::BigIntWithControl => bigint_with_control::DOMAIN_SIZE,
            DelegationCircuitType::Blake2WithCompression => blake2_with_compression::DOMAIN_SIZE,
        }
    }

    pub fn get_lde_factor(&self) -> usize {
        match self {
            DelegationCircuitType::BigIntWithControl => bigint_with_control::LDE_FACTOR,
            DelegationCircuitType::Blake2WithCompression => blake2_with_compression::LDE_FACTOR,
        }
    }

    pub fn get_lde_source_cosets(&self) -> &'static [usize] {
        match self {
            DelegationCircuitType::BigIntWithControl => bigint_with_control::LDE_SOURCE_COSETS,
            DelegationCircuitType::Blake2WithCompression => {
                blake2_with_compression::LDE_SOURCE_COSETS
            }
        }
    }

    pub fn get_tree_cap_size(&self) -> usize {
        match self {
            DelegationCircuitType::BigIntWithControl => bigint_with_control::TREE_CAP_SIZE,
            DelegationCircuitType::Blake2WithCompression => blake2_with_compression::TREE_CAP_SIZE,
        }
    }

    pub fn get_witness_factory_fn<A: GoodAllocator>(&self) -> fn(A) -> DelegationWitness<A> {
        match self {
            DelegationCircuitType::BigIntWithControl => |allocator| {
                bigint_with_control_factory_fn(
                    bigint_with_control::DELEGATION_TYPE_ID as u16,
                    bigint_with_control::NUM_DELEGATION_CYCLES,
                    allocator,
                )
            },
            DelegationCircuitType::Blake2WithCompression => |allocator| {
                blake2_with_control_factory_fn(
                    blake2_with_compression::DELEGATION_TYPE_ID as u16,
                    blake2_with_compression::NUM_DELEGATION_CYCLES,
                    allocator,
                )
            },
        }
    }
}

impl From<u16> for DelegationCircuitType {
    #[inline(always)]
    fn from(delegation_type: u16) -> Self {
        match delegation_type as u32 {
            bigint_with_control::DELEGATION_TYPE_ID => DelegationCircuitType::BigIntWithControl,
            blake2_with_compression::DELEGATION_TYPE_ID => {
                DelegationCircuitType::Blake2WithCompression
            }
            _ => panic!("unknown delegation type {}", delegation_type),
        }
    }
}
