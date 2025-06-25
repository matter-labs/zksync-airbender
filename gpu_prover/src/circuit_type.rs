use prover::risc_v_simulator::delegations::blake2_round_function_with_compression_mode::BLAKE2_ROUND_FUNCTION_WITH_EXTENDED_CONTROL_ACCESS_ID;
use prover::risc_v_simulator::delegations::u256_ops_with_control::U256_OPS_WITH_CONTROL_ACCESS_ID;

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum CircuitType {
    Main(MainCircuitType),
    Delegation(DelegationCircuitType),
}

impl CircuitType {
    pub fn from_delegation_type(delegation_type: u16) -> Self {
        Self::Delegation(delegation_type.into())
    }

    pub fn as_main(&self) -> Option<MainCircuitType> {
        match self {
            CircuitType::Main(circuit_type) => Some(*circuit_type),
            _ => None,
        }
    }

    pub fn as_delegation(&self) -> Option<DelegationCircuitType> {
        match self {
            CircuitType::Delegation(circuit_type) => Some(*circuit_type),
            _ => None,
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum MainCircuitType {
    FinalReducedRiscVMachine,
    MachineWithoutSignedMulDiv,
    ReducedRiscVMachine,
    RiscVCycles,
}

#[repr(u32)]
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum DelegationCircuitType {
    BigIntWithControl = U256_OPS_WITH_CONTROL_ACCESS_ID,
    Blake2WithCompression = BLAKE2_ROUND_FUNCTION_WITH_EXTENDED_CONTROL_ACCESS_ID,
}

impl From<u16> for DelegationCircuitType {
    fn from(delegation_type: u16) -> Self {
        match delegation_type as u32 {
            U256_OPS_WITH_CONTROL_ACCESS_ID => DelegationCircuitType::BigIntWithControl,
            BLAKE2_ROUND_FUNCTION_WITH_EXTENDED_CONTROL_ACCESS_ID => {
                DelegationCircuitType::Blake2WithCompression
            }
            _ => panic!("unknown delegation type {}", delegation_type),
        }
    }
}
