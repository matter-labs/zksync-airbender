use fft::GoodAllocator;
use prover::tracers::delegation::{
    bigint_with_control_factory_fn, blake2_with_control_factory_fn, DelegationWitness,
};
use trace_and_split::setups::{bigint_with_control, blake2_with_compression};

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
    BigIntWithControl = bigint_with_control::DELEGATION_TYPE_ID,
    Blake2WithCompression = blake2_with_compression::DELEGATION_TYPE_ID,
}

impl DelegationCircuitType {
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
