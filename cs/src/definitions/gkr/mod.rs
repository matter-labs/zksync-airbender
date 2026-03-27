use super::{Box, Vec};

mod lookup;
mod ram_access;
mod utils;

pub use self::lookup::*;
pub use self::ram_access::*;
pub use self::utils::*;

use crate::definitions::GKRAddress;
use crate::definitions::REGISTER_SIZE;
use crate::gkr_compiler::CompiledDelegationCircuitState;
use common_constants::NUM_TIMESTAMP_COLUMNS_FOR_RAM;

#[derive(Clone, Copy, Hash, Debug, serde::Serialize, serde::Deserialize)]
pub struct GKRMachineState {
    pub pc: [usize; REGISTER_SIZE],
    pub timestamp: [usize; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
}

#[derive(Clone, Copy, Hash, Debug, serde::Serialize, serde::Deserialize)]
pub struct MachineStatePermutationDescription {
    pub execute: usize,
    pub initial_state: GKRMachineState,
    pub final_state: GKRMachineState,
}

#[derive(Clone, Hash, Debug, serde::Serialize, serde::Deserialize)]
pub struct DecoderPlacementDescription {
    // rs1 is always in memory
    pub rs1_index: usize,
    // can be memory or witness, as there can be some selection there
    pub rs2_index: GKRAddress,
    pub rd_index: GKRAddress,
    // can rarely happen to be in memory columns too
    pub circuit_family_mask_bits: Box<[GKRAddress]>,
    // the rest are either all in memory, or all in witness
    pub decoder_witness_is_in_memory: bool,
    pub imm: [usize; REGISTER_SIZE],
    pub funct3: Option<usize>,
}

#[derive(Clone, Debug, Hash, serde::Serialize, serde::Deserialize)]
pub struct GKRMemoryLayout {
    pub ram_access_sets: Vec<RamQuery>,
    pub machine_state: Option<MachineStatePermutationDescription>,
    pub delegation_state: Option<CompiledDelegationCircuitState>,
    pub decoder_input: Option<DecoderPlacementDescription>,
    pub indirect_access_variable_offsets: Vec<usize>,
    pub total_width: usize,
}

#[derive(Clone, Debug, Hash, serde::Serialize, serde::Deserialize)]
pub struct GKRWitnessLayout {
    // we use separate multiplicities columns for tables of width 1 for an optimization
    // in the prover
    pub multiplicities_columns_for_range_check_16: core::ops::Range<usize>,
    pub multiplicities_columns_for_timestamp_range_check: usize,
    pub multiplicities_columns_for_generic_lookup: core::ops::Range<usize>,
    pub total_width: usize,
}
