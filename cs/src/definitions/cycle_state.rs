use field::PrimeField;

use crate::definitions::{Variable, NUM_TIMESTAMP_COLUMNS_FOR_RAM, REGISTER_SIZE};

use super::{ColumnAddress, ColumnSet};

#[derive(Clone, Copy, Debug)]
pub struct MachineCycleStartOrEndState<F: PrimeField> {
    pub pc: [Variable; 2],
    pub(crate) timestamp: [Variable; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
    pub(crate) _marker: core::marker::PhantomData<F>,
}

// NOTE: unfortunately decoder would need to make some
// bit decompositions to understand how to form an immediate,
// and `circuit_family_extra_mask` for the corresponding families would
// indicate whether it's REG-IMM or REG-REG instruction

#[derive(Clone, Copy, Debug)]
pub struct DecoderData<F: PrimeField> {
    pub rs1_index: Variable,
    pub rs2_index: Variable,
    pub rd_index: Variable,
    pub rd_is_zero: Variable,
    pub imm: [Variable; REGISTER_SIZE],
    pub funct3: Variable,
    pub funct7: Option<Variable>,
    pub circuit_family_extra_mask: Variable,
    pub(crate) _marker: core::marker::PhantomData<F>,
}

#[derive(Clone, Copy, Debug)]
pub struct DecoderDataForDecoderCircuit<F: PrimeField> {
    pub decoder_data: DecoderData<F>,
    pub circuit_family: Variable,
}

#[derive(Clone, Copy, Debug)]
pub struct DecoderCircuitMachineState<F: PrimeField> {
    pub cycle_start_state: MachineCycleStartOrEndState<F>,
    pub decoder_data: DecoderDataForDecoderCircuit<F>,
}

#[derive(Clone, Copy, Debug)]
pub struct OpcodeFamilyCircuitState<F: PrimeField> {
    pub(crate) execute: Variable, // Boolean
    pub cycle_start_state: MachineCycleStartOrEndState<F>,
    pub decoder_data: DecoderData<F>,
    pub cycle_end_state: MachineCycleStartOrEndState<F>,
}

#[derive(Clone, Copy, Debug, serde::Serialize, serde::Deserialize)]
pub struct MachineStatePermutationVariables {
    pub pc: ColumnSet<2>,
    pub timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
}

#[derive(Clone, Copy, Debug, serde::Serialize, serde::Deserialize)]
pub struct IntermediateStatePermutationVariables {
    pub execute: ColumnSet<1>,
    pub pc: ColumnSet<2>,
    pub timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
    pub rs1_index: ColumnSet<1>,
    // can be memory or witness, as there can be some selection there
    pub rs2_index: ColumnAddress,
    pub rd_index: ColumnAddress,
    // the rest are either all in memory, or all in witness
    pub decoder_witness_is_in_memory: bool,
    pub rd_is_zero: ColumnSet<1>,
    pub imm: ColumnSet<REGISTER_SIZE>,
    pub funct3: ColumnSet<1>,
    pub funct7: ColumnSet<1>,         // can be empty
    pub circuit_family: ColumnSet<1>, // can be empty
    pub circuit_family_extra_mask: ColumnAddress,
}
