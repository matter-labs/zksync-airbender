#pragma once

#include "column.cuh"

using namespace ::airbender::witness::column;

namespace airbender::witness::layout {

struct ShuffleRamInitAndTeardownLayout {
  ColumnSet<REGISTER_SIZE> lazy_init_addresses_columns;
  ColumnSet<REGISTER_SIZE> lazy_teardown_values_columns;
  ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM> lazy_teardown_timestamps_columns;
};

struct DelegationRequestLayout {
  ColumnSet<1> multiplicity;
  ColumnSet<1> delegation_type;
  ColumnSet<1> abi_mem_offset_high;
};

struct DelegationProcessingLayout {
  ColumnSet<1> multiplicity;
  ColumnSet<1> abi_mem_offset_high;
  ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM> write_timestamp;
};

struct MachineStatePermutationVariables {
  const ColumnSet<2> pc;
  ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM> timestamp;
};

struct IntermediateStatePermutationVariables {
  const ColumnSet<1> execute;
  const ColumnSet<2> pc;
  const ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM> timestamp;
  const ColumnSet<1> rs1_index;
  const ColumnAddress rs2_index;
  const ColumnAddress rd_index;
  const bool decoder_witness_is_in_memory;
  const ColumnSet<1> rd_is_zero;
  const ColumnSet<REGISTER_SIZE> imm;
  const ColumnSet<1> funct3;
  const ColumnSet<1> funct7;
  const ColumnSet<1> circuit_family;
  const ColumnAddress circuit_family_extra_mask;
};

} // namespace airbender::witness::layout