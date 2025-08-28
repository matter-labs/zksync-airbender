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

} // namespace airbender::witness::layout