#include "layout.cuh"
#include "memory.cuh"
#include "option.cuh"
#include "trace_main.cuh"

using namespace ::airbender::witness::layout;
using namespace ::airbender::witness::memory;
using namespace ::airbender::witness::option;
using namespace ::airbender::witness::trace::main;

namespace airbender::witness::memory::main {

struct MainMemorySubtree {
  const ShuffleRamInitAndTeardownLayouts shuffle_ram_init_and_teardown_layouts;
  const ShuffleRamAccessSets shuffle_ram_access_sets;
  const OptionU32::Option<DelegationRequestLayout> delegation_request_layout;
};

template <bool COMPUTE_WITNESS>
DEVICE_FORCEINLINE void process_shuffle_ram_access_sets(const ShuffleRamAccessSets &shuffle_ram_access_sets,
                                                        const MemoryQueriesTimestampComparisonAuxVars &memory_queries_timestamp_comparison_aux_vars,
                                                        const MainTrace &oracle, const TimestampScalar timestamp_high_from_circuit_sequence,
                                                        const matrix_setter<bf, st_modifier::cg> memory, const matrix_setter<bf, st_modifier::cg> witness,
                                                        const unsigned index) {
#pragma unroll
  for (u32 i = 0; i < MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT; ++i) {
    if (i == shuffle_ram_access_sets.count)
      break;
    const auto [tag, payload] = shuffle_ram_access_sets.sets[i];
    ShuffleRamAddressEnum address = {};
    ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM> read_timestamp_columns = {};
    ColumnSet<REGISTER_SIZE> read_value_columns = {};
    switch (tag) {
    case Readonly: {
      auto columns = payload.shuffle_ram_query_read_columns;
      address = columns.address;
      read_timestamp_columns = columns.read_timestamp;
      read_value_columns = columns.read_value;
      break;
    }
    case Write: {
      const auto columns = payload.shuffle_ram_query_write_columns;
      address = columns.address;
      read_timestamp_columns = columns.read_timestamp;
      read_value_columns = columns.read_value;
      break;
    }
    }
    switch (address.tag) {
    case RegisterOnly: {
      const auto register_index = address.payload.register_only_access_address.register_index;
      const u16 value = oracle.get_witness_from_placeholder<u16>({ShuffleRamAddress, i}, index);
      write_u16_value(register_index, value, memory);
      PRINT_U16(M, register_index, value);
      break;
    }
    case RegisterOrRam: {
      const auto [is_register_columns, address_columns] = address.payload.register_or_ram_access_address;
      const bool is_register_value = oracle.get_witness_from_placeholder<bool>({ShuffleRamIsRegisterAccess, i}, index);
      write_bool_value(is_register_columns, is_register_value, memory);
      PRINT_U16(M, is_register_columns, is_register_value);
      const u32 address_value = oracle.get_witness_from_placeholder<u32>({ShuffleRamAddress, i}, index);
      write_u32_value(address_columns, address_value, memory);
      PRINT_U32(M, address_columns, address_value);
      break;
    }
    }
    const TimestampData read_timestamp_value = oracle.get_witness_from_placeholder<TimestampData>({ShuffleRamReadTimestamp, i}, index);
    write_timestamp_value(read_timestamp_columns, read_timestamp_value, memory);
    PRINT_TS(M, read_timestamp_columns, read_timestamp_value);
    const u32 read_value_value = oracle.get_witness_from_placeholder<u32>({ShuffleRamReadValue, i}, index);
    write_u32_value(read_value_columns, read_value_value, memory);
    PRINT_U32(M, read_value_columns, read_value_value);
    if (tag == Write) {
      const auto write_value_columns = payload.shuffle_ram_query_write_columns.write_value;
      const u32 write_value_value = oracle.get_witness_from_placeholder<u32>({ShuffleRamWriteValue, i}, index);
      write_u32_value(write_value_columns, write_value_value, memory);
      PRINT_U32(M, write_value_columns, write_value_value);
    }
    if (!COMPUTE_WITNESS)
      continue;
    const TimestampScalar write_timestamp_base =
        timestamp_high_from_circuit_sequence + (static_cast<TimestampScalar>(index + 1) << TimestampData::NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP);
    const ColumnAddress borrow_address = memory_queries_timestamp_comparison_aux_vars.addresses[i];
    const u32 read_timestamp_low = read_timestamp_value.get_low();
    const TimestampData write_timestamp = TimestampData::from_scalar(write_timestamp_base + i);
    const u32 write_timestamp_low = write_timestamp.get_low();
    const bool intermediate_borrow = TimestampData::sub_borrow(read_timestamp_low, write_timestamp_low).y;
    write_bool_value(borrow_address, intermediate_borrow, witness);
    PRINT_U16(W, borrow_address, intermediate_borrow);
  }
}

DEVICE_FORCEINLINE void process_delegation_requests(const DelegationRequestLayout &delegation_request_layout, const MainTrace &oracle,
                                                    const matrix_setter<bf, st_modifier::cg> memory, const unsigned index) {
  const auto [multiplicity, delegation_type, abi_mem_offset_high] = delegation_request_layout;
  const bool execute_delegation_value = oracle.get_witness_from_placeholder<bool>({ExecuteDelegation}, index);
  write_bool_value(multiplicity, execute_delegation_value, memory);
  PRINT_U16(M, multiplicity, execute_delegation_value);
  const u16 delegation_type_value = oracle.get_witness_from_placeholder<u16>({DelegationType}, index);
  write_u16_value(delegation_type, delegation_type_value, memory);
  PRINT_U16(M, delegation_type, delegation_type_value);
  const u16 abi_mem_offset_high_value = oracle.get_witness_from_placeholder<u16>({DelegationABIOffset}, index);
  write_u16_value(abi_mem_offset_high, abi_mem_offset_high_value, memory);
  PRINT_U16(M, abi_mem_offset_high, abi_mem_offset_high_value);
}

template <bool COMPUTE_WITNESS>
DEVICE_FORCEINLINE void generate(const MainMemorySubtree &subtree, const MemoryQueriesTimestampComparisonAuxVars &memory_queries_timestamp_comparison_aux_vars,
                                 const ShuffleRamInitsAndTeardowns &inits_and_teardowns, const ShuffleRamAuxComparisonSets &aux_comparison_sets,
                                 const MainTrace &oracle, const TimestampScalar timestamp_high_from_circuit_sequence,
                                 matrix_setter<bf, st_modifier::cg> memory, matrix_setter<bf, st_modifier::cg> witness, const unsigned count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;
  memory.add_row(gid);
  witness.add_row(gid);
  process_inits_and_teardowns<COMPUTE_WITNESS>(subtree.shuffle_ram_init_and_teardown_layouts, inits_and_teardowns, aux_comparison_sets, memory, witness, count,
                                               gid);
  process_shuffle_ram_access_sets<COMPUTE_WITNESS>(subtree.shuffle_ram_access_sets, memory_queries_timestamp_comparison_aux_vars, oracle,
                                                   timestamp_high_from_circuit_sequence, memory, witness, gid);
  if (subtree.delegation_request_layout.tag == OptionU32::Some)
    process_delegation_requests(subtree.delegation_request_layout.value, oracle, memory, gid);
}

EXTERN __global__ void ab_generate_memory_values_main_kernel(const __grid_constant__ MainMemorySubtree subtree,
                                                             const __grid_constant__ ShuffleRamInitsAndTeardowns inits_and_teardowns,
                                                             const __grid_constant__ MainTrace oracle, const matrix_setter<bf, st_modifier::cg> memory,
                                                             const unsigned count) {
  generate<false>(subtree, {}, inits_and_teardowns, {}, oracle, {}, memory, memory, count);
}

EXTERN __global__ void ab_generate_memory_and_witness_values_main_kernel(
    const __grid_constant__ MainMemorySubtree subtree,
    const __grid_constant__ MemoryQueriesTimestampComparisonAuxVars memory_queries_timestamp_comparison_aux_vars,
    const __grid_constant__ ShuffleRamInitsAndTeardowns inits_and_teardowns, const __grid_constant__ ShuffleRamAuxComparisonSets aux_comparison_sets,
    const __grid_constant__ MainTrace oracle, const __grid_constant__ TimestampScalar timestamp_high_from_circuit_sequence,
    const matrix_setter<bf, st_modifier::cg> memory, const matrix_setter<bf, st_modifier::cg> witness, const unsigned count) {
  generate<true>(subtree, memory_queries_timestamp_comparison_aux_vars, inits_and_teardowns, aux_comparison_sets, oracle, timestamp_high_from_circuit_sequence,
                 memory, witness, count);
}

} // namespace airbender::witness::memory::main