#include "layout.cuh"
#include "memory.cuh"
#include "option.cuh"
#include "trace_main.cuh"

using namespace ::airbender::witness::layout;
using namespace ::airbender::witness::memory;
using namespace ::airbender::witness::option;
using namespace ::airbender::witness::trace::main;

namespace airbender::witness::memory::main {

#define MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT 4

struct MainMemorySubtree {
  ShuffleRamInitAndTeardownLayout shuffle_ram_inits_and_teardowns;
  u32 shuffle_ram_access_sets_count;
  ShuffleRamQueryColumns shuffle_ram_access_sets[MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT];
  Option<DelegationRequestLayout> delegation_request_layout;
};

struct MemoryQueriesTimestampComparisonAuxVars {
  u32 addresses_count;
  ColumnAddress addresses[MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT];
};

// #define PRINT_THREAD_IDX 0xffffffff
// #define PRINT_U16(p, c, v) if (index == PRINT_THREAD_IDX) printf(#p"[%u] <- %u\n", c.offset, v)
// #define PRINT_U32(p, c, v) if (index == PRINT_THREAD_IDX) printf(#p"[%u] <- %u\n"#p"[%u] <- %u\n", c.offset, v & 0xffff, c.offset + 1, v >> 16)
// #define PRINT_TS(p, c, v) if (index == PRINT_THREAD_IDX) printf(#p"[%u] <- %u\n"#p"[%u] <- %u\n", c.offset, v.get_low(), c.offset + 1, v.get_high())

#define PRINT_U16(p, c, v)
#define PRINT_U32(p, c, v)
#define PRINT_TS(p, c, v)

template <bool COMPUTE_WITNESS>
DEVICE_FORCEINLINE void process_lazy_inits_and_teardowns(const MainMemorySubtree &subtree, const ShuffleRamSetupAndTeardown &setup_and_teardown,
                                                         const ShuffleRamAuxComparisonSet &lazy_init_address_aux_vars,
                                                         const matrix_setter<bf, st_modifier::cg> memory, const matrix_setter<bf, st_modifier::cg> witness,
                                                         const unsigned count, const unsigned index) {
  const auto lazy_inits_and_teardowns = setup_and_teardown.lazy_init_data;
  const auto [addresses_columns, values_columns, timestamps_columns] = subtree.shuffle_ram_inits_and_teardowns;
  const auto [init_address, teardown_value, teardown_timestamp] = lazy_inits_and_teardowns[index];
  write_u32_value(addresses_columns, init_address, memory);
  PRINT_U32(M, addresses_columns, init_address);
  write_u32_value(values_columns, teardown_value, memory);
  PRINT_U32(M, values_columns, teardown_value);
  write_timestamp_value(timestamps_columns, teardown_timestamp, memory);
  PRINT_TS(M, timestamps_columns, teardown_timestamp);
  if (!COMPUTE_WITNESS)
    return;
  u16 low_value;
  u16 high_value;
  bool intermediate_borrow_value;
  bool final_borrow_value;
  if (index == count - 1) {
    low_value = 0;
    high_value = 0;
    intermediate_borrow_value = false;
    final_borrow_value = true;
  } else {
    const u32 next_row_lazy_init_address_value = lazy_inits_and_teardowns[index + 1].address;
    const auto [a_low, a_high] = u32_to_u16_tuple(init_address);
    const auto [b_low, b_high] = u32_to_u16_tuple(next_row_lazy_init_address_value);
    const auto [low, intermediate_borrow] = sub_borrow(a_low, b_low);
    const auto [t, of0] = sub_borrow(a_high, b_high);
    const auto [high, of1] = sub_borrow(t, intermediate_borrow);
    low_value = low;
    high_value = high;
    intermediate_borrow_value = intermediate_borrow;
    final_borrow_value = of0 || of1;
  }
  const auto [aux_low_high, intermediate_borrow_address, final_borrow_address] = lazy_init_address_aux_vars;
  const auto [low_address, high_address] = aux_low_high;
  write_u16_value(low_address, low_value, witness);
  PRINT_U16(W, low_address, low_value);
  write_u16_value(high_address, high_value, witness);
  PRINT_U16(W, high_address, high_value);
  write_bool_value(intermediate_borrow_address, intermediate_borrow_value, witness);
  PRINT_U16(W, intermediate_borrow_address, intermediate_borrow_value);
  write_bool_value(final_borrow_address, final_borrow_value, witness);
  PRINT_U16(W, final_borrow_address, final_borrow_value);
}

template <bool COMPUTE_WITNESS>
DEVICE_FORCEINLINE void
process_shuffle_ram_access_sets(const MainMemorySubtree &subtree, const MemoryQueriesTimestampComparisonAuxVars &memory_queries_timestamp_comparison_aux_vars,
                                const MainTrace &trace, const TimestampScalar timestamp_high_from_circuit_sequence,
                                const matrix_setter<bf, st_modifier::cg> memory, const matrix_setter<bf, st_modifier::cg> witness, const unsigned index) {
#pragma unroll
  for (u32 i = 0; i < MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT; ++i) {
    if (i == subtree.shuffle_ram_access_sets_count)
      break;
    const auto [tag, payload] = subtree.shuffle_ram_access_sets[i];
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
      const u16 value = trace.get_witness_from_placeholder<u16>({ShuffleRamAddress, i}, index);
      write_u16_value(register_index, value, memory);
      PRINT_U16(M, register_index, value);
      break;
    }
    case RegisterOrRam: {
      const auto [is_register_columns, address_columns] = address.payload.register_or_ram_access_address;
      const bool is_register_value = trace.get_witness_from_placeholder<bool>({ShuffleRamIsRegisterAccess, i}, index);
      write_bool_value(is_register_columns, is_register_value, memory);
      PRINT_U16(M, is_register_columns, is_register_value);
      const u32 address_value = trace.get_witness_from_placeholder<u32>({ShuffleRamAddress, i}, index);
      write_u32_value(address_columns, address_value, memory);
      PRINT_U32(M, address_columns, address_value);
      break;
    }
    }
    const TimestampData read_timestamp_value = trace.get_witness_from_placeholder<TimestampData>({ShuffleRamReadTimestamp, i}, index);
    write_timestamp_value(read_timestamp_columns, read_timestamp_value, memory);
    PRINT_TS(M, read_timestamp_columns, read_timestamp_value);
    const u32 read_value_value = trace.get_witness_from_placeholder<u32>({ShuffleRamReadValue, i}, index);
    write_u32_value(read_value_columns, read_value_value, memory);
    PRINT_U32(M, read_value_columns, read_value_value);
    if (tag == Write) {
      const auto write_value_columns = payload.shuffle_ram_query_write_columns.write_value;
      const u32 write_value_value = trace.get_witness_from_placeholder<u32>({ShuffleRamWriteValue, i}, index);
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

DEVICE_FORCEINLINE void process_delegation_requests(const MainMemorySubtree &subtree, const MainTrace &trace, const matrix_setter<bf, st_modifier::cg> memory,
                                                    const unsigned index) {
  const auto [multiplicity, delegation_type, abi_mem_offset_high] = subtree.delegation_request_layout.value;
  const bool execute_delegation_value = trace.get_witness_from_placeholder<bool>({ExecuteDelegation}, index);
  write_bool_value(multiplicity, execute_delegation_value, memory);
  PRINT_U16(M, multiplicity, execute_delegation_value);
  const u16 delegation_type_value = trace.get_witness_from_placeholder<u16>({DelegationType}, index);
  write_u16_value(delegation_type, delegation_type_value, memory);
  PRINT_U16(M, delegation_type, delegation_type_value);
  const u16 abi_mem_offset_high_value = trace.get_witness_from_placeholder<u16>({DelegationABIOffset}, index);
  write_u16_value(abi_mem_offset_high, abi_mem_offset_high_value, memory);
  PRINT_U16(M, abi_mem_offset_high, abi_mem_offset_high_value);
}

template <bool COMPUTE_WITNESS>
DEVICE_FORCEINLINE void generate(const MainMemorySubtree &subtree, const MemoryQueriesTimestampComparisonAuxVars &memory_queries_timestamp_comparison_aux_vars,
                                 const ShuffleRamSetupAndTeardown &setup_and_teardown, const ShuffleRamAuxComparisonSet &lazy_init_address_aux_vars,
                                 const MainTrace &trace, const TimestampScalar timestamp_high_from_circuit_sequence, matrix_setter<bf, st_modifier::cg> memory,
                                 matrix_setter<bf, st_modifier::cg> witness, const unsigned count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;
  memory.add_row(gid);
  witness.add_row(gid);
  process_lazy_inits_and_teardowns<COMPUTE_WITNESS>(subtree, setup_and_teardown, lazy_init_address_aux_vars, memory, witness, count, gid);
  process_shuffle_ram_access_sets<COMPUTE_WITNESS>(subtree, memory_queries_timestamp_comparison_aux_vars, trace, timestamp_high_from_circuit_sequence, memory,
                                                   witness, gid);
  if (subtree.delegation_request_layout.tag == Some)
    process_delegation_requests(subtree, trace, memory, gid);
}

EXTERN __global__ void ab_generate_memory_values_main_kernel(const __grid_constant__ MainMemorySubtree subtree,
                                                             const __grid_constant__ ShuffleRamSetupAndTeardown setup_and_teardown,
                                                             const __grid_constant__ MainTrace trace, const matrix_setter<bf, st_modifier::cg> memory,
                                                             const unsigned count) {
  generate<false>(subtree, {}, setup_and_teardown, {}, trace, {}, memory, memory, count);
}

EXTERN __global__ void ab_generate_memory_and_witness_values_main_kernel(
    const __grid_constant__ MainMemorySubtree subtree,
    const __grid_constant__ MemoryQueriesTimestampComparisonAuxVars memory_queries_timestamp_comparison_aux_vars,
    const __grid_constant__ ShuffleRamSetupAndTeardown setup_and_teardown, const __grid_constant__ ShuffleRamAuxComparisonSet lazy_init_address_aux_vars,
    const __grid_constant__ MainTrace trace, const __grid_constant__ TimestampScalar timestamp_high_from_circuit_sequence,
    const matrix_setter<bf, st_modifier::cg> memory, const matrix_setter<bf, st_modifier::cg> witness, const unsigned count) {
  generate<true>(subtree, memory_queries_timestamp_comparison_aux_vars, setup_and_teardown, lazy_init_address_aux_vars, trace,
                 timestamp_high_from_circuit_sequence, memory, witness, count);
}

} // namespace airbender::witness::memory::main