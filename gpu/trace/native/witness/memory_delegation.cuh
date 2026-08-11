#pragma once

#include "memory.cuh"
#include "trace_delegation.cuh"

using namespace ::airbender::trace::witness::memory;
using namespace ::airbender::trace::witness::trace::delegation;

namespace airbender::trace::witness::memory::delegation {

#define MAX_RAM_ACCESS_SETS_COUNT 64
#define MAX_INDIRECT_ACCESS_VARIABLE_OFFSETS_COUNT 16

struct DelegationProcessingLayout {
  const u32 execute;
  const u32 invocation_timestamp[NUM_TIMESTAMP_COLUMNS_FOR_RAM];
};

struct DelegationMemoryLayout {
  const u32 total_width;
  const DelegationProcessingLayout delegation_state;
  const u32 indirect_access_variable_offsets_count;
  const u16 indirect_access_variable_offsets[MAX_INDIRECT_ACCESS_VARIABLE_OFFSETS_COUNT];
  const u32 ram_access_sets_count;
  const RamQuery ram_access_sets[MAX_RAM_ACCESS_SETS_COUNT];
};

struct DelegationAuxLayoutData {
  const RamAuxComparisonSet shuffle_ram_timestamp_comparison_aux_vars[MAX_RAM_ACCESS_SETS_COUNT];
};

template <typename DESCRIPTION, typename Memory>
DEVICE_FORCEINLINE void process_delegation_requests_execution(const DelegationProcessingLayout &delegation_state, const DelegationTrace<DESCRIPTION> &oracle,
                                                              const Memory &memory, const unsigned index) {
  const bool execute_delegation_value = oracle.get_witness_from_placeholder_bool({ExecuteDelegation}, index);
  write_bool_value(delegation_state.execute, execute_delegation_value, memory);
  PRINT_U16(M, delegation_state.execute, execute_delegation_value);

  const TimestampData delegation_write_timestamp_value = oracle.get_witness_from_placeholder_ts({DelegationWriteTimestamp}, index);
  write_timestamp_value(delegation_state.invocation_timestamp, delegation_write_timestamp_value, memory);
  PRINT_TS(M, delegation_state.invocation_timestamp, delegation_write_timestamp_value);
}

template <bool COMPUTE_WITNESS, typename DESCRIPTION, typename Memory, typename Witness>
DEVICE_FORCEINLINE void process_indirect_memory_accesses(const DelegationMemoryLayout &layout, const DelegationAuxLayoutData &aux_layout_data,
                                                         const DelegationTrace<DESCRIPTION> &oracle, const Memory &memory, const Witness &witness,
                                                         const unsigned index) {
  const TimestampData invocation_timestamp = oracle.get_witness_from_placeholder_ts({DelegationWriteTimestamp}, index);

#pragma unroll
  for (u32 variable_offset_idx = 0; variable_offset_idx < MAX_INDIRECT_ACCESS_VARIABLE_OFFSETS_COUNT; ++variable_offset_idx) {
    if (variable_offset_idx == layout.indirect_access_variable_offsets_count)
      break;
    const u16 value = oracle.get_witness_from_placeholder_u16({DelegationIndirectAccessVariableOffset, variable_offset_idx}, index);
    write_u16_value(layout.indirect_access_variable_offsets[variable_offset_idx], value, memory);
    PRINT_U16(M, layout.indirect_access_variable_offsets[variable_offset_idx], value);
  }

  for (u32 access_idx = 0; access_idx < MAX_RAM_ACCESS_SETS_COUNT; ++access_idx) {
    if (access_idx == layout.ram_access_sets_count)
      break;

    const auto &mem_query = layout.ram_access_sets[access_idx];
    TimestampData read_timestamp_value{};
    u32 local_timestamp_in_cycle = 0;

    switch (mem_query.tag) {
    case Readonly: {
      const auto &query = mem_query.payload.ram_read_query;
      local_timestamp_in_cycle = query.in_cycle_write_index;
      switch (query.address.tag) {
      case ConstantRegister: {
        const u32 register_index = query.address.payload.constant_register_access_address.register_index;
        read_timestamp_value = oracle.get_witness_from_placeholder_ts({DelegationRegisterReadTimestamp, register_index}, index);
        write_timestamp_value(query.read_timestamp, read_timestamp_value, memory);
        PRINT_TS(M, query.read_timestamp, read_timestamp_value);

        const u32 read_value_value = oracle.get_witness_from_placeholder_u32({DelegationRegisterReadValue, register_index}, index);
        write_ram_word_value(query.read_value, read_value_value, memory);
        print_ram_word_value(query.read_value, read_value_value, index);
        break;
      }
      case IndirectRam: {
        const auto &address = query.address.payload.indirect_ram_access_address;
        const u32 register_index = address.base_register_index;
        const u32 word_index = address.indirect_access_idx_for_register;
        read_timestamp_value = oracle.get_witness_from_placeholder_ts({DelegationIndirectReadTimestamp, {register_index, word_index}}, index);
        write_timestamp_value(query.read_timestamp, read_timestamp_value, memory);
        PRINT_TS(M, query.read_timestamp, read_timestamp_value);

        const u32 read_value_value = oracle.get_witness_from_placeholder_u32({DelegationIndirectReadValue, {register_index, word_index}}, index);
        write_ram_word_value(query.read_value, read_value_value, memory);
        print_ram_word_value(query.read_value, read_value_value, index);
        break;
      }
      case RegisterOnly:
      case RegisterOrRam:
        __trap();
      }
      break;
    }
    case Write: {
      const auto &query = mem_query.payload.ram_write_query;
      local_timestamp_in_cycle = query.in_cycle_write_index;
      switch (query.address.tag) {
      case ConstantRegister: {
        const u32 register_index = query.address.payload.constant_register_access_address.register_index;
        read_timestamp_value = oracle.get_witness_from_placeholder_ts({DelegationRegisterReadTimestamp, register_index}, index);
        write_timestamp_value(query.read_timestamp, read_timestamp_value, memory);
        PRINT_TS(M, query.read_timestamp, read_timestamp_value);

        const u32 read_value_value = oracle.get_witness_from_placeholder_u32({DelegationRegisterReadValue, register_index}, index);
        write_ram_word_value(query.read_value, read_value_value, memory);
        print_ram_word_value(query.read_value, read_value_value, index);

        const u32 write_value_value = oracle.get_witness_from_placeholder_u32({DelegationRegisterWriteValue, register_index}, index);
        write_ram_word_value(query.write_value, write_value_value, memory);
        print_ram_word_value(query.write_value, write_value_value, index);
        break;
      }
      case IndirectRam: {
        const auto &address = query.address.payload.indirect_ram_access_address;
        const u32 register_index = address.base_register_index;
        const u32 word_index = address.indirect_access_idx_for_register;
        read_timestamp_value = oracle.get_witness_from_placeholder_ts({DelegationIndirectReadTimestamp, {register_index, word_index}}, index);
        write_timestamp_value(query.read_timestamp, read_timestamp_value, memory);
        PRINT_TS(M, query.read_timestamp, read_timestamp_value);

        const u32 read_value_value = oracle.get_witness_from_placeholder_u32({DelegationIndirectReadValue, {register_index, word_index}}, index);
        write_ram_word_value(query.read_value, read_value_value, memory);
        print_ram_word_value(query.read_value, read_value_value, index);

        const u32 write_value_value = oracle.get_witness_from_placeholder_u32({DelegationIndirectWriteValue, {register_index, word_index}}, index);
        write_ram_word_value(query.write_value, write_value_value, memory);
        print_ram_word_value(query.write_value, write_value_value, index);
        break;
      }
      case RegisterOnly:
      case RegisterOrRam:
        __trap();
      }
      break;
    }
    }

    if (!COMPUTE_WITNESS)
      continue;

    const auto borrow_address = aux_layout_data.shuffle_ram_timestamp_comparison_aux_vars[access_idx].intermediate_borrow;
    const TimestampData write_timestamp = TimestampData::from_scalar(invocation_timestamp.as_scalar() + local_timestamp_in_cycle);
    const bool intermediate_borrow = TimestampData::sub_borrow(read_timestamp_value.get_low(), write_timestamp.get_low()).y;
    write_bool_value(borrow_address, intermediate_borrow, witness);
    PRINT_U16(W, borrow_address, intermediate_borrow);
  }
}

template <bool COMPUTE_WITNESS, typename DESCRIPTION, typename Memory, typename Witness>
DEVICE_FORCEINLINE void process_delegation_row(const DelegationMemoryLayout &layout, const DelegationAuxLayoutData &aux_layout_data,
                                               const DelegationTrace<DESCRIPTION> &oracle, const Memory &memory, const Witness &witness, const unsigned index) {
  process_delegation_requests_execution(layout.delegation_state, oracle, memory, index);
  process_indirect_memory_accesses<COMPUTE_WITNESS>(layout, aux_layout_data, oracle, memory, witness, index);
}

} // namespace airbender::trace::witness::memory::delegation
