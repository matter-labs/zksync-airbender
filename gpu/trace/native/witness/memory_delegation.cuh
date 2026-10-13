#pragma once

#include "memory.cuh"
#include "option.cuh"
#include "trace_delegation.cuh"

using namespace ::airbender::trace::witness::memory;
using namespace ::airbender::trace::witness::option;
using namespace ::airbender::trace::witness::trace::delegation;

namespace airbender::trace::witness::memory::delegation {

#define MAX_RAM_ACCESS_SETS_COUNT 64
#define MAX_INDIRECT_ACCESS_VARIABLE_OFFSETS_COUNT 16
#define MAX_RELATIVE_TIMESTAMP_GROUPS_COUNT 8
#define MAX_RELATIVE_TIMESTAMP_GROUP_MEMBERS_COUNT 16

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

struct RelativeTimestampGroup {
  const u32 borrow;
  const u32 members_count;
  const u32 members[MAX_RELATIVE_TIMESTAMP_GROUP_MEMBERS_COUNT];
};

struct OptionalRamAuxComparisonSet {
  const OptionU32::OptionTag tag;
  const u32 intermediate_borrow;
};

struct DelegationAuxLayoutData {
  const OptionalRamAuxComparisonSet shuffle_ram_timestamp_comparison_aux_vars[MAX_RAM_ACCESS_SETS_COUNT];
  const u32 relative_timestamp_groups_count;
  const RelativeTimestampGroup relative_timestamp_groups[MAX_RELATIVE_TIMESTAMP_GROUPS_COUNT];
};

static_assert(sizeof(OptionalRamAuxComparisonSet) == 8);
static_assert(offsetof(OptionalRamAuxComparisonSet, intermediate_borrow) == 4);
static_assert(sizeof(RelativeTimestampGroup) == 72);
static_assert(offsetof(RelativeTimestampGroup, borrow) == 0);
static_assert(offsetof(RelativeTimestampGroup, members_count) == 4);
static_assert(offsetof(RelativeTimestampGroup, members) == 8);
static_assert(offsetof(DelegationAuxLayoutData, relative_timestamp_groups_count) == 512);
static_assert(offsetof(DelegationAuxLayoutData, relative_timestamp_groups) == 516);
static_assert(sizeof(DelegationAuxLayoutData) == 1092);

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

template <typename DESCRIPTION>
DEVICE_FORCEINLINE TimestampData get_read_timestamp(const RamAddress &address, const DelegationTrace<DESCRIPTION> &oracle, const unsigned index) {
  switch (address.tag) {
  case ConstantRegister:
    return oracle.get_witness_from_placeholder_ts({DelegationRegisterReadTimestamp, address.payload.constant_register_access_address.register_index}, index);
  case IndirectRam: {
    const auto &indirect = address.payload.indirect_ram_access_address;
    return oracle.get_witness_from_placeholder_ts({DelegationIndirectReadTimestamp, {indirect.base_register_index, indirect.indirect_access_idx_for_register}},
                                                  index);
  }
  case RegisterOnly:
  case RegisterOrRam:
    __trap();
  }
  return {};
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

    const auto &comparison_set = aux_layout_data.shuffle_ram_timestamp_comparison_aux_vars[access_idx];
    if (comparison_set.tag == OptionU32::None)
      continue;

    const u32 borrow_address = comparison_set.intermediate_borrow;
    const TimestampData write_timestamp = TimestampData::from_scalar(invocation_timestamp.as_scalar() + local_timestamp_in_cycle);
    const bool intermediate_borrow = TimestampData::sub_borrow(read_timestamp_value.get_low(), write_timestamp.get_low()).y;
    write_bool_value(borrow_address, intermediate_borrow, witness);
    PRINT_U16(W, borrow_address, intermediate_borrow);
  }

  if (!COMPUTE_WITNESS)
    return;

  for (u32 group_idx = 0; group_idx < MAX_RELATIVE_TIMESTAMP_GROUPS_COUNT; ++group_idx) {
    if (group_idx == aux_layout_data.relative_timestamp_groups_count)
      break;

    const auto &group = aux_layout_data.relative_timestamp_groups[group_idx];
    TimestampData read_timestamp_value{};
    for (u32 member_idx = 0; member_idx < MAX_RELATIVE_TIMESTAMP_GROUP_MEMBERS_COUNT; ++member_idx) {
      if (member_idx == group.members_count)
        break;
      const auto &mem_query = layout.ram_access_sets[group.members[member_idx]];
      const RamAddress &address = mem_query.tag == Readonly ? mem_query.payload.ram_read_query.address : mem_query.payload.ram_write_query.address;
      const TimestampData member_read_timestamp_value = get_read_timestamp(address, oracle, index);
      if (member_idx == 0)
        read_timestamp_value = member_read_timestamp_value;
      else if (member_read_timestamp_value.as_scalar() != read_timestamp_value.as_scalar())
        __trap();
    }

    const u32 borrow = invocation_timestamp.get_high() - read_timestamp_value.get_high();
    if (borrow > 1)
      __trap();
    write_bool_value(group.borrow, borrow, witness);
    PRINT_U16(W, group.borrow, borrow);
  }
}

template <bool COMPUTE_WITNESS, typename DESCRIPTION, typename Memory, typename Witness>
DEVICE_FORCEINLINE void process_delegation_row(const DelegationMemoryLayout &layout, const DelegationAuxLayoutData &aux_layout_data,
                                               const DelegationTrace<DESCRIPTION> &oracle, const Memory &memory, const Witness &witness, const unsigned index) {
  process_delegation_requests_execution(layout.delegation_state, oracle, memory, index);
  process_indirect_memory_accesses<COMPUTE_WITNESS>(layout, aux_layout_data, oracle, memory, witness, index);
}

} // namespace airbender::trace::witness::memory::delegation
