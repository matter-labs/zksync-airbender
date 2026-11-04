#include "layout.cuh"
#include "memory.cuh"
#include "option.cuh"
#include "placeholder.cuh"
#include "trace_unrolled.cuh"

using namespace ::airbender::witness::layout;
using namespace ::airbender::witness::memory;
using namespace ::airbender::witness::option;
using namespace ::airbender::witness::placeholder;
using namespace ::airbender::witness::trace::unrolled;

namespace airbender::witness::memory::unrolled {

struct ShuffleRamAuxComparisonSets {
  const u32 count;
  const ShuffleRamAuxComparisonSet sets[MAX_INITS_AND_TEARDOWNS_SETS_COUNT];
};

#define MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT 4

struct MemoryQueriesTimestampComparisonAuxVars {
  const u32 count;
  const ColumnAddress addresses[MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT];
};

struct ShuffleRamAccessSets {
  const u32 count;
  const ShuffleRamQueryColumns sets[MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT];
};

struct __align__(16) InitAndTeardown {
  u32 address;
  u32 teardown_value;
  TimestampData teardown_timestamp;
};

struct ShuffleRamInitsAndTeardowns {
  const u32 count;
  const InitAndTeardown *const __restrict__ inits_and_teardowns;
};

struct UnrolledFamilyMemorySubtree {
  const ShuffleRamInitAndTeardownLayouts init_and_teardown_layouts;
  const MachineStatePermutationVariables machine_state_layout;
  const IntermediateStatePermutationVariables intermediate_state_layout;
  const ShuffleRamAccessSets shuffle_ram_access_sets;
  const OptionU32::Option<DelegationRequestLayout> delegation_request_layout;
};

template <bool COMPUTE_WITNESS>
DEVICE_FORCEINLINE void process_inits_and_teardowns(const ShuffleRamInitAndTeardownLayouts &init_and_teardown_layouts,
                                                    const ShuffleRamAuxComparisonSets &aux_comparison_sets,
                                                    const ShuffleRamInitsAndTeardowns &inits_and_teardowns, const matrix_setter<bf, st_modifier::cg> memory,
                                                    const matrix_setter<bf, st_modifier::cg> witness, const unsigned count, const unsigned index) {
  const unsigned padding = init_and_teardown_layouts.count * count - inits_and_teardowns.count;
  const auto get_data = [=](const unsigned absolute_index) -> InitAndTeardown {
    return absolute_index >= padding ? inits_and_teardowns.inits_and_teardowns[absolute_index - padding] : InitAndTeardown{};
  };
#pragma unroll
  for (u32 i = 0; i < MAX_INITS_AND_TEARDOWNS_SETS_COUNT; ++i) {
    if (i == init_and_teardown_layouts.count)
      break;
    const auto [addresses_columns, values_columns, timestamps_columns] = init_and_teardown_layouts.layouts[i];
    const auto [init_address, teardown_value, teardown_timestamp] = get_data(i * count + index);
    write_u32_value(addresses_columns, init_address, memory);
    PRINT_U32(M, addresses_columns, init_address);
    write_u32_value(values_columns, teardown_value, memory);
    PRINT_U32(M, values_columns, teardown_value);
    write_timestamp_value(timestamps_columns, teardown_timestamp, memory);
    PRINT_TS(M, timestamps_columns, teardown_timestamp);
    if (!COMPUTE_WITNESS)
      continue;
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
      const u32 next_row_lazy_init_address_value = get_data(i * count + index + 1).address;
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
    const auto [aux_low_high, intermediate_borrow_address, final_borrow_address] = aux_comparison_sets.sets[i];
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
}

template <bool COMPUTE_WITNESS, typename ORACLE>
DEVICE_FORCEINLINE void process_machine_state_assuming_preprocessed_decoder(
    const UnrolledFamilyMemorySubtree &subtree, const OptionU32::Option<ColumnAddress> &executor_family_circuit_next_timestamp_aux_var, const ORACLE &oracle,
    const matrix_setter<bf, st_modifier::cg> memory, const matrix_setter<bf, st_modifier::cg> witness, u32 *const __restrict__ decoder_lookup_mapping,
    const unsigned index) {
  const IntermediateStatePermutationVariables input_state_and_decoder_parts = subtree.intermediate_state_layout;
  const ColumnSet<1> execute_column = input_state_and_decoder_parts.execute;
  const bool execute_value = oracle.get_witness_from_placeholder_bool({ExecuteOpcodeFamilyCycle}, index);
  write_bool_value(execute_column, execute_value, memory);
  PRINT_U16(M, execute_column, execute_value);
  const ColumnSet<2> initial_pc_columns = input_state_and_decoder_parts.pc;
  const u32 initial_pc_value = oracle.get_witness_from_placeholder_u32({PcInit}, index);
  write_u32_value(initial_pc_columns, initial_pc_value, memory);
  PRINT_U32(M, initial_pc_columns, initial_pc_value);
  const ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM> initial_timestamp_columns = input_state_and_decoder_parts.timestamp;
  const TimestampData initial_timestamp_value = oracle.get_witness_from_placeholder_ts({OpcodeFamilyCycleInitialTimestamp}, index);
  write_timestamp_value(initial_timestamp_columns, initial_timestamp_value, memory);
  PRINT_TS(M, initial_timestamp_columns, initial_timestamp_value);
  const auto [pc_columns, final_ts_columns] = subtree.machine_state_layout;
  const u32 pc_value = oracle.get_witness_from_placeholder_u32({PcFin}, index);
  write_u32_value(pc_columns, pc_value, memory);
  PRINT_U32(M, pc_columns, pc_value);
  TimestampData final_ts_value = oracle.get_witness_from_placeholder_ts({OpcodeFamilyCycleInitialTimestamp}, index);
  const bool intermediate_carry_value = final_ts_value.increment();
  write_timestamp_value(final_ts_columns, final_ts_value, memory);
  PRINT_TS(M, final_ts_columns, final_ts_value);
  const ExecutorFamilyDecoderData decoder_data = oracle.get_executor_family_data(index);
  if (input_state_and_decoder_parts.circuit_family_extra_mask.tag == MemorySubtree) {
    const u32 circuit_family_extra_mask = input_state_and_decoder_parts.circuit_family_extra_mask.offset;
    const auto family_mask_column = ColumnSet<1>{circuit_family_extra_mask, 1};
    const u32 family_mask_value = decoder_data.opcode_family_bits;
    write_u32_as_bf_value(family_mask_column, family_mask_value, memory);
    PRINT_R32(M, family_mask_column, family_mask_value);
  }
  if (!COMPUTE_WITNESS)
    return;
  if (executor_family_circuit_next_timestamp_aux_var.tag == OptionU32::Some) {
    const ColumnAddress immediate_carry_column = executor_family_circuit_next_timestamp_aux_var.value;
    write_bool_value(immediate_carry_column, intermediate_carry_value, witness);
    PRINT_U16(W, immediate_carry_column, intermediate_carry_value);
  }
  if (input_state_and_decoder_parts.rs2_index.tag == WitnessSubtree) {
    const u32 offset = input_state_and_decoder_parts.rs2_index.offset;
    const auto rs2_index_column = ColumnSet<1>{offset, 1};
    const u8 rs2_index_value = decoder_data.rs2_index;
    write_u8_value(rs2_index_column, rs2_index_value, witness);
    PRINT_U8(W, rs2_index_column, rs2_index_value);
  }
  if (input_state_and_decoder_parts.rd_index.tag == WitnessSubtree) {
    const u32 offset = input_state_and_decoder_parts.rd_index.offset;
    const auto rd_index_column = ColumnSet<1>{offset, 1};
    const u8 rd_index_value = decoder_data.rd_index;
    write_u8_value(rd_index_column, rd_index_value, witness);
    PRINT_U8(W, rd_index_column, rd_index_value);
  }
  if (input_state_and_decoder_parts.circuit_family_extra_mask.tag == WitnessSubtree) {
    const u32 circuit_family_extra_mask = input_state_and_decoder_parts.circuit_family_extra_mask.offset;
    const auto family_mask_column = ColumnSet<1>{circuit_family_extra_mask, 1};
    const u32 family_mask_value = decoder_data.opcode_family_bits;
    write_u32_as_bf_value(family_mask_column, family_mask_value, witness);
    PRINT_R32(W, family_mask_column, family_mask_value);
  }
  if (input_state_and_decoder_parts.decoder_witness_is_in_memory)
    return;
  const ColumnSet<1> rd_is_zero_column = input_state_and_decoder_parts.rd_is_zero;
  const bool rd_is_zero_value = decoder_data.rd_is_zero;
  write_bool_value(rd_is_zero_column, rd_is_zero_value, witness);
  PRINT_U16(W, rd_is_zero_column, rd_is_zero_value);
  const ColumnSet<REGISTER_SIZE> imm_columns = input_state_and_decoder_parts.imm;
  const u32 imm_value = decoder_data.imm;
  write_u32_value(imm_columns, imm_value, witness);
  PRINT_U32(W, imm_columns, imm_value);
  const ColumnSet<1> funct3_column = input_state_and_decoder_parts.funct3;
  const u8 funct3_value = decoder_data.funct3;
  write_u8_value(funct3_column, funct3_value, witness);
  PRINT_U8(W, funct3_column, funct3_value);
  decoder_lookup_mapping[index] = execute_value ? initial_pc_value / 4 : 0xffffffff;
}

template <bool COMPUTE_WITNESS, typename ORACLE>
DEVICE_FORCEINLINE void process_shuffle_ram_access_sets(const ShuffleRamAccessSets &shuffle_ram_access_sets,
                                                        const MemoryQueriesTimestampComparisonAuxVars &memory_queries_timestamp_comparison_aux_vars,
                                                        const ORACLE &oracle, const matrix_setter<bf, st_modifier::cg> memory,
                                                        const matrix_setter<bf, st_modifier::cg> witness, const unsigned index) {
  const TimestampScalar cycle_timestamp = oracle.get_witness_from_placeholder_ts({OpcodeFamilyCycleInitialTimestamp}, index).as_scalar();
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
      const u8 value = oracle.get_witness_from_placeholder_u8({ShuffleRamAddress, i}, index);
      write_u8_value(register_index, value, memory);
      PRINT_U8(M, register_index, value);
      break;
    }
    case RegisterOrRam: {
      const auto [is_register_columns, address_columns] = address.payload.register_or_ram_access_address;
      const bool is_register_value = oracle.get_witness_from_placeholder_bool({ShuffleRamIsRegisterAccess, i}, index);
      write_bool_value(is_register_columns, is_register_value, memory);
      PRINT_U16(M, is_register_columns, is_register_value);
      const u32 address_value = oracle.get_witness_from_placeholder_u32({ShuffleRamAddress, i}, index);
      write_u32_value(address_columns, address_value, memory);
      PRINT_U32(M, address_columns, address_value);
      break;
    }
    }
    const TimestampData read_timestamp_value = oracle.get_witness_from_placeholder_ts({ShuffleRamReadTimestamp, i}, index);
    write_timestamp_value(read_timestamp_columns, read_timestamp_value, memory);
    PRINT_TS(M, read_timestamp_columns, read_timestamp_value);
    const u32 read_value_value = oracle.get_witness_from_placeholder_u32({ShuffleRamReadValue, i}, index);
    write_u32_value(read_value_columns, read_value_value, memory);
    PRINT_U32(M, read_value_columns, read_value_value);
    if (tag == Write) {
      const auto write_value_columns = payload.shuffle_ram_query_write_columns.write_value;
      const u32 write_value_value = oracle.get_witness_from_placeholder_u32({ShuffleRamWriteValue, i}, index);
      write_u32_value(write_value_columns, write_value_value, memory);
      PRINT_U32(M, write_value_columns, write_value_value);
    }
    if (!COMPUTE_WITNESS)
      continue;
    const ColumnAddress borrow_address = memory_queries_timestamp_comparison_aux_vars.addresses[i];
    const u32 read_timestamp_low = read_timestamp_value.get_low();
    const TimestampData write_timestamp = TimestampData::from_scalar(cycle_timestamp + i);
    const u32 write_timestamp_low = write_timestamp.get_low();
    const bool intermediate_borrow = TimestampData::sub_borrow(read_timestamp_low, write_timestamp_low).y;
    write_bool_value(borrow_address, intermediate_borrow, witness);
    PRINT_U16(W, borrow_address, intermediate_borrow);
  }
}

template <typename ORACLE>
DEVICE_FORCEINLINE void process_delegation_requests(const DelegationRequestLayout &delegation_request_layout, const ORACLE &oracle,
                                                    const matrix_setter<bf, st_modifier::cg> memory, const unsigned index) {
  const auto [multiplicity, delegation_type, abi_mem_offset_high] = delegation_request_layout;
  const bool execute_delegation_value = oracle.get_witness_from_placeholder_bool({ExecuteDelegation}, index);
  write_bool_value(multiplicity, execute_delegation_value, memory);
  PRINT_U16(M, multiplicity, execute_delegation_value);
  const u16 delegation_type_value = oracle.get_witness_from_placeholder_u16({DelegationType}, index);
  write_u16_value(delegation_type, delegation_type_value, memory);
  PRINT_U16(M, delegation_type, delegation_type_value);
  if (abi_mem_offset_high.num_elements == 0)
    return;
  const u16 abi_mem_offset_high_value = oracle.get_witness_from_placeholder_u16({DelegationABIOffset}, index);
  write_u16_value(abi_mem_offset_high, abi_mem_offset_high_value, memory);
  PRINT_U16(M, abi_mem_offset_high, abi_mem_offset_high_value);
}

EXTERN __global__ void ab_generate_memory_values_unrolled_memory_kernel(const __grid_constant__ UnrolledFamilyMemorySubtree subtree,
                                                                        const __grid_constant__ UnrolledMemoryOracle oracle,
                                                                        matrix_setter<bf, st_modifier::cg> memory, const unsigned count) {
  const unsigned index = blockIdx.x * blockDim.x + threadIdx.x;
  if (index >= count)
    return;
  memory.add_row(index);
  process_machine_state_assuming_preprocessed_decoder<false>(subtree, {}, oracle, memory, memory, nullptr, index);
  process_shuffle_ram_access_sets<false>(subtree.shuffle_ram_access_sets, {}, oracle, memory, memory, index);
}

EXTERN __global__ void ab_generate_memory_values_unrolled_non_memory_kernel(const __grid_constant__ UnrolledFamilyMemorySubtree subtree,
                                                                            const __grid_constant__ UnrolledNonMemoryOracle oracle,
                                                                            matrix_setter<bf, st_modifier::cg> memory, const unsigned count) {
  const unsigned index = blockIdx.x * blockDim.x + threadIdx.x;
  if (index >= count)
    return;
  memory.add_row(index);
  process_machine_state_assuming_preprocessed_decoder<false>(subtree, {}, oracle, memory, memory, nullptr, index);
  process_shuffle_ram_access_sets<false>(subtree.shuffle_ram_access_sets, {}, oracle, memory, memory, index);
  if (subtree.delegation_request_layout.tag == OptionU32::Some)
    process_delegation_requests(subtree.delegation_request_layout.value, oracle, memory, index);
}

EXTERN __global__ void
ab_generate_memory_values_unrolled_inits_and_teardowns_kernel(const __grid_constant__ ShuffleRamInitAndTeardownLayouts init_and_teardown_layouts,
                                                              const __grid_constant__ ShuffleRamInitsAndTeardowns inits_and_teardowns,
                                                              matrix_setter<bf, st_modifier::cg> memory, const unsigned count) {
  const unsigned index = blockIdx.x * blockDim.x + threadIdx.x;
  if (index >= count)
    return;
  memory.add_row(index);
  process_inits_and_teardowns<false>(init_and_teardown_layouts, {}, inits_and_teardowns, memory, memory, count, index);
}

EXTERN __global__ void ab_generate_memory_values_unrolled_unified_kernel(const __grid_constant__ UnrolledFamilyMemorySubtree subtree,
                                                                         const __grid_constant__ ShuffleRamInitsAndTeardowns inits_and_teardowns,
                                                                         const __grid_constant__ UnrolledUnifiedOracle oracle,
                                                                         matrix_setter<bf, st_modifier::cg> memory, const unsigned count) {
  const unsigned index = blockIdx.x * blockDim.x + threadIdx.x;
  if (index >= count)
    return;
  memory.add_row(index);
  process_inits_and_teardowns<false>(subtree.init_and_teardown_layouts, {}, inits_and_teardowns, memory, memory, count, index);
  process_machine_state_assuming_preprocessed_decoder<false>(subtree, {}, oracle, memory, memory, nullptr, index);
  process_shuffle_ram_access_sets<false>(subtree.shuffle_ram_access_sets, {}, oracle, memory, memory, index);
  if (subtree.delegation_request_layout.tag == OptionU32::Some)
    process_delegation_requests(subtree.delegation_request_layout.value, oracle, memory, index);
}

EXTERN __global__ void ab_generate_memory_and_witness_values_unrolled_memory_kernel(
    const __grid_constant__ UnrolledFamilyMemorySubtree subtree,
    const __grid_constant__ OptionU32::Option<ColumnAddress> executor_family_circuit_next_timestamp_aux_var,
    const __grid_constant__ MemoryQueriesTimestampComparisonAuxVars memory_queries_timestamp_comparison_aux_vars,
    const __grid_constant__ UnrolledMemoryOracle oracle, matrix_setter<bf, st_modifier::cg> memory, matrix_setter<bf, st_modifier::cg> witness,
    u32 *const __restrict__ decoder_lookup_mapping, const unsigned count) {
  const unsigned index = blockIdx.x * blockDim.x + threadIdx.x;
  if (index >= count)
    return;
  memory.add_row(index);
  witness.add_row(index);
  process_machine_state_assuming_preprocessed_decoder<true>(subtree, executor_family_circuit_next_timestamp_aux_var, oracle, memory, witness,
                                                            decoder_lookup_mapping, index);
  process_shuffle_ram_access_sets<true>(subtree.shuffle_ram_access_sets, memory_queries_timestamp_comparison_aux_vars, oracle, memory, witness, index);
}

EXTERN __global__ void ab_generate_memory_and_witness_values_unrolled_non_memory_kernel(
    const __grid_constant__ UnrolledFamilyMemorySubtree subtree,
    const __grid_constant__ OptionU32::Option<ColumnAddress> executor_family_circuit_next_timestamp_aux_var,
    const __grid_constant__ MemoryQueriesTimestampComparisonAuxVars memory_queries_timestamp_comparison_aux_vars,
    const __grid_constant__ UnrolledNonMemoryOracle oracle, matrix_setter<bf, st_modifier::cg> memory, matrix_setter<bf, st_modifier::cg> witness,
    u32 *const __restrict__ decoder_lookup_mapping, const unsigned count) {
  const unsigned index = blockIdx.x * blockDim.x + threadIdx.x;
  if (index >= count)
    return;
  memory.add_row(index);
  witness.add_row(index);
  process_machine_state_assuming_preprocessed_decoder<true>(subtree, executor_family_circuit_next_timestamp_aux_var, oracle, memory, witness,
                                                            decoder_lookup_mapping, index);
  process_shuffle_ram_access_sets<true>(subtree.shuffle_ram_access_sets, memory_queries_timestamp_comparison_aux_vars, oracle, memory, witness, index);
  if (subtree.delegation_request_layout.tag == OptionU32::Some)
    process_delegation_requests(subtree.delegation_request_layout.value, oracle, memory, index);
}

EXTERN __global__ void ab_generate_memory_and_witness_values_unrolled_inits_and_teardowns_kernel(
    const __grid_constant__ ShuffleRamInitAndTeardownLayouts init_and_teardown_layouts, const __grid_constant__ ShuffleRamAuxComparisonSets aux_comparison_sets,
    const __grid_constant__ ShuffleRamInitsAndTeardowns inits_and_teardowns, matrix_setter<bf, st_modifier::cg> memory,
    matrix_setter<bf, st_modifier::cg> witness, const unsigned count) {
  const unsigned index = blockIdx.x * blockDim.x + threadIdx.x;
  if (index >= count)
    return;
  memory.add_row(index);
  witness.add_row(index);
  process_inits_and_teardowns<true>(init_and_teardown_layouts, aux_comparison_sets, inits_and_teardowns, memory, witness, count, index);
}

EXTERN __global__ void ab_generate_memory_and_witness_values_unrolled_unified_kernel(
    const __grid_constant__ UnrolledFamilyMemorySubtree subtree, const __grid_constant__ ShuffleRamAuxComparisonSets aux_comparison_sets,
    const __grid_constant__ OptionU32::Option<ColumnAddress> executor_family_circuit_next_timestamp_aux_var,
    const __grid_constant__ MemoryQueriesTimestampComparisonAuxVars memory_queries_timestamp_comparison_aux_vars,
    const __grid_constant__ ShuffleRamInitsAndTeardowns inits_and_teardowns, const __grid_constant__ UnrolledUnifiedOracle oracle,
    matrix_setter<bf, st_modifier::cg> memory, matrix_setter<bf, st_modifier::cg> witness, u32 *const __restrict__ decoder_lookup_mapping,
    const unsigned count) {
  const unsigned index = blockIdx.x * blockDim.x + threadIdx.x;
  if (index >= count)
    return;
  memory.add_row(index);
  witness.add_row(index);
  process_inits_and_teardowns<true>(subtree.init_and_teardown_layouts, aux_comparison_sets, inits_and_teardowns, memory, witness, count, index);
  process_machine_state_assuming_preprocessed_decoder<true>(subtree, executor_family_circuit_next_timestamp_aux_var, oracle, memory, witness,
                                                            decoder_lookup_mapping, index);
  process_shuffle_ram_access_sets<true>(subtree.shuffle_ram_access_sets, memory_queries_timestamp_comparison_aux_vars, oracle, memory, witness, index);
  if (subtree.delegation_request_layout.tag == OptionU32::Some)
    process_delegation_requests(subtree.delegation_request_layout.value, oracle, memory, index);
}

} // namespace airbender::witness::memory::unrolled