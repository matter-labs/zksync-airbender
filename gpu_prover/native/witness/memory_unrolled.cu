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

struct UnrolledFamilyMemorySubtree {
  const OptionU32::Option<DelegationRequestLayout> delegation_request_layout;
  const MachineStatePermutationVariables machine_state_layout;
  const IntermediateStatePermutationVariables intermediate_state_layout;
  const ShuffleRamAccessSets shuffle_ram_access_sets;
};

template <bool COMPUTE_WITNESS, typename ORACLE>
DEVICE_FORCEINLINE void process_machine_state_assuming_preprocessed_decoder(
    const UnrolledFamilyMemorySubtree &subtree, const OptionU32::Option<ColumnAddress> &executor_family_circuit_next_timestamp_aux_var, const ORACLE &oracle,
    const matrix_setter<bf, st_modifier::cg> memory, const matrix_setter<bf, st_modifier::cg> witness, u32 *const __restrict__ decoder_lookup_mapping,
    const unsigned index) {
  const IntermediateStatePermutationVariables input_state_and_decoder_parts = subtree.intermediate_state_layout;
  const ColumnSet<1> execute_column = input_state_and_decoder_parts.execute;
  const bool execute_value = oracle.template get_witness_from_placeholder<bool>({ExecuteOpcodeFamilyCycle}, index);
  write_bool_value(execute_column, execute_value, memory);
  PRINT_U16(M, execute_column, execute_value);
  const ColumnSet<2> initial_pc_columns = input_state_and_decoder_parts.pc;
  const u32 initial_pc_value = oracle.template get_witness_from_placeholder<u32>({PcInit}, index);
  write_u32_value(initial_pc_columns, initial_pc_value, memory);
  PRINT_U32(M, initial_pc_columns, initial_pc_value);
  const ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM> initial_timestamp_columns = input_state_and_decoder_parts.timestamp;
  const TimestampData initial_timestamp_value = oracle.template get_witness_from_placeholder<TimestampData>({OpcodeFamilyCycleInitialTimestamp}, index);
  write_timestamp_value(initial_timestamp_columns, initial_timestamp_value, memory);
  PRINT_TS(M, initial_timestamp_columns, initial_timestamp_value);
  const auto [pc_columns, final_ts_columns] = subtree.machine_state_layout;
  const u32 pc_value = oracle.template get_witness_from_placeholder<u32>({PcFin}, index);
  write_u32_value(pc_columns, pc_value, memory);
  PRINT_U32(M, pc_columns, pc_value);
  TimestampData final_ts_value = oracle.template get_witness_from_placeholder<TimestampData>({OpcodeFamilyCycleInitialTimestamp}, index);
  const bool intermediate_carry_value = final_ts_value.increment();
  write_timestamp_value(final_ts_columns, final_ts_value, memory);
  PRINT_TS(M, final_ts_columns, final_ts_value);
  const ExecutorFamilyDecoderData decoder_data = oracle.get_executor_family_data(index);
  if (input_state_and_decoder_parts.circuit_family_extra_mask.tag == MemorySubtree) {
    const u32 circuit_family_extra_mask = input_state_and_decoder_parts.circuit_family_extra_mask.offset;
    const auto family_mask_column = ColumnSet<1>{circuit_family_extra_mask, 1};
    const u8 family_mask_value = decoder_data.opcode_family_bits;
    write_u8_value(family_mask_column, family_mask_value, memory);
    PRINT_U8(M, family_mask_column, family_mask_value);
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
    const u8 family_mask_value = decoder_data.opcode_family_bits;
    write_u8_value(family_mask_column, family_mask_value, witness);
    PRINT_U8(W, family_mask_column, family_mask_value);
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
  const TimestampScalar cycle_timestamp = oracle.template get_witness_from_placeholder<TimestampData>({OpcodeFamilyCycleInitialTimestamp}, index).as_scalar();
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
      const u8 value = oracle.template get_witness_from_placeholder<u8>({ShuffleRamAddress, i}, index);
      write_u8_value(register_index, value, memory);
      PRINT_U8(M, register_index, value);
      break;
    }
    case RegisterOrRam: {
      const auto [is_register_columns, address_columns] = address.payload.register_or_ram_access_address;
      const bool is_register_value = oracle.template get_witness_from_placeholder<bool>({ShuffleRamIsRegisterAccess, i}, index);
      write_bool_value(is_register_columns, is_register_value, memory);
      PRINT_U16(M, is_register_columns, is_register_value);
      const u32 address_value = oracle.template get_witness_from_placeholder<u32>({ShuffleRamAddress, i}, index);
      write_u32_value(address_columns, address_value, memory);
      PRINT_U32(M, address_columns, address_value);
      break;
    }
    }
    const TimestampData read_timestamp_value = oracle.template get_witness_from_placeholder<TimestampData>({ShuffleRamReadTimestamp, i}, index);
    write_timestamp_value(read_timestamp_columns, read_timestamp_value, memory);
    PRINT_TS(M, read_timestamp_columns, read_timestamp_value);
    const u32 read_value_value = oracle.template get_witness_from_placeholder<u32>({ShuffleRamReadValue, i}, index);
    write_u32_value(read_value_columns, read_value_value, memory);
    PRINT_U32(M, read_value_columns, read_value_value);
    if (tag == Write) {
      const auto write_value_columns = payload.shuffle_ram_query_write_columns.write_value;
      const u32 write_value_value = oracle.template get_witness_from_placeholder<u32>({ShuffleRamWriteValue, i}, index);
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
  const bool execute_delegation_value = oracle.template get_witness_from_placeholder<bool>({ExecuteDelegation}, index);
  write_bool_value(multiplicity, execute_delegation_value, memory);
  PRINT_U16(M, multiplicity, execute_delegation_value);
  const u16 delegation_type_value = oracle.template get_witness_from_placeholder<u16>({DelegationType}, index);
  write_u16_value(delegation_type, delegation_type_value, memory);
  PRINT_U16(M, delegation_type, delegation_type_value);
  if (abi_mem_offset_high.num_elements == 0)
    return;
  const u16 abi_mem_offset_high_value = oracle.template get_witness_from_placeholder<u16>({DelegationABIOffset}, index);
  write_u16_value(abi_mem_offset_high, abi_mem_offset_high_value, memory);
  PRINT_U16(M, abi_mem_offset_high, abi_mem_offset_high_value);
}

template <bool COMPUTE_WITNESS, typename ORACLE>
DEVICE_FORCEINLINE void generate_family(const UnrolledFamilyMemorySubtree &subtree,
                                        const OptionU32::Option<ColumnAddress> &executor_family_circuit_next_timestamp_aux_var,
                                        const MemoryQueriesTimestampComparisonAuxVars &memory_queries_timestamp_comparison_aux_vars, const ORACLE &oracle,
                                        matrix_setter<bf, st_modifier::cg> memory, matrix_setter<bf, st_modifier::cg> witness,
                                        u32 *const __restrict__ decoder_lookup_mapping, const unsigned count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;
  memory.add_row(gid);
  witness.add_row(gid);
  process_machine_state_assuming_preprocessed_decoder<COMPUTE_WITNESS>(subtree, executor_family_circuit_next_timestamp_aux_var, oracle, memory, witness,
                                                                       decoder_lookup_mapping, gid);
  process_shuffle_ram_access_sets<COMPUTE_WITNESS>(subtree.shuffle_ram_access_sets, memory_queries_timestamp_comparison_aux_vars, oracle, memory, witness, gid);
  if (subtree.delegation_request_layout.tag == OptionU32::Some)
    process_delegation_requests(subtree.delegation_request_layout.value, oracle, memory, gid);
}

template <bool COMPUTE_WITNESS>
DEVICE_FORCEINLINE void generate_inits_and_teardowns(const ShuffleRamInitAndTeardownLayouts &init_and_teardown_layouts,
                                                     const ShuffleRamInitsAndTeardowns &inits_and_teardowns,
                                                     const ShuffleRamAuxComparisonSets &aux_comparison_sets, matrix_setter<bf, st_modifier::cg> memory,
                                                     matrix_setter<bf, st_modifier::cg> witness, const unsigned count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;
  memory.add_row(gid);
  witness.add_row(gid);
  process_inits_and_teardowns<COMPUTE_WITNESS>(init_and_teardown_layouts, inits_and_teardowns, aux_comparison_sets, memory, witness, count, gid);
}

EXTERN __global__ void ab_generate_memory_values_unrolled_memory_kernel(const __grid_constant__ UnrolledFamilyMemorySubtree subtree,
                                                                        const __grid_constant__ UnrolledMemoryOracle oracle,
                                                                        const matrix_setter<bf, st_modifier::cg> memory, const unsigned count) {
  generate_family<false>(subtree, {}, {}, oracle, memory, memory, nullptr, count);
}

EXTERN __global__ void ab_generate_memory_values_unrolled_non_memory_kernel(const __grid_constant__ UnrolledFamilyMemorySubtree subtree,
                                                                            const __grid_constant__ UnrolledNonMemoryOracle oracle,
                                                                            const matrix_setter<bf, st_modifier::cg> memory, const unsigned count) {
  generate_family<false>(subtree, {}, {}, oracle, memory, memory, nullptr, count);
}

EXTERN __global__ void ab_generate_memory_values_inits_and_teardowns_kernel(const __grid_constant__ ShuffleRamInitAndTeardownLayouts init_and_teardown_layouts,
                                                                            const __grid_constant__ ShuffleRamInitsAndTeardowns inits_and_teardowns,
                                                                            const matrix_setter<bf, st_modifier::cg> memory, const unsigned count) {
  generate_inits_and_teardowns<false>(init_and_teardown_layouts, inits_and_teardowns, {}, memory, memory, count);
}

EXTERN __global__ void ab_generate_memory_and_witness_values_unrolled_memory_kernel(
    const __grid_constant__ UnrolledFamilyMemorySubtree subtree,
    const __grid_constant__ OptionU32::Option<ColumnAddress> executor_family_circuit_next_timestamp_aux_var,
    const __grid_constant__ MemoryQueriesTimestampComparisonAuxVars memory_queries_timestamp_comparison_aux_vars,
    const __grid_constant__ UnrolledMemoryOracle oracle, const matrix_setter<bf, st_modifier::cg> memory, const matrix_setter<bf, st_modifier::cg> witness,
    u32 *const __restrict__ decoder_lookup_mapping, const unsigned count) {
  generate_family<true>(subtree, executor_family_circuit_next_timestamp_aux_var, memory_queries_timestamp_comparison_aux_vars, oracle, memory, witness,
                        decoder_lookup_mapping, count);
}

EXTERN __global__ void ab_generate_memory_and_witness_values_unrolled_non_memory_kernel(
    const __grid_constant__ UnrolledFamilyMemorySubtree subtree,
    const __grid_constant__ OptionU32::Option<ColumnAddress> executor_family_circuit_next_timestamp_aux_var,
    const __grid_constant__ MemoryQueriesTimestampComparisonAuxVars memory_queries_timestamp_comparison_aux_vars,
    const __grid_constant__ UnrolledNonMemoryOracle oracle, const matrix_setter<bf, st_modifier::cg> memory, const matrix_setter<bf, st_modifier::cg> witness,
    u32 *const __restrict__ decoder_lookup_mapping, const unsigned count) {
  generate_family<true>(subtree, executor_family_circuit_next_timestamp_aux_var, memory_queries_timestamp_comparison_aux_vars, oracle, memory, witness,
                        decoder_lookup_mapping, count);
}

EXTERN __global__ void ab_generate_memory_and_witness_values_inits_and_teardowns_kernel(
    const __grid_constant__ ShuffleRamInitAndTeardownLayouts init_and_teardown_layouts, const __grid_constant__ ShuffleRamInitsAndTeardowns inits_and_teardowns,
    const __grid_constant__ ShuffleRamAuxComparisonSets aux_comparison_sets, const matrix_setter<bf, st_modifier::cg> memory,
    const matrix_setter<bf, st_modifier::cg> witness, const unsigned count) {
  generate_inits_and_teardowns<true>(init_and_teardown_layouts, inits_and_teardowns, aux_comparison_sets, memory, witness, count);
}

} // namespace airbender::witness::memory::unrolled