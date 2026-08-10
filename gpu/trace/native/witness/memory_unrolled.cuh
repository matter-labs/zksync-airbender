#pragma once

#include "memory.cuh"
#include "option.cuh"
#include "placeholder.cuh"
#include "trace_unrolled.cuh"

using namespace ::airbender::trace::witness::memory;
using namespace ::airbender::trace::witness::option;
using namespace ::airbender::trace::witness::placeholder;
using namespace ::airbender::trace::witness::trace::unrolled;

namespace airbender::trace::witness::memory::unrolled {

#define MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT 4

struct MachineState {
  const u32 pc[REGISTER_SIZE];
  const u32 timestamp[NUM_TIMESTAMP_COLUMNS_FOR_RAM];
};

struct MachineStatePermutationDescription {
  const u32 execute;
  const MachineState initial_state;
  const MachineState final_state;
};

#define MAX_CIRCUIT_FAMILY_MASK_BITS 32

struct DecoderPlacementDescription {
  const u32 rs1_index;
  const Address rs2_index;
  const Address rd_index;
  const u32 circuit_family_mask_bits_count;
  const Address circuit_family_mask_bits[MAX_CIRCUIT_FAMILY_MASK_BITS];
  const bool decoder_witness_is_in_memory;
  const u32 imm[REGISTER_SIZE];
  const OptionU32::Option<u32> funct3;
};

struct UnrolledMemoryLayout {
  const u32 shuffle_ram_access_sets_count;
  const RamQuery shuffle_ram_access_sets[MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT];
  const MachineStatePermutationDescription machine_state;
  const DecoderPlacementDescription decoder_input;
  const u32 decoder_lookup_offset;
};

struct AuxLayoutData {
  RamAuxComparisonSet shuffle_ram_timestamp_comparison_aux_vars[MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT];
};

template <unsigned N, typename T> DEVICE_FORCEINLINE void copy_array(const T src[N], T dst[N]) {
#pragma unroll
  for (unsigned i = 0; i < N; i++)
    dst[i] = src[i];
}

DEVICE_FORCEINLINE void copy_timestamp(const u32 src[NUM_TIMESTAMP_COLUMNS_FOR_RAM], u32 dst[NUM_TIMESTAMP_COLUMNS_FOR_RAM]) {
  copy_array<NUM_TIMESTAMP_COLUMNS_FOR_RAM>(src, dst);
}

DEVICE_FORCEINLINE void copy_register(const u32 src[REGISTER_SIZE], u32 dst[REGISTER_SIZE]) { copy_array<REGISTER_SIZE>(src, dst); }

struct NoopUnrolledCapture {
  DEVICE_FORCEINLINE void on_machine_state(bool, u32, TimestampData, u32, TimestampData) const {}
  DEVICE_FORCEINLINE void on_decoder(const ExecutorFamilyDecoderData &) const {}

  template <unsigned I> DEVICE_FORCEINLINE void on_ram_access(TimestampData, u32, bool, u32, bool) const {}
};

template <bool COMPUTE_WITNESS, typename ORACLE, typename Capture>
DEVICE_FORCEINLINE void
process_machine_state_assuming_preprocessed_decoder(const UnrolledMemoryLayout &layout, const ORACLE &oracle, const matrix_setter<bf, st_modifier::cg> memory,
                                                    const matrix_setter<bf, st_modifier::cg> witness, u32 *const __restrict__ decoder_lookup_mapping,
                                                    Capture &capture, const unsigned index) {
  const MachineStatePermutationDescription machine_state = layout.machine_state;
  const u32 execute_column = machine_state.execute;
  const bool execute_value = oracle.get_witness_from_placeholder_bool({ExecuteOpcodeFamilyCycle}, index);
  write_bool_value(execute_column, execute_value, memory);
  PRINT_U16(M, execute_column, execute_value);
  const auto [initial_pc_columns, initial_timestamp_columns] = machine_state.initial_state;
  const u32 initial_pc_value = oracle.get_witness_from_placeholder_u32({PcInit}, index);
  write_u32_value(initial_pc_columns, initial_pc_value, memory);
  PRINT_U32(M, initial_pc_columns, initial_pc_value);
  const TimestampData initial_timestamp_value = oracle.get_witness_from_placeholder_ts({OpcodeFamilyCycleInitialTimestamp}, index);
  write_timestamp_value(initial_timestamp_columns, initial_timestamp_value, memory);
  PRINT_TS(M, initial_timestamp_columns, initial_timestamp_value);
  const auto [final_pc_columns, final_timestamp_columns] = machine_state.final_state;
  const u32 final_pc_value = oracle.get_witness_from_placeholder_u32({PcFin}, index);
  write_u32_value(final_pc_columns, final_pc_value, memory);
  PRINT_U32(M, final_pc_columns, final_pc_value);
  TimestampData final_timestamp_value = initial_timestamp_value;
  final_timestamp_value.increment();
  write_timestamp_value(final_timestamp_columns, final_timestamp_value, memory);
  PRINT_TS(M, final_timestamp_columns, final_timestamp_value);
  capture.on_machine_state(execute_value, initial_pc_value, initial_timestamp_value, final_pc_value, final_timestamp_value);
  const DecoderPlacementDescription decoder_input = layout.decoder_input;
  const ExecutorFamilyDecoderData decoder_data = oracle.get_executor_family_data(index);
  capture.on_decoder(decoder_data);
#pragma unroll
  for (int i = 0; i < MAX_CIRCUIT_FAMILY_MASK_BITS; i++) {
    if (i == decoder_input.circuit_family_mask_bits_count)
      break;
    const auto circuit_family_mask_bit = decoder_input.circuit_family_mask_bits[i];
    if (circuit_family_mask_bit.tag != BaseLayerMemory)
      continue;
    const bool bit = decoder_data.opcode_family_bits & (1 << i);
    const u32 family_mask_bit_column = circuit_family_mask_bit.offset;
    write_bool_value(family_mask_bit_column, bit, memory);
    PRINT_R32(M, family_mask_bit_column, bit);
  }
  if (!COMPUTE_WITNESS)
    return;
  if (decoder_input.rs2_index.tag == BaseLayerWitness) {
    const u32 rs2_index_column = decoder_input.rs2_index.offset;
    const u16 rs2_index_value = decoder_data.rs2_index;
    write_u16_value(rs2_index_column, rs2_index_value, witness);
    PRINT_U16(W, rs2_index_column, rs2_index_value);
  }
  if (decoder_input.rd_index.tag == BaseLayerWitness) {
    const u32 rd_index_column = decoder_input.rd_index.offset;
    const u8 rd_index_value = decoder_data.rd_index;
    write_u8_value(rd_index_column, rd_index_value, witness);
    PRINT_U8(W, rd_index_column, rd_index_value);
  }
#pragma unroll
  for (int i = 0; i < MAX_CIRCUIT_FAMILY_MASK_BITS; i++) {
    if (i == decoder_input.circuit_family_mask_bits_count)
      break;
    const auto circuit_family_mask_bit = decoder_input.circuit_family_mask_bits[i];
    if (circuit_family_mask_bit.tag != BaseLayerWitness)
      continue;
    const bool bit = decoder_data.opcode_family_bits & (1 << i);
    const u32 family_mask_bit_column = circuit_family_mask_bit.offset;
    write_bool_value(family_mask_bit_column, bit, witness);
    PRINT_R32(W, family_mask_bit_column, bit);
  }
  if (decoder_input.decoder_witness_is_in_memory)
    return;
  u32 imm_columns[REGISTER_SIZE] = {};
  copy_register(decoder_input.imm, imm_columns);
  const u32 imm_value = decoder_data.imm;
  write_u32_value(imm_columns, imm_value, witness);
  PRINT_U32(W, imm_columns, imm_value);
  if (decoder_input.funct3.tag == OptionU32::Some) {
    const u32 funct3_column = decoder_input.funct3.value;
    const u8 funct3_value = decoder_data.funct3;
    write_u8_value(funct3_column, funct3_value, witness);
    PRINT_U8(W, funct3_column, funct3_value);
  }
  decoder_lookup_mapping[index] = execute_value ? initial_pc_value / 4 + layout.decoder_lookup_offset : 0xffffffff;
}

template <unsigned I, bool COMPUTE_WITNESS, typename ORACLE, typename Capture>
DEVICE_FORCEINLINE void process_shuffle_ram_access_set(const UnrolledMemoryLayout &layout, const AuxLayoutData &aux_layout_data, const ORACLE &oracle,
                                                       const TimestampScalar cycle_timestamp, const matrix_setter<bf, st_modifier::cg> memory,
                                                       const matrix_setter<bf, st_modifier::cg> witness, Capture &capture, const unsigned index) {
  if (I >= layout.shuffle_ram_access_sets_count)
    return;
  const auto [tag, payload] = layout.shuffle_ram_access_sets[I];
  RamAddress address = {};
  u32 read_timestamp_columns[NUM_TIMESTAMP_COLUMNS_FOR_RAM] = {};
  RamWordRepresentation read_value = {};
  switch (tag) {
  case Readonly: {
    const auto query = payload.ram_read_query;
    address = query.address;
    copy_timestamp(query.read_timestamp, read_timestamp_columns);
    read_value = query.read_value;
    break;
  }
  case Write: {
    const auto query = payload.ram_write_query;
    address = query.address;
    copy_timestamp(query.read_timestamp, read_timestamp_columns);
    read_value = query.read_value;
    break;
  }
  }
  switch (address.tag) {
  case RegisterOnly: {
    const u32 register_index = address.payload.register_only_access_address.register_index;
    const u16 value = oracle.get_witness_from_placeholder_u16({ShuffleRamAddress, I}, index);
    write_u16_value(register_index, value, memory);
    PRINT_U16(M, register_index, value);
    break;
  }
  case RegisterOrRam: {
    const auto [address_space, address_columns] = address.payload.register_or_ram_access_address;
    const bool is_register_value = oracle.get_witness_from_placeholder_bool({ShuffleRamIsRegisterAccess, I}, index);
    switch (address_space.tag) {
    case RegisterAddressSpace: {
      write_bool_value(address_space.value, is_register_value, memory);
      PRINT_U16(M, address_space.value, is_register_value);
      break;
    }
    case RamAddressSpace: {
      write_bool_value(address_space.value, !is_register_value, memory);
      PRINT_U16(M, address_space.value, !is_register_value);
      break;
    }
    }
    const u32 address_value = oracle.get_witness_from_placeholder_u32({ShuffleRamAddress, I}, index);
    write_u32_value(address_columns, address_value, memory);
    PRINT_U32(M, address_columns, address_value);
    break;
  }
  }
  const TimestampData read_timestamp_value = oracle.get_witness_from_placeholder_ts({ShuffleRamReadTimestamp, I}, index);
  write_timestamp_value(read_timestamp_columns, read_timestamp_value, memory);
  PRINT_TS(M, read_timestamp_columns, read_timestamp_value);
  const u32 read_value_value = oracle.get_witness_from_placeholder_u32({ShuffleRamReadValue, I}, index);
  write_ram_word_value(read_value, read_value_value, memory);
  print_ram_word_value(read_value, read_value_value, index);
  const bool has_write = tag == Write;
  u32 write_value_value = 0;
  if (has_write) {
    const auto write_value = payload.ram_write_query.write_value;
    write_value_value = oracle.get_witness_from_placeholder_u32({ShuffleRamWriteValue, I}, index);
    write_ram_word_value(write_value, write_value_value, memory);
    print_ram_word_value(write_value, write_value_value, index);
  }
  if (!COMPUTE_WITNESS)
    return;
  const auto comparison_set = aux_layout_data.shuffle_ram_timestamp_comparison_aux_vars[I];
  const u32 borrow_address = comparison_set.intermediate_borrow.offset;
  const u32 read_timestamp_low = read_timestamp_value.get_low();
  const TimestampData write_timestamp = TimestampData::from_scalar(cycle_timestamp + I);
  const u32 write_timestamp_low = write_timestamp.get_low();
  const bool intermediate_borrow = TimestampData::sub_borrow(read_timestamp_low, write_timestamp_low).y;
  write_bool_value(borrow_address, intermediate_borrow, witness);
  PRINT_U16(W, borrow_address, intermediate_borrow);
  capture.template on_ram_access<I>(read_timestamp_value, read_value_value, has_write, write_value_value, intermediate_borrow);
}

template <bool COMPUTE_WITNESS, typename ORACLE, typename Capture>
DEVICE_FORCEINLINE void process_shuffle_ram_access_sets(const UnrolledMemoryLayout &layout, const AuxLayoutData &aux_layout_data, const ORACLE &oracle,
                                                        const matrix_setter<bf, st_modifier::cg> memory, const matrix_setter<bf, st_modifier::cg> witness,
                                                        Capture &capture, const unsigned index) {
  const TimestampScalar cycle_timestamp = oracle.get_witness_from_placeholder_ts({OpcodeFamilyCycleInitialTimestamp}, index).as_scalar();
  process_shuffle_ram_access_set<0, COMPUTE_WITNESS>(layout, aux_layout_data, oracle, cycle_timestamp, memory, witness, capture, index);
  process_shuffle_ram_access_set<1, COMPUTE_WITNESS>(layout, aux_layout_data, oracle, cycle_timestamp, memory, witness, capture, index);
  process_shuffle_ram_access_set<2, COMPUTE_WITNESS>(layout, aux_layout_data, oracle, cycle_timestamp, memory, witness, capture, index);
  process_shuffle_ram_access_set<3, COMPUTE_WITNESS>(layout, aux_layout_data, oracle, cycle_timestamp, memory, witness, capture, index);
}

} // namespace airbender::trace::witness::memory::unrolled
