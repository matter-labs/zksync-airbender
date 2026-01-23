#pragma once

#include "common.cuh"
#include "placeholder.cuh"
#include "trace.cuh"

using namespace ::airbender::witness;
using namespace ::airbender::witness::placeholder;
using namespace ::airbender::witness::trace;

namespace airbender::witness::trace::delegation {

struct RegisterOrIndirectReadData {
  const u32 read_value;
  const TimestampData timestamp;
};

struct RegisterOrIndirectReadWriteData {
  const u32 read_value;
  const u32 write_value;
  const TimestampData timestamp;
};

struct RegisterOrIndirectVariableOffsetData {
  const u16 variable_offset_value;
};

constexpr u16 NON_DETERMINISM_CSR = 0x7c0;

struct BigintWithControlAbiDescription {
  static constexpr unsigned REG_ACCESSES = 3;     // 3 x 16B = 48B
  static constexpr unsigned INDIRECT_READS = 8;   // 8 x 12B = 96B
  static constexpr unsigned INDIRECT_WRITES = 8;  // 8 x 16B = 128B
  static constexpr unsigned VARIABLE_OFFSETS = 0; // 0 x 2B = 0B
  static constexpr u16 DELEGATION_TYPE = NON_DETERMINISM_CSR + 10;
  static constexpr unsigned BASE_REGISTER = 10;
  DEVICE_FORCEINLINE static constexpr bool use_read_indirects(const u16 reg_idx) { return reg_idx == 11; }
};

struct Blake2sRoundFunctionAbiDescription {
  static constexpr unsigned REG_ACCESSES = 3;     // 3 x 16B = 48B
  static constexpr unsigned INDIRECT_READS = 16;  // 16 x 12B = 192B
  static constexpr unsigned INDIRECT_WRITES = 24; // 24 x 16B = 384B
  static constexpr unsigned VARIABLE_OFFSETS = 0; // 0 x 2B = 0B
  static constexpr u16 DELEGATION_TYPE = NON_DETERMINISM_CSR + 7;
  static constexpr unsigned BASE_REGISTER = 10;
  DEVICE_FORCEINLINE static constexpr bool use_read_indirects(const u16 reg_idx) { return reg_idx == 11; }
};

#define KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS 6

struct KeccakSpecial5AbiDescription {
  static constexpr unsigned REG_ACCESSES = 2;                                           // 2 x 16B = 32B
  static constexpr unsigned INDIRECT_READS = 0;                                         // 0 x 12B = 0B
  static constexpr unsigned INDIRECT_WRITES = KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS * 2; // 6 x 2 x 16B = 192B
  static constexpr unsigned VARIABLE_OFFSETS = KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS;    // 6 x 2B = 12B
  static constexpr u16 DELEGATION_TYPE = NON_DETERMINISM_CSR + 11;
  static constexpr unsigned BASE_REGISTER = 10;
  DEVICE_FORCEINLINE static constexpr bool use_read_indirects(const u16) { return false; }
};

template <typename DESCRIPTION> struct DelegationWitness {
  const TimestampScalar write_timestamp;
  // instead of
  // const RegisterOrIndirectReadWriteData reg_accesses[DESCRIPTION::REG_ACCESSES];
  // const RegisterOrIndirectReadData indirect_reads[DESCRIPTION::INDIRECT_READS];
  // const RegisterOrIndirectReadWriteData indirect_writes[DESCRIPTION::INDIRECT_WRITES];
  // const u16 variables_offsets[DESCRIPTION::VARIABLE_OFFSETS];
  // we implement this as a single byte array to avoid compilation errors when some of the arrays would be zero-size
  const u8 contents[DESCRIPTION::REG_ACCESSES * sizeof(RegisterOrIndirectReadWriteData) + DESCRIPTION::INDIRECT_READS * sizeof(RegisterOrIndirectReadData) +
                    DESCRIPTION::INDIRECT_WRITES * sizeof(RegisterOrIndirectReadWriteData) + DESCRIPTION::VARIABLE_OFFSETS * sizeof(u16)];

  DEVICE_FORCEINLINE const RegisterOrIndirectReadWriteData *reg_accesses() const { return reinterpret_cast<const RegisterOrIndirectReadWriteData *>(contents); }

  DEVICE_FORCEINLINE const RegisterOrIndirectReadData *indirect_reads() const {
    constexpr size_t offset = DESCRIPTION::REG_ACCESSES * sizeof(RegisterOrIndirectReadWriteData);
    return reinterpret_cast<const RegisterOrIndirectReadData *>(contents + offset);
  }

  DEVICE_FORCEINLINE const RegisterOrIndirectReadWriteData *indirect_writes() const {
    constexpr size_t offset =
        DESCRIPTION::REG_ACCESSES * sizeof(RegisterOrIndirectReadWriteData) + DESCRIPTION::INDIRECT_READS * sizeof(RegisterOrIndirectReadData);
    return reinterpret_cast<const RegisterOrIndirectReadWriteData *>(contents + offset);
  }

  DEVICE_FORCEINLINE const u16 *variables_offsets() const {
    constexpr size_t offset = DESCRIPTION::REG_ACCESSES * sizeof(RegisterOrIndirectReadWriteData) +
                              DESCRIPTION::INDIRECT_READS * sizeof(RegisterOrIndirectReadData) +
                              DESCRIPTION::INDIRECT_WRITES * sizeof(RegisterOrIndirectReadWriteData);
    return reinterpret_cast<const u16 *>(contents + offset);
  }
};

template <typename DESCRIPTION> struct DelegationTrace {
  const u32 requests_count;
  const DelegationWitness<DESCRIPTION> *const __restrict__ tracing_data;

  DEVICE_FORCEINLINE u32 get_witness_from_placeholder_u32(const Placeholder placeholder, const unsigned trace_row) const {
    if (trace_row >= requests_count)
      return 0;
    const auto [register_index, word_index] = placeholder.payload;
    const unsigned reg_offset = register_index - DESCRIPTION::BASE_REGISTER;
    const auto cycle_data = tracing_data + trace_row;
    switch (placeholder.tag) {
    case DelegationRegisterReadValue: {
      return cycle_data->reg_accesses()[reg_offset].read_value;
    }
    case DelegationRegisterWriteValue: {
      return cycle_data->reg_accesses()[reg_offset].write_value;
    }
    case DelegationIndirectReadValue: {
      return DESCRIPTION::use_read_indirects(register_index) ? cycle_data->indirect_reads()[word_index].read_value
                                                             : cycle_data->indirect_writes()[word_index].read_value;
    }
    case DelegationIndirectWriteValue: {
      if (DESCRIPTION::use_read_indirects(register_index)) {
        __trap();
      }
      return cycle_data->indirect_writes()[word_index].write_value;
    }
    default:
      __trap();
    }
  }

  DEVICE_FORCEINLINE u16 get_witness_from_placeholder_u16(const Placeholder placeholder, const unsigned trace_row) const {
    if (trace_row >= requests_count)
      return 0;
    switch (placeholder.tag) {
    case DelegationABIOffset:
      return 0;
    case DelegationType:
      return DESCRIPTION::DELEGATION_TYPE;
    case DelegationIndirectAccessVariableOffset: {
      const u32 variable_index = placeholder.payload[0];
      const auto cycle_data = tracing_data + trace_row;
      return cycle_data->variables_offsets()[variable_index];
    }
    default:
      __trap();
    }
  }

  DEVICE_FORCEINLINE bool get_witness_from_placeholder_bool(const Placeholder placeholder, const unsigned trace_row) const {
    if (trace_row >= requests_count)
      return false;
    switch (placeholder.tag) {
    case ExecuteDelegation:
      return true;
    default:
      __trap();
    }
  }

  DEVICE_FORCEINLINE TimestampData get_witness_from_placeholder_ts(const Placeholder placeholder, const unsigned trace_row) const {
    if (trace_row >= requests_count)
      return {};
    const auto [register_index, word_index] = placeholder.payload;
    const unsigned reg_offset = register_index - DESCRIPTION::BASE_REGISTER;
    const auto cycle_data = tracing_data + trace_row;
    switch (placeholder.tag) {
    case DelegationWriteTimestamp:
      return TimestampData::from_scalar(cycle_data->write_timestamp);
    case DelegationRegisterReadTimestamp: {
      return cycle_data->reg_accesses()[reg_offset].timestamp;
    }
    case DelegationIndirectReadTimestamp: {
      return DESCRIPTION::use_read_indirects(register_index) ? cycle_data->indirect_reads()[word_index].timestamp
                                                             : cycle_data->indirect_writes()[word_index].timestamp;
    }
    default:
      __trap();
    }
  }
};

typedef DelegationTrace<BigintWithControlAbiDescription> BigintWithControlOracle;
typedef DelegationTrace<Blake2sRoundFunctionAbiDescription> Blake2WithCompressionOracle;
typedef DelegationTrace<KeccakSpecial5AbiDescription> KeccakSpecial5Oracle;

} // namespace airbender::witness::trace::delegation