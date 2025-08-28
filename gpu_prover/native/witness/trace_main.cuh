#pragma once

#include "placeholder.cuh"
#include "trace.cuh"

using namespace ::airbender::witness::placeholder;
using namespace ::airbender::witness::trace;

namespace airbender::witness::trace::main {

struct __align__(8) SingleCycleTracingData {
  u32 pc;
  u32 rs1_read_value;
  TimestampData rs1_read_timestamp;
  u16 rs1_reg_idx;
  // 16
  u32 rs2_or_mem_word_read_value;
  RegIndexOrMemWordIndex rs2_or_mem_word_address;
  TimestampData rs2_or_mem_read_timestamp;
  u16 delegation_request;
  // 32
  u32 rd_or_mem_word_read_value;
  u32 rd_or_mem_word_write_value;
  RegIndexOrMemWordIndex rd_or_mem_word_address;
  TimestampData rd_or_mem_read_timestamp;
  // 52
  u32 non_determinism_read;
};

struct MainTrace {
  const SingleCycleTracingData *const __restrict__ cycle_data;

  template <typename T> DEVICE_FORCEINLINE T get_witness_from_placeholder(Placeholder, unsigned) const;
};

template <> DEVICE_FORCEINLINE u32 MainTrace::get_witness_from_placeholder<u32>(const Placeholder placeholder, const unsigned trace_step) const {
  const SingleCycleTracingData *const data = &cycle_data[trace_step];
  switch (placeholder.tag) {
  case PcInit:
    return data->pc;
  case SecondRegMem:
    return data->rs2_or_mem_word_read_value;
  case WriteRdReadSetWitness:
    return data->rd_or_mem_word_read_value;
  case MemSlot: {
    // decide whether we did store or load
    const auto rs2_or_mem_address_is_register = data->rs2_or_mem_word_address.is_register();
    const auto rd_or_mem_address_is_register = data->rd_or_mem_word_address.is_register();
    if (!rs2_or_mem_address_is_register && rd_or_mem_address_is_register) {
      // it is LOAD
      // In this case we return from rs2 or mem
      return data->rs2_or_mem_word_read_value;
    }
    if (rs2_or_mem_address_is_register && !rd_or_mem_address_is_register) {
      // it is STORE
      // In this case we return from rd or mem
      return data->rd_or_mem_word_read_value;
    }
    return 0;
  };
  case ShuffleRamAddress: {
    switch (placeholder.payload.u32) {
    case 0:
      return data->rs1_reg_idx;
    case 1:
      return data->rs2_or_mem_word_address.as_u32_formal_address();
    case 2:
      return data->rd_or_mem_word_address.as_u32_formal_address();
    default:
      __trap();
    }
  }
  case ShuffleRamReadValue: {
    switch (placeholder.payload.u32) {
    case 0:
      return data->rs1_read_value;
    case 1:
      return data->rs2_or_mem_word_read_value;
    case 2:
      return data->rd_or_mem_word_read_value;
    default:
      __trap();
    }
  }
  case ShuffleRamWriteValue: {
    switch (placeholder.payload.u32) {
    case 0:
      return data->rs1_read_value;
    case 1:
      return data->rs2_or_mem_word_read_value;
    case 2:
      return data->rd_or_mem_word_write_value;
    default:
      __trap();
    }
  }
  case ExternalOracle:
    return data->non_determinism_read;
  default:
    __trap();
  }
}

template <> DEVICE_FORCEINLINE u16 MainTrace::get_witness_from_placeholder<u16>(const Placeholder placeholder, const unsigned trace_step) const {
  const SingleCycleTracingData *const data = &cycle_data[trace_step];
  switch (placeholder.tag) {
  case DelegationABIOffset:
    return 0;
  case DelegationType:
    return data->delegation_request;
  case ShuffleRamAddress: {
    switch (placeholder.payload.u32) {
    case 0:
      return data->rs1_reg_idx;
    case 1:
      return data->rs2_or_mem_word_address.as_u32_formal_address();
    case 2:
      return data->rd_or_mem_word_address.as_u32_formal_address();
    default:
      __trap();
    }
  }
  case ExecuteDelegation:
    return data->delegation_request != 0;
  default:
    __trap();
  }
}

template <> DEVICE_FORCEINLINE bool MainTrace::get_witness_from_placeholder<bool>(const Placeholder placeholder, const unsigned trace_step) const {
  const SingleCycleTracingData *data = &cycle_data[trace_step];
  switch (placeholder.tag) {
  case ShuffleRamIsRegisterAccess:
    switch (placeholder.payload.u32) {
    case 0:
      return true;
    case 1:
      return data->rs2_or_mem_word_address.is_register();
    case 2:
      return data->rd_or_mem_word_address.is_register();
    default:
      __trap();
    }
  case ExecuteDelegation:
    return data->delegation_request != 0;
  default:
    __trap();
  }
}

template <>
DEVICE_FORCEINLINE TimestampData MainTrace::get_witness_from_placeholder<TimestampData>(const Placeholder placeholder, const unsigned trace_step) const {
  const SingleCycleTracingData *data = &cycle_data[trace_step];
  switch (placeholder.tag) {
  case ShuffleRamReadTimestamp:
    switch (placeholder.payload.u32) {
    case 0:
      return data->rs1_read_timestamp;
    case 1:
      return data->rs2_or_mem_read_timestamp;
    case 2:
      return data->rd_or_mem_read_timestamp;
    default:
      __trap();
    }
  default:
    __trap();
  }
}

struct __align__(16) LazyInitAndTeardown {
  u32 address;
  u32 teardown_value;
  TimestampData teardown_timestamp;
};

struct ShuffleRamSetupAndTeardown {
  const LazyInitAndTeardown *const __restrict__ lazy_init_data;
};

} // namespace airbender::witness::trace::main