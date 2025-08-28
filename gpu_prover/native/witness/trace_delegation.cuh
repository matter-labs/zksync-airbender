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

#define MAX_INDIRECT_ACCESS_REGISTERS 2
#define MAX_INDIRECT_ACCESS_WORDS 24
#define USE_WRITES_MASK (1u << 31)

struct DelegationTrace {
  const u32 num_requests;
  const u32 num_register_accesses_per_delegation;
  const u32 num_indirect_reads_per_delegation;
  const u32 num_indirect_writes_per_delegation;
  const u32 base_register_index;
  const u16 delegation_type;
  const u32 indirect_accesses_properties[MAX_INDIRECT_ACCESS_REGISTERS][MAX_INDIRECT_ACCESS_WORDS];
  const TimestampData *const write_timestamp;
  const RegisterOrIndirectReadWriteData *const register_accesses;
  const RegisterOrIndirectReadData *const indirect_reads;
  const RegisterOrIndirectReadWriteData *const indirect_writes;

  template <typename T> DEVICE_FORCEINLINE T get_witness_from_placeholder(Placeholder, unsigned) const;
};

template <> DEVICE_FORCEINLINE u32 DelegationTrace::get_witness_from_placeholder<u32>(const Placeholder placeholder, const unsigned trace_row) const {
  if (trace_row >= num_requests)
    return 0;
  const auto [register_index, word_index] = placeholder.payload.delegation_payload;
  const unsigned register_offset = register_index - base_register_index;
  switch (placeholder.tag) {
  case DelegationRegisterReadValue: {
    const unsigned offset = trace_row * num_register_accesses_per_delegation + register_offset;
    return register_accesses[offset].read_value;
  }
  case DelegationRegisterWriteValue: {
    const unsigned offset = trace_row * num_register_accesses_per_delegation + register_offset;
    return register_accesses[offset].write_value;
  }
  case DelegationIndirectReadValue: {
    const u32 access = indirect_accesses_properties[register_offset][word_index];
    const bool use_writes = access & USE_WRITES_MASK;
    const u32 index = access & ~USE_WRITES_MASK;
    const u32 t = use_writes ? num_indirect_writes_per_delegation : num_indirect_reads_per_delegation;
    const unsigned offset = trace_row * t + index;
    return use_writes ? indirect_writes[offset].read_value : indirect_reads[offset].read_value;
  }
  case DelegationIndirectWriteValue: {
    const u32 access = indirect_accesses_properties[register_offset][word_index];
    const u32 index = access & ~USE_WRITES_MASK;
    const unsigned offset = trace_row * num_indirect_writes_per_delegation + index;
    return indirect_writes[offset].write_value;
  }
  default:
    __trap();
  }
}

template <> DEVICE_FORCEINLINE u16 DelegationTrace::get_witness_from_placeholder<u16>(const Placeholder placeholder, const unsigned trace_row) const {
  if (trace_row >= num_requests)
    return 0;
  switch (placeholder.tag) {
  case DelegationABIOffset:
    return 0;
  case DelegationType:
    return delegation_type;
  default:
    __trap();
  }
}

template <> DEVICE_FORCEINLINE bool DelegationTrace::get_witness_from_placeholder<bool>(const Placeholder placeholder, const unsigned trace_row) const {
  if (trace_row >= num_requests)
    return false;
  switch (placeholder.tag) {
  case ExecuteDelegation:
    return true;
  default:
    __trap();
  }
}

template <>
DEVICE_FORCEINLINE TimestampData DelegationTrace::get_witness_from_placeholder<TimestampData>(const Placeholder placeholder, const unsigned trace_row) const {
  if (trace_row >= num_requests)
    return {};
  const auto [register_index, word_index] = placeholder.payload.delegation_payload;
  switch (placeholder.tag) {
  case DelegationWriteTimestamp:
    return write_timestamp[trace_row];
  case DelegationRegisterReadTimestamp: {
    const unsigned register_offset = register_index - base_register_index;
    const unsigned offset = trace_row * num_register_accesses_per_delegation + register_offset;
    return register_accesses[offset].timestamp;
  }
  case DelegationIndirectReadTimestamp: {
    const unsigned register_offset = register_index - base_register_index;
    const u32 access = indirect_accesses_properties[register_offset][word_index];
    const bool use_writes = access & USE_WRITES_MASK;
    const u32 index = access & ~USE_WRITES_MASK;
    const u32 t = use_writes ? num_indirect_writes_per_delegation : num_indirect_reads_per_delegation;
    const unsigned offset = trace_row * t + index;
    return use_writes ? indirect_writes[offset].timestamp : indirect_reads[offset].timestamp;
  }
  default:
    __trap();
  }
}

} // namespace airbender::witness::trace::delegation