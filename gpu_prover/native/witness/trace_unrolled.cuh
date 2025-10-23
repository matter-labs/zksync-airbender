#pragma once

#include "option.cuh"
#include "placeholder.cuh"
#include "trace.cuh"

using namespace ::airbender::witness::option;
using namespace ::airbender::witness::placeholder;
using namespace ::airbender::witness::trace;

namespace airbender::witness::trace::unrolled {

static constexpr u32 NON_DETERMINISM_CSR = 0x7c0;

struct ExecutorFamilyDecoderData {
  const u32 imm;
  const u8 rs1_index;
  const u8 rs2_index;
  const u8 rd_index;
  const bool rd_is_zero;
  const u8 funct3;
  const OptionU8::Option<u8> funct7;
  const u8 opcode_family_bits;
};

static constexpr u16 MEM_LOAD_TRACE_DATA_MARKER = 0;
static constexpr u16 MEM_STORE_TRACE_DATA_MARKER = MEM_LOAD_TRACE_DATA_MARKER + 1;

struct LoadOpcodeTracingData {
  const u32 initial_pc;
  const u32 opcode;
  const u32 rs1_value;
  const u32 aligned_ram_address;
  const u32 aligned_ram_read_value;
  const u32 rd_old_value;
  const u32 rd_value;
};

struct StoreOpcodeTracingData {
  const u32 initial_pc;
  const u32 opcode;
  const u32 rs1_value;
  const u32 aligned_ram_address;
  const u32 aligned_ram_old_value;
  const u32 rs2_value;
  const u32 aligned_ram_write_value;
};

union OpcodeTracingData {
  LoadOpcodeTracingData load;
  StoreOpcodeTracingData store;
};

struct MemoryOpcodeTracingDataWithTimestamp {
  const OpcodeTracingData opcode_data;
  const u16 discr;
  const TimestampData rs1_read_timestamp;
  const TimestampData rs2_or_ram_read_timestamp;
  const TimestampData rd_or_ram_read_timestamp;
  const TimestampData cycle_timestamp;

  DEVICE_FORCEINLINE u32 initial_pc() const {
    switch (discr) {
    case MEM_LOAD_TRACE_DATA_MARKER:
      return opcode_data.load.initial_pc;
    case MEM_STORE_TRACE_DATA_MARKER:
      return opcode_data.store.initial_pc;
    default:
      __trap();
    }
  }

  DEVICE_FORCEINLINE LoadOpcodeTracingData as_load_data() const {
    switch (discr) {
    case MEM_LOAD_TRACE_DATA_MARKER:
      return opcode_data.load;
    case MEM_STORE_TRACE_DATA_MARKER:
    default:
      __trap();
    }
  }

  DEVICE_FORCEINLINE StoreOpcodeTracingData as_store_data() const {
    switch (discr) {
    case MEM_LOAD_TRACE_DATA_MARKER:
      __trap();
    case MEM_STORE_TRACE_DATA_MARKER:
      return opcode_data.store;
    default:
      __trap();
    }
  }

  DEVICE_FORCEINLINE u32 rs2_or_ram_read_value() const {
    switch (discr) {
    case MEM_LOAD_TRACE_DATA_MARKER:
      return opcode_data.load.aligned_ram_read_value;
    case MEM_STORE_TRACE_DATA_MARKER:
      return opcode_data.store.rs2_value;
    default:
      __trap();
    }
  }

  DEVICE_FORCEINLINE u32 ram_address() const {
    switch (discr) {
    case MEM_LOAD_TRACE_DATA_MARKER:
      return opcode_data.load.aligned_ram_address;
    case MEM_STORE_TRACE_DATA_MARKER:
      return opcode_data.store.aligned_ram_address;
    default:
      __trap();
    }
  }

  DEVICE_FORCEINLINE u32 rd_or_ram_read_value() const {
    switch (discr) {
    case MEM_LOAD_TRACE_DATA_MARKER:
      return opcode_data.load.rd_old_value;
    case MEM_STORE_TRACE_DATA_MARKER:
      return opcode_data.store.aligned_ram_old_value;
    default:
      __trap();
    }
  }

  DEVICE_FORCEINLINE u32 rd_or_ram_write_value() const {
    switch (discr) {
    case MEM_LOAD_TRACE_DATA_MARKER:
      return opcode_data.load.rd_value;
    case MEM_STORE_TRACE_DATA_MARKER:
      return opcode_data.store.aligned_ram_write_value;
    default:
      __trap();
    }
  }
};

struct UnrolledMemoryTrace {
  const u32 cycles_count;
  const MemoryOpcodeTracingDataWithTimestamp *const __restrict__ tracing_data;
};

struct UnrolledMemoryOracle {
  const UnrolledMemoryTrace trace;
  const ExecutorFamilyDecoderData *const __restrict__ decoder_table;

  DEVICE_FORCEINLINE ExecutorFamilyDecoderData get_executor_family_data(const unsigned trace_step) const {
    if (trace_step >= trace.cycles_count)
      return { .rd_is_zero = true };
    const u32 pc = trace.tracing_data[trace_step].opcode_data.load.initial_pc;
    return decoder_table[pc / 4];
  }

  template <typename T> [[nodiscard]] T get_witness_from_placeholder(Placeholder, unsigned) const;
};

template <> DEVICE_FORCEINLINE u32 UnrolledMemoryOracle::get_witness_from_placeholder<u32>(const Placeholder placeholder, const unsigned trace_step) const {
  if (trace_step >= trace.cycles_count) {
    switch (placeholder.tag) {
    case PcInit:
      return 0;
    case PcFin:
      return 4;
    default:
      return 0;
    }
  }
  const MemoryOpcodeTracingDataWithTimestamp *const cycle_data = &trace.tracing_data[trace_step];
  switch (placeholder.tag) {
  case PcInit:
    return cycle_data->initial_pc();
  case PcFin:
    return cycle_data->initial_pc() + 4;
  case ShuffleRamReadValue: {
    switch (placeholder.payload[0]) {
    case 0:
      return cycle_data->opcode_data.load.rs1_value;
    case 1:
      return cycle_data->rs2_or_ram_read_value();
    case 2:
      return cycle_data->rd_or_ram_read_value();
    default:
      __trap();
    }
  }
  case ShuffleRamWriteValue: {
    switch (placeholder.payload[0]) {
    case 2:
      return cycle_data->opcode_data.load.rd_value;
    default:
      __trap();
    }
  }
  case ShuffleRamAddress: {
    const ExecutorFamilyDecoderData decoded = get_executor_family_data(trace_step);
    switch (placeholder.payload[0]) {
    case 1: {
      switch (cycle_data->discr) {
      case MEM_LOAD_TRACE_DATA_MARKER:
        return cycle_data->ram_address();
      case MEM_STORE_TRACE_DATA_MARKER:
        return decoded.rs2_index;
      default:
        __trap();
      }
    }
    case 2: {
      switch (cycle_data->discr) {
      case MEM_LOAD_TRACE_DATA_MARKER:
        return decoded.rd_index;
      case MEM_STORE_TRACE_DATA_MARKER:
        return cycle_data->ram_address();
      default:
        __trap();
      }
    }
    default:
      __trap();
    }
  }
  default:
    __trap();
  }
}

template <> DEVICE_FORCEINLINE u16 UnrolledMemoryOracle::get_witness_from_placeholder<u16>(const Placeholder placeholder, const unsigned trace_step) const {
  if (trace_step >= trace.cycles_count)
    return 0;
  switch (placeholder.tag) {
  default:
    __trap();
  }
}

template <> DEVICE_FORCEINLINE u8 UnrolledMemoryOracle::get_witness_from_placeholder<u8>(const Placeholder placeholder, const unsigned trace_step) const {
  if (trace_step >= trace.cycles_count)
    return 0;
  const ExecutorFamilyDecoderData decoded = get_executor_family_data(trace_step);
  switch (placeholder.tag) {
  case ShuffleRamAddress: {
    switch (placeholder.payload[0]) {
    case 0:
      return decoded.rs1_index;
    default:
      __trap();
    }
  }
  default:
    __trap();
  }
}

template <> DEVICE_FORCEINLINE bool UnrolledMemoryOracle::get_witness_from_placeholder<bool>(const Placeholder placeholder, const unsigned trace_step) const {
  if (trace_step >= trace.cycles_count) {
    switch (placeholder.tag) {
    case ShuffleRamIsRegisterAccess: {
      switch (placeholder.payload[0]) {
      case 2:
        return true;
      default:
        return false;
      }
    }
    default:
      return false;
    }
  }
  switch (placeholder.tag) {
  case ShuffleRamIsRegisterAccess: {
    const MemoryOpcodeTracingDataWithTimestamp *const cycle_data = &trace.tracing_data[trace_step];
    switch (placeholder.payload[0]) {
    case 0:
      return true;
    case 1: {
      switch (cycle_data->discr) {
      case MEM_LOAD_TRACE_DATA_MARKER:
        return false;
      case MEM_STORE_TRACE_DATA_MARKER:
        return true;
      default:
        __trap();
      }
    }
    case 2: {
      switch (cycle_data->discr) {
      case MEM_LOAD_TRACE_DATA_MARKER:
        return true;
      case MEM_STORE_TRACE_DATA_MARKER:
        return false;
      default:
        __trap();
      }
    }
    default:
      __trap();
    }
  }
  case  ExecuteOpcodeFamilyCycle:
    return true;
  default:
    __trap();
  }
}

template <>
DEVICE_FORCEINLINE TimestampData UnrolledMemoryOracle::get_witness_from_placeholder<TimestampData>(const Placeholder placeholder,
                                                                                                   const unsigned trace_step) const {
  if (trace_step >= trace.cycles_count) {
    switch (placeholder.tag) {
    case OpcodeFamilyCycleInitialTimestamp:
      return TimestampData::from_scalar(TimestampData::MAX_INITIAL_TIMESTAMP);
    default:
      return {};
    }
  }
  const MemoryOpcodeTracingDataWithTimestamp *const cycle_data = &trace.tracing_data[trace_step];
  switch (placeholder.tag) {
  case ShuffleRamReadTimestamp: {
    switch (placeholder.payload[0]) {
    case 0:
      return cycle_data->rs1_read_timestamp;
    case 1:
      return cycle_data->rs2_or_ram_read_timestamp;
    case 2:
      return cycle_data->rd_or_ram_read_timestamp;
    default:
      __trap();
    }
  }
  case OpcodeFamilyCycleInitialTimestamp:
    return cycle_data->cycle_timestamp;
  default:
    __trap();
  }
}

struct NonMemoryOpcodeTracingData {
  const u32 initial_pc;
  const u32 opcode;
  const u32 rs1_value;
  const u32 rs2_value;
  const u32 rd_old_value;
  const u32 rd_value;
  const u32 new_pc;
  const u16 delegation_type;
};

struct NonMemoryOpcodeTracingDataWithTimestamp {
  const NonMemoryOpcodeTracingData opcode_data;
  const TimestampData rs1_read_timestamp;
  const TimestampData rs2_read_timestamp;
  const TimestampData rd_read_timestamp;
  const TimestampData cycle_timestamp;
};

struct UnrolledNonMemoryTrace {
  const u32 cycles_count;
  const NonMemoryOpcodeTracingDataWithTimestamp *const __restrict__ tracing_data;
};

struct UnrolledNonMemoryOracle {
  const UnrolledNonMemoryTrace trace;
  const ExecutorFamilyDecoderData *const __restrict__ decoder_table;
  const u32 default_pc_value_in_padding;

  DEVICE_FORCEINLINE ExecutorFamilyDecoderData get_executor_family_data(const unsigned trace_step) const {
    if (trace_step >= trace.cycles_count)
      return { .rd_is_zero = true };
    const NonMemoryOpcodeTracingData *const opcode_data = &trace.tracing_data[trace_step].opcode_data;
    const u32 pc = opcode_data->initial_pc;
    return decoder_table[pc / 4];
  }

  template <typename T> [[nodiscard]] T get_witness_from_placeholder(Placeholder, unsigned) const;
};

template <> DEVICE_FORCEINLINE u32 UnrolledNonMemoryOracle::get_witness_from_placeholder<u32>(const Placeholder placeholder, const unsigned trace_step) const {
  if (trace_step >= trace.cycles_count) {
    switch (placeholder.tag) {
    case PcFin:
      return default_pc_value_in_padding;
    default:
      return 0;
    }
  }
  const NonMemoryOpcodeTracingData *const opcode_data = &trace.tracing_data[trace_step].opcode_data;
  switch (placeholder.tag) {
  case PcInit:
    return opcode_data->initial_pc;
  case PcFin:
    return opcode_data->new_pc;
  case ShuffleRamReadValue: {
    switch (placeholder.payload[0]) {
    case 0:
      return opcode_data->rs1_value;
    case 1:
      return opcode_data->rs2_value;
    case 2:
      return opcode_data->rd_old_value;
    default:
      __trap();
    }
  }
  case ShuffleRamWriteValue: {
    switch (placeholder.payload[0]) {
    case 2:
      return opcode_data->rd_value;
    default:
      __trap();
    }
  }
  case ExternalOracle:
    return opcode_data->delegation_type == NON_DETERMINISM_CSR ? opcode_data->rd_value : 0;
  default:
    __trap();
  }
}

template <> DEVICE_FORCEINLINE u16 UnrolledNonMemoryOracle::get_witness_from_placeholder<u16>(const Placeholder placeholder, const unsigned trace_step) const {
  if (trace_step >= trace.cycles_count)
    return 0;
  const NonMemoryOpcodeTracingData *const opcode_data = &trace.tracing_data[trace_step].opcode_data;
  switch (placeholder.tag) {
  case DelegationType: {
    const u16 delegation_type = opcode_data->delegation_type;
    return delegation_type != 0 && delegation_type != NON_DETERMINISM_CSR ? delegation_type : 0;
  }
  case DelegationABIOffset:
    return 0;
  default:
    __trap();
  }
}

template <> DEVICE_FORCEINLINE u8 UnrolledNonMemoryOracle::get_witness_from_placeholder<u8>(const Placeholder placeholder, const unsigned trace_step) const {
  if (trace_step >= trace.cycles_count)
    return 0;
  const ExecutorFamilyDecoderData decoded = get_executor_family_data(trace_step);
  switch (placeholder.tag) {
  case ShuffleRamAddress: {
    switch (placeholder.payload[0]) {
    case 0:
      return decoded.rs1_index;
    case 1:
      return decoded.rs2_index;
    case 2:
      return decoded.rd_index;
    default:
      __trap();
    }
  }
  default:
    __trap();
  }
}

template <>
DEVICE_FORCEINLINE bool UnrolledNonMemoryOracle::get_witness_from_placeholder<bool>(const Placeholder placeholder, const unsigned trace_step) const {
  if (trace_step >= trace.cycles_count)
    return false;
  switch (placeholder.tag) {
  case ShuffleRamIsRegisterAccess: {
    switch (placeholder.payload[0]) {
    case 0:
    case 1:
    case 2:
      return true;
    default:
      __trap();
    }
  }
  case ExecuteDelegation: {
    const u16 delegation_type = trace.tracing_data[trace_step].opcode_data.delegation_type;
    return delegation_type != 0 && delegation_type != NON_DETERMINISM_CSR;
  }
  case  ExecuteOpcodeFamilyCycle:
    return true;
  default:
    __trap();
  }
}

template <>
DEVICE_FORCEINLINE TimestampData UnrolledNonMemoryOracle::get_witness_from_placeholder<TimestampData>(const Placeholder placeholder,
                                                                                                      const unsigned trace_step) const {
  if (trace_step >= trace.cycles_count) {
    switch (placeholder.tag) {
    case OpcodeFamilyCycleInitialTimestamp:
      return TimestampData::from_scalar(TimestampData::MAX_INITIAL_TIMESTAMP);
    default:
      return {};
    }
  }
  const NonMemoryOpcodeTracingDataWithTimestamp *const cycle_data = &trace.tracing_data[trace_step];
  switch (placeholder.tag) {
  case ShuffleRamReadTimestamp: {
    switch (placeholder.payload[0]) {
    case 0:
      return cycle_data->rs1_read_timestamp;
    case 1:
      return cycle_data->rs2_read_timestamp;
    case 2:
      return cycle_data->rd_read_timestamp;
    default:
      __trap();
    }
  }
  case OpcodeFamilyCycleInitialTimestamp:
    return cycle_data->cycle_timestamp;
  default:
    __trap();
  }
}

} // namespace airbender::witness::trace::unrolled