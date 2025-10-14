#pragma once

#include "column.cuh"
#include "common.cuh"

using namespace ::airbender::witness;
using namespace ::airbender::witness::column;

namespace airbender::witness::trace {

typedef u64 TimestampScalar;

struct TimestampData {
  static constexpr unsigned NUM_TIMESTAMP_DATA_LIMBS = 3;
  static constexpr unsigned TIMESTAMP_COLUMNS_NUM_BITS = 19;
  static constexpr unsigned TIMESTAMP_COLUMNS_NUM_BITS_MASK = (1u << TIMESTAMP_COLUMNS_NUM_BITS) - 1;
  static constexpr unsigned NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP = 2;
  static constexpr u32 TOTAL_TIMESTAMP_BITS = TIMESTAMP_COLUMNS_NUM_BITS * NUM_TIMESTAMP_COLUMNS_FOR_RAM;
  static constexpr TimestampScalar TIMESTAMP_STEP = 1ul << NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP;
  static constexpr TimestampScalar MAX_INITIAL_TIMESTAMP = (1ul << TOTAL_TIMESTAMP_BITS) - TIMESTAMP_STEP * 2;

  u16 limbs[NUM_TIMESTAMP_DATA_LIMBS];

  DEVICE_FORCEINLINE TimestampScalar as_scalar() const {
    TimestampScalar result = limbs[0];
#pragma unroll
    for (int i = 1; i < NUM_TIMESTAMP_DATA_LIMBS; ++i)
      result |= static_cast<TimestampScalar>(limbs[i]) << (i * 16);
    return result;
  }

  static constexpr DEVICE_FORCEINLINE TimestampData from_scalar(const TimestampScalar scalar) {
    TimestampData result{};
    result.limbs[0] = scalar & TIMESTAMP_COLUMNS_NUM_BITS_MASK;
#pragma unroll
    for (int i = 1; i < NUM_TIMESTAMP_DATA_LIMBS; ++i)
      result.limbs[i] = static_cast<u16>(scalar >> (i * 16) & TIMESTAMP_COLUMNS_NUM_BITS_MASK);
    return result;
  }

  DEVICE_FORCEINLINE u32 get_low() const { return as_scalar() & (1u << TIMESTAMP_COLUMNS_NUM_BITS) - 1; }

  DEVICE_FORCEINLINE u32 get_high() const { return as_scalar() >> TIMESTAMP_COLUMNS_NUM_BITS; }

  static DEVICE_FORCEINLINE uint2 sub_borrow(const u32 lhs, const u32 rhs) {
    const u32 t = (1u << TIMESTAMP_COLUMNS_NUM_BITS) + lhs - rhs;
    const u32 borrow = (t >> TIMESTAMP_COLUMNS_NUM_BITS) ^ 1;
    const u32 result = t & TIMESTAMP_COLUMNS_NUM_BITS_MASK;
    return {result, borrow};
  }

  DEVICE_FORCEINLINE bool increment() {
    const TimestampScalar initial_ts = as_scalar();
    const TimestampScalar final_ts = initial_ts + TIMESTAMP_STEP;
    const bool intermediate_carry = final_ts >> TIMESTAMP_COLUMNS_NUM_BITS != initial_ts >> TIMESTAMP_COLUMNS_NUM_BITS;
    *this = from_scalar(final_ts);
    return intermediate_carry;
  }
};

struct RegIndexOrMemWordIndex {
  static constexpr u32 IS_RAM_MASK = 0x80000000;
  u32 value;

  DEVICE_FORCEINLINE u32 as_u32_formal_address() const { return is_register() ? value : value << 2; }

  DEVICE_FORCEINLINE bool is_register() const { return !(value & IS_RAM_MASK); }
};

struct __align__(16) InitAndTeardown {
  u32 address;
  u32 teardown_value;
  TimestampData teardown_timestamp;
};

struct ShuffleRamInitsAndTeardowns {
  // const u32 count;
  const InitAndTeardown *const __restrict__ inits_and_teardowns;
};

} // namespace airbender::witness::trace