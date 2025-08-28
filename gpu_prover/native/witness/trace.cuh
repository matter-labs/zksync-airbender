#pragma once

#include "common.cuh"

using namespace ::airbender::witness;

namespace airbender::witness::trace {

typedef u64 TimestampScalar;

struct TimestampData {
  static constexpr unsigned NUM_TIMESTAMP_DATA_LIMBS = 3;
  static constexpr unsigned TIMESTAMP_COLUMNS_NUM_BITS = 19;
  static constexpr unsigned TIMESTAMP_COLUMNS_NUM_BITS_MASK = (1u << TIMESTAMP_COLUMNS_NUM_BITS) - 1;
  static constexpr unsigned NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP = 2;

  u16 limbs[NUM_TIMESTAMP_DATA_LIMBS];

  DEVICE_FORCEINLINE TimestampScalar as_scalar() const {
    TimestampScalar result = limbs[0];
#pragma unroll
    for (int i = 1; i < NUM_TIMESTAMP_DATA_LIMBS; ++i)
      result |= static_cast<TimestampScalar>(limbs[i]) << (i * 16);
    return result;
  }

  static DEVICE_FORCEINLINE TimestampData from_scalar(TimestampScalar scalar) {
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
};

struct RegIndexOrMemWordIndex {
  static constexpr u32 IS_RAM_MASK = 0x80000000;
  u32 value;

  DEVICE_FORCEINLINE u32 as_u32_formal_address() const { return is_register() ? value : value << 2; }

  DEVICE_FORCEINLINE bool is_register() const { return !(value & IS_RAM_MASK); }
};

} // namespace airbender::witness::trace