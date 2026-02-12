#pragma once

#include <cstdint>

#include "../common.cuh"
#include "../field.cuh"

using namespace ::airbender::field;

namespace airbender::witness {

typedef base_field bf;
typedef uint8_t u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;

DEVICE_FORCEINLINE uchar2 u16_to_u8_tuple(const u16 value) { return *reinterpret_cast<const uchar2 *>(&value); }

DEVICE_FORCEINLINE u16 u8_tuple_to_u16(const uchar2 value) { return *reinterpret_cast<const u16 *>(&value); }

DEVICE_FORCEINLINE ushort2 u32_to_u16_tuple(const u32 value) { return *reinterpret_cast<const ushort2 *>(&value); }

DEVICE_FORCEINLINE u32 u16_tuple_to_u32(const ushort2 value) { return *reinterpret_cast<const u32 *>(&value); }

DEVICE_FORCEINLINE uint2 u64_to_u32_tuple(const u64 value) { return *reinterpret_cast<const uint2 *>(&value); }

DEVICE_FORCEINLINE u64 u32_tuple_to_u64(const uint2 value) { return *reinterpret_cast<const u64 *>(&value); }

DEVICE_FORCEINLINE uchar2 add_carry(const u8 lhs, const u8 rhs) {
  const u16 sum = static_cast<u16>(lhs) + static_cast<u16>(rhs);
  return u16_to_u8_tuple(sum);
}

DEVICE_FORCEINLINE uchar2 sub_borrow(const u8 lhs, const u8 rhs) {
  const u16 diff = u8_tuple_to_u16(uchar2(lhs, 1)) - static_cast<u16>(rhs);
  return u16_to_u8_tuple(diff ^ 1u << 8);
}

DEVICE_FORCEINLINE ushort2 add_carry(const u16 lhs, const u16 rhs) {
  const u32 sum = static_cast<u32>(lhs) + static_cast<u32>(rhs);
  return u32_to_u16_tuple(sum);
}

DEVICE_FORCEINLINE ushort2 sub_borrow(const u16 lhs, const u16 rhs) {
  const u32 diff = u16_tuple_to_u32(ushort2(lhs, 1)) - static_cast<u32>(rhs);
  return u32_to_u16_tuple(diff ^ 1u << 16);
}

DEVICE_FORCEINLINE uint2 add_carry(const u32 lhs, const u32 rhs) {
  const u64 sum = static_cast<u64>(lhs) + static_cast<u64>(rhs);
  return u64_to_u32_tuple(sum);
}

DEVICE_FORCEINLINE uint2 sub_borrow(const u32 lhs, const u32 rhs) {
  const u64 diff = u32_tuple_to_u64(uint2(lhs, 1)) - static_cast<u64>(rhs);
  return u64_to_u32_tuple(diff ^ 1ull << 32);
}

} // namespace airbender::witness