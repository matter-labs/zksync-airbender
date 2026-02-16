#pragma once

#include "../field.cuh"

using namespace ::airbender::field;

namespace airbender::witness {

#define REGISTER_SIZE 2
#define NUM_TIMESTAMP_COLUMNS_FOR_RAM 2

enum AddressTag : u32 {
  BaseLayerWitness,
  BaseLayerMemory,
  InnerLayer,
  Setup,
  OptimizedOut,
  Cached,
};

struct Address {
  AddressTag tag;
  u32 offset;
  u32 layer;
};

struct NoFieldLinearTerm {
  u32 coefficient;
  Address address;
};

#define MAX_LINEAR_TERMS_COUNT 4

struct NoFieldLinearRelation {
  u32 linear_terms_count;
  NoFieldLinearTerm linear_terms[MAX_LINEAR_TERMS_COUNT];
  u32 constant;
};

DEVICE_FORCEINLINE bf evaluate_linear_relation(const matrix_getter<bf, ld_modifier::cg> memory, const matrix_getter<bf, ld_modifier::cg> witness,
                                               const NoFieldLinearRelation relation) {
  bf result = relation.constant == 0 ? bf::ZERO() : bf::from_canonical_u32(relation.constant);
#pragma unroll
  for (int i = 0; i < MAX_LINEAR_TERMS_COUNT; ++i) {
    if (i == relation.linear_terms_count)
      break;
    const auto [coefficient, address] = relation.linear_terms[i];
    bf value;
    switch (address.tag) {
    case BaseLayerMemory:
      value = memory.get_at_col(address.offset);
      break;
    case BaseLayerWitness:
      value = witness.get_at_col(address.offset);
      break;
    default:
      __trap();
      break;
    }
    switch (coefficient) {
    case 0:
      __trap();
      break;
    case 1:
      // no need to multiply by 1
      break;
    case bf::ORDER - 1:
      // minus one, just negate
      value = bf::neg(value);
      break;
    default:
      value = bf::mul(value, bf::from_canonical_u32(coefficient));
      break;
    }
    result = bf::add(result, value);
  }
  return result;
}

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