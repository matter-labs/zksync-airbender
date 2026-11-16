#pragma once

#include "primitives/ptx.cuh"

namespace airbender::trace::witness {

#define REGISTER_SIZE 2
#define NUM_TIMESTAMP_COLUMNS_FOR_RAM 2

enum AddressTag : u32 {
  BaseLayerWitness,
  BaseLayerMemory,
  InnerLayer,
  Setup,
  ScratchSpace,
  Cached,
};

struct Address {
  AddressTag tag;
  u32 offset;
  u32 layer;
};

template <typename F> struct witness_field;

#define MAX_LINEAR_TERMS_COUNT 4

template <typename F> struct LinearTerm {
  F coefficient;
  Address address;
  u32 padding;
};

template <typename F> struct LinearRelation {
  F constant;
  LinearTerm<F> linear_terms[MAX_LINEAR_TERMS_COUNT];
  u32 linear_terms_count;
  u32 padding[3];
};

template <typename F, typename Memory, typename Witness, typename Scratch>
DEVICE_FORCEINLINE F evaluate_linear_relation(const Memory &memory, const Witness &witness, const Scratch &scratch, const LinearRelation<F> relation) {
  F result = witness_field<F>::linear_relation_constant(relation.constant, relation.linear_terms_count);
#pragma unroll
  for (int i = 0; i < MAX_LINEAR_TERMS_COUNT; ++i) {
    if (i == relation.linear_terms_count)
      break;
    const auto &term = relation.linear_terms[i];
    const auto coefficient = term.coefficient;
    const auto address = term.address;
    F value = F::ZERO();
    switch (address.tag) {
    case BaseLayerMemory:
      value = memory.get_at_col(address.offset);
      break;
    case BaseLayerWitness:
      value = witness.get_at_col(address.offset);
      break;
    case ScratchSpace:
      value = scratch.get_at_col(address.offset);
      break;
    default:
      __trap();
      break;
    }
    result = witness_field<F>::add_linear_term(coefficient, value, result);
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

} // namespace airbender::trace::witness
