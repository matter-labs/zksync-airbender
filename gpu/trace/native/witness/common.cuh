#pragma once

#include "primitives/field.cuh"

using namespace ::airbender::primitives::field;

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

template <> struct witness_field<bf> {
  static DEVICE_FORCEINLINE bf from_u32(u32 value) { return bf::from_u32_unchecked(value); }
  static consteval DEVICE_FORCEINLINE bf constant(u32 value) { return bf::const_into_mont(value); }
  static DEVICE_FORCEINLINE bf from_raw(u32 value) { return bf::from_raw_repr_with_reduction(value); }
  static DEVICE_FORCEINLINE u32 to_integer(bf value) { return bf::into_canonical_u32(value); }
  static DEVICE_FORCEINLINE u32 to_raw(bf value) { return bf::into_raw_u32(value); }
  static DEVICE_FORCEINLINE u32 to_bounded(bf value) { return bf::into_canonical_u32(value); }
  static DEVICE_FORCEINLINE bool to_mask(bf value) { return static_cast<bool>(bf::into_canonical_u32(value)); }
  static DEVICE_FORCEINLINE bool equal(bf lhs, bf rhs) { return lhs.limb == rhs.limb; }
  static DEVICE_FORCEINLINE void print(bf value) { printf("%u", value.limb); }
};

#define MAX_LINEAR_TERMS_COUNT 4

template <typename F> struct LinearTerm {
  F coefficient;
  Address address;
  u32 padding;
};
template <> struct LinearTerm<bf> {
  u32 coefficient;
  Address address;
};

template <typename F> struct LinearRelation {
  F constant;
  LinearTerm<F> linear_terms[MAX_LINEAR_TERMS_COUNT];
  u32 linear_terms_count;
  u32 padding[3];
};
template <> struct LinearRelation<bf> {
  u32 linear_terms_count;
  LinearTerm<bf> linear_terms[MAX_LINEAR_TERMS_COUNT];
  u32 constant;
};

template <typename F, typename Memory, typename Witness, typename Scratch>
DEVICE_FORCEINLINE F evaluate_linear_relation(const Memory &memory, const Witness &witness, const Scratch &scratch, const LinearRelation<F> relation) {
  F result;
  if constexpr (std::is_same_v<F, bf>) {
    result = relation.constant == 0 ? bf::ZERO() : bf::from_u32_unchecked(relation.constant);
  } else {
    if (relation.linear_terms_count > MAX_LINEAR_TERMS_COUNT)
      __trap();
    result = relation.constant;
  }
#pragma unroll
  for (int i = 0; i < MAX_LINEAR_TERMS_COUNT; ++i) {
    if (i == relation.linear_terms_count)
      break;
    const auto &term = relation.linear_terms[i];
    const auto coefficient = term.coefficient;
    const auto address = term.address;
    F value;
    if constexpr (!std::is_same_v<F, bf>)
      value = F::ZERO();
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
    if constexpr (std::is_same_v<F, bf>) {
      switch (coefficient) {
      case 0:
        __trap();
        break;
      case 1:
        break;
      case bf::ORDER - 1:
        value = bf::neg(value);
        break;
      default:
        value = bf::mul(value, bf::from_u32_unchecked(coefficient));
        break;
      }
      result = bf::add(result, value);
    } else {
      if (F::is_zero(coefficient))
        __trap();
      result = F::fma(coefficient, value, result);
    }
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
