#pragma once

#include "primitives/baby_bear/field.cuh"
#include "witness/common.cuh"

using namespace ::airbender::primitives::field;

namespace airbender::trace::witness {

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

template <> struct LinearTerm<bf> {
  u32 coefficient;
  Address address;
};

template <> struct LinearRelation<bf> {
  u32 linear_terms_count;
  LinearTerm<bf> linear_terms[MAX_LINEAR_TERMS_COUNT];
  u32 constant;
};

template <typename Memory, typename Witness, typename Scratch>
DEVICE_FORCEINLINE bf evaluate_linear_relation(const Memory &memory, const Witness &witness, const Scratch &scratch, const LinearRelation<bf> relation) {
  bf result;
  result = relation.constant == 0 ? bf::ZERO() : bf::from_u32_unchecked(relation.constant);
#pragma unroll
  for (int i = 0; i < MAX_LINEAR_TERMS_COUNT; ++i) {
    if (i == relation.linear_terms_count)
      break;
    const auto &term = relation.linear_terms[i];
    const auto coefficient = term.coefficient;
    const auto address = term.address;
    bf value;
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
  }
  return result;
}

} // namespace airbender::trace::witness

#include "witness/lookup_mapping.cuh"
#include "witness/multiplicities.cuh"
#include "witness/tables.cuh"

namespace airbender::trace::witness::tables {

template <unsigned K, unsigned V, typename F = bf> struct TableDriver;

template <> struct witness_table_key<bf> {
  static DEVICE_FORCEINLINE u32 to_u32(const bf value) { return bf::into_canonical_u32(value); }
};

} // namespace airbender::trace::witness::tables

namespace airbender::trace::witness::multiplicities {

#define MAX_LOOKUP_EXPRESSIONS_RELATIONS_COUNT 128

using LookupExpressionsBf = LookupExpressions<bf, MAX_LOOKUP_EXPRESSIONS_RELATIONS_COUNT>;

template <> DEVICE_FORCEINLINE auto counter_word<bf>(bf *ptr) { return &ptr->limb; }
template <> DEVICE_FORCEINLINE auto counter_word<const bf>(const bf *ptr) { return &ptr->limb; }

} // namespace airbender::trace::witness::multiplicities
