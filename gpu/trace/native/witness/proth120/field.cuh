#pragma once

#include "../tables.cuh"
#include "primitives/proth120.cuh"

namespace airbender::trace::witness::proth120 {

DEVICE_FORCEINLINE pr pr_from_u32(const u32 value) {
  const u32 natural[4] = {value, 0, 0, 0};
  return pr::from_u128_with_reduction(natural);
}

DEVICE_FORCEINLINE pr pr_natural(const pr value) { return pr::mul(value, pr{{1, 0, 0, 0}}); }

DEVICE_FORCEINLINE u32 pr_to_u32_or_zero(const pr value) {
  const pr natural = pr_natural(value);
  return (natural.limbs[1] | natural.limbs[2] | natural.limbs[3]) ? 0 : natural.limbs[0];
}

DEVICE_FORCEINLINE u32 pr_to_u32_bounded(const pr value) {
  const pr natural = pr_natural(value);
  if (natural.limbs[1] | natural.limbs[2] | natural.limbs[3])
    __trap();
  return natural.limbs[0];
}

DEVICE_FORCEINLINE bool pr_to_mask(const pr value) { return pr::eq(value, pr::ONE()); }

} // namespace airbender::trace::witness::proth120

namespace airbender::trace::witness::tables {

template <> struct witness_table_key<pr> {
  static DEVICE_FORCEINLINE u32 to_u32(const pr value) { return ::airbender::trace::witness::proth120::pr_to_u32_bounded(value); }
};

} // namespace airbender::trace::witness::tables

namespace airbender::trace::witness {
template <> struct witness_field<pr> {
  static DEVICE_FORCEINLINE pr from_u32(u32 value) { return proth120::pr_from_u32(value); }
  static DEVICE_FORCEINLINE pr from_raw(u32 value) { return proth120::pr_from_u32(value); }
  static DEVICE_FORCEINLINE u32 to_integer(pr value) { return proth120::pr_to_u32_or_zero(value); }
  static DEVICE_FORCEINLINE u32 to_raw(pr value) { return proth120::pr_to_u32_or_zero(value); }
  static DEVICE_FORCEINLINE u32 to_bounded(pr value) { return proth120::pr_to_u32_bounded(value); }
  static DEVICE_FORCEINLINE bool to_mask(pr value) { return proth120::pr_to_mask(value); }
  static DEVICE_FORCEINLINE bool equal(pr lhs, pr rhs) { return pr::eq(lhs, rhs); }
  static DEVICE_FORCEINLINE void print(pr value) { printf("[%u, %u, %u, %u]", value.limbs[0], value.limbs[1], value.limbs[2], value.limbs[3]); }
};
} // namespace airbender::trace::witness
