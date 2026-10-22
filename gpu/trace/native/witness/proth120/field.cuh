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
