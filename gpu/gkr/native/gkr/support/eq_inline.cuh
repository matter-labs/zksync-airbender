#pragma once

#include "gkr/support/descriptors.cuh"

namespace airbender::gkr {

// `gkr_compute_eq_inline` variant that reads high slabs from caller-supplied
// global pointers rather than the single `ab_gkr_eq_high` constant. Used by
// WHIR's batched accumulator where every query needs its own factored-eq state.
template <typename E>
DEVICE_FORCEINLINE E gkr_compute_eq_inline_global(const E *__restrict__ eq_high_0, const E *__restrict__ eq_high_1, const E *__restrict__ eq_low,
                                                  const gkr_eq_sizes &sizes, const unsigned gid) {
  const unsigned shift1 = sizes.low;
  const unsigned shift0 = sizes.low + sizes.high[1];
  const unsigned hi0 = (gid >> shift0) & ((1u << sizes.high[0]) - 1u);
  const unsigned hi1 = (gid >> shift1) & ((1u << sizes.high[1]) - 1u);
  const unsigned lo = gid & ((1u << sizes.low) - 1u);

  E acc = load<E, ld_modifier::ca>(eq_high_0, hi0);
  acc = E::mul(acc, load<E, ld_modifier::ca>(eq_high_1, hi1));
  acc = E::mul(acc, load<E, ld_modifier::cs>(eq_low, lo));
  return acc;
}

} // namespace airbender::gkr
