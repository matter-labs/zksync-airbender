#pragma once
#include "descriptors.cuh"

EXTERN __device__ __constant__ e4
    ab_gkr_eq_high[airbender::prover::gkr::GKR_EQ_HIGH_SLOTS][airbender::prover::gkr::GKR_EQ_GROUP_TABLE_LEN];

namespace airbender::prover::gkr {

// Per-row inline eq: strict 3-slot layout [high[0], high[1], low].
// High slabs live in __constant__ memory (LDC broadcast path); the low slab
// stays in global memory and is read with `ld.global.cs` (each thread reads
// its own entry, no row-level reuse).
//
// `acc` is initialized from the first load rather than from `E::ONE()` to
// save one full E::mul per row.
template <typename E>
DEVICE_FORCEINLINE E gkr_compute_eq_inline(const E *__restrict__ eq_low, const gkr_eq_sizes &sizes, const unsigned gid) {
  const unsigned shift1 = sizes.low;
  const unsigned shift0 = sizes.low + sizes.high[1];
  const unsigned hi0 = (gid >> shift0) & ((1u << sizes.high[0]) - 1u);
  const unsigned hi1 = (gid >> shift1) & ((1u << sizes.high[1]) - 1u);
  const unsigned lo = gid & ((1u << sizes.low) - 1u);

  E acc = load<E, ld_modifier::ca>(&ab_gkr_eq_high[0][0], hi0);
  acc = E::mul(acc, load<E, ld_modifier::ca>(&ab_gkr_eq_high[1][0], hi1));
  acc = E::mul(acc, load<E, ld_modifier::cs>(eq_low, lo));
  return acc;
}

// `gkr_compute_eq_inline` variant that reads high slabs from caller-supplied
// global pointers rather than the single `ab_gkr_eq_high` constant. Used by
// WHIR's batched accumulator where every query needs its own factored-eq state.
template <typename E>
DEVICE_FORCEINLINE E gkr_compute_eq_inline_global(const E *__restrict__ eq_high_0, const E *__restrict__ eq_high_1,
                                                  const E *__restrict__ eq_low, const gkr_eq_sizes &sizes, const unsigned gid) {
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

} // namespace airbender::prover::gkr
