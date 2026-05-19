#pragma once
#include "descriptors.cuh"

namespace airbender::prover::gkr {

// Per-row inline eq: product of high-group factors (warp-uniform reads from
// the high_slab — broadcast through L1/L2 read-only cache via `ld.global.ca`)
// and one lane-varying low-group factor (each thread reads its own entry; 32
// lanes in a warp read consecutive low_buffer entries, coalescing into ~4
// cache lines and staying hot in L1 for the lifetime of a sumcheck round).
//
// `layout` is a small (8 B) descriptor produced on the host side. Its
// `high_group_base_idx` lets the fold path advance which slab slot is treated
// as "group 0" without rewriting the high slab on every round (used in the
// future fold step).
template <typename E>
DEVICE_FORCEINLINE E gkr_compute_eq_inline(const E *__restrict__ high_slab, const gkr_eq_layout_compact &layout, const E *__restrict__ low_buffer,
                                           const unsigned gid) {
  E acc = E::ONE();
  unsigned consumed = 0;
  unsigned challenge_count = layout.low_group_size;
#pragma unroll
  for (unsigned i = 0; i < GKR_EQ_MAX_HIGH_GROUPS; ++i) {
    if (i < layout.num_high_groups)
      challenge_count += layout.high_group_sizes[i];
  }

#pragma unroll
  for (unsigned i = 0; i < GKR_EQ_MAX_HIGH_GROUPS; ++i) {
    if (i >= layout.num_high_groups)
      break;
    const unsigned g_size = layout.high_group_sizes[i];
    const unsigned shift = challenge_count - consumed - g_size;
    const unsigned local = (gid >> shift) & ((1u << g_size) - 1u);
    const unsigned slab_offset = (layout.high_group_base_idx + i) * GKR_EQ_GROUP_TABLE_LEN + local;
    acc = E::mul(acc, load<E, ld_modifier::ca>(high_slab, slab_offset));
    consumed += g_size;
  }

  const unsigned low_local = gid & ((1u << layout.low_group_size) - 1u);
  acc = E::mul(acc, load<E, ld_modifier::ca>(low_buffer, low_local));
  return acc;
}

} // namespace airbender::prover::gkr
