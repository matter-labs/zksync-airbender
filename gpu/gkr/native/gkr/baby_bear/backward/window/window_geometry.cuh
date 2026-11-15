#pragma once

#include "gkr/baby_bear/backward/window/window_source.cuh"
#include "gkr/backward/window/window_geometry.cuh"

namespace airbender::gkr::backward {

DEVICE_FORCEINLINE e4 bwd_window_quartet_shuffle_add(const e4 value, const u32 mask) {
  e4 shuffled;
  const uint4 *source = reinterpret_cast<const uint4 *>(&value);
  uint4 *destination = reinterpret_cast<uint4 *>(&shuffled);
  destination[0] = shfl_xor(0xffffffffu, source[0], mask, BWD_WINDOW_WARP_LANES);
  return e4::add(value, shuffled);
}

// One row-tile-major group of 27 cells; this warp owns the three x2 cells of its
// selector pair.
//
// The tensor's axes are the rounds that bind them: the tail plays round 0 on
// axis 0, and round `r` binds trace row bit `r`. A window's `x2` is the corner's
// LOW bit — the pair axis the program's quadratic term is taken over — so the
// cell index is `9 * x2 + 3 * x1 + x0`, not the selector-major order the
// executor evaluates in.
// Sum each cell within four-lane groups, then assign one cell to each
// lane role for the remaining reduction. All lanes participate; roles 0–2
// publish the same three tensor cells after inactive rows contribute zero.
DEVICE_FORCEINLINE void bwd_window_publish(e4 *partials, const size_t tile_slot, const u32 lane, const bool active, const bwd_window_selector_pair selector,
                                           const e4 equality, const e4 (&values)[3]) {
  e4 sums[3];
#pragma unroll
  for (u32 x2 = 0; x2 < 3; ++x2) {
    sums[x2] = active ? e4::mul(equality, values[x2]) : e4::ZERO();
    sums[x2] = bwd_window_quartet_shuffle_add(sums[x2], 1);
    sums[x2] = bwd_window_quartet_shuffle_add(sums[x2], 2);
  }
  const u32 role = lane & 3u;
  e4 value = role == 0 ? sums[0] : role == 1 ? sums[1] : role == 2 ? sums[2] : e4::ZERO();
#pragma unroll
  for (u32 mask = 4; mask < BWD_WINDOW_WARP_LANES; mask <<= 1)
    value = bwd_window_quartet_shuffle_add(value, mask);
  if (lane < 3)
    store<e4, st_modifier::cs>(partials, value, tile_slot * BWD_WINDOW_TENSOR_CELLS + 9 * lane + 3 * selector.x1 + selector.x0);
}

} // namespace airbender::gkr::backward
