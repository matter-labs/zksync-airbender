#pragma once

#include "window_source.cuh"

namespace airbender::gkr::backward {

// Nine warps, one per (x0, x1) selector pair; the warp's lane is its row inside
// the block's 32-row tile.
DEVICE_FORCEINLINE u32 bwd_window_row_tile() { return blockIdx.x; }

DEVICE_FORCEINLINE u32 bwd_window_lane() { return threadIdx.x & BWD_WINDOW_LANE_INDEX_MASK; }

DEVICE_FORCEINLINE u32 bwd_window_selector_id() { return threadIdx.x >> BWD_WINDOW_WARP_SHIFT; }

// `2` is the infinity endpoint. The flags go through `__all_sync` so the
// predicate is provably warp-uniform to the compiler, which is what keeps the
// endpoint branches out of the per-thread path.
DEVICE_FORCEINLINE bwd_window_selector_pair bwd_window_selector(const u32 selector_id) {
  const u32 x0 = selector_id / 3;
  const u32 x1 = selector_id % 3;
  return {x0, x1, __all_sync(0xffffffffu, x0 == 2) != 0, __all_sync(0xffffffffu, x1 == 2) != 0};
}

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
