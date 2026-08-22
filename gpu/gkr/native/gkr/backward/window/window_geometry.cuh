#pragma once

#include "window_source.cuh"

namespace airbender::gkr::backward {

// Nine warps, one per (x0, x1) selector pair; the warp's lane is its row inside
// the block's 32-row tile.
DEVICE_FORCEINLINE u32 bwd_window_row_tile() { return blockIdx.x; }

DEVICE_FORCEINLINE u32 bwd_window_lane() { return threadIdx.x & BWD_SEG_LANE_INDEX_MASK; }

DEVICE_FORCEINLINE u32 bwd_window_selector_id() { return threadIdx.x >> BWD_SEG_WARP_SHIFT; }

// `2` is the infinity endpoint. The flags go through `__all_sync` so the
// predicate is provably warp-uniform to the compiler, which is what keeps the
// endpoint branches out of the per-thread path.
DEVICE_FORCEINLINE bwd_window_selector_pair bwd_window_selector(const u32 selector_id) {
  const u32 x0 = selector_id / 3;
  const u32 x1 = selector_id % 3;
  return {x0, x1, __all_sync(0xffffffffu, x0 == 2) != 0, __all_sync(0xffffffffu, x1 == 2) != 0};
}

// One row-tile-major group of 27 cells; this warp owns the three x2 cells of its
// selector pair.
//
// The tensor's axes are the rounds that bind them: the tail plays round 0 on
// axis 0, and round `r` binds trace row bit `r`. A window's `x2` is the corner's
// LOW bit — the pair axis the program's quadratic term is taken over — so the
// cell index is `9 * x2 + 3 * x1 + x0`, not the selector-major order the
// executor evaluates in.
DEVICE_FORCEINLINE void bwd_window_publish(const bwd_window_desc &desc, const u32 row_tile, const u32 lane, const bool active,
                                           const bwd_window_selector_pair selector, const e4 (&values)[3]) {
  const e4 equality = gkr_compute_eq_inline<e4>(desc.eq_low, desc.eq_sizes, active ? row_tile * BWD_WINDOW_ROWS_PER_TILE + lane : 0);
  const u32 cell_base = 3 * selector.x1 + selector.x0;
#pragma unroll
  for (u32 x2 = 0; x2 < 3; ++x2) {
    e4 value = active ? e4::mul(equality, values[x2]) : e4::ZERO();
    value = bwd_window_warp_sum(value);
    if (lane == 0)
      store<e4, st_modifier::cs>(desc.partials, value, static_cast<size_t>(row_tile) * BWD_WINDOW_TENSOR_CELLS + 9 * x2 + cell_base);
  }
}

} // namespace airbender::gkr::backward
