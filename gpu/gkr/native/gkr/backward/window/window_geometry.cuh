#pragma once

#include "gkr/backward/window/window_source.cuh"

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

} // namespace airbender::gkr::backward
