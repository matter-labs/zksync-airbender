#pragma once

#include "common.cuh"

namespace airbender::gkr_uniskip_bench {

// k is FIXED at 4: 16 taps on H, plus the 16 cells of the odd coset gamma*H.
// Shaped so k=3/5 stays a one-line change, but nothing here is parameterized.
constexpr u32 UNISKIP_TAPS = 16;
constexpr u32 UNISKIP_CELLS = 32; // 0..15 = H (direct taps), 16..31 = coset

// Launch geometry: warp w owns cells 4w..4w+3.
constexpr u32 UNISKIP_THREADS_PER_BLOCK = 256;
constexpr u32 UNISKIP_WARPS_PER_BLOCK = 8;
constexpr u32 UNISKIP_CELLS_PER_WARP = 4;

static_assert(UNISKIP_CELLS == 2 * UNISKIP_TAPS);
static_assert(UNISKIP_WARPS_PER_BLOCK * 32 == UNISKIP_THREADS_PER_BLOCK);
static_assert(UNISKIP_WARPS_PER_BLOCK * UNISKIP_CELLS_PER_WARP == UNISKIP_CELLS);

} // namespace airbender::gkr_uniskip_bench
