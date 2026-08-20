#pragma once

#include "windowed_r0_prototype_source.cuh"

namespace airbender::gkr_windowed_bench {

struct r0pb_owned_cell {
  r0_selector_pair selector;
  u32 x2;

  DEVICE_FORCEINLINE u32 output_index() const { return 9 * selector.x0 + 3 * selector.x1 + x2; }
};

struct r0pb_cta288_pair_geometry {
  static constexpr u32 threads = 288;
  static constexpr u32 owned_cells = 3;

  DEVICE_FORCEINLINE static u32 row_tile() { return blockIdx.x; }
  DEVICE_FORCEINLINE static r0pb_owned_cell cell(const u32 index) {
    const u32 warp = threadIdx.x >> 5;
    return {{warp / 3, warp % 3}, index};
  }
};

struct r0pb_cta96_partitioned_geometry {
  static constexpr u32 threads = 96;
  static constexpr u32 owned_cells = 3;

  DEVICE_FORCEINLINE static u32 row_tile() { return blockIdx.x / 3; }
  DEVICE_FORCEINLINE static r0pb_owned_cell cell(const u32 index) {
    const u32 selector = 3 * (blockIdx.x % 3) + (threadIdx.x >> 5);
    return {{selector / 3, selector % 3}, index};
  }
};

struct r0pb_cta96_x0_major_geometry {
  static constexpr u32 threads = 96;
  static constexpr u32 owned_cells = 9;

  DEVICE_FORCEINLINE static u32 row_tile() { return blockIdx.x; }
  DEVICE_FORCEINLINE static r0pb_owned_cell cell(const u32 index) { return {{threadIdx.x >> 5, index / 3}, index % 3}; }
};

struct r0pb_cta96_x1_major_geometry {
  static constexpr u32 threads = 96;
  static constexpr u32 owned_cells = 9;

  DEVICE_FORCEINLINE static u32 row_tile() { return blockIdx.x; }
  DEVICE_FORCEINLINE static r0pb_owned_cell cell(const u32 index) { return {{index / 3, threadIdx.x >> 5}, index % 3}; }
};

struct r0pb_cta96_x2_major_geometry {
  static constexpr u32 threads = 96;
  static constexpr u32 owned_cells = 9;

  DEVICE_FORCEINLINE static u32 row_tile() { return blockIdx.x; }
  DEVICE_FORCEINLINE static r0pb_owned_cell cell(const u32 index) { return {{index / 3, index % 3}, threadIdx.x >> 5}; }
};

// Sectioned geometry names are deliberately separate from the historical
// prototype geometry IDs even where their ownership is identical.  This keeps
// the old 245-symbol bank frozen while the sectioned family evolves.
using r0pb_sectioned_wide9_geometry = r0pb_cta288_pair_geometry;
using r0pb_sectioned_split3_geometry = r0pb_cta96_partitioned_geometry;

struct r0pb_sectioned_serial3_low_geometry {
  static constexpr u32 threads = 96;
  static constexpr u32 partitions = 3;
  static constexpr u32 cells_per_partition = 3;
};

using r0pb_sectioned_serial3_high_geometry = r0pb_cta96_x0_major_geometry;

static_assert(r0pb_cta288_pair_geometry::threads == 288);
static_assert(r0pb_cta96_partitioned_geometry::threads == 96);
static_assert(r0pb_cta96_x0_major_geometry::threads == 96);
static_assert(r0pb_cta96_x1_major_geometry::threads == 96);
static_assert(r0pb_cta96_x2_major_geometry::threads == 96);
static_assert(r0pb_sectioned_wide9_geometry::threads == 288);
static_assert(r0pb_sectioned_split3_geometry::threads == 96);
static_assert(r0pb_sectioned_serial3_low_geometry::threads == 96);
static_assert(r0pb_sectioned_serial3_high_geometry::threads == 96);

} // namespace airbender::gkr_windowed_bench
