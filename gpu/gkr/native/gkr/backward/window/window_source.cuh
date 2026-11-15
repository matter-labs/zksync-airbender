#pragma once

#include "gkr/backward/window/window_abi.cuh"

namespace airbender::gkr::backward {

// The (x0, x1) corner the owning warp evaluates. `2` means the infinity
// endpoint, i.e. the finite difference across that axis. Both flags are carried
// rather than recomputed so the warp-uniform `__all_sync` form survives into the
// hot loop.
struct bwd_window_selector_pair {
  u32 x0;
  u32 x1;
  bool inf0;
  bool inf1;

  DEVICE_FORCEINLINE bool x0_infinity() const { return inf0; }
  DEVICE_FORCEINLINE bool x1_infinity() const { return inf1; }
  DEVICE_FORCEINLINE bool has_infinity() const { return inf0 || inf1; }
};

// The eight corners of one row live contiguously, x0 the most significant bit.
constexpr HOST_DEVICE_FORCEINLINE u32 bwd_window_corner_index(const u32 row, const u32 bit0, const u32 bit1, const u32 bit2) {
  return (row << 3) | (bit2 | (bit1 << 1) | (bit0 << 2));
}

static_assert(bwd_window_corner_index(3, 0, 0, 0) == 24);
static_assert(bwd_window_corner_index(3, 0, 0, 1) == 25);
static_assert(bwd_window_corner_index(3, 0, 1, 0) == 26);
static_assert(bwd_window_corner_index(3, 1, 0, 0) == 28);
static_assert(bwd_window_corner_index(3, 1, 1, 1) == 31);

template <typename T, u32 Count> struct alignas((sizeof(T) * Count < 32) ? sizeof(T) * Count : 32) bwd_window_packed_values {
  T values[Count];
};

template <typename T> struct bwd_window_pair {
  T values[2];
};

template <typename T> struct bwd_window_triplet {
  T values[3];
};

template <typename T, u32 Count> DEVICE_FORCEINLINE bwd_window_packed_values<T, Count> bwd_window_load(const T *column, const u32 index) {
  using packed = bwd_window_packed_values<T, Count>;
  return load<packed, ld_modifier::ca>(reinterpret_cast<const packed *>(column + index));
}

} // namespace airbender::gkr::backward
