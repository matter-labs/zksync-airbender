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

// The infinity cell is the product of endpoint differences; each pair already
// includes the x0/x1 selector differences.
template <typename T, typename Factor>
DEVICE_FORCEINLINE bwd_window_triplet<T> bwd_window_endpoint_product(const bwd_window_pair<T> a, const bwd_window_pair<Factor> b) {
  const T leading = T::mul(T::sub(a.values[1], a.values[0]), Factor::sub(b.values[1], b.values[0]));
  return {{T::mul(a.values[0], b.values[0]), T::mul(a.values[1], b.values[1]), leading}};
}

// Both x2 endpoints of a materialized column in one vector load per corner pair:
// the two x2 corners are adjacent, so a finite axis reads them together and an
// infinite axis widens the same load.
template <typename T> DEVICE_FORCEINLINE bwd_window_pair<T> bwd_window_direct_pair(const T *column, const u32 row, const bwd_window_selector_pair selector) {
  if (!selector.x0_infinity() && !selector.x1_infinity()) {
    const auto values = bwd_window_load<T, 2>(column, bwd_window_corner_index(row, selector.x0, selector.x1, 0));
    return {{values.values[0], values.values[1]}};
  }
  if (selector.x0_infinity() && !selector.x1_infinity()) {
    const auto zero = bwd_window_load<T, 2>(column, bwd_window_corner_index(row, 0, selector.x1, 0));
    const auto one = bwd_window_load<T, 2>(column, bwd_window_corner_index(row, 1, selector.x1, 0));
    return {{T::sub(one.values[0], zero.values[0]), T::sub(one.values[1], zero.values[1])}};
  }
  if (!selector.x0_infinity() && selector.x1_infinity()) {
    const auto values = bwd_window_load<T, 4>(column, bwd_window_corner_index(row, selector.x0, 0, 0));
    return {{T::sub(values.values[2], values.values[0]), T::sub(values.values[3], values.values[1])}};
  }
  const auto values = bwd_window_load<T, 8>(column, bwd_window_corner_index(row, 0, 0, 0));
  const T at_x1_zero_0 = T::sub(values.values[4], values.values[0]);
  const T at_x1_zero_1 = T::sub(values.values[5], values.values[1]);
  const T at_x1_one_0 = T::sub(values.values[6], values.values[2]);
  const T at_x1_one_1 = T::sub(values.values[7], values.values[3]);
  return {{T::sub(at_x1_one_0, at_x1_zero_0), T::sub(at_x1_one_1, at_x1_zero_1)}};
}

} // namespace airbender::gkr::backward
