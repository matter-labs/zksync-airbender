#pragma once

#include "window_accumulator.cuh"

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

DEVICE_FORCEINLINE bf bwd_window_sub(const bf one, const bf zero) { return bf::sub(one, zero); }

DEVICE_FORCEINLINE e4 bwd_window_sub(const e4 one, const e4 zero) { return e4::sub(one, zero); }

template <typename T, u32 Count> struct alignas((sizeof(T) * Count < 32) ? sizeof(T) * Count : 32) bwd_window_packed_values {
  T values[Count];
};

template <typename T> struct bwd_window_pair {
  T values[2];
};

template <typename T> struct bwd_window_triplet {
  T values[3];
};

// The infinity cell is the product of endpoint differences; each pair already
// includes the x0/x1 selector differences.
template <typename T, typename Factor>
DEVICE_FORCEINLINE bwd_window_triplet<T> bwd_window_endpoint_product(const bwd_window_pair<T> a, const bwd_window_pair<Factor> b) {
  const T leading = T::mul(bwd_window_sub(a.values[1], a.values[0]), bwd_window_sub(b.values[1], b.values[0]));
  return {{T::mul(a.values[0], b.values[0]), T::mul(a.values[1], b.values[1]), leading}};
}

template <typename T, u32 Count> DEVICE_FORCEINLINE bwd_window_packed_values<T, Count> bwd_window_load(const T *column, const u32 index) {
  using packed = bwd_window_packed_values<T, Count>;
  return load<packed, ld_modifier::ca>(reinterpret_cast<const packed *>(column + index));
}

struct bwd_window_direct_bf_source {
  const bf *column;
};

struct bwd_window_direct_e4_source {
  const e4 *column;
};

// A virtual-setup source has no matrix: the wire carries its kind in the
// operand word and the value is produced from the row index.
struct bwd_window_procedural_bf_source {
  u8 procedural_kind;
};

DEVICE_FORCEINLINE bwd_window_direct_bf_source bwd_window_direct_bf(const bwd_window_desc &desc, const u16 packed) {
  const bwd_source_window &address = desc.slot[bwd_source_lane_slot(packed)];
  const bf *base = reinterpret_cast<const bf *>(address.base);
  return {base + (static_cast<size_t>(bwd_source_lane_column(packed)) << address.log2_stride)};
}

DEVICE_FORCEINLINE bwd_window_direct_e4_source bwd_window_direct_e4(const bwd_window_desc &desc, const u16 packed) {
  const bwd_source_window &address = desc.slot[bwd_source_lane_slot(packed)];
  const e4 *base = reinterpret_cast<const e4 *>(address.base);
  return {base + (static_cast<size_t>(bwd_source_lane_column(packed)) << address.log2_stride)};
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
    return {{bwd_window_sub(one.values[0], zero.values[0]), bwd_window_sub(one.values[1], zero.values[1])}};
  }
  if (!selector.x0_infinity() && selector.x1_infinity()) {
    const auto values = bwd_window_load<T, 4>(column, bwd_window_corner_index(row, selector.x0, 0, 0));
    return {{bwd_window_sub(values.values[2], values.values[0]), bwd_window_sub(values.values[3], values.values[1])}};
  }
  const auto values = bwd_window_load<T, 8>(column, bwd_window_corner_index(row, 0, 0, 0));
  const T at_x1_zero_0 = bwd_window_sub(values.values[4], values.values[0]);
  const T at_x1_zero_1 = bwd_window_sub(values.values[5], values.values[1]);
  const T at_x1_one_0 = bwd_window_sub(values.values[6], values.values[2]);
  const T at_x1_one_1 = bwd_window_sub(values.values[7], values.values[3]);
  return {{bwd_window_sub(at_x1_one_0, at_x1_zero_0), bwd_window_sub(at_x1_one_1, at_x1_zero_1)}};
}

DEVICE_FORCEINLINE bwd_window_pair<bf> bwd_window_pair_values(const bwd_window_direct_bf_source source, const u32 row,
                                                              const bwd_window_selector_pair selector) {
  return bwd_window_direct_pair(source.column, row, selector);
}

DEVICE_FORCEINLINE bwd_window_pair<e4> bwd_window_pair_values(const bwd_window_direct_e4_source source, const u32 row,
                                                              const bwd_window_selector_pair selector) {
  return bwd_window_direct_pair(source.column, row, selector);
}

// Coefficient ids index the shared output bank directly: its first two slots hold
// the reserved `+1` / `-1` literals as ordinary filled plans, so the hot loop
// needs no literal branch.
DEVICE_FORCEINLINE e4 bwd_window_coefficient(const u16 id) { return AB_GKR_BWD_COEFF(id); }

template <bool MayNegate> DEVICE_FORCEINLINE e4 bwd_window_signed_coefficient(const u16 encoded) {
  const e4 value = bwd_window_coefficient(encoded & BWD_WINDOW_ID_MASK);
  if constexpr (MayNegate)
    return (encoded & BWD_WINDOW_FLAG) != 0 ? e4::neg(value) : value;
  return value;
}

} // namespace airbender::gkr::backward
