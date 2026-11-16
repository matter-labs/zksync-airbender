#pragma once

#include "gkr/baby_bear/backward/window/window_accumulator.cuh"

#include "gkr/backward/window/window_source.cuh"

namespace airbender::gkr::backward {

struct bwd_window_direct_bf_source {
  const bf *column;
};

struct bwd_window_direct_e4_source {
  const e4 *column;
};

DEVICE_FORCEINLINE bwd_window_direct_bf_source bwd_window_direct_bf(const bwd_window_desc &desc, const u16 packed) {
  const bwd_source_window &address = desc.slot[bwd_source_lane_slot(packed)];
  const u64 pointer = mad_wide(bwd_source_lane_column(packed), address.r0_stride_bytes, reinterpret_cast<u64>(address.base));
  return {reinterpret_cast<const bf *>(pointer)};
}

DEVICE_FORCEINLINE bwd_window_direct_e4_source bwd_window_direct_e4(const bwd_window_desc &desc, const u16 packed) {
  const bwd_source_window &address = desc.slot[bwd_source_lane_slot(packed)];
  const u64 pointer = mad_wide(bwd_source_lane_column(packed), address.r0_stride_bytes, reinterpret_cast<u64>(address.base));
  return {reinterpret_cast<const e4 *>(pointer)};
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
