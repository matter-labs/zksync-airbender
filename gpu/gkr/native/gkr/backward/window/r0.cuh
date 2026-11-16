#pragma once

#include "gkr/backward/window/window_geometry.cuh"

namespace airbender::gkr::backward {

// An aligned eight-corner window stays within one virtual-source region, so
// its procedural endpoints are affine in the row.
template <typename F, typename Small>
DEVICE_FORCEINLINE bwd_window_pair<F> bwd_window_procedural_pair(const u8 procedural_kind, const u32 row, const bwd_window_selector_pair selector) {
  static_assert(GKR_TIMESTAMP_COLUMNS_NUM_BITS >= 3);
  const u32 base = row << 3;
  u32 origin;
  u32 step;
  switch (procedural_kind) {
  case BWD_COEFF_PROCEDURAL_RANGE_CHECK_16_BITS:
    if (base >= (1u << 16))
      return {{F::ZERO(), F::ZERO()}};
    origin = base;
    step = 1;
    break;
  case BWD_COEFF_PROCEDURAL_RANGE_CHECK_TIMESTAMP:
    if (base >= (1u << GKR_TIMESTAMP_COLUMNS_NUM_BITS))
      return {{F::ZERO(), F::ZERO()}};
    origin = base;
    step = 1;
    break;
  case BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_LOW:
    origin = (base << 2) & 0xffffu;
    step = 4;
    break;
  case BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_HIGH: {
    const F value = selector.has_infinity() ? F::ZERO() : Small::from_u32(base >> 14);
    return {{value, value}};
  }
  default:
    return {{F::ZERO(), F::ZERO()}};
  }
  if (selector.has_infinity()) {
    const u32 slope = selector.x0_infinity() ? (selector.x1_infinity() ? 0 : 4 * step) : 2 * step;
    const F value = Small::from_u32(slope);
    return {{value, value}};
  }
  const u32 value = origin + step * (4 * selector.x0 + 2 * selector.x1);
  return {{Small::from_u32(value), Small::from_u32(value + step)}};
}

} // namespace airbender::gkr::backward
