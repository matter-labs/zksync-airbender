#pragma once

#include "window_abi.cuh"

#include <type_traits>

namespace airbender::gkr::backward {

// The u96 accumulator's high word represents hi * 2^64 in a sum of raw
// Montgomery products. After Montgomery reduction it contributes hi * 2^32,
// i.e. the Montgomery representation of hi. Express that scale directly in
// raw Montgomery form; this is runtime carry arithmetic, not integer decoding.
DEVICE_FORCEINLINE bf bwd_window_high_word_contribution(const u32 hi) { return bf::mul(bf::from_reduced_raw_repr(hi), bf::from_reduced_raw_repr(bf::MONT_R2)); }

// Deferred-reduction accumulator for a run of raw 32x32 Montgomery products:
// three-word running sum, one Montgomery reduction at the end.
struct bwd_window_u96_accumulator {
  u32 lo = 0;
  u32 mid = 0;
  u32 hi = 0;

  DEVICE_FORCEINLINE void add_product(const u32 a, const u32 b) {
    lo = mad_lo_cc(a, b, lo);
    mid = madc_hi_cc(a, b, mid);
    hi = addc(hi, 0u);
  }

  DEVICE_FORCEINLINE bf reduce() const {
    const u64 low = static_cast<u64>(lo) | (static_cast<u64>(mid) << 32);
    return bf::add(bf::red_wide(low), bwd_window_high_word_contribution(hi));
  }
};

static_assert(sizeof(bwd_window_u96_accumulator) == 12, "u96 accumulator layout drift");
static_assert(std::is_trivially_copyable_v<bwd_window_u96_accumulator>);
static_assert(bwd_window_u96_accumulator{}.lo == 0 && bwd_window_u96_accumulator{}.mid == 0 && bwd_window_u96_accumulator{}.hi == 0);

} // namespace airbender::gkr::backward
