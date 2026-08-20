#pragma once

#include "windowed_r0_prototype_abi.cuh"

#include <type_traits>

namespace airbender::gkr_windowed_bench {

// The u96 accumulator's high word represents hi * 2^64 in a sum of raw
// Montgomery products. After Montgomery reduction it contributes hi * 2^32,
// i.e. the Montgomery representation of hi. Express that scale directly in
// raw Montgomery form; this is runtime carry arithmetic, not integer decoding.
DEVICE_FORCEINLINE bf r0_u96_high_word_contribution(const u32 hi) { return bf::mul(bf::from_reduced_raw_repr(hi), bf::from_reduced_raw_repr(bf::MONT_R2)); }

struct r0_u64_accumulator {
  u64 value = 0;
  u32 segment_length = 0;

  DEVICE_FORCEINLINE void prepare_next_product() {
    if (segment_length == 4) {
      value = mul_wide(bf::red_wide(value).limb, bf::MONT_R);
      segment_length = 0;
    }
  }

  DEVICE_FORCEINLINE void add_product(const u32 a, const u32 b) {
    prepare_next_product();
    value = mad_wide(a, b, value);
    ++segment_length;
  }

  DEVICE_FORCEINLINE bf reduce() const { return bf::red_wide(value); }
};

struct r0_u96_accumulator {
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
    return bf::add(bf::red_wide(low), r0_u96_high_word_contribution(hi));
  }
};

struct r0_inner_canonical {};

struct r0_inner_u64 {
  r0_u64_accumulator values[3]{};
};

struct r0_outer_canonical {};

struct r0_outer_u64 {
  r0_u64_accumulator values[3][4]{};
};

struct r0_outer_u96 {
  r0_u96_accumulator values[3][4]{};
};

static_assert(sizeof(r0_u64_accumulator) == 16);
static_assert(sizeof(r0_u96_accumulator) == 12);
static_assert(sizeof(r0_inner_u64) == 48);
static_assert(sizeof(r0_outer_u64) == 192);
static_assert(sizeof(r0_outer_u96) == 144);
static_assert(std::is_trivially_copyable_v<r0_u64_accumulator>);
static_assert(std::is_trivially_copyable_v<r0_u96_accumulator>);
static_assert(std::is_trivially_copyable_v<r0_inner_u64>);
static_assert(std::is_trivially_copyable_v<r0_outer_u64>);
static_assert(std::is_trivially_copyable_v<r0_outer_u96>);
static_assert(r0_u64_accumulator{}.value == 0 && r0_u64_accumulator{}.segment_length == 0);
static_assert(r0_u96_accumulator{}.lo == 0 && r0_u96_accumulator{}.mid == 0 && r0_u96_accumulator{}.hi == 0);

} // namespace airbender::gkr_windowed_bench
