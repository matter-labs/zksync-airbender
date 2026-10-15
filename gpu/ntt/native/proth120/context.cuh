#pragma once

#include <common.cuh>
#include <cstddef>
#include <primitives/memory.cuh>
#include <primitives/proth120.cuh>
#include <type_traits>

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;

namespace airbender::ntt {

struct proth120_twiddle_descriptor {
  const pr *forward_low;
  const pr *forward_high;
  const pr *inverse_low;
  const pr *inverse_high;
  u32 log_max_domain;
  u32 low_bits;
};

static_assert(sizeof(proth120_twiddle_descriptor) == 40);
static_assert(alignof(proth120_twiddle_descriptor) == 8);
static_assert(offsetof(proth120_twiddle_descriptor, forward_low) == 0);
static_assert(offsetof(proth120_twiddle_descriptor, forward_high) == 8);
static_assert(offsetof(proth120_twiddle_descriptor, inverse_low) == 16);
static_assert(offsetof(proth120_twiddle_descriptor, inverse_high) == 24);
static_assert(offsetof(proth120_twiddle_descriptor, log_max_domain) == 32);
static_assert(offsetof(proth120_twiddle_descriptor, low_bits) == 36);
static_assert(std::is_standard_layout_v<proth120_twiddle_descriptor>);
static_assert(std::is_trivially_copyable_v<proth120_twiddle_descriptor>);

DEVICE_FORCEINLINE pr pr_split_table_power(const pr *low, const pr *high, const u32 low_bits, const u64 e) {
  const u32 lo = static_cast<u32>(e & ((u64{1} << low_bits) - 1));
  const u32 hi = static_cast<u32>(e >> low_bits);
  if (hi == 0)
    return load_ca(low + lo);
  const pr high_power = load_ca(high + hi);
  return lo == 0 ? high_power : pr::mul(high_power, load_ca(low + lo));
}

DEVICE_FORCEINLINE pr pr_root_power(const proth120_twiddle_descriptor &d, const u64 e) {
  return pr_split_table_power(d.forward_low, d.forward_high, d.low_bits, e);
}

DEVICE_FORCEINLINE pr pr_root_power_inv(const proth120_twiddle_descriptor &d, const u64 e) {
  return pr_split_table_power(d.inverse_low, d.inverse_high, d.low_bits, e);
}

DEVICE_FORCEINLINE pr get_forward_pr_twiddle(const proth120_twiddle_descriptor &d, const u32 r) {
  return pr_root_power(d, bitreverse_low_bits(r, d.log_max_domain - 1));
}

constexpr DEVICE_FORCEINLINE pr TWO_INV() { return {{0xffffffee, 0xffffffff, 0xffffffff, 0x01ffffff}}; }

template <u32 LOG_VALUES, u32 STAGE>
DEVICE_FORCEINLINE void pr_convert_leaf_stage(const proth120_twiddle_descriptor &d, pr (&source)[1u << LOG_VALUES], pr (&target)[1u << LOG_VALUES],
                                              const pr root_inv) {
  constexpr u32 VALUES = 1u << LOG_VALUES;
  constexpr u32 GROUPS = 1u << STAGE;
  constexpr u32 BLOCK = VALUES >> STAGE;
  constexpr u32 HALF = BLOCK / 2;
#pragma unroll
  for (u32 group = 0; group < GROUPS; group++) {
#pragma unroll
    for (u32 t = 0; t < HALF; t++) {
      const pr a = source[group * BLOCK + 2 * t];
      const pr b = source[group * BLOCK + 2 * t + 1];
      const u64 exponent = static_cast<u64>(bitreverse_low_bits(t, LOG_VALUES - 1)) << (d.log_max_domain - LOG_VALUES);
      const pr twiddle = pr_root_power_inv(d, exponent);
      target[group * HALF + t] = pr::mul(pr::add(a, b), TWO_INV());
      target[(group | GROUPS) * HALF + t] = pr::mul(pr::mul(pr::sub(a, b), pr::mul(root_inv, twiddle)), TWO_INV());
    }
  }
  if constexpr (STAGE + 1 < LOG_VALUES)
    pr_convert_leaf_stage<LOG_VALUES, STAGE + 1>(d, target, source, pr::sqr(root_inv));
  else if constexpr (LOG_VALUES & 1) {
#pragma unroll
    for (u32 slot = 0; slot < VALUES; slot++)
      source[slot] = target[slot];
  }
}

template <u32 LOG_VALUES>
DEVICE_FORCEINLINE void ab_pr_convert_leaf(const proth120_twiddle_descriptor &d, proth120 (&leaf)[1u << LOG_VALUES], proth120 base_root_inv) {
  static_assert(LOG_VALUES <= 4);
  if constexpr (LOG_VALUES > 0) {
    pr scratch[1u << LOG_VALUES];
    pr_convert_leaf_stage<LOG_VALUES, 0>(d, leaf, scratch, base_root_inv);
  }
}

} // namespace airbender::ntt
