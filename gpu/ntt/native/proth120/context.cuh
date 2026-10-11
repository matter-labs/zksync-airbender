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

DEVICE_FORCEINLINE pr pr_split_table_power(const pr *low, const pr *high, const u32 low_bits, const u32 e) {
  const u32 lo = e & ((1u << low_bits) - 1u);
  const u32 hi = e >> low_bits;
  if (hi == 0)
    return load_ca(low + lo);
  const pr high_power = load_ca(high + hi);
  return lo == 0 ? high_power : pr::mul(high_power, load_ca(low + lo));
}

DEVICE_FORCEINLINE pr pr_root_power(const proth120_twiddle_descriptor &d, const u32 e) {
  return pr_split_table_power(d.forward_low, d.forward_high, d.low_bits, e);
}

DEVICE_FORCEINLINE pr pr_root_power_inv(const proth120_twiddle_descriptor &d, const u32 e) {
  return pr_split_table_power(d.inverse_low, d.inverse_high, d.low_bits, e);
}

DEVICE_FORCEINLINE pr get_forward_pr_twiddle(const proth120_twiddle_descriptor &d, const u32 r) {
  return pr_root_power(d, bitreverse_low_bits(r, d.log_max_domain - 1));
}

constexpr DEVICE_FORCEINLINE pr TWO_INV() { return {{0xffffffee, 0xffffffff, 0xffffffff, 0x01ffffff}}; }

} // namespace airbender::ntt
