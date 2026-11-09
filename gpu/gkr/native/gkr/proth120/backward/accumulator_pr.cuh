#pragma once
#include "primitives/proth120.cuh"
#include <cassert>

namespace airbender::gkr::proth120::backward {

using pr = ::airbender::primitives::field::proth120;

DEVICE_FORCEINLINE pr pr_zero() {
  pr zero;
#pragma unroll
  for (u32 i = 0; i < 4; i++)
    zero.limbs[i] = 0;
  return zero;
}

DEVICE_FORCEINLINE pr pr_one() {
  pr one;
  one.limbs[0] = 0xffffffdcu;
  one.limbs[1] = 0xffffffffu;
  one.limbs[2] = 0xffffffffu;
  one.limbs[3] = 0x03ffffffu;
  return one;
}

static_assert(pr::MONT_R[0] == 0xffffffdcu && pr::MONT_R[1] == 0xffffffffu && pr::MONT_R[2] == 0xffffffffu && pr::MONT_R[3] == 0x03ffffffu);

DEVICE_FORCEINLINE pr pr_neg(const pr x) { return pr::is_zero(x) ? x : pr::sub(pr_zero(), x); }

constexpr u32 PR_SUM32_TERMS = 32;

struct PrSum32 {
  u32 limbs[4];
  u32 count;

  static DEVICE_FORCEINLINE PrSum32 zero() {
    PrSum32 result;
#pragma unroll
    for (u32 i = 0; i < 4; i++)
      result.limbs[i] = 0;
    result.count = 0;
    return result;
  }

  DEVICE_FORCEINLINE void add(const pr value) {
    assert(count < PR_SUM32_TERMS);
    pr raw = {{limbs[0], limbs[1], limbs[2], limbs[3]}};
    ::airbender::primitives::field::proth120_detail::add_limbs<false>(raw, value, raw);
#pragma unroll
    for (u32 i = 0; i < 4; i++)
      limbs[i] = raw.limbs[i];
    count++;
  }

  DEVICE_FORCEINLINE bool full() const { return count == PR_SUM32_TERMS; }

  DEVICE_FORCEINLINE pr flush() {
    const pr result = pr::reduce_lazy({{limbs[0], limbs[1], limbs[2], limbs[3]}});
#pragma unroll
    for (u32 i = 0; i < 4; i++)
      limbs[i] = 0;
    count = 0;
    return result;
  }
};

static_assert(sizeof(PrSum32) == 20);
static_assert(u64{PR_SUM32_TERMS} * (u64{pr::ORDER[3]} + 1) <= (1ull << 32));

} // namespace airbender::gkr::proth120::backward
