#pragma once
// Adapted from matter-labs/era-bellman-cuda, src/ff_dispatch_st.cuh (MIT OR Apache-2.0).

#include "../common.cuh"
#include "carry_chain.cuh"
#include "memory.cuh"
#include "ptx.cuh"
#include <cassert>
#include <cstddef>
#include <type_traits>

namespace airbender::primitives::field {

// Kernel-local temporaries may use [0, 2p); every published field buffer is canonical Montgomery.
struct __align__(16) proth120 {
  u32 limbs[4];

  static constexpr u32 MONT_K = 0xffffffffu;
  static constexpr u32 ORDER[4] = {1, 0, 0, 0x07000000};
  static constexpr u32 MONT_R[4] = {0xffffffdc, 0xffffffff, 0xffffffff, 0x03ffffff};
  static constexpr u32 MONT_R2[4] = {0x6db6e0a8, 0xdb6db6db, 0xb6db6db6, 0x05b6db6d};
  static constexpr u32 MODULUS_BITS = 123;

  static constexpr DEVICE_FORCEINLINE proth120 ZERO() { return {{0, 0, 0, 0}}; }
  static constexpr DEVICE_FORCEINLINE proth120 ONE() { return {{0xffffffdc, 0xffffffff, 0xffffffff, 0x03ffffff}}; }
  static constexpr DEVICE_FORCEINLINE proth120 TWO() { return {{0xffffffb7, 0xffffffff, 0xffffffff, 0x00ffffff}}; }

  static DEVICE_FORCEINLINE proth120 add(proth120 x, proth120 y);
  static DEVICE_FORCEINLINE proth120 sub(proth120 x, proth120 y);
  static DEVICE_FORCEINLINE proth120 mul(proth120 x, proth120 y);
  static DEVICE_FORCEINLINE proth120 sqr(proth120 x);
  static DEVICE_FORCEINLINE proth120 neg(proth120 x) { return is_zero(x) ? ZERO() : sub(ZERO(), x); }
  static DEVICE_FORCEINLINE proth120 dbl(proth120 x);
  static DEVICE_FORCEINLINE proth120 fma(proth120 a, proth120 b, proth120 c) { return add(mul(a, b), c); }
  static DEVICE_FORCEINLINE proth120 fms(proth120 a, proth120 b, proth120 c) { return sub(mul(a, b), c); }

  template <unsigned K> static DEVICE_FORCEINLINE proth120 pow_log2_exp(proth120 x) {
#pragma unroll
    for (unsigned i = 0; i < K; i++)
      x = sqr(x);
    return x;
  }

  static DEVICE_FORCEINLINE bool eq(proth120 x, proth120 y) {
    return ((x.limbs[0] ^ y.limbs[0]) | (x.limbs[1] ^ y.limbs[1]) | (x.limbs[2] ^ y.limbs[2]) | (x.limbs[3] ^ y.limbs[3])) == 0;
  }
  static DEVICE_FORCEINLINE bool is_zero(proth120 x) { return (x.limbs[0] | x.limbs[1] | x.limbs[2] | x.limbs[3]) == 0; }

  DEVICE_FORCEINLINE proth120 operator-() const { return neg(*this); }
  DEVICE_FORCEINLINE proth120 operator+(proth120 v) const { return add(*this, v); }
  DEVICE_FORCEINLINE proth120 operator-(proth120 v) const { return sub(*this, v); }
  DEVICE_FORCEINLINE proth120 operator*(proth120 v) const { return mul(*this, v); }
  DEVICE_FORCEINLINE proth120 &operator+=(proth120 v) {
    *this = add(*this, v);
    return *this;
  }
  DEVICE_FORCEINLINE proth120 &operator-=(proth120 v) {
    *this = sub(*this, v);
    return *this;
  }
  DEVICE_FORCEINLINE proth120 &operator*=(proth120 v) {
    *this = mul(*this, v);
    return *this;
  }
};

using pr = proth120;
static_assert(sizeof(proth120) == 16 && alignof(proth120) == 16);
static_assert(std::is_standard_layout_v<proth120>);
static_assert(std::is_trivially_copyable_v<proth120>);
static_assert(offsetof(proth120, limbs) == 0);

namespace proth120_detail {

static constexpr u32 LC = 4;
static_assert(LC % 2 == 0);

struct __align__(16) proth120_wide {
  u32 limbs[8];

  DEVICE_FORCEINLINE void set_lo(proth120 x) {
#pragma unroll
    for (u32 i = 0; i < LC; i++)
      limbs[i] = x.limbs[i];
  }
  DEVICE_FORCEINLINE void set_hi(proth120 x) {
#pragma unroll
    for (u32 i = 0; i < LC; i++)
      limbs[i + LC] = x.limbs[i];
  }
  DEVICE_FORCEINLINE proth120 get_lo() const {
    proth120 r{};
#pragma unroll
    for (u32 i = 0; i < LC; i++)
      r.limbs[i] = limbs[i];
    return r;
  }
  DEVICE_FORCEINLINE proth120 get_hi() const {
    proth120 r{};
#pragma unroll
    for (u32 i = 0; i < LC; i++)
      r.limbs[i] = limbs[i + LC];
    return r;
  }
};

template <u32 N = 1> consteval DEVICE_FORCEINLINE proth120 MODULUS() {
  static_assert(N == 0 || N == 1 || N == 2 || N == 4);
  return {{N, 0, 0, 0x07000000u * N}};
}

template <u32 N = 1> consteval DEVICE_FORCEINLINE proth120_wide MODULUS_SQUARED() {
  static_assert(N == 0 || N == 1 || N == 2 || N == 4);
  return {{N, 0, 0, 0x0e000000u * N, 0, 0, 0, 0x00310000u * N}};
}

template <bool SUBTRACT, bool CARRY_OUT> DEVICE_FORCEINLINE u32 add_sub_limbs(const proth120 &xs, const proth120 &ys, proth120 &rs) {
  const u32 *x = xs.limbs;
  const u32 *y = ys.limbs;
  u32 *r = rs.limbs;
  carry_chain<CARRY_OUT ? LC + 1 : LC> chain;
#pragma unroll
  for (u32 i = 0; i < LC; i++)
    r[i] = SUBTRACT ? chain.sub(x[i], y[i]) : chain.add(x[i], y[i]);
  if (!CARRY_OUT)
    return 0;
  return SUBTRACT ? chain.sub(0, 0) : chain.add(0, 0);
}

template <bool SUBTRACT, bool CARRY_OUT> DEVICE_FORCEINLINE u32 add_sub_limbs(const proth120_wide &xs, const proth120_wide &ys, proth120_wide &rs) {
  const u32 *x = xs.limbs;
  const u32 *y = ys.limbs;
  u32 *r = rs.limbs;
  carry_chain<CARRY_OUT ? 2 * LC + 1 : 2 * LC> chain;
#pragma unroll
  for (u32 i = 0; i < 2 * LC; i++) {
    r[i] = SUBTRACT ? chain.sub(x[i], y[i]) : chain.add(x[i], y[i]);
  }
  if (!CARRY_OUT)
    return 0;
  return SUBTRACT ? chain.sub(0, 0) : chain.add(0, 0);
}

template <bool CARRY_OUT, typename T> DEVICE_FORCEINLINE u32 add_limbs(const T &xs, const T &ys, T &rs) { return add_sub_limbs<false, CARRY_OUT>(xs, ys, rs); }

template <bool CARRY_OUT, typename T> DEVICE_FORCEINLINE u32 sub_limbs(const T &xs, const T &ys, T &rs) { return add_sub_limbs<true, CARRY_OUT>(xs, ys, rs); }

template <u32 REDUCTION_SIZE = 1> DEVICE_FORCEINLINE proth120 reduce(const proth120 &xs) {
  static_assert(REDUCTION_SIZE == 0 || REDUCTION_SIZE == 1 || REDUCTION_SIZE == 2 || REDUCTION_SIZE == 4);
  if (REDUCTION_SIZE == 0)
    return xs;
  constexpr proth120 modulus = MODULUS<REDUCTION_SIZE>();
  proth120 rs = {};
  return sub_limbs<true>(xs, modulus, rs) ? xs : rs;
}

template <u32 REDUCTION_SIZE = 1> DEVICE_FORCEINLINE proth120_wide reduce_wide(const proth120_wide &xs) {
  static_assert(REDUCTION_SIZE == 0 || REDUCTION_SIZE == 1 || REDUCTION_SIZE == 2 || REDUCTION_SIZE == 4);
  if (REDUCTION_SIZE == 0)
    return xs;
  const proth120_wide modulus_squared = MODULUS_SQUARED<REDUCTION_SIZE>();
  proth120_wide rs = {};
  return sub_limbs<true>(xs, modulus_squared, rs) ? xs : rs;
}

template <u32 REDUCTION_SIZE = 1> DEVICE_FORCEINLINE proth120 add_pick_reduction_size(const proth120 &xs, const proth120 &ys) {
  static_assert(REDUCTION_SIZE == 0 || REDUCTION_SIZE == 1 || REDUCTION_SIZE == 2 || REDUCTION_SIZE == 4);
  proth120 rs = {};
  add_limbs<false>(xs, ys, rs);
  return reduce<REDUCTION_SIZE>(rs);
}

template <u32 REDUCTION_SIZE = 1> DEVICE_FORCEINLINE proth120_wide add_wide(const proth120_wide &xs, const proth120_wide &ys) {
  static_assert(REDUCTION_SIZE == 0 || REDUCTION_SIZE == 1 || REDUCTION_SIZE == 2 || REDUCTION_SIZE == 4);
  proth120_wide rs = {};
  add_limbs<false>(xs, ys, rs);
  return reduce_wide<REDUCTION_SIZE>(rs);
}

template <u32 REDUCTION_SIZE = 1> DEVICE_FORCEINLINE proth120 sub_pick_reduction_size(const proth120 &xs, const proth120 &ys) {
  static_assert(REDUCTION_SIZE == 0 || REDUCTION_SIZE == 1 || REDUCTION_SIZE == 2 || REDUCTION_SIZE == 4);
  proth120 rs = {};
  if (REDUCTION_SIZE == 0) {
    sub_limbs<false>(xs, ys, rs);
  } else {
    u32 carry = sub_limbs<true>(xs, ys, rs);
    if (carry == 0)
      return rs;
    const proth120 modulus = MODULUS<REDUCTION_SIZE>();
    add_limbs<false>(rs, modulus, rs);
  }
  return rs;
}

template <u32 REDUCTION_SIZE = 1> DEVICE_FORCEINLINE proth120_wide sub_wide(const proth120_wide &xs, const proth120_wide &ys) {
  static_assert(REDUCTION_SIZE == 0 || REDUCTION_SIZE == 1 || REDUCTION_SIZE == 2 || REDUCTION_SIZE == 4);
  proth120_wide rs = {};
  if (REDUCTION_SIZE == 0) {
    sub_limbs<false>(xs, ys, rs);
  } else {
    u32 carry = sub_limbs<true>(xs, ys, rs);
    if (carry == 0)
      return rs;
    const proth120_wide modulus_squared = MODULUS_SQUARED<REDUCTION_SIZE>();
    add_limbs<false>(rs, modulus_squared, rs);
  }
  return rs;
}

// The following algorithms are adaptations of
// http://www.acsel-lab.com/arithmetic/arith23/data/1616a047.pdf,
// taken from https://github.com/z-prize/test-msm-gpu (under Apache 2.0 license)
// and modified to use our datatypes.
DEVICE_FORCEINLINE void mul_n(u32 *acc, const u32 *a, u32 bi, size_t n = LC) {
#pragma unroll
  for (size_t i = 0; i < n; i += 2) {
    acc[i] = ptx::mul_lo(a[i], bi);
    acc[i + 1] = ptx::mul_hi(a[i], bi);
  }
}

DEVICE_FORCEINLINE void cmad_n(u32 *acc, const u32 *a, u32 bi, size_t n = LC) {
  acc[0] = ptx::mad_lo_cc(a[0], bi, acc[0]);
  acc[1] = ptx::madc_hi_cc(a[0], bi, acc[1]);
#pragma unroll
  for (size_t i = 2; i < n; i += 2) {
    acc[i] = ptx::madc_lo_cc(a[i], bi, acc[i]);
    acc[i + 1] = ptx::madc_hi_cc(a[i], bi, acc[i + 1]);
  }
}

DEVICE_FORCEINLINE void madc_n_rshift(u32 *odd, const u32 *a, u32 bi) {
  constexpr u32 n = LC;
#pragma unroll
  for (size_t i = 0; i < n - 2; i += 2) {
    odd[i] = ptx::madc_lo_cc(a[i], bi, odd[i + 2]);
    odd[i + 1] = ptx::madc_hi_cc(a[i], bi, odd[i + 3]);
  }
  odd[n - 2] = ptx::madc_lo_cc(a[n - 2], bi, 0);
  odd[n - 1] = ptx::madc_hi(a[n - 2], bi, 0);
}

DEVICE_FORCEINLINE void mad_n_redc(u32 *even, u32 *odd, const u32 *a, u32 bi, bool first = false) {
  constexpr u32 n = LC;
  constexpr auto modulus = MODULUS<1>();
  const u32 *const MOD = modulus.limbs;
  if (first) {
    mul_n(odd, a + 1, bi);
    mul_n(even, a, bi);
  } else {
    even[0] = ptx::add_cc(even[0], odd[1]);
    madc_n_rshift(odd, a + 1, bi);
    cmad_n(even, a, bi);
    odd[n - 1] = ptx::addc(odd[n - 1], 0);
  }
  u32 mi = even[0] * proth120::MONT_K;
  odd[2] = ptx::mad_lo_cc(MOD[3], mi, odd[2]);
  odd[3] = ptx::madc_hi(MOD[3], mi, odd[3]);
  even[0] = ptx::add_cc(even[0], mi);
  even[1] = ptx::addc_cc(even[1], 0);
  even[2] = ptx::addc_cc(even[2], 0);
  even[3] = ptx::addc_cc(even[3], 0);
  odd[n - 1] = ptx::addc(odd[n - 1], 0);
}

DEVICE_FORCEINLINE void mad_row(u32 *odd, u32 *even, const u32 *a, u32 bi, size_t n = LC) {
  cmad_n(odd, a + 1, bi, n - 2);
  odd[n - 2] = ptx::madc_lo_cc(a[n - 1], bi, 0);
  odd[n - 1] = ptx::madc_hi(a[n - 1], bi, 0);
  cmad_n(even, a, bi, n);
  odd[n - 1] = ptx::addc(odd[n - 1], 0);
}

DEVICE_FORCEINLINE void qad_row(u32 *odd, u32 *even, const u32 *a, u32 bi, size_t n = LC) {
  cmad_n(odd, a, bi, n - 2);
  odd[n - 2] = ptx::madc_lo_cc(a[n - 2], bi, 0);
  odd[n - 1] = ptx::madc_hi(a[n - 2], bi, 0);
  cmad_n(even, a + 1, bi, n - 2);
  odd[n - 1] = ptx::addc(odd[n - 1], 0);
}

DEVICE_FORCEINLINE void multiply_raw(const proth120 &as, const proth120 &bs, proth120_wide &rs) {
  const u32 *a = as.limbs;
  const u32 *b = bs.limbs;
  u32 *even = rs.limbs;
  __align__(8) u32 odd[2 * LC - 2];
  mul_n(even, a, b[0]);
  mul_n(odd, a + 1, b[0]);
  mad_row(&even[2], &odd[0], a, b[1]);
  size_t i;
#pragma unroll
  for (i = 2; i < LC - 1; i += 2) {
    mad_row(&odd[i], &even[i], a, b[i]);
    mad_row(&even[i + 2], &odd[i], a, b[i + 1]);
  }
  even[1] = ptx::add_cc(even[1], odd[0]);
  for (i = 1; i < 2 * LC - 2; i++)
    even[i + 1] = ptx::addc_cc(even[i + 1], odd[i]);
  even[i + 1] = ptx::addc(even[i + 1], 0);
}

DEVICE_FORCEINLINE void sqr_raw(const proth120 &as, proth120_wide &rs) {
  const u32 *a = as.limbs;
  u32 *even = rs.limbs;
  size_t i = 0, j;
  __align__(8) u32 odd[2 * LC - 2];

  mul_n(even + 2, a + 2, a[0], LC - 2);
  mul_n(odd, a + 1, a[0], LC);

  static_assert(LC == 4);
  // #pragma unroll
  //     while (i < LC - 4) {
  //       ++i;
  //       mad_row(&even[2 * i + 2], &odd[2 * i], &a[i + 1], a[i], LC - i - 1);
  //       ++i;
  //       qad_row(&odd[2 * i], &even[2 * i + 2], &a[i + 1], a[i], LC - i);
  //     }

  even[2 * LC - 4] = ptx::mul_lo(a[LC - 1], a[LC - 3]);
  even[2 * LC - 3] = ptx::mul_hi(a[LC - 1], a[LC - 3]);
  odd[2 * LC - 6] = ptx::mad_lo_cc(a[LC - 2], a[LC - 3], odd[2 * LC - 6]);
  odd[2 * LC - 5] = ptx::madc_hi_cc(a[LC - 2], a[LC - 3], odd[2 * LC - 5]);
  even[2 * LC - 3] = ptx::addc(even[2 * LC - 3], 0);

  odd[2 * LC - 4] = ptx::mul_lo(a[LC - 1], a[LC - 2]);
  odd[2 * LC - 3] = ptx::mul_hi(a[LC - 1], a[LC - 2]);

  even[2] = ptx::add_cc(even[2], odd[1]);
  for (j = 2; j < 2 * LC - 3; j++)
    even[j + 1] = ptx::addc_cc(even[j + 1], odd[j]);
  even[j + 1] = ptx::addc(odd[j], 0);

  even[0] = 0;
  even[1] = ptx::add_cc(odd[0], odd[0]);
  for (j = 2; j < 2 * LC - 1; j++)
    even[j] = ptx::addc_cc(even[j], even[j]);
  even[j] = ptx::addc(0u, 0u);

  i = 0;
  even[2 * i] = ptx::mad_lo_cc(a[i], a[i], even[2 * i]);
  even[2 * i + 1] = ptx::madc_hi_cc(a[i], a[i], even[2 * i + 1]);
  for (++i; i < LC; i++) {
    even[2 * i] = ptx::madc_lo_cc(a[i], a[i], even[2 * i]);
    even[2 * i + 1] = ptx::madc_hi_cc(a[i], a[i], even[2 * i + 1]);
  }
}

DEVICE_FORCEINLINE void mul_by_1_row(u32 *even, u32 *odd, bool first = false) {
  u32 mi;
  constexpr auto modulus = MODULUS<1>();
  const u32 *const MOD = modulus.limbs;
  if (first) {
    mi = even[0] * proth120::MONT_K;
    mul_n(odd, MOD + 1, mi);
    cmad_n(even, MOD, mi);
    odd[LC - 1] = ptx::addc(odd[LC - 1], 0);
  } else {
    even[0] = ptx::add_cc(even[0], odd[1]);
    mi = even[0] * proth120::MONT_K;
    madc_n_rshift(odd, MOD + 1, mi);
    cmad_n(even, MOD, mi);
    odd[LC - 1] = ptx::addc(odd[LC - 1], 0);
  }
}

DEVICE_FORCEINLINE void redc_wide_inplace(proth120_wide &xs) {
  u32 *even = xs.limbs;
  u32 odd[LC];
  size_t i;
#pragma unroll
  for (i = 0; i < LC; i += 2) {
    mul_by_1_row(&even[0], &odd[0], i == 0);
    mul_by_1_row(&odd[0], &even[0]);
  }
  even[0] = ptx::add_cc(even[0], odd[1]);
#pragma unroll
  for (i = 1; i < LC - 1; i++)
    even[i] = ptx::addc_cc(even[i], odd[i + 1]);
  even[i] = ptx::addc(even[i], 0);
  xs.limbs[0] = ptx::add_cc(xs.limbs[0], xs.limbs[LC]);
#pragma unroll
  for (i = 1; i < LC - 1; i++)
    xs.limbs[i] = ptx::addc_cc(xs.limbs[i], xs.limbs[i + LC]);
  xs.limbs[LC - 1] = ptx::addc(xs.limbs[LC - 1], xs.limbs[2 * LC - 1]);
}

DEVICE_FORCEINLINE void montmul_raw(const proth120 &a_in, const proth120 &b_in, proth120 &r_in) {
  constexpr u32 n = LC;
  const u32 *a = a_in.limbs;
  const u32 *b = b_in.limbs;
  u32 *even = r_in.limbs;
  __align__(8) u32 odd[n + 1];
  size_t i;
#pragma unroll
  for (i = 0; i < n; i += 2) {
    mad_n_redc(&even[0], &odd[0], a, b[i], i == 0);
    mad_n_redc(&odd[0], &even[0], a, b[i + 1]);
  }
  even[0] = ptx::add_cc(even[0], odd[1]);
#pragma unroll
  for (i = 1; i < n - 1; i++)
    even[i] = ptx::addc_cc(even[i], odd[i + 1]);
  even[i] = ptx::addc(even[i], 0);
}

template <u32 REDUCTION_SIZE = 1> DEVICE_FORCEINLINE proth120_wide mul_wide(const proth120 &xs, const proth120 &ys) {
  static_assert(REDUCTION_SIZE == 0 || REDUCTION_SIZE == 1 || REDUCTION_SIZE == 2 || REDUCTION_SIZE == 4);
  static_assert(!(proth120::ORDER[LC - 1] >> 30));
  proth120_wide rs = {0};
  multiply_raw(xs, ys, rs);
  return reduce_wide<REDUCTION_SIZE>(rs);
}

template <u32 REDUCTION_SIZE = 1> DEVICE_FORCEINLINE proth120 redc_wide(const proth120_wide &xs) {
  static_assert(REDUCTION_SIZE == 0 || REDUCTION_SIZE == 1 || REDUCTION_SIZE == 2 || REDUCTION_SIZE == 4);
  proth120_wide tmp{xs};
  redc_wide_inplace(tmp);
  return reduce<REDUCTION_SIZE>(proth120{tmp.get_lo()});
}

template <u32 REDUCTION_SIZE = 1> DEVICE_FORCEINLINE proth120 mul_pick_reduction_size(const proth120 &xs, const proth120 &ys) {
  static_assert(REDUCTION_SIZE == 0 || REDUCTION_SIZE == 1 || REDUCTION_SIZE == 2 || REDUCTION_SIZE == 4);
  static_assert(!(proth120::ORDER[LC - 1] >> 30));
  proth120 rs{};
  montmul_raw(xs, ys, rs);
  return reduce<REDUCTION_SIZE>(rs);
}

template <u32 REDUCTION_SIZE = 1> DEVICE_FORCEINLINE proth120 sqr_pick_reduction_size(const proth120 &xs) {
  static_assert(REDUCTION_SIZE == 0 || REDUCTION_SIZE == 1 || REDUCTION_SIZE == 2 || REDUCTION_SIZE == 4);
  static_assert(!(proth120::ORDER[LC - 1] >> 30));
  proth120_wide rs = {0};
  sqr_raw(xs, rs);
  redc_wide_inplace(rs);
  return reduce<REDUCTION_SIZE>(proth120{rs.get_lo()});
}

DEVICE_FORCEINLINE proth120 scalar_mul(u32 k, proth120 x) {
  proth120 r = proth120::ZERO();
  while (k) {
    if (k & 1)
      r = proth120::add(r, x);
    k >>= 1;
    if (k)
      x = proth120::dbl(x);
  }
  return r;
}

DEVICE_FORCEINLINE proth120 half(proth120 x) {
  if (x.limbs[0] & 1)
    add_limbs<false>(x, MODULUS<1>(), x);
  proth120 r{};
#pragma unroll
  for (u32 i = 0; i < LC - 1; i++)
    r.limbs[i] = __funnelshift_r(x.limbs[i], x.limbs[i + 1], 1);
  r.limbs[LC - 1] = x.limbs[LC - 1] >> 1;
  return r;
}

DEVICE_FORCEINLINE u32 extract_bits(const u32 words[4], u32 offset, u32 count) {
  assert(count <= 32 && offset <= 128 && count <= 128 - offset);
  if (count == 0)
    return 0;
  u32 i = offset / 32, shift = offset % 32;
  u32 v = words[i] >> shift;
  if (shift && i < 3)
    v |= words[i + 1] << (32 - shift);
  return v & (count == 32 ? 0xffffffffu : (1u << count) - 1u);
}

} // namespace proth120_detail

DEVICE_FORCEINLINE proth120 proth120::add(proth120 x, proth120 y) { return proth120_detail::add_pick_reduction_size<1>(x, y); }
DEVICE_FORCEINLINE proth120 proth120::sub(proth120 x, proth120 y) { return proth120_detail::sub_pick_reduction_size<1>(x, y); }
DEVICE_FORCEINLINE proth120 proth120::mul(proth120 x, proth120 y) { return proth120_detail::mul_pick_reduction_size<1>(x, y); }
DEVICE_FORCEINLINE proth120 proth120::sqr(proth120 x) { return proth120_detail::sqr_pick_reduction_size<1>(x); }
DEVICE_FORCEINLINE proth120 proth120::dbl(proth120 x) {
  proth120 r{};
  r.limbs[0] = x.limbs[0] << 1;
#pragma unroll
  for (u32 i = 1; i < proth120_detail::LC; i++)
    r.limbs[i] = __funnelshift_r(x.limbs[i - 1], x.limbs[i], 31);
  return proth120_detail::reduce<1>(r);
}

} // namespace airbender::primitives::field
