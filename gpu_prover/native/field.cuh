#pragma once
#include "common.cuh"
#include "memory.cuh"
#include "ptx.cuh"

namespace airbender::field {

#define bf base_field
#define e2 ext2_field
#define e4 ext4_field
#define e6 ext6_field

struct bf {
  u32 limb = 0;

  static constexpr u32 ORDER = 0x78000001;  // 2^31 - 2^27 + 1 = 15 * 2^27 + 1
  static constexpr u32 MONT_K = 0x77ffffff; // ORDER*MONT_K mod 2^32 = -1 mod 2^32
  static constexpr u64 MONT_R_U64 = (static_cast<u64>(1) << 32) % static_cast<u64>(ORDER);
  static constexpr u32 MONT_R = MONT_R_U64;
  static constexpr u32 MONT_R2 = MONT_R_U64 * MONT_R_U64 % static_cast<u64>(ORDER);

  constexpr bf() = default;

  explicit constexpr HOST_DEVICE_FORCEINLINE bf(const u32 limb) : limb(limb) {}

  static consteval u32 const_mont_mul(const u32 x, const u32 y) {
    u64 product = static_cast<u64>(x) * static_cast<u64>(y);
    const u32 m = static_cast<u32>(product) * MONT_K;
    product += static_cast<u64>(m) * static_cast<u64>(ORDER);
    u32 result = product >> 32;
    if (result >= ORDER) {
      result -= ORDER;
    }
    return result;
  }

  static consteval bf const_into_mont(const u32 x) { return bf(const_mont_mul(x, MONT_R2)); }

  static consteval bf ZERO() { return bf(0); }

  static consteval bf ONE() { return bf(MONT_R); }

  static consteval bf TWO() { return const_into_mont(2); }

  static consteval bf NON_RES() { return const_into_mont(11); }

  static constexpr DEVICE_FORCEINLINE bf from_raw_u32(const u32 x) { return bf(x); }

  static constexpr DEVICE_FORCEINLINE u32 into_raw_u32(const bf x) { return x.limb; }

  static constexpr DEVICE_FORCEINLINE bf from_lt_2_order_u32(const u32 x) { return bf(x < ORDER ? x : x - ORDER); }

  static constexpr DEVICE_FORCEINLINE bf from_non_reduced_u32(const u32 x) { return from_lt_2_order_u32(x < ORDER ? x : x - ORDER); }

  static constexpr DEVICE_FORCEINLINE bf add(const bf x, const bf y) { return from_lt_2_order_u32(x.limb + y.limb); }

  static DEVICE_FORCEINLINE bf red(const u64 x) {
    const auto x_u32 = reinterpret_cast<const u32 *>(&x);
    const u32 lo = x_u32[0];
    const u32 hi = x_u32[1];
    const u32 m = mul_lo(lo, MONT_K);
    [[maybe_unused]] const u32 out_lo = mad_lo_cc(m, ORDER, lo); // unused (should always yield zero) but we need the carry
    const u32 out_hi = madc_hi(m, ORDER, hi);                    // should not carry out, because output is < 2N
    return from_lt_2_order_u32(out_hi);
  }

  static DEVICE_FORCEINLINE bf mul_u32(const u32 x, const u32 y) { return red(mul_wide(x, y)); }

  static DEVICE_FORCEINLINE bf mul(const bf x, const bf y) { return mul_u32(x.limb, y.limb); }

  static DEVICE_FORCEINLINE bf mul_by_non_residue(const bf x) { return mul(x, NON_RES()); }

  static DEVICE_FORCEINLINE bf into_mont(const bf x) { return mul_u32(x.limb, MONT_R2); }

  static DEVICE_FORCEINLINE bf from_mont(const bf x) { return mul_u32(x.limb, 1); }

  static DEVICE_FORCEINLINE bf from_canonical_u32(const u32 x) { return bf::into_mont(bf(x)); }

  static DEVICE_FORCEINLINE u32 into_canonical_u32(const bf x) { return bf::from_mont(x).limb; }

  static constexpr DEVICE_FORCEINLINE bf neg(const bf x) { return bf(x.limb == 0 ? 0 : ORDER - x.limb); }

  static constexpr DEVICE_FORCEINLINE bf sub(const bf x, const bf y) { return from_lt_2_order_u32(ORDER + x.limb - y.limb); }

  static DEVICE_FORCEINLINE bf sqr(const bf x) { return mul(x, x); }

  static constexpr DEVICE_FORCEINLINE bf dbl(const bf x) { return add(x, x); }

  template <unsigned LOG2_EXP> static DEVICE_FORCEINLINE bf pow_log2_exp(const bf x) {
    bf result = x;
#pragma unroll
    for (int i = 0; i < LOG2_EXP; ++i)
      result = sqr(result);
    return result;
  }

  static DEVICE_FORCEINLINE bf inv(const bf x) {
    if (x.limb == 0)
      return bf(0); // Placeholder: returning zero for undefined inversion

    // Fermat's little theorem: a^(p-1) = 1 (mod p) => a^(p-2) = a^(-1) (mod p)
    // Exponent: 0x78000001 - 2 = 0x77ffffff
    // 0x77ffffff = 0b0111_0111_1111_1111_1111_1111_1111_1111
    // 10
    const bf p_10 = sqr(x);
    const bf p_11 = mul(p_10, x);
    const bf p_110 = sqr(p_11);
    const bf p_111 = mul(p_110, x);
    const bf p_1110 = sqr(p_111);
    const bf p_1111 = mul(p_1110, x);

    bf result = p_1110;
    result = sqr(result);
    result = sqr(result);
    result = sqr(result);
    // 0111_0000
    result = mul(result, p_111);
    // 0111_0111

#pragma unroll
    for (int i = 0; i < 6; ++i) {
      // _1111 per iteration
      result = sqr(result);
      result = sqr(result);
      result = sqr(result);
      result = sqr(result);
      result = mul(result, p_1111);
    }

    return result;
  }

  static DEVICE_FORCEINLINE bf pow(bf x, const unsigned power) {
    auto result = ONE();
    for (unsigned i = power;;) {
      if (i & 1)
        result = mul(result, x);
      i >>= 1;
      if (!i)
        break;
      x = sqr(x);
    }
    return result;
  }

  DEVICE_FORCEINLINE bf operator-() const { return neg(*this); }

  DEVICE_FORCEINLINE bf operator+(const bf rhs) const { return add(*this, rhs); }

  DEVICE_FORCEINLINE bf operator-(const bf rhs) const { return sub(*this, rhs); }

  DEVICE_FORCEINLINE bf operator*(const bf rhs) const { return mul(*this, rhs); }

  DEVICE_FORCEINLINE bf &operator+=(const bf rhs) {
    *this = add(*this, rhs);
    return *this;
  }

  DEVICE_FORCEINLINE bf &operator-=(const bf rhs) {
    *this = sub(*this, rhs);
    return *this;
  }

  DEVICE_FORCEINLINE bf &operator*=(const bf rhs) {
    *this = mul(*this, rhs);
    return *this;
  }
};

struct __align__(8) e2 {
  bf coefficients[2];

  constexpr e2() = default;

  explicit constexpr HOST_DEVICE_FORCEINLINE e2(const bf c[2]) : coefficients{c[0], c[1]} {}

  explicit constexpr HOST_DEVICE_FORCEINLINE e2(const bf c0, const bf c1) : coefficients{c0, c1} {}

  DEVICE_FORCEINLINE bf &operator[](const unsigned idx) { return coefficients[idx]; }

  DEVICE_FORCEINLINE const bf &operator[](const unsigned idx) const { return coefficients[idx]; }

  DEVICE_FORCEINLINE const bf &base_coefficient_from_flat_idx(const unsigned idx) const { return coefficients[idx]; }

  static consteval e2 ZERO() { return e2(bf::ZERO(), bf::ZERO()); }

  static consteval e2 ONE() { return e2(bf::ONE(), bf::ZERO()); }

  static DEVICE_FORCEINLINE e2 add(const e2 x, const bf y) { return e2(bf::add(x[0], y), x[1]); }

  static DEVICE_FORCEINLINE e2 add(const bf x, const e2 y) { return e2(bf::add(x, y[0]), y[1]); }

  static DEVICE_FORCEINLINE e2 add(const e2 x, const e2 y) { return e2(bf::add(x[0], y[0]), bf::add(x[1], y[1])); }

  static DEVICE_FORCEINLINE e2 sub(const e2 x, const bf y) { return e2(bf::sub(x[0], y), x[1]); }

  static DEVICE_FORCEINLINE e2 sub(const bf x, const e2 y) { return e2(bf::sub(x, y[0]), bf::neg(y[1])); }

  static DEVICE_FORCEINLINE e2 sub(const e2 x, const e2 y) { return e2(bf::sub(x[0], y[0]), bf::sub(x[1], y[1])); }

  static DEVICE_FORCEINLINE e2 dbl(const e2 x) { return e2(bf::dbl(x[0]), bf::dbl(x[1])); }

  static DEVICE_FORCEINLINE e2 neg(const e2 x) { return e2(bf::neg(x[0]), bf::neg(x[1])); }

  static DEVICE_FORCEINLINE e2 mul(const e2 x, const bf y) { return e2(bf::mul(x[0], y), bf::mul(x[1], y)); }

  static DEVICE_FORCEINLINE e2 mul(const bf x, const e2 y) { return e2(bf::mul(x, y[0]), bf::mul(x, y[1])); }

  static DEVICE_FORCEINLINE e2 mul(const e2 x, const e2 y) {
    const auto a = bf::add(x[0], x[1]);
    const auto b = bf::add(y[0], y[1]);
    const auto c = bf::mul(x[0], y[0]);
    const auto d = bf::mul(x[1], y[1]);
    const auto e = bf::add(c, bf::mul_by_non_residue(d));
    const auto f = bf::sub(bf::mul(a, b), bf::add(c, d));
    return e2(e, f);
  }

  static DEVICE_FORCEINLINE e2 mul_by_quadratic_non_residue(const e2 x) {
    const auto a = bf::mul_by_non_residue(x[1]);
    const auto b = x[0];
    return e2(a, b);
  }

  static DEVICE_FORCEINLINE e2 mul_by_cubic_non_residue(const e2 x) {
    const auto a = x[0];
    const auto b = x[1];
    const auto c = bf::mul_by_non_residue(b);
    const auto d = bf::add(a, c);
    const auto e = bf::add(a, b);
    return e2(d, e);
  }

  static DEVICE_FORCEINLINE e2 sqr(const e2 x) {
    const auto a = bf::sqr(x[0]);
    const auto b = bf::mul(x[0], x[1]);
    const auto c = bf::sqr(x[1]);
    const auto e = bf::add(a, bf::mul_by_non_residue(c));
    const auto f = bf::dbl(b);
    return e2(e, f);
  }

  static DEVICE_FORCEINLINE e2 inv(const e2 x) {
    const auto a = x[0];
    const auto b = x[1];
    const auto c = bf::sub(bf::sqr(a), bf::mul_by_non_residue(bf::sqr(b)));
    const auto d = bf::inv(c);
    const auto e = bf::mul(a, d);
    const auto f = bf::neg(bf::mul(b, d));
    return e2(e, f);
  }

  static DEVICE_FORCEINLINE e2 pow(e2 x, const unsigned power) {
    auto result = ONE();
    for (unsigned i = power;;) {
      if (i & 1)
        result = mul(result, x);
      i >>= 1;
      if (!i)
        break;
      x = sqr(x);
    }
    return result;
  }

  DEVICE_FORCEINLINE e2 operator-() const { return neg(*this); }

  template <class T> DEVICE_FORCEINLINE e2 operator+(const T other) const { return add(*this, other); }

  template <class T> DEVICE_FORCEINLINE e2 operator-(const T other) const { return sub(*this, other); }

  template <class T> DEVICE_FORCEINLINE e2 operator*(const T other) const { return mul(*this, other); }

  template <class T> DEVICE_FORCEINLINE e2 &operator+=(const T rhs) {
    *this = add(*this, rhs);
    return *this;
  }

  template <class T> DEVICE_FORCEINLINE e2 &operator-=(const T rhs) {
    *this = sub(*this, rhs);
    return *this;
  }

  template <class T> DEVICE_FORCEINLINE e2 &operator*=(const T rhs) {
    *this = mul(*this, rhs);
    return *this;
  }
};

struct __align__(16) e4 {
  e2 coefficients[2];

  constexpr e4() = default;

  explicit constexpr HOST_DEVICE_FORCEINLINE e4(const bf c[4]) : coefficients{e2(c[0], c[1]), e2(c[2], c[3])} {}

  explicit constexpr HOST_DEVICE_FORCEINLINE e4(const e2 c[2]) : coefficients{c[0], c[1]} {}

  explicit constexpr HOST_DEVICE_FORCEINLINE e4(const e2 c0, const e2 c1) : coefficients{c0, c1} {}

  DEVICE_FORCEINLINE e2 &operator[](const unsigned idx) { return coefficients[idx]; }

  DEVICE_FORCEINLINE const e2 &operator[](const unsigned idx) const { return coefficients[idx]; }

  DEVICE_FORCEINLINE const bf &base_coefficient_from_flat_idx(const unsigned idx) const { return coefficients[(idx & 2) >> 1][idx & 1]; }

  static consteval HOST_DEVICE_FORCEINLINE e4 ZERO() { return e4(e2::ZERO(), e2::ZERO()); }

  static consteval HOST_DEVICE_FORCEINLINE e4 ONE() { return e4(e2::ONE(), e2::ZERO()); }

  static DEVICE_FORCEINLINE e4 add(const e4 x, const bf y) { return e4(e2::add(x[0], y), x[1]); }

  static DEVICE_FORCEINLINE e4 add(const e4 x, const e2 y) { return e4(e2::add(x[0], y), x[1]); }

  static DEVICE_FORCEINLINE e4 add(const bf x, const e4 y) { return e4(e2::add(x, y[0]), y[1]); }

  static DEVICE_FORCEINLINE e4 add(const e2 x, const e4 y) { return e4(e2::add(x, y[0]), y[1]); }

  static DEVICE_FORCEINLINE e4 add(const e4 x, const e4 y) { return e4(e2::add(x[0], y[0]), e2::add(x[1], y[1])); }

  static DEVICE_FORCEINLINE e4 sub(const e4 x, const bf y) { return e4(e2::sub(x[0], y), x[1]); }

  static DEVICE_FORCEINLINE e4 sub(const e4 x, const e2 y) { return e4(e2::sub(x[0], y), x[1]); }

  static DEVICE_FORCEINLINE e4 sub(const bf x, const e4 y) { return e4(e2::sub(x, y[0]), e2::neg(y[1])); }

  static DEVICE_FORCEINLINE e4 sub(const e2 x, const e4 y) { return e4(e2::sub(x, y[0]), e2::neg(y[1])); }

  static DEVICE_FORCEINLINE e4 sub(const e4 x, const e4 y) { return e4(e2::sub(x[0], y[0]), e2::sub(x[1], y[1])); }

  static DEVICE_FORCEINLINE e4 dbl(const e4 x) { return e4(e2::dbl(x[0]), e2::dbl(x[1])); }

  static DEVICE_FORCEINLINE e4 neg(const e4 x) { return e4(e2::neg(x[0]), e2::neg(x[1])); }

  static DEVICE_FORCEINLINE e4 mul(const e4 x, const bf y) { return e4(e2::mul(x[0], y), e2::mul(x[1], y)); }

  static DEVICE_FORCEINLINE e4 mul(const e4 x, const e2 y) { return e4(e2::mul(x[0], y), e2::mul(x[1], y)); }

  static DEVICE_FORCEINLINE e4 mul(const bf x, const e4 y) { return e4(e2::mul(x, y[0]), e2::mul(x, y[1])); }

  static DEVICE_FORCEINLINE e4 mul(const e2 x, const e4 y) { return e4(e2::mul(x, y[0]), e2::mul(x, y[1])); }

  static DEVICE_FORCEINLINE e4 mul(const e4 x, const e4 y) {
    const auto a = e2::add(x[0], x[1]);
    const auto b = e2::add(y[0], y[1]);
    const auto c = e2::mul(x[0], y[0]);
    const auto d = e2::mul(x[1], y[1]);
    const auto e = e2::add(c, e2::mul_by_quadratic_non_residue(d));
    const auto f = e2::sub(e2::mul(a, b), e2::add(c, d));
    return e4(e, f);
  }

  static DEVICE_FORCEINLINE e4 sqr(const e4 x) {
    const auto a = e2::sqr(x[0]);
    const auto b = e2::mul(x[0], x[1]);
    const auto c = e2::sqr(x[1]);
    const auto e = e2::add(a, e2::mul_by_quadratic_non_residue(c));
    const auto f = e2::dbl(b);
    return e4(e, f);
  }

  static DEVICE_FORCEINLINE e4 inv(const e4 x) {
    const auto a = x[0];
    const auto b = x[1];
    const auto c = e2::sub(e2::sqr(a), e2::mul_by_quadratic_non_residue(e2::sqr(b)));
    const auto d = e2::inv(c);
    const auto e = e2::mul(a, d);
    const auto f = e2::neg(e2::mul(b, d));
    return e4(e, f);
  }

  static DEVICE_FORCEINLINE e4 pow(e4 x, const unsigned power) {
    auto result = ONE();
    for (unsigned i = power;;) {
      if (i & 1)
        result = mul(result, x);
      i >>= 1;
      if (!i)
        break;
      x = sqr(x);
    }
    return result;
  }

  DEVICE_FORCEINLINE e4 operator-() const { return neg(*this); }

  template <class T> DEVICE_FORCEINLINE e4 operator+(const T other) const { return add(*this, other); }

  template <class T> DEVICE_FORCEINLINE e4 operator-(const T other) const { return sub(*this, other); }

  template <class T> DEVICE_FORCEINLINE e4 operator*(const T other) const { return mul(*this, other); }

  template <class T> DEVICE_FORCEINLINE e4 &operator+=(const T rhs) {
    *this = add(*this, rhs);
    return *this;
  }

  template <class T> DEVICE_FORCEINLINE e4 &operator-=(const T rhs) {
    *this = sub(*this, rhs);
    return *this;
  }

  template <class T> DEVICE_FORCEINLINE e4 &operator*=(const T rhs) {
    *this = mul(*this, rhs);
    return *this;
  }
};

struct __align__(8) e6 {
  e2 coefficients[3];

  constexpr e6() = default;

  explicit constexpr HOST_DEVICE_FORCEINLINE e6(const bf c[6]) : coefficients{e2(c[0], c[1]), e2(c[2], c[3]), e2(c[4], c[5])} {}

  explicit constexpr HOST_DEVICE_FORCEINLINE e6(const e2 c[3]) : coefficients{c[0], c[1], c[2]} {}

  explicit constexpr HOST_DEVICE_FORCEINLINE e6(const e2 c0, const e2 c1, const e2 c2) : coefficients{c0, c1, c2} {}

  DEVICE_FORCEINLINE e2 &operator[](const unsigned idx) { return coefficients[idx]; }

  DEVICE_FORCEINLINE const e2 &operator[](const unsigned idx) const { return coefficients[idx]; }

  DEVICE_FORCEINLINE const bf &base_coefficient_from_flat_idx(const unsigned idx) const { return coefficients[idx / 3][idx % 3]; }

  static consteval HOST_DEVICE_FORCEINLINE e6 ZERO() { return e6(e2::ZERO(), e2::ZERO(), e2::ZERO()); }

  static consteval HOST_DEVICE_FORCEINLINE e6 ONE() { return e6(e2::ONE(), e2::ZERO(), e2::ZERO()); }

  static DEVICE_FORCEINLINE e6 add(const e6 x, const bf y) { return e6(e2::add(x[0], y), x[1], x[2]); }

  static DEVICE_FORCEINLINE e6 add(const e6 x, const e2 y) { return e6(e2::add(x[0], y), x[1], x[2]); }

  static DEVICE_FORCEINLINE e6 add(const bf x, const e6 y) { return e6(e2::add(x, y[0]), y[1], y[2]); }

  static DEVICE_FORCEINLINE e6 add(const e2 x, const e6 y) { return e6(e2::add(x, y[0]), y[1], y[2]); }

  static DEVICE_FORCEINLINE e6 add(const e6 x, const e6 y) { return e6(e2::add(x[0], y[0]), e2::add(x[1], y[1]), e2::add(x[2], y[2])); }

  static DEVICE_FORCEINLINE e6 sub(const e6 x, const bf y) { return e6(e2::sub(x[0], y), x[1], x[2]); }

  static DEVICE_FORCEINLINE e6 sub(const e6 x, const e2 y) { return e6(e2::sub(x[0], y), x[1], x[2]); }

  static DEVICE_FORCEINLINE e6 sub(const bf x, const e6 y) { return e6(e2::sub(x, y[0]), e2::neg(y[1]), e2::neg(y[2])); }

  static DEVICE_FORCEINLINE e6 sub(const e2 x, const e6 y) { return e6(e2::sub(x, y[0]), e2::neg(y[1]), e2::neg(y[2])); }

  static DEVICE_FORCEINLINE e6 sub(const e6 x, const e6 y) { return e6(e2::sub(x[0], y[0]), e2::sub(x[1], y[1]), e2::sub(x[2], y[2])); }

  static DEVICE_FORCEINLINE e6 dbl(const e6 x) { return e6(e2::dbl(x[0]), e2::dbl(x[1]), e2::dbl(x[2])); }

  static DEVICE_FORCEINLINE e6 neg(const e6 x) { return e6(e2::neg(x[0]), e2::neg(x[1]), e2::neg(x[2])); }

  static DEVICE_FORCEINLINE e6 mul(const e6 x, const bf y) { return e6(e2::mul(x[0], y), e2::mul(x[1], y), e2::mul(x[2], y)); }

  static DEVICE_FORCEINLINE e6 mul(const e6 x, const e2 y) { return e6(e2::mul(x[0], y), e2::mul(x[1], y), e2::mul(x[2], y)); }

  static DEVICE_FORCEINLINE e6 mul(const bf x, const e6 y) { return e6(e2::mul(x, y[0]), e2::mul(x, y[1]), e2::mul(x, y[2])); }

  static DEVICE_FORCEINLINE e6 mul(const e2 x, const e6 y) { return e6(e2::mul(x, y[0]), e2::mul(x, y[1]), e2::mul(x, y[2])); }

  static DEVICE_FORCEINLINE e6 mul(const e6 x, const e6 y) {
    const auto a_a = e2::mul(x[0], y[0]);
    const auto b_b = e2::mul(x[1], y[1]);
    const auto c_c = e2::mul(x[2], y[2]);
    auto t1 = e2::add(y[1], y[2]);
    t1 = e2::mul(t1, e2::add(x[1], x[2]));
    t1 = e2::sub(t1, e2::add(b_b, c_c));
    t1 = e2::add(e2::mul_by_cubic_non_residue(t1), a_a);
    auto t2 = e2::add(y[0], y[1]);
    t2 = e2::mul(t2, e2::add(x[0], x[1]));
    t2 = e2::sub(t2, e2::add(a_a, b_b));
    t2 = e2::add(t2, e2::mul_by_cubic_non_residue(c_c));
    auto t3 = e2::add(y[0], y[2]);
    t3 = e2::mul(t3, e2::add(x[0], x[2]));
    t3 = e2::sub(t3, e2::add(a_a, c_c));
    t3 = e2::add(t3, b_b);
    return e6(t1, t2, t3);
  }

  static DEVICE_FORCEINLINE e6 sqr(const e6 x) {
    const auto s0 = e2::sqr(x[0]);
    const auto ab = e2::mul(x[0], x[1]);
    const auto s1 = e2::dbl(ab);
    const auto s2 = e2::sqr(e2::add(e2::sub(x[0], x[1]), x[2]));
    const auto bc = e2::mul(x[1], x[2]);
    const auto s3 = e2::dbl(bc);
    const auto s4 = e2::sqr(x[2]);
    const auto a = e2::add(e2::mul_by_cubic_non_residue(s3), s0);
    const auto b = e2::add(e2::mul_by_cubic_non_residue(s4), s1);
    const auto c = e2::sub(e2::add(e2::add(s1, s2), s3), e2::add(s0, s4));
    return e6(a, b, c);
  }

  static DEVICE_FORCEINLINE e6 inv(const e6 x) {
    const auto c0 = e2::add(e2::neg(e2::mul(e2::mul_by_cubic_non_residue(x[2]), x[1])), e2::sqr(x[0]));
    const auto c1 = e2::sub(e2::mul_by_cubic_non_residue(e2::sqr(x[2])), e2::mul(x[0], x[1]));
    const auto c2 = e2::sub(e2::sqr(x[1]), e2::mul(x[0], x[2]));
    const auto tmp1 = e2::mul(x[2], c1);
    const auto tmp2 = e2::mul(x[1], c2);
    const auto tmp3 = e2::mul(x[0], c0);
    const auto t = e2::inv(e2::add(e2::mul_by_cubic_non_residue(e2::add(tmp1, tmp2)), tmp3));
    const auto a = e2::mul(c0, t);
    const auto b = e2::mul(c1, t);
    const auto c = e2::mul(c2, t);
    return e6(a, b, c);
  }

  static DEVICE_FORCEINLINE e6 pow(e6 x, const unsigned power) {
    auto result = ONE();
    for (unsigned i = power;;) {
      if (i & 1)
        result = mul(result, x);
      i >>= 1;
      if (!i)
        break;
      x = sqr(x);
    }
    return result;
  }

  DEVICE_FORCEINLINE e6 operator-() const { return neg(*this); }

  template <class T> DEVICE_FORCEINLINE e6 operator+(const T other) const { return add(*this, other); }

  template <class T> DEVICE_FORCEINLINE e6 operator-(const T other) const { return sub(*this, other); }

  template <class T> DEVICE_FORCEINLINE e6 operator*(const T other) const { return mul(*this, other); }

  template <class T> DEVICE_FORCEINLINE e6 &operator+=(const T rhs) {
    *this = add(*this, rhs);
    return *this;
  }

  template <class T> DEVICE_FORCEINLINE e6 &operator-=(const T rhs) {
    *this = sub(*this, rhs);
    return *this;
  }

  template <class T> DEVICE_FORCEINLINE e6 &operator*=(const T rhs) {
    *this = mul(*this, rhs);
    return *this;
  }
};

using namespace memory;

template <ld_modifier LD_MODIFIER = ld_modifier::none> struct bf_vector_getter : vector_getter<bf, LD_MODIFIER> {};

template <st_modifier ST_MODIFIER = st_modifier::none> struct bf_vector_setter : vector_setter<bf, ST_MODIFIER> {};

template <ld_modifier LD_MODIFIER = ld_modifier::none, st_modifier ST_MODIFIER = st_modifier::none>
struct bf_vector_getter_setter : vector_getter_setter<bf, LD_MODIFIER, ST_MODIFIER> {};

template <ld_modifier LD_MODIFIER = ld_modifier::none> struct bf_matrix_getter : matrix_getter<bf, LD_MODIFIER> {
  explicit bf_matrix_getter(size_t stride) : matrix_getter<bf, LD_MODIFIER>(stride) {}
};

template <st_modifier ST_MODIFIER = st_modifier::none> struct bf_matrix_setter : matrix_setter<bf, ST_MODIFIER> {
  explicit bf_matrix_setter(size_t stride) : matrix_setter<bf, ST_MODIFIER>(stride) {}
};

template <ld_modifier LD_MODIFIER = ld_modifier::none, st_modifier ST_MODIFIER = st_modifier::none>
struct bf_matrix_getter_setter : matrix_getter_setter<bf, LD_MODIFIER, ST_MODIFIER> {
  explicit bf_matrix_getter_setter(size_t stride) : matrix_getter_setter<bf, LD_MODIFIER, ST_MODIFIER>(stride) {}
};

template <ld_modifier LD_MODIFIER = ld_modifier::none> struct e2_vector_getter : vector_getter<e2, LD_MODIFIER> {};

template <st_modifier ST_MODIFIER = st_modifier::none> struct e2_vector_setter : vector_setter<e2, ST_MODIFIER> {};

template <ld_modifier LD_MODIFIER = ld_modifier::none, st_modifier ST_MODIFIER = st_modifier::none>
struct e2_vector_getter_setter : vector_getter_setter<e2, LD_MODIFIER, ST_MODIFIER> {};

template <ld_modifier LD_MODIFIER = ld_modifier::none> struct e2_matrix_getter : matrix_getter<e2, LD_MODIFIER> {
  explicit e2_matrix_getter(size_t stride) : matrix_getter<e2, LD_MODIFIER>(stride) {}
};

template <st_modifier ST_MODIFIER = st_modifier::none> struct e2_matrix_setter : matrix_setter<e2, ST_MODIFIER> {
  explicit e2_matrix_setter(size_t stride) : matrix_setter<e2, ST_MODIFIER>(stride) {}
};

template <ld_modifier LD_MODIFIER = ld_modifier::none, st_modifier ST_MODIFIER = st_modifier::none>
struct e2_matrix_getter_setter : matrix_getter_setter<e2, LD_MODIFIER, ST_MODIFIER> {
  explicit e2_matrix_getter_setter(size_t stride) : matrix_getter_setter<e2, LD_MODIFIER, ST_MODIFIER>(stride) {}
};

template <ld_modifier LD_MODIFIER = ld_modifier::none> struct e4_vector_getter : vector_getter<e4, LD_MODIFIER> {};

template <st_modifier ST_MODIFIER = st_modifier::none> struct e4_vector_setter : vector_setter<e4, ST_MODIFIER> {};

template <ld_modifier LD_MODIFIER = ld_modifier::none, st_modifier ST_MODIFIER = st_modifier::none>
struct e4_vector_getter_setter : vector_getter_setter<e4, LD_MODIFIER, ST_MODIFIER> {};

template <ld_modifier LD_MODIFIER = ld_modifier::none> struct e4_matrix_getter : matrix_getter<e4, LD_MODIFIER> {
  explicit e4_matrix_getter(size_t stride) : matrix_getter<e4, LD_MODIFIER>(stride) {}
};

template <st_modifier ST_MODIFIER = st_modifier::none> struct e4_matrix_setter : matrix_setter<e4, ST_MODIFIER> {
  explicit e4_matrix_setter(size_t stride) : matrix_setter<e4, ST_MODIFIER>(stride) {}
};

template <ld_modifier LD_MODIFIER = ld_modifier::none, st_modifier ST_MODIFIER = st_modifier::none>
struct e4_matrix_getter_setter : matrix_getter_setter<e4, LD_MODIFIER, ST_MODIFIER> {
  explicit e4_matrix_getter_setter(size_t stride) : matrix_getter_setter<e4, LD_MODIFIER, ST_MODIFIER>(stride) {}
};

template <ld_modifier LD_MODIFIER = ld_modifier::none> struct e6_vector_getter : vector_getter<e6, LD_MODIFIER> {};

template <st_modifier ST_MODIFIER = st_modifier::none> struct e6_vector_setter : vector_setter<e6, ST_MODIFIER> {};

template <ld_modifier LD_MODIFIER = ld_modifier::none, st_modifier ST_MODIFIER = st_modifier::none>
struct e6_vector_getter_setter : vector_getter_setter<e6, LD_MODIFIER, ST_MODIFIER> {};

template <ld_modifier LD_MODIFIER = ld_modifier::none> struct e6_matrix_getter : matrix_getter<e6, LD_MODIFIER> {
  explicit e6_matrix_getter(size_t stride) : matrix_getter<e6, LD_MODIFIER>(stride) {}
};

template <st_modifier ST_MODIFIER = st_modifier::none> struct e6_matrix_setter : matrix_setter<e6, ST_MODIFIER> {
  explicit e6_matrix_setter(size_t stride) : matrix_setter<e6, ST_MODIFIER>(stride) {}
};

template <ld_modifier LD_MODIFIER = ld_modifier::none, st_modifier ST_MODIFIER = st_modifier::none>
struct e6_matrix_getter_setter : matrix_getter_setter<e6, LD_MODIFIER, ST_MODIFIER> {
  explicit e6_matrix_getter_setter(size_t stride) : matrix_getter_setter<e6, LD_MODIFIER, ST_MODIFIER>(stride) {}
};
} // namespace airbender::field
