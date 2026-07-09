#pragma once
#include "../common.cuh"
#include "memory.cuh"
#include "ptx.cuh"

namespace airbender::primitives::field {

using namespace ptx;

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

  static constexpr DEVICE_FORCEINLINE bf from_reduced_raw_repr(const u32 x) { return bf(x); }

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

  // Extended Montgomery reduction for inputs up to ~4*p^2 (< 2^64).
  // Standard red() only handles inputs < p*2^32. This variant tracks the carry
  // from the intermediate m*ORDER + x that can overflow u64 when x >= p*2^32.
  // Output: fully reduced in [0, p).
  static DEVICE_FORCEINLINE bf red_wide(const u64 x) {
    const auto x_u32 = reinterpret_cast<const u32 *>(&x);
    const u32 lo = x_u32[0];
    const u32 hi = x_u32[1];
    const u32 m = mul_lo(lo, MONT_K);
    [[maybe_unused]] const u32 out_lo = mad_lo_cc(m, ORDER, lo);
    const u32 out_mid = madc_hi_cc(m, ORDER, hi);
    const u32 carry = addc(0u, 0u);
    // When carry=1 the true quotient is out_mid + 2^32.
    // 2^32 mod p = MONT_R, and out_mid < p in this case, so out_mid + MONT_R < 2p.
    // When carry=0 the result can be up to ~2.87p, needing two conditional subtracts.
    u32 r = carry ? (out_mid + MONT_R) : out_mid;
    if (r >= ORDER)
      r -= ORDER;
    if (r >= ORDER)
      r -= ORDER;
    return bf(r);
  }

  static DEVICE_FORCEINLINE bf mul_u32(const u32 x, const u32 y) { return red(mul_wide(x, y)); }

  static DEVICE_FORCEINLINE bf mul(const bf x, const bf y) { return mul_u32(x.limb, y.limb); }

  // Multiply by the non-residue (11) using Solinas reduction instead of full Montgomery mul.
  // Since 11 is small and p = 2^31 - 2^27 + 1, we compute 11*x.limb mod p directly:
  //   t = 11 * x.limb          (< 11*p < 2^35, fits in u64)
  //   t mod p via: 2^31 ≡ 2^27 - 1 (mod p)
  // Cost: 1 mul-pipe op + ALU, vs 4 mul-pipe ops for a full Montgomery mul.
  static DEVICE_FORCEINLINE bf mul_by_non_residue(const bf x) {
    const u64 t = static_cast<u64>(x.limb) * 11u;
    const u32 lo = static_cast<u32>(t) & 0x7FFFFFFFu; // lower 31 bits
    const u32 hi = static_cast<u32>(t >> 31);         // upper bits (≤ 10)
    const u32 corr = (hi << 27) - hi;                 // hi * (2^27 - 1)
    return from_lt_2_order_u32(lo + corr);
  }

  static DEVICE_FORCEINLINE bf into_mont(const bf x) { return mul_u32(x.limb, MONT_R2); }

  static DEVICE_FORCEINLINE bf from_mont(const bf x) { return mul_u32(x.limb, 1); }

  static DEVICE_FORCEINLINE bf from_u32_unchecked(const u32 x) { return bf::into_mont(bf(x)); }

  static DEVICE_FORCEINLINE u32 into_canonical_u32(const bf x) { return bf::from_mont(x).limb; }

  // Mirrors host `BabyBearField::from_u32_with_reduction`: reduce an arbitrary u32 to [0, ORDER)
  // via at most two conditional subtractions, then Montgomery-convert (multiply by MONT_R2).
  static DEVICE_FORCEINLINE bf from_u32_with_reduction(const u32 x) {
    u32 r = x;
    if (r >= ORDER)
      r -= ORDER;
    if (r >= ORDER)
      r -= ORDER;
    return bf::into_mont(bf(r));
  }

  // Mirrors host `BabyBearField::from_raw_repr_with_reduction`: reduce an arbitrary u32 to
  // [0, ORDER) via at most two conditional subtractions, then store raw — i.e. treat the
  // reduced u32 as already being in Montgomery form. This is the transcript-squeeze conversion
  // used to derive E4 challenges from raw Blake2s output words.
  static constexpr DEVICE_FORCEINLINE bf from_raw_repr_with_reduction(const u32 x) {
    u32 r = x;
    if (r >= ORDER)
      r -= ORDER;
    if (r >= ORDER)
      r -= ORDER;
    return bf(r);
  }

  static constexpr DEVICE_FORCEINLINE bf neg(const bf x) { return bf(x.limb == 0 ? 0 : ORDER - x.limb); }

  static constexpr DEVICE_FORCEINLINE bf sub(const bf x, const bf y) { return from_lt_2_order_u32(ORDER + x.limb - y.limb); }

  static DEVICE_FORCEINLINE bf sqr(const bf x) { return mul(x, x); }

  // Fused multiply-add: a*b + c.
  // In Montgomery form, the wide product a.limb*b.limb has an R² factor while c.limb has R.
  // To get (a*b + c)*R after reduction, we add c.limb to the HIGH word of the wide product
  // (equivalent to adding c * 2^32 = c * R). Then red_wide gives the correct result.
  // Overflow: hi(a*b) + c.limb < p + p = 2p < 2^32 (no u32 overflow in high word).
  // Total value < p² + p·2³² < 2⁶⁴, and red_wide handles any u64 input.
  static DEVICE_FORCEINLINE bf fma(const bf a, const bf b, const bf c) {
    u64 w = mul_wide(a.limb, b.limb);
    reinterpret_cast<u32 *>(&w)[1] += c.limb;
    return red_wide(w);
  }

  // Fused multiply-subtract: a*b - c. Same principle but adds ORDER - c.limb to the high word.
  static DEVICE_FORCEINLINE bf fms(const bf a, const bf b, const bf c) {
    u64 w = mul_wide(a.limb, b.limb);
    reinterpret_cast<u32 *>(&w)[1] += ORDER - c.limb;
    return red_wide(w);
  }

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

    // Fermat's little theorem: a^(p-2) = a^(-1) (mod p)
    // Exponent: p - 2 = 0x77ffffff = 0b0111_0111_111111_111111_111111_111111
    //
    // Addition chain (29 sqr + 8 mul = 37 ops):
    //   Build x^7, x^56 (intermediate), x^63, x^119 = x^63 * x^56.
    //   Then 4× [sqr^6, mul x^63] appends 24 one-bits via a 6-bit window.
    const bf x2 = sqr(x);
    const bf x3 = mul(x2, x);
    const bf x7 = mul(sqr(x3), x);      // x^6 * x
    const bf x56 = pow_log2_exp<3>(x7); // x^7 << 3
    const bf x63 = mul(x56, x7);        // x^56 + x^7 = x^63 = 0b111111
    bf result = mul(x63, x56);          // x^63 + x^56 = x^119 = 0b01110111

#pragma unroll
    for (int i = 0; i < 4; ++i) {
      result = mul(pow_log2_exp<6>(result), x63); // shift 6, fill with 111111
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

  static constexpr DEVICE_FORCEINLINE e2 from_scalar(const bf x) { return e2(x, bf::ZERO()); }

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

  // Schoolbook multiplication with lazy reduction.
  // Accumulates 2 products per output coefficient in u64, reduces once.
  //   out[0] = x0·y0 + 11·x1·y1
  //   out[1] = x0·y1 + x1·y0
  // Overflow safety: 2·p² ≈ 8.11e18 < p·2³² ≈ 8.65e18. Standard red() handles this.
  static DEVICE_FORCEINLINE e2 mul(const e2 x, const e2 y) {
    const u32 x1n = bf::mul_by_non_residue(x[1]).limb;
    const u64 acc0 = mad_wide(x1n, y[1].limb, mul_wide(x[0].limb, y[0].limb));
    const u64 acc1 = mad_wide(x[1].limb, y[0].limb, mul_wide(x[0].limb, y[1].limb));
    return e2(bf::red(acc0), bf::red(acc1));
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

  // Squaring with lazy reduction.
  //   out[0] = x0² + 11·x1²
  //   out[1] = 2·x0·x1
  static DEVICE_FORCEINLINE e2 sqr(const e2 x) {
    const u32 x1n = bf::mul_by_non_residue(x[1]).limb;
    const u64 acc0 = mad_wide(x1n, x[1].limb, mul_wide(x[0].limb, x[0].limb));
    const u64 acc1 = mad_wide(x[0].limb, x[1].limb, mul_wide(x[0].limb, x[1].limb));
    return e2(bf::red(acc0), bf::red(acc1));
  }

  // Fused multiply-add: a*b + c. Adds c to the HIGH word of each 2-product accumulator
  // (c * 2^32 = c * R), then reduces with red_wide. This corrects the R-factor mismatch
  // between the R² wide product and the R-form addend.
  // Overflow: 2·p² + p·2³² ≈ 1.68e19 < 2⁶⁴. red_wide handles any u64 input.
  static DEVICE_FORCEINLINE e2 fma(const e2 a, const e2 b, const e2 c) {
    const u32 a1n = bf::mul_by_non_residue(a[1]).limb;
    u64 acc0 = mad_wide(a1n, b[1].limb, mul_wide(a[0].limb, b[0].limb));
    u64 acc1 = mad_wide(a[1].limb, b[0].limb, mul_wide(a[0].limb, b[1].limb));
    reinterpret_cast<u32 *>(&acc0)[1] += c[0].limb;
    reinterpret_cast<u32 *>(&acc1)[1] += c[1].limb;
    return e2(bf::red_wide(acc0), bf::red_wide(acc1));
  }

  // Fused multiply-subtract: a*b - c. Adds (ORDER - cᵢ) to the high word.
  static DEVICE_FORCEINLINE e2 fms(const e2 a, const e2 b, const e2 c) {
    const u32 a1n = bf::mul_by_non_residue(a[1]).limb;
    u64 acc0 = mad_wide(a1n, b[1].limb, mul_wide(a[0].limb, b[0].limb));
    u64 acc1 = mad_wide(a[1].limb, b[0].limb, mul_wide(a[0].limb, b[1].limb));
    reinterpret_cast<u32 *>(&acc0)[1] += bf::ORDER - c[0].limb;
    reinterpret_cast<u32 *>(&acc1)[1] += bf::ORDER - c[1].limb;
    return e2(bf::red_wide(acc0), bf::red_wide(acc1));
  }

  // Fused scalar multiply-add: x*s + z where s is a base field scalar.
  static DEVICE_FORCEINLINE e2 fma(const e2 x, const bf s, const e2 z) { return e2(bf::fma(x[0], s, z[0]), bf::fma(x[1], s, z[1])); }

  static DEVICE_FORCEINLINE e2 fma(const bf s, const e2 x, const e2 z) { return fma(x, s, z); }

  // Mixed: x*s + z_bf where z_bf is a base field element (added only to coefficient 0).
  static DEVICE_FORCEINLINE e2 fma(const e2 x, const bf s, const bf z) { return e2(bf::fma(x[0], s, z), bf::mul(x[1], s)); }

  static DEVICE_FORCEINLINE e2 fma(const bf s, const e2 x, const bf z) { return fma(x, s, z); }

  // Fused scalar multiply-subtract: x*s - z where s is a base field scalar.
  static DEVICE_FORCEINLINE e2 fms(const e2 x, const bf s, const e2 z) { return e2(bf::fms(x[0], s, z[0]), bf::fms(x[1], s, z[1])); }

  static DEVICE_FORCEINLINE e2 fms(const bf s, const e2 x, const e2 z) { return fms(x, s, z); }

  // Mixed: x*s - z_bf where z_bf is a base field element (subtracted only from coefficient 0).
  static DEVICE_FORCEINLINE e2 fms(const e2 x, const bf s, const bf z) { return e2(bf::fms(x[0], s, z), bf::mul(x[1], s)); }

  static DEVICE_FORCEINLINE e2 fms(const bf s, const e2 x, const bf z) { return fms(x, s, z); }

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

  static constexpr DEVICE_FORCEINLINE e4 from_scalar(const bf x) { return e4(e2(x, bf::ZERO()), e2::ZERO()); }

  static constexpr DEVICE_FORCEINLINE e4 from_scalar(const e2 x) { return e4(x, e2::ZERO()); }

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

  // Flat quartic multiplication with lazy reduction.
  // Operates directly on 4 bf limbs instead of tower Karatsuba over e2.
  // Accumulates 4 products per output coefficient in u64, reduces once.
  //
  // For e4 = bf[α,β,αβ] with α²=11, β²=α, the multiplication table gives:
  //   out[0] = a₀b₀ + 11·a₁b₁ + 11·a₂b₃ + 11·a₃b₂
  //   out[1] = a₀b₁ + a₁b₀  +    a₂b₂  + 11·a₃b₃
  //   out[2] = a₀b₂ + 11·a₁b₃ +  a₂b₀  + 11·a₃b₁
  //   out[3] = a₀b₃ + a₁b₂  +    a₂b₁  +    a₃b₀
  //
  // Overflow safety: 4·p² ≈ 1.62e19 < 2⁶⁴ ≈ 1.84e19.
  static DEVICE_FORCEINLINE e4 mul(const e4 x, const e4 y) {
    const u32 a0 = x[0][0].limb, a1 = x[0][1].limb, a2 = x[1][0].limb, a3 = x[1][1].limb;
    const u32 b0 = y[0][0].limb, b1 = y[0][1].limb, b2 = y[1][0].limb, b3 = y[1][1].limb;

    // Precompute aᵢ·11 via Solinas reduction (1 mul-pipe op each)
    const u32 a1n = bf::mul_by_non_residue(bf(a1)).limb;
    const u32 a2n = bf::mul_by_non_residue(bf(a2)).limb;
    const u32 a3n = bf::mul_by_non_residue(bf(a3)).limb;

    u64 acc;

    acc = mul_wide(a0, b0);
    acc = mad_wide(a1n, b1, acc);
    acc = mad_wide(a2n, b3, acc);
    acc = mad_wide(a3n, b2, acc);
    const bf o0 = bf::red_wide(acc);

    acc = mul_wide(a0, b1);
    acc = mad_wide(a1, b0, acc);
    acc = mad_wide(a2, b2, acc);
    acc = mad_wide(a3n, b3, acc);
    const bf o1 = bf::red_wide(acc);

    acc = mul_wide(a0, b2);
    acc = mad_wide(a1n, b3, acc);
    acc = mad_wide(a2, b0, acc);
    acc = mad_wide(a3n, b1, acc);
    const bf o2 = bf::red_wide(acc);

    acc = mul_wide(a0, b3);
    acc = mad_wide(a1, b2, acc);
    acc = mad_wide(a2, b1, acc);
    acc = mad_wide(a3, b0, acc);
    const bf o3 = bf::red_wide(acc);

    return e4(e2(o0, o1), e2(o2, o3));
  }

  // Flat quartic squaring with lazy reduction.
  // Exploits aᵢ=bᵢ symmetry: cross-products appear doubled.
  //   out[0] = a₀² + 11·a₁² + 2·11·a₂a₃
  //   out[1] = 2·a₀a₁ + a₂² + 11·a₃²
  //   out[2] = 2·a₀a₂ + 2·11·a₁a₃
  //   out[3] = 2·(a₀a₃ + a₁a₂)
  static DEVICE_FORCEINLINE e4 sqr(const e4 x) {
    const u32 a0 = x[0][0].limb, a1 = x[0][1].limb, a2 = x[1][0].limb, a3 = x[1][1].limb;

    const u32 a1n = bf::mul_by_non_residue(bf(a1)).limb;
    const u32 a3n = bf::mul_by_non_residue(bf(a3)).limb;

    u64 acc;

    // out[0] = a0² + 11·a1² + 2·11·a2·a3
    // Rewrite as: a0·a0 + a1n·a1 + a2n·a3 + a3n·a2 (same as mul with a=b, but we can also
    // factor the doubled cross-product: a0·a0 + a1n·a1 + 2·a3n·a2)
    // Using 2·a3n·a2 = a3n·a2 + a3n·a2 via double accumulation:
    acc = mul_wide(a0, a0);
    acc = mad_wide(a1n, a1, acc);
    acc = mad_wide(a3n, a2, acc);
    acc = mad_wide(a3n, a2, acc); // doubled cross-product
    const bf o0 = bf::red_wide(acc);

    // out[1] = 2·a0·a1 + a2² + 11·a3²
    acc = mul_wide(a0, a1);
    acc = mad_wide(a0, a1, acc); // doubled
    acc = mad_wide(a2, a2, acc);
    acc = mad_wide(a3n, a3, acc);
    const bf o1 = bf::red_wide(acc);

    // out[2] = 2·a0·a2 + 2·11·a1·a3
    acc = mul_wide(a0, a2);
    acc = mad_wide(a0, a2, acc); // doubled
    acc = mad_wide(a1n, a3, acc);
    acc = mad_wide(a1n, a3, acc); // doubled
    const bf o2 = bf::red_wide(acc);

    // out[3] = 2·(a0·a3 + a1·a2)
    acc = mul_wide(a0, a3);
    acc = mad_wide(a1, a2, acc);
    acc = mad_wide(a0, a3, acc); // doubled
    acc = mad_wide(a1, a2, acc); // doubled
    const bf o3 = bf::red_wide(acc);

    return e4(e2(o0, o1), e2(o2, o3));
  }

  // Fused multiply-add: x*y + z.
  // Cannot fuse into the flat quartic accumulator (4·p² + p·2³² > 2⁶⁴ would overflow).
  static DEVICE_FORCEINLINE e4 fma(const e4 x, const e4 y, const e4 z) { return add(mul(x, y), z); }

  // Fused multiply-subtract: x*y - z.
  static DEVICE_FORCEINLINE e4 fms(const e4 x, const e4 y, const e4 z) { return sub(mul(x, y), z); }

  // Fused scalar multiply-add: x*s + z where s is a base field scalar.
  // Each output coefficient: xᵢ·s + zᵢ. Uses bf::fma (1 product, fusible).
  static DEVICE_FORCEINLINE e4 fma(const e4 x, const bf s, const e4 z) {
    return e4(e2(bf::fma(x[0][0], s, z[0][0]), bf::fma(x[0][1], s, z[0][1])), e2(bf::fma(x[1][0], s, z[1][0]), bf::fma(x[1][1], s, z[1][1])));
  }

  // Swapped: s*x + z (commutative in first two args).
  static DEVICE_FORCEINLINE e4 fma(const bf s, const e4 x, const e4 z) { return fma(x, s, z); }

  // Mixed: x*s + z_bf where z_bf is a base field element (added only to coefficient 0).
  static DEVICE_FORCEINLINE e4 fma(const e4 x, const bf s, const bf z) {
    return e4(e2(bf::fma(x[0][0], s, z), bf::mul(x[0][1], s)), e2(bf::mul(x[1][0], s), bf::mul(x[1][1], s)));
  }

  // Swapped: s*x + z_bf.
  static DEVICE_FORCEINLINE e4 fma(const bf s, const e4 x, const bf z) { return fma(x, s, z); }

  // Fused scalar multiply-subtract: x*s - z where s is a base field scalar.
  static DEVICE_FORCEINLINE e4 fms(const e4 x, const bf s, const e4 z) {
    return e4(e2(bf::fms(x[0][0], s, z[0][0]), bf::fms(x[0][1], s, z[0][1])), e2(bf::fms(x[1][0], s, z[1][0]), bf::fms(x[1][1], s, z[1][1])));
  }

  // Swapped: s*x - z.
  static DEVICE_FORCEINLINE e4 fms(const bf s, const e4 x, const e4 z) { return fms(x, s, z); }

  // Mixed: x*s - z_bf where z_bf is a base field element (subtracted only from coefficient [0][0]).
  static DEVICE_FORCEINLINE e4 fms(const e4 x, const bf s, const bf z) {
    return e4(e2(bf::fms(x[0][0], s, z), bf::mul(x[0][1], s)), e2(bf::mul(x[1][0], s), bf::mul(x[1][1], s)));
  }

  // Swapped: s*x - z_bf.
  static DEVICE_FORCEINLINE e4 fms(const bf s, const e4 x, const bf z) { return fms(x, s, z); }

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

  static constexpr DEVICE_FORCEINLINE e6 from_scalar(const bf x) { return e6(e2(x, bf::ZERO()), e2::ZERO(), e2::ZERO()); }

  static constexpr DEVICE_FORCEINLINE e6 from_scalar(const e2 x) { return e6(x, e2::ZERO(), e2::ZERO()); }

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

  // Fused multiply-add: x*y + z. Not fused internally (Karatsuba e6*e6 can't absorb addend).
  static DEVICE_FORCEINLINE e6 fma(const e6 x, const e6 y, const e6 z) { return add(mul(x, y), z); }

  // Fused multiply-subtract: x*y - z.
  static DEVICE_FORCEINLINE e6 fms(const e6 x, const e6 y, const e6 z) { return sub(mul(x, y), z); }

  // Fused scalar multiply-add: x*s + z where s is a base field scalar.
  static DEVICE_FORCEINLINE e6 fma(const e6 x, const bf s, const e6 z) { return e6(e2::fma(x[0], s, z[0]), e2::fma(x[1], s, z[1]), e2::fma(x[2], s, z[2])); }

  static DEVICE_FORCEINLINE e6 fma(const bf s, const e6 x, const e6 z) { return fma(x, s, z); }

  // Fused scalar multiply-subtract: x*s - z where s is a base field scalar.
  static DEVICE_FORCEINLINE e6 fms(const e6 x, const bf s, const e6 z) { return e6(e2::fms(x[0], s, z[0]), e2::fms(x[1], s, z[1]), e2::fms(x[2], s, z[2])); }

  static DEVICE_FORCEINLINE e6 fms(const bf s, const e6 x, const e6 z) { return fms(x, s, z); }

  // Fused e2-scalar multiply-add: x*s + z where s is an e2 scalar.
  static DEVICE_FORCEINLINE e6 fma(const e6 x, const e2 s, const e6 z) { return e6(e2::fma(x[0], s, z[0]), e2::fma(x[1], s, z[1]), e2::fma(x[2], s, z[2])); }

  static DEVICE_FORCEINLINE e6 fma(const e2 s, const e6 x, const e6 z) { return fma(x, s, z); }

  // Fused e2-scalar multiply-subtract: x*s - z where s is an e2 scalar.
  static DEVICE_FORCEINLINE e6 fms(const e6 x, const e2 s, const e6 z) { return e6(e2::fms(x[0], s, z[0]), e2::fms(x[1], s, z[1]), e2::fms(x[2], s, z[2])); }

  static DEVICE_FORCEINLINE e6 fms(const e2 s, const e6 x, const e6 z) { return fms(x, s, z); }

  // Mixed: x*s + z_bf where z_bf is a base field element (added only to coefficient [0]).
  static DEVICE_FORCEINLINE e6 fma(const e6 x, const bf s, const bf z) { return e6(e2::fma(x[0], s, z), e2::mul(x[1], s), e2::mul(x[2], s)); }

  static DEVICE_FORCEINLINE e6 fma(const bf s, const e6 x, const bf z) { return fma(x, s, z); }

  // Mixed: x*s - z_bf.
  static DEVICE_FORCEINLINE e6 fms(const e6 x, const bf s, const bf z) { return e6(e2::fms(x[0], s, z), e2::mul(x[1], s), e2::mul(x[2], s)); }

  static DEVICE_FORCEINLINE e6 fms(const bf s, const e6 x, const bf z) { return fms(x, s, z); }

  // Mixed: x*s + z_e2 where z_e2 is an e2 element (added only to coefficient [0]).
  static DEVICE_FORCEINLINE e6 fma(const e6 x, const e2 s, const e2 z) { return e6(e2::fma(x[0], s, z), e2::mul(x[1], s), e2::mul(x[2], s)); }

  static DEVICE_FORCEINLINE e6 fma(const e2 s, const e6 x, const e2 z) { return fma(x, s, z); }

  // Mixed: x*s - z_e2.
  static DEVICE_FORCEINLINE e6 fms(const e6 x, const e2 s, const e2 z) { return e6(e2::fms(x[0], s, z), e2::mul(x[1], s), e2::mul(x[2], s)); }

  static DEVICE_FORCEINLINE e6 fms(const e2 s, const e6 x, const e2 z) { return fms(x, s, z); }

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
} // namespace airbender::primitives::field
