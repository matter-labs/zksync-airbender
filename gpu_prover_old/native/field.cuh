#pragma once
#include "common.cuh"
#include "memory.cuh"

// Mersenne31 field arithmetic partially based on
// https://github.com/Plonky3/Plonky3/tree/main/mersenne-31
// https://github.com/ingonyama-zk/papers/blob/main/Mersenne31_polynomial_arithmetic.pdf

namespace airbender::field {

struct base_field {
  static constexpr uint32_t ORDER = (1u << 31) - 1;
  static constexpr uint32_t MINUS_ONE = ORDER - 1;
  uint32_t limb{};
  static consteval HOST_DEVICE_FORCEINLINE base_field zero() { return base_field(0); }
  static consteval HOST_DEVICE_FORCEINLINE base_field one() { return base_field(1); }
  static consteval HOST_DEVICE_FORCEINLINE base_field two() { return base_field(2); }
  static consteval HOST_DEVICE_FORCEINLINE base_field minus_one() { return base_field(MINUS_ONE); }
  constexpr base_field() = default;
  explicit constexpr HOST_DEVICE_FORCEINLINE base_field(const uint32_t limb) : limb(limb) {}

  static constexpr DEVICE_FORCEINLINE uint32_t into_canonical_u32(const base_field value) { return value.limb == ORDER ? 0 : value.limb; }

  static constexpr DEVICE_FORCEINLINE base_field into_canonical(const base_field value) { return base_field(into_canonical_u32(value)); }

  static DEVICE_FORCEINLINE base_field from_u32(const uint32_t value) {
    const uint32_t msb = value >> 31;
    const uint32_t lsb = value & ORDER;
    return add(base_field(msb), base_field(lsb));
  }

  static DEVICE_FORCEINLINE base_field from_u32_max_minus_one(const uint32_t value) {
    const uint32_t msb = value >> 31;
    const uint32_t lsb = value & ORDER;
    return base_field(msb + lsb);
  }

  static DEVICE_FORCEINLINE base_field from_u62_max_minus_one(const uint64_t value) {
    const auto msb = static_cast<uint32_t>(value >> 31);
    const auto lsb = static_cast<uint32_t>(value & ORDER);
    return from_u32_max_minus_one(msb + lsb);
  }

  static DEVICE_FORCEINLINE base_field add(const base_field x, const base_field y) { return from_u32_max_minus_one(x.limb + y.limb); }
  static DEVICE_FORCEINLINE base_field neg(const base_field x) { return base_field(ORDER - x.limb); }
  static DEVICE_FORCEINLINE base_field sub(const base_field x, const base_field y) { return add(x, neg(y)); }

  static DEVICE_FORCEINLINE base_field mul(const base_field x, const base_field y) {
    const uint64_t product = static_cast<uint64_t>(x.limb) * static_cast<uint64_t>(y.limb);
    return from_u62_max_minus_one(product);
  }

  static DEVICE_FORCEINLINE base_field sqr(const base_field x) { return mul(x, x); }
  static DEVICE_FORCEINLINE base_field dbl(const base_field x) { return shl(x, 1); }

  static DEVICE_FORCEINLINE base_field shl(const base_field x, const uint32_t shift) {
    const uint32_t hi = (x.limb << shift) & ORDER;
    const uint32_t lo = x.limb >> (31 - shift);
    return base_field(hi | lo);
  }

  static DEVICE_FORCEINLINE base_field shr(const base_field x, const uint32_t shift) {
    const uint32_t hi = (x.limb << (31 - shift)) & ORDER;
    const uint32_t lo = x.limb >> shift;
    return base_field(hi | lo);
  }

  static DEVICE_FORCEINLINE base_field pow(const base_field x, const uint32_t power) {
    auto result = one();
    base_field value = x;
    for (uint32_t i = power;;) {
      if (i & 1)
        result = mul(result, value);
      i >>= 1;
      if (!i)
        break;
      value = sqr(value);
    }
    return result;
  }

  template <unsigned LOG_P> static DEVICE_FORCEINLINE base_field pow_exp2(const base_field x) {
    base_field result = x;
#pragma unroll
    for (unsigned i = 0; i < LOG_P; ++i)
      result = sqr(result);
    return result;
  }

  static DEVICE_FORCEINLINE base_field inv(const base_field x) {
    // inv(x) = x^(ORDER - 2) = x^0b1111111111111111111111111111101
    const base_field a = mul(pow_exp2<2>(x), x);  // x^0b101
    const base_field b = mul(sqr(a), a);          // x^0b1111
    const base_field c = mul(pow_exp2<4>(b), b);  // x^0b11111111
    const base_field d = pow_exp2<4>(c);          // x^0b111111110000
    const base_field e = mul(d, b);               // x^0b111111111111
    const base_field f = mul(pow_exp2<4>(d), c);  // x^0b1111111111111111
    const base_field g = mul(pow_exp2<12>(f), e); // x^0b1111111111111111111111111111
    const base_field h = mul(pow_exp2<3>(g), a);  // x^0b1111111111111111111111111111101
    return h;
  }

  DEVICE_FORCEINLINE base_field operator-() const { return neg(*this); }
  DEVICE_FORCEINLINE base_field operator+(const base_field rhs) const { return add(*this, rhs); }
  DEVICE_FORCEINLINE base_field operator-(const base_field rhs) const { return sub(*this, rhs); }
  DEVICE_FORCEINLINE base_field operator*(const base_field rhs) const { return mul(*this, rhs); }
  DEVICE_FORCEINLINE base_field &operator+=(const base_field rhs) {
    *this = add(*this, rhs);
    return *this;
  }
  DEVICE_FORCEINLINE base_field &operator-=(const base_field rhs) {
    *this = sub(*this, rhs);
    return *this;
  }
  DEVICE_FORCEINLINE base_field &operator*=(const base_field rhs) {
    *this = mul(*this, rhs);
    return *this;
  }
};

struct __align__(8) ext2_field {
  base_field coefficients[2];
  static consteval HOST_DEVICE_FORCEINLINE base_field non_residue() { return base_field::minus_one(); }
  static consteval HOST_DEVICE_FORCEINLINE ext2_field zero() { return ext2_field(base_field::zero(), base_field::zero()); }
  static consteval HOST_DEVICE_FORCEINLINE ext2_field one() { return ext2_field(base_field::one(), base_field::zero()); }
  constexpr ext2_field() = default;
  explicit constexpr HOST_DEVICE_FORCEINLINE ext2_field(const base_field c[2]) : coefficients{c[0], c[1]} {}
  explicit constexpr HOST_DEVICE_FORCEINLINE ext2_field(const base_field c0, const base_field c1) : coefficients{c0, c1} {}
  DEVICE_FORCEINLINE base_field &operator[](const unsigned idx) { return coefficients[idx]; }
  DEVICE_FORCEINLINE const base_field &operator[](const unsigned idx) const { return coefficients[idx]; }
  DEVICE_FORCEINLINE const base_field &base_coefficient_from_flat_idx(const unsigned idx) const { return coefficients[idx]; }
  static DEVICE_FORCEINLINE base_field mul_by_non_residue(const base_field x) { return base_field::mul(x, non_residue()); }
  static DEVICE_FORCEINLINE ext2_field add(const ext2_field x, const base_field y) { return ext2_field(base_field::add(x[0], y), x[1]); }
  static DEVICE_FORCEINLINE ext2_field add(const base_field x, const ext2_field y) { return ext2_field(base_field::add(x, y[0]), y[1]); }

  static DEVICE_FORCEINLINE ext2_field add(const ext2_field x, const ext2_field y) {
    return ext2_field(base_field::add(x[0], y[0]), base_field::add(x[1], y[1]));
  }

  static DEVICE_FORCEINLINE ext2_field sub(const ext2_field x, const base_field y) { return ext2_field(base_field::sub(x[0], y), x[1]); }
  static DEVICE_FORCEINLINE ext2_field sub(const base_field x, const ext2_field y) { return ext2_field(base_field::sub(x, y[0]), base_field::neg(y[1])); }

  static DEVICE_FORCEINLINE ext2_field sub(const ext2_field x, const ext2_field y) {
    return ext2_field(base_field::sub(x[0], y[0]), base_field::sub(x[1], y[1]));
  }

  static DEVICE_FORCEINLINE ext2_field dbl(const ext2_field x) { return ext2_field(base_field::dbl(x[0]), base_field::dbl(x[1])); }
  static DEVICE_FORCEINLINE ext2_field neg(const ext2_field x) { return ext2_field(base_field::neg(x[0]), base_field::neg(x[1])); }
  static DEVICE_FORCEINLINE ext2_field mul(const ext2_field x, const base_field y) { return ext2_field(base_field::mul(x[0], y), base_field::mul(x[1], y)); }
  static DEVICE_FORCEINLINE ext2_field mul(const base_field x, const ext2_field y) { return ext2_field(base_field::mul(x, y[0]), base_field::mul(x, y[1])); }

  static DEVICE_FORCEINLINE ext2_field mul(const ext2_field x, const ext2_field y) {
    const auto a = base_field::mul(x[0], y[0]);
    const auto b = base_field::mul(x[1], y[0]);
    const auto c = base_field::mul(x[0], y[1]);
    const auto d = base_field::mul(x[1], y[1]);
    const auto e = base_field::add(a, mul_by_non_residue(d));
    const auto f = base_field::add(b, c);
    return ext2_field(e, f);
  }

  static DEVICE_FORCEINLINE ext2_field sqr(const ext2_field x) {
    const auto a = base_field::sqr(x[0]);
    const auto b = base_field::mul(x[0], x[1]);
    const auto c = base_field::sqr(x[1]);
    const auto e = base_field::add(a, mul_by_non_residue(c));
    const auto f = base_field::dbl(b);
    return ext2_field(e, f);
  }

  static DEVICE_FORCEINLINE ext2_field inv(const ext2_field x) {
    const auto a = x[0];
    const auto b = x[1];
    const auto c = base_field::sub(base_field::sqr(a), mul_by_non_residue(base_field::sqr(b)));
    const auto d = base_field::inv(c);
    const auto e = base_field::mul(a, d);
    const auto f = base_field::neg(base_field::mul(b, d));
    return ext2_field(e, f);
  }

  static DEVICE_FORCEINLINE ext2_field pow(const ext2_field x, const unsigned power) {
    auto result = one();
    ext2_field value = x;
    for (uint32_t i = power;;) {
      if (i & 1)
        result = mul(result, value);
      i >>= 1;
      if (!i)
        break;
      value = sqr(value);
    }
    return result;
  }

  static DEVICE_FORCEINLINE ext2_field shr(const ext2_field x, const unsigned shift) {
    return ext2_field(base_field::shr(x[0], shift), base_field::shr(x[1], shift));
  }

  static DEVICE_FORCEINLINE ext2_field shl(const ext2_field x, const unsigned shift) {
    return ext2_field(base_field::shl(x[0], shift), base_field::shl(x[1], shift));
  }

  DEVICE_FORCEINLINE ext2_field operator-() const { return neg(*this); }
  template <class T> DEVICE_FORCEINLINE ext2_field operator+(const T other) const { return add(*this, other); }
  template <class T> DEVICE_FORCEINLINE ext2_field operator-(const T other) const { return sub(*this, other); }
  template <class T> DEVICE_FORCEINLINE ext2_field operator*(const T other) const { return mul(*this, other); }
  template <class T> DEVICE_FORCEINLINE ext2_field &operator+=(const T rhs) {
    *this = add(*this, rhs);
    return *this;
  }
  template <class T> DEVICE_FORCEINLINE ext2_field &operator-=(const T rhs) {
    *this = sub(*this, rhs);
    return *this;
  }
  template <class T> DEVICE_FORCEINLINE ext2_field &operator*=(const T rhs) {
    *this = mul(*this, rhs);
    return *this;
  }
};

struct __align__(16) ext4_field {
  ext2_field coefficients[2];
  static consteval HOST_DEVICE_FORCEINLINE ext2_field non_residue() { return ext2_field(base_field::two(), base_field::one()); }
  static consteval HOST_DEVICE_FORCEINLINE ext4_field zero() { return ext4_field(ext2_field::zero(), ext2_field::zero()); }
  static consteval HOST_DEVICE_FORCEINLINE ext4_field one() { return ext4_field(ext2_field::one(), ext2_field::zero()); }
  constexpr ext4_field() = default;
  explicit constexpr HOST_DEVICE_FORCEINLINE ext4_field(const base_field c[4]) : coefficients{ext2_field(c[0], c[1]), ext2_field(c[2], c[3])} {}
  explicit constexpr HOST_DEVICE_FORCEINLINE ext4_field(const ext2_field c[2]) : coefficients{c[0], c[1]} {}
  explicit constexpr HOST_DEVICE_FORCEINLINE ext4_field(const ext2_field c0, const ext2_field c1) : coefficients{c0, c1} {}
  DEVICE_FORCEINLINE ext2_field &operator[](const unsigned idx) { return coefficients[idx]; }
  DEVICE_FORCEINLINE const ext2_field &operator[](const unsigned idx) const { return coefficients[idx]; }
  DEVICE_FORCEINLINE const base_field &base_coefficient_from_flat_idx(const unsigned idx) const { return coefficients[(idx & 2) >> 1][idx & 1]; }
  static DEVICE_FORCEINLINE ext2_field mul_by_non_residue(const ext2_field x) { return ext2_field::mul(x, non_residue()); }
  static DEVICE_FORCEINLINE ext4_field add(const ext4_field x, const base_field y) { return ext4_field(ext2_field::add(x[0], y), x[1]); }
  static DEVICE_FORCEINLINE ext4_field add(const ext4_field x, const ext2_field y) { return ext4_field(ext2_field::add(x[0], y), x[1]); }
  static DEVICE_FORCEINLINE ext4_field add(const base_field x, const ext4_field y) { return ext4_field(ext2_field::add(x, y[0]), y[1]); }
  static DEVICE_FORCEINLINE ext4_field add(const ext2_field x, const ext4_field y) { return ext4_field(ext2_field::add(x, y[0]), y[1]); }

  static DEVICE_FORCEINLINE ext4_field add(const ext4_field x, const ext4_field y) {
    return ext4_field(ext2_field::add(x[0], y[0]), ext2_field::add(x[1], y[1]));
  }

  static DEVICE_FORCEINLINE ext4_field sub(const ext4_field x, const base_field y) { return ext4_field(ext2_field::sub(x[0], y), x[1]); }
  static DEVICE_FORCEINLINE ext4_field sub(const ext4_field x, const ext2_field y) { return ext4_field(ext2_field::sub(x[0], y), x[1]); }
  static DEVICE_FORCEINLINE ext4_field sub(const base_field x, const ext4_field y) { return ext4_field(ext2_field::sub(x, y[0]), ext2_field::neg(y[1])); }
  static DEVICE_FORCEINLINE ext4_field sub(const ext2_field x, const ext4_field y) { return ext4_field(ext2_field::sub(x, y[0]), ext2_field::neg(y[1])); }

  static DEVICE_FORCEINLINE ext4_field sub(const ext4_field x, const ext4_field y) {
    return ext4_field(ext2_field::sub(x[0], y[0]), ext2_field::sub(x[1], y[1]));
  }

  static DEVICE_FORCEINLINE ext4_field dbl(const ext4_field x) { return ext4_field(ext2_field::dbl(x[0]), ext2_field::dbl(x[1])); }
  static DEVICE_FORCEINLINE ext4_field neg(const ext4_field x) { return ext4_field(ext2_field::neg(x[0]), ext2_field::neg(x[1])); }
  static DEVICE_FORCEINLINE ext4_field mul(const ext4_field x, const base_field y) { return ext4_field(ext2_field::mul(x[0], y), ext2_field::mul(x[1], y)); }
  static DEVICE_FORCEINLINE ext4_field mul(const ext4_field x, const ext2_field y) { return ext4_field(ext2_field::mul(x[0], y), ext2_field::mul(x[1], y)); }
  static DEVICE_FORCEINLINE ext4_field mul(const base_field x, const ext4_field y) { return ext4_field(ext2_field::mul(x, y[0]), ext2_field::mul(x, y[1])); }
  static DEVICE_FORCEINLINE ext4_field mul(const ext2_field x, const ext4_field y) { return ext4_field(ext2_field::mul(x, y[0]), ext2_field::mul(x, y[1])); }

  static DEVICE_FORCEINLINE ext4_field mul(const ext4_field x, const ext4_field y) {
    const auto a = ext2_field::mul(x[0], y[0]);
    const auto b = ext2_field::mul(x[1], y[0]);
    const auto c = ext2_field::mul(x[0], y[1]);
    const auto d = ext2_field::mul(x[1], y[1]);
    const auto e = ext2_field::add(a, mul_by_non_residue(d));
    const auto f = ext2_field::add(b, c);
    return ext4_field(e, f);
  }

  static DEVICE_FORCEINLINE ext4_field sqr(const ext4_field x) {
    const auto a = ext2_field::sqr(x[0]);
    const auto b = ext2_field::mul(x[0], x[1]);
    const auto c = ext2_field::sqr(x[1]);
    const auto e = ext2_field::add(a, mul_by_non_residue(c));
    const auto f = ext2_field::dbl(b);
    return ext4_field(e, f);
  }

  static DEVICE_FORCEINLINE ext4_field inv(const ext4_field x) {
    const auto a = x[0];
    const auto b = x[1];
    const auto c = ext2_field::sub(ext2_field::sqr(a), mul_by_non_residue(ext2_field::sqr(b)));
    const auto d = ext2_field::inv(c);
    const auto e = ext2_field::mul(a, d);
    const auto f = ext2_field::neg(ext2_field::mul(b, d));
    return ext4_field(e, f);
  }

  static DEVICE_FORCEINLINE ext4_field pow(const ext4_field x, const unsigned power) {
    auto result = one();
    ext4_field value = x;
    for (uint32_t i = power;;) {
      if (i & 1)
        result = mul(result, value);
      i >>= 1;
      if (!i)
        break;
      value = sqr(value);
    }
    return result;
  }

  static DEVICE_FORCEINLINE ext4_field shr(const ext4_field x, const unsigned shift) {
    return ext4_field(ext2_field::shr(x[0], shift), ext2_field::shr(x[1], shift));
  }

  static DEVICE_FORCEINLINE ext4_field shl(const ext4_field x, const unsigned shift) {
    return ext4_field(ext2_field::shl(x[0], shift), ext2_field::shl(x[1], shift));
  }

  DEVICE_FORCEINLINE ext4_field operator-() const { return neg(*this); }
  template <class T> DEVICE_FORCEINLINE ext4_field operator+(const T other) const { return add(*this, other); }
  template <class T> DEVICE_FORCEINLINE ext4_field operator-(const T other) const { return sub(*this, other); }
  template <class T> DEVICE_FORCEINLINE ext4_field operator*(const T other) const { return mul(*this, other); }
  template <class T> DEVICE_FORCEINLINE ext4_field &operator+=(const T rhs) {
    *this = add(*this, rhs);
    return *this;
  }
  template <class T> DEVICE_FORCEINLINE ext4_field &operator-=(const T rhs) {
    *this = sub(*this, rhs);
    return *this;
  }
  template <class T> DEVICE_FORCEINLINE ext4_field &operator*=(const T rhs) {
    *this = mul(*this, rhs);
    return *this;
  }
};

using namespace memory;

template <ld_modifier LD_MODIFIER = ld_modifier::none> struct bf_vector_getter : vector_getter<base_field, LD_MODIFIER> {};

template <st_modifier ST_MODIFIER = st_modifier::none> struct bf_vector_setter : vector_setter<base_field, ST_MODIFIER> {};

template <ld_modifier LD_MODIFIER = ld_modifier::none, st_modifier ST_MODIFIER = st_modifier::none>
struct bf_vector_getter_setter : vector_getter_setter<base_field, LD_MODIFIER, ST_MODIFIER> {};

template <ld_modifier LD_MODIFIER = ld_modifier::none> struct bf_matrix_getter : matrix_getter<base_field, LD_MODIFIER> {
  explicit bf_matrix_getter(size_t stride) : matrix_getter<base_field, LD_MODIFIER>(stride) {}
};

template <st_modifier ST_MODIFIER = st_modifier::none> struct bf_matrix_setter : matrix_setter<base_field, ST_MODIFIER> {
  explicit bf_matrix_setter(size_t stride) : matrix_setter<base_field, ST_MODIFIER>(stride) {}
};

template <ld_modifier LD_MODIFIER = ld_modifier::none, st_modifier ST_MODIFIER = st_modifier::none>
struct bf_matrix_getter_setter : matrix_getter_setter<base_field, LD_MODIFIER, ST_MODIFIER> {
  explicit bf_matrix_getter_setter(size_t stride) : matrix_getter_setter<base_field, LD_MODIFIER, ST_MODIFIER>(stride) {}
};

template <ld_modifier LD_MODIFIER = ld_modifier::none> struct e2_vector_getter : vector_getter<ext2_field, LD_MODIFIER> {};

template <st_modifier ST_MODIFIER = st_modifier::none> struct e2_vector_setter : vector_setter<ext2_field, ST_MODIFIER> {};

template <ld_modifier LD_MODIFIER = ld_modifier::none, st_modifier ST_MODIFIER = st_modifier::none>
struct e2_vector_getter_setter : vector_getter_setter<ext2_field, LD_MODIFIER, ST_MODIFIER> {};

template <ld_modifier LD_MODIFIER = ld_modifier::none> struct e2_matrix_getter : matrix_getter<ext2_field, LD_MODIFIER> {
  explicit e2_matrix_getter(size_t stride) : matrix_getter<ext2_field, LD_MODIFIER>(stride) {}
};

template <st_modifier ST_MODIFIER = st_modifier::none> struct e2_matrix_setter : matrix_setter<ext2_field, ST_MODIFIER> {
  explicit e2_matrix_setter(size_t stride) : matrix_setter<ext2_field, ST_MODIFIER>(stride) {}
};

template <ld_modifier LD_MODIFIER = ld_modifier::none, st_modifier ST_MODIFIER = st_modifier::none>
struct e2_matrix_getter_setter : matrix_getter_setter<ext2_field, LD_MODIFIER, ST_MODIFIER> {
  explicit e2_matrix_getter_setter(size_t stride) : matrix_getter_setter<ext2_field, LD_MODIFIER, ST_MODIFIER>(stride) {}
};

template <ld_modifier LD_MODIFIER = ld_modifier::none> struct e4_vector_getter : vector_getter<ext4_field, LD_MODIFIER> {};

template <st_modifier ST_MODIFIER = st_modifier::none> struct e4_vector_setter : vector_setter<ext4_field, ST_MODIFIER> {};

template <ld_modifier LD_MODIFIER = ld_modifier::none, st_modifier ST_MODIFIER = st_modifier::none>
struct e4_vector_getter_setter : vector_getter_setter<ext4_field, LD_MODIFIER, ST_MODIFIER> {};

template <ld_modifier LD_MODIFIER = ld_modifier::none> struct e4_matrix_getter : matrix_getter<ext4_field, LD_MODIFIER> {
  explicit e4_matrix_getter(size_t stride) : matrix_getter<ext4_field, LD_MODIFIER>(stride) {}
};

template <st_modifier ST_MODIFIER = st_modifier::none> struct e4_matrix_setter : matrix_setter<ext4_field, ST_MODIFIER> {
  explicit e4_matrix_setter(size_t stride) : matrix_setter<ext4_field, ST_MODIFIER>(stride) {}
};

template <ld_modifier LD_MODIFIER = ld_modifier::none, st_modifier ST_MODIFIER = st_modifier::none>
struct e4_matrix_getter_setter : matrix_getter_setter<ext4_field, LD_MODIFIER, ST_MODIFIER> {
  explicit e4_matrix_getter_setter(size_t stride) : matrix_getter_setter<ext4_field, LD_MODIFIER, ST_MODIFIER>(stride) {}
};
} // namespace airbender::field
