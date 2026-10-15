#pragma once

#include <common.cuh>
#include "large_field_utils/carry_chain.cuh"
#include "large_field_utils/ff_config.cuh"

namespace airbender::primitives::field {

// For simplicity, and to imitate babybear, these classes are hardcoded to implement proth120.
// They aren't meant as templates that can be instantiated for other fields with arbitrary limb count.

#define LIMBS_ALIGNMENT(x) ((x) % 4 == 0 ? 16 : ((x) % 2 == 0 ? 8 : 4))
static constexpr u32 LIMBS_COUNT = 4;
static constexpr u32 ALIGN_WIDTH = LIMBS_ALIGNMENT(LIMBS_COUNT);
#define ALIGN __align__(ALIGN_WIDTH)

struct ALIGN storage {
  u32 raw[LIMBS_COUNT];
};

struct ALIGN storage_wide {
  u32 raw[2 * LIMBS_COUNT];
};

// "wide" (2 * limbs count) storage.
// Minimal helper, not a full-fledged distinct field class.
// Declared separately from the pr class because a caller might want to make standalone instances,
// e.g. as temporaries during a chain of wide operations without montgomery reductions.
struct ALIGN proth120_wide {
  static_assert(LIMBS_COUNT ^ 1);
  static constexpr u32 LC = LIMBS_COUNT;
  static constexpr u32 LC2 = LIMBS_COUNT * 2;
  storage_wide limbs;

  void __device__ __forceinline__ set_lo(const storage &in) {
#pragma unroll
    for (u32 i = 0; i < LC; i++)
      limbs.raw[i] = in.raw[i];
  }

  void __device__ __forceinline__ set_hi(const storage &in) {
#pragma unroll
    for (u32 i = 0; i < LC; i++)
      limbs.raw[i + LC] = in.raw[i];
  }

  __device__ __forceinline__ storage get_lo() {
    storage out{};
#pragma unroll
    for (u32 i = 0; i < LC; i++)
      out.raw[i] = limbs.raw[i];
    return out;
  }

  __device__ __forceinline__ storage get_hi() {
    storage out{};
#pragma unroll
    for (u32 i = 0; i < LC; i++)
      out.raw[i] = limbs.raw[i + LC];
    return out;
  }
};

// proth120 implementation. Since it's a base field, it imitates babybear bf, and contains all the "meat":
//  - public interface
//  - data (limbs)
//  - internal helper functions
//  - useful constants stored as primitive types
// The only difference is we instantiate it with an externally defined MONT_K constant.
template <const u32 &MONT_K> struct ALIGN proth120 {
  static constexpr u32 LC = LIMBS_COUNT;
  storage limbs;

  // field structure size = 8 * 32 bit
  static constexpr u32 limbs_count = 4;
  static constexpr storage zero = {0u, 0u, 0u, 0u};
  // modulus = 7 * 2^120 + 1 = 9304595970494411110326649421962412033
  static constexpr storage modulus = {0x00000001, 0x00000000, 0x00000000, 0x07000000};
  // modulus * 2
  static constexpr storage modulus_2 = {0x00000002, 0x00000000, 0x00000000, 0x0e000000};
  // modulus * 4
  static constexpr storage modulus_4 = {0x00000004, 0x00000000, 0x00000000, 0x1c000000};
  // modulus^2
  static constexpr storage_wide modulus_squared = {0x00000001, 0x00000000, 0x00000000, 0x0e000000,
                                                   0x00000000, 0x00000000, 0x00000000, 0x00310000};
  // 2 * modulus^2
  static constexpr storage_wide modulus_squared_2 = {0x00000002, 0x00000000, 0x00000000, 0x1c000000,
                                                     0x00000000, 0x00000000, 0x00000000, 0x00620000};
  // 4 * modulus^2
  static constexpr storage_wide modulus_squared_4 = {0x00000004, 0x00000000, 0x00000000, 0x38000000,
                                                     0x00000000, 0x00000000, 0x00000000, 0x00c40000};
  // Montgomery constant r2 = (2^128)^2 % modulus. Used to convert to montgomery form: a_mont = redc(a_raw, r2)
  static constexpr storage r2 = {0x6db6e0a8, 0xdb6db6db, 0xb6db6db6, 0x05b6db6d};
  // 1 in montgomery form: 2^128 % modulus
  static constexpr storage one = {0xffffffdc, 0xffffffff, 0xffffffff, 0x03ffffff};

  static constexpr u32 modulus_bits_count = 123;

  constexpr proth120() = default;

  explicit constexpr HOST_DEVICE_FORCEINLINE proth120(storage limbs) : limbs{limbs} {}

  // return modulus
  template <u32 MULTIPLIER = 1> static consteval DEVICE_FORCEINLINE proth120 MODULUS() {
    switch (MULTIPLIER) {
    case 1:
      return proth120{modulus};
    case 2:
      return proth120{modulus_2};
    case 4:
      return proth120{modulus_4};
    default:
      return {};
    }
  }

  // return modulus^2, helpful for ab +/- cd
  template <u32 MULTIPLIER = 1> static consteval DEVICE_FORCEINLINE proth120_wide MODULUS_SQUARED() {
    switch (MULTIPLIER) {
    case 1:
      return proth120_wide{modulus_squared};
    case 2:
      return proth120_wide{modulus_squared_2};
    case 4:
      return proth120_wide{modulus_squared_4};
    default:
      return {};
    }
  }

  // return r^2
  static consteval DEVICE_FORCEINLINE proth120 R2() { return proth120(r2); }

  // return one in montgomery form
  static constexpr DEVICE_FORCEINLINE proth120 ONE() { return proth120(one); }

  // add or subtract limbs
  template <bool SUBTRACT, bool CARRY_OUT> static constexpr DEVICE_FORCEINLINE u32 add_sub_limbs(const proth120 &xs, const proth120 &ys, proth120 &rs) {
    const u32 *x = xs.limbs.raw;
    const u32 *y = ys.limbs.raw;
    u32 *r = rs.limbs.raw;
    carry_chain<CARRY_OUT ? LC + 1 : LC> chain;
#pragma unroll
    for (u32 i = 0; i < LC; i++)
      r[i] = SUBTRACT ? chain.sub(x[i], y[i]) : chain.add(x[i], y[i]);
    if (!CARRY_OUT)
      return 0;
    return SUBTRACT ? chain.sub(0, 0) : chain.add(0, 0);
  }

  // If we want, we could make "2*LC" a template parameter to deduplicate with "pr" overload, but that's a minor issue.
  template <bool SUBTRACT, bool CARRY_OUT>
  static constexpr DEVICE_FORCEINLINE u32 add_sub_limbs(const proth120_wide &xs, const proth120_wide &ys, proth120_wide &rs) {
    const u32 *x = xs.limbs.raw;
    const u32 *y = ys.limbs.raw;
    u32 *r = rs.limbs.raw;
    carry_chain<CARRY_OUT ? 2 * LC + 1 : 2 * LC> chain;
#pragma unroll
    for (u32 i = 0; i < 2 * LC; i++) {
      r[i] = SUBTRACT ? chain.sub(x[i], y[i]) : chain.add(x[i], y[i]);
    }
    if (!CARRY_OUT)
      return 0;
    return SUBTRACT ? chain.sub(0, 0) : chain.add(0, 0);
  }

  template <bool CARRY_OUT, typename T> static constexpr DEVICE_FORCEINLINE u32 add_limbs(const T &xs, const T &ys, T &rs) {
    return add_sub_limbs<false, CARRY_OUT>(xs, ys, rs);
  }

  template <bool CARRY_OUT, typename T> static constexpr DEVICE_FORCEINLINE u32 sub_limbs(const T &xs, const T &ys, T &rs) {
    return add_sub_limbs<true, CARRY_OUT>(xs, ys, rs);
  }

  // return xs == 0 with field operands
  static constexpr DEVICE_FORCEINLINE bool is_zero(const proth120 &xs) {
    const u32 *x = xs.limbs.raw;
    u32 limbs_or = x[0];
#pragma unroll
    for (u32 i = 1; i < LC; i++)
      limbs_or |= x[i];
    return limbs_or == 0;
  }

  // return xs == ys with field operands
  static constexpr DEVICE_FORCEINLINE bool eq(const proth120 &xs, const proth120 &ys) {
    const u32 *x = xs.limbs.raw;
    const u32 *y = ys.limbs.raw;
    u32 limbs_or = x[0] ^ y[0];
#pragma unroll
    for (u32 i = 1; i < LC; i++)
      limbs_or |= x[i] ^ y[i];
    return limbs_or == 0;
  }

  template <u32 REDUCTION_SIZE = 1> static constexpr DEVICE_FORCEINLINE proth120 reduce(const proth120 &xs) {
    if (REDUCTION_SIZE == 0)
      return xs;
    constexpr proth120 modulus = MODULUS<REDUCTION_SIZE>();
    proth120 rs = {};
    return sub_limbs<true>(xs, modulus, rs) ? xs : rs;
  }

  template <u32 REDUCTION_SIZE = 1> static constexpr DEVICE_FORCEINLINE proth120_wide reduce_wide(const proth120_wide &xs) {
    if (REDUCTION_SIZE == 0)
      return xs;
    const proth120_wide modulus_squared = MODULUS_SQUARED<REDUCTION_SIZE>();
    proth120_wide rs = {};
    return sub_limbs<true>(xs, modulus_squared, rs) ? xs : rs;
  }

  template <u32 REDUCTION_SIZE = 1> static constexpr DEVICE_FORCEINLINE proth120 add_pick_reduction_size(const proth120 &xs, const proth120 &ys) {
    proth120 rs = {};
    add_limbs<false>(xs, ys, rs);
    return reduce<REDUCTION_SIZE>(rs);
  }

  // return xs + ys with field operands. Assumes xs and ys are canonical.
  static constexpr DEVICE_FORCEINLINE proth120 add(const proth120 xs, const proth120 ys) {
    return add_pick_reduction_size<1>(xs, ys);
  }

  template <u32 REDUCTION_SIZE = 1> static constexpr DEVICE_FORCEINLINE proth120_wide add_wide(const proth120_wide &xs, const proth120_wide &ys) {
    proth120_wide rs = {};
    add_limbs<false>(xs, ys, rs);
    return reduce_wide<REDUCTION_SIZE>(rs);
  }

  template <u32 REDUCTION_SIZE = 1> static DEVICE_FORCEINLINE proth120 sub_pick_reduction_size(const proth120 &xs, const proth120 &ys) {
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

  // return xs - ys with field operands
  static DEVICE_FORCEINLINE proth120 sub(const proth120 xs, const proth120 ys) {
    return sub_pick_reduction_size<1>(xs, ys);
  }

  template <u32 REDUCTION_SIZE = 1> static DEVICE_FORCEINLINE proth120_wide sub_wide(const proth120_wide &xs, const proth120_wide &ys) {
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
  // We had our own implementation of http://www.acsel-lab.com/arithmetic/arith23/data/1616a047.pdf,
  // but the sppark versions achieved lower instruction count thanks to clever carry handling,
  // so we decided to just use theirs.

  static DEVICE_FORCEINLINE void mul_n(u32 *acc, const u32 *a, u32 bi, size_t n = LC) {
#pragma unroll
    for (size_t i = 0; i < n; i += 2) {
      acc[i] = ptx::mul_lo(a[i], bi);
      acc[i + 1] = ptx::mul_hi(a[i], bi);
    }
  }

  static DEVICE_FORCEINLINE void cmad_n(u32 *acc, const u32 *a, u32 bi, size_t n = LC) {
    acc[0] = ptx::mad_lo_cc(a[0], bi, acc[0]);
    acc[1] = ptx::madc_hi_cc(a[0], bi, acc[1]);
#pragma unroll
    for (size_t i = 2; i < n; i += 2) {
      acc[i] = ptx::madc_lo_cc(a[i], bi, acc[i]);
      acc[i + 1] = ptx::madc_hi_cc(a[i], bi, acc[i + 1]);
    }
    // return carry flag
  }

  static DEVICE_FORCEINLINE void madc_n_rshift(u32 *odd, const u32 *a, u32 bi) {
    constexpr u32 n = LC;
#pragma unroll
    for (size_t i = 0; i < n - 2; i += 2) {
      odd[i] = ptx::madc_lo_cc(a[i], bi, odd[i + 2]);
      odd[i + 1] = ptx::madc_hi_cc(a[i], bi, odd[i + 3]);
    }
    odd[n - 2] = ptx::madc_lo_cc(a[n - 2], bi, 0);
    odd[n - 1] = ptx::madc_hi(a[n - 2], bi, 0);
  }

  static DEVICE_FORCEINLINE void mad_n_redc(u32 *even, u32 *odd, const u32 *a, u32 bi, bool first = false) {
    constexpr u32 n = LC;
    constexpr auto modulus = MODULUS<1>();
    const u32 *const MOD = modulus.limbs.raw;
    if (first) {
      mul_n(odd, a + 1, bi);
      mul_n(even, a, bi);
    } else {
      even[0] = ptx::add_cc(even[0], odd[1]);
      madc_n_rshift(odd, a + 1, bi);
      cmad_n(even, a, bi);
      odd[n - 1] = ptx::addc(odd[n - 1], 0);
    }
    u32 mi = even[0] * MONT_K;
    cmad_n(odd, MOD + 1, mi);
    cmad_n(even, MOD, mi);
    odd[n - 1] = ptx::addc(odd[n - 1], 0);
  }

  static DEVICE_FORCEINLINE void mad_row(u32 *odd, u32 *even, const u32 *a, u32 bi, size_t n = LC) {
    cmad_n(odd, a + 1, bi, n - 2);
    odd[n - 2] = ptx::madc_lo_cc(a[n - 1], bi, 0);
    odd[n - 1] = ptx::madc_hi(a[n - 1], bi, 0);
    cmad_n(even, a, bi, n);
    odd[n - 1] = ptx::addc(odd[n - 1], 0);
  }

  static DEVICE_FORCEINLINE void qad_row(u32 *odd, u32 *even, const u32 *a, u32 bi, size_t n = LC) {
    cmad_n(odd, a, bi, n - 2);
    odd[n - 2] = ptx::madc_lo_cc(a[n - 2], bi, 0);
    odd[n - 1] = ptx::madc_hi(a[n - 2], bi, 0);
    cmad_n(even, a + 1, bi, n - 2);
    odd[n - 1] = ptx::addc(odd[n - 1], 0);
  }

  static DEVICE_FORCEINLINE void multiply_raw(const proth120 &as, const proth120 &bs, proth120_wide &rs) {
    const u32 *a = as.limbs.raw;
    const u32 *b = bs.limbs.raw;
    u32 *even = rs.limbs.raw;
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
    // merge |even| and |odd|
    even[1] = ptx::add_cc(even[1], odd[0]);
    for (i = 1; i < 2 * LC - 2; i++)
      even[i + 1] = ptx::addc_cc(even[i + 1], odd[i]);
    even[i + 1] = ptx::addc(even[i + 1], 0);
  }

  static DEVICE_FORCEINLINE void sqr_raw(const proth120 &as, proth120_wide &rs) {
    const u32 *a = as.limbs.raw;
    u32 *even = rs.limbs.raw;
    size_t i = 0, j;
    __align__(8) u32 odd[2 * LC - 2];

    // perform |a[i]|*|a[j]| for all j>i
    mul_n(even + 2, a + 2, a[0], LC - 2);
    mul_n(odd, a + 1, a[0], LC);

   static_assert(LC == 4);
   // The following logic is unnecessary for LC == 4
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

    // merge |even[2:]| and |odd[1:]|
    even[2] = ptx::add_cc(even[2], odd[1]);
    for (j = 2; j < 2 * LC - 3; j++)
      even[j + 1] = ptx::addc_cc(even[j + 1], odd[j]);
    even[j + 1] = ptx::addc(odd[j], 0);

    // double |even|
    even[0] = 0;
    even[1] = ptx::add_cc(odd[0], odd[0]);
    for (j = 2; j < 2 * LC - 1; j++)
      even[j] = ptx::addc_cc(even[j], even[j]);
    even[j] = ptx::addc(0u, 0u);

    // accumulate "diagonal" |a[i]|*|a[i]| proth120oduct
    i = 0;
    even[2 * i] = ptx::mad_lo_cc(a[i], a[i], even[2 * i]);
    even[2 * i + 1] = ptx::madc_hi_cc(a[i], a[i], even[2 * i + 1]);
    for (++i; i < LC; i++) {
      even[2 * i] = ptx::madc_lo_cc(a[i], a[i], even[2 * i]);
      even[2 * i + 1] = ptx::madc_hi_cc(a[i], a[i], even[2 * i + 1]);
    }
  }

  static DEVICE_FORCEINLINE void mul_by_1_row(u32 *even, u32 *odd, bool first = false) {
    u32 mi;
    constexpr auto modulus = MODULUS<1>();
    const u32 *const MOD = modulus.limbs.raw;
    if (first) {
      mi = even[0] * MONT_K;
      mul_n(odd, MOD + 1, mi);
      cmad_n(even, MOD, mi);
      odd[LC - 1] = ptx::addc(odd[LC - 1], 0);
    } else {
      even[0] = ptx::add_cc(even[0], odd[1]);
      // we trust the compiler to *not* touch the carry flag here
      // this code sits in between two "asm volatile" instructions which should guarantee that nothing else interferes with the carry flag
      mi = even[0] * MONT_K;
      madc_n_rshift(odd, MOD + 1, mi);
      cmad_n(even, MOD, mi);
      odd[LC - 1] = ptx::addc(odd[LC - 1], 0);
    }
  }

  // Performs Montgomery reduction on a proth120_wide input. Input value must be in the range [0, mod*2^(32*LC)).
  // Does not implement an in-place reduce<REDUCTION_SIZE> epilogue. If you want to further reduce the result,
  // call reduce<whatever>(xs.get_lo()) after the call to redc_wide_inplace.
  static DEVICE_FORCEINLINE void redc_wide_inplace(proth120_wide &xs) {
    u32 *even = xs.limbs.raw;
    // Yields montmul of lo LC limbs * 1.
    // Since the hi LC limbs don't participate in computing the "mi" factor at each mul-and-rightshift stage,
    // it's ok to ignore the hi LC limbs during this proth120ocess and just add them in afterward.
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
    // Adds in (hi LC limbs), implicitly right-shifting them by LC limbs as if they had participated in the
    // add-and-rightshift stages above.
    xs.limbs.raw[0] = ptx::add_cc(xs.limbs.raw[0], xs.limbs.raw[LC]);
#pragma unroll
    for (i = 1; i < LC - 1; i++)
      xs.limbs.raw[i] = ptx::addc_cc(xs.limbs.raw[i], xs.limbs.raw[i + LC]);
    xs.limbs.raw[LC - 1] = ptx::addc(xs.limbs.raw[LC - 1], xs.limbs.raw[2 * LC - 1]);
  }

  static DEVICE_FORCEINLINE void montmul_raw(const proth120 &a_in, const proth120 &b_in, proth120 &r_in) {
    constexpr u32 n = LC;
    constexpr auto modulus = MODULUS<1>();
    const u32 *const MOD = modulus.limbs.raw;
    const u32 *a = a_in.limbs.raw;
    const u32 *b = b_in.limbs.raw;
    u32 *even = r_in.limbs.raw;
    __align__(8) u32 odd[n + 1];
    size_t i;
#pragma unroll
    for (i = 0; i < n; i += 2) {
      mad_n_redc(&even[0], &odd[0], a, b[i], i == 0);
      mad_n_redc(&odd[0], &even[0], a, b[i + 1]);
    }
    // merge |even| and |odd|
    even[0] = ptx::add_cc(even[0], odd[1]);
#pragma unroll
    for (i = 1; i < n - 1; i++)
      even[i] = ptx::addc_cc(even[i], odd[i + 1]);
    even[i] = ptx::addc(even[i], 0);
    // final reduction from [0, 2*mod) to [0, mod) not done here, instead performed optionally in the mul wrapper
  }

  // Returns xs * ys without Montgomery reduction.
  template <u32 REDUCTION_SIZE = 1> static constexpr DEVICE_FORCEINLINE proth120_wide mul_wide(const proth120 &xs, const proth120 &ys) {
    // Forces us to think more carefully about the last carry bit if we use a modulus with fewer than 2 leading zeroes of slack
    static_assert(!(modulus.raw[LC - 1] >> 30));
    proth120_wide rs = {0};
    multiply_raw(xs, ys, rs);
    return reduce_wide<REDUCTION_SIZE>(rs);
  }

  // Performs Montgomery reduction on a proth120_wide input. Input value must be in the range [0, mod*2^(32*LC)).
  template <u32 REDUCTION_SIZE = 1> static constexpr DEVICE_FORCEINLINE proth120 redc_wide(const proth120_wide &xs) {
    proth120_wide tmp{xs};
    redc_wide_inplace(tmp); // after reduce_twopass, tmp's low LC limbs should represent a value in [0, 2*mod)
    return reduce<REDUCTION_SIZE>(proth120{tmp.get_lo()});
  }

  template <u32 REDUCTION_SIZE = 1> static constexpr DEVICE_FORCEINLINE proth120 mul_pick_reduction_size(const proth120 &xs, const proth120 &ys) {
    // Forces us to think more carefully about the last carry bit if we use a modulus with fewer than 2 leading zeroes of slack
    static_assert(!(modulus.raw[LC - 1] >> 30));
    proth120 rs{zero};
    montmul_raw(xs, ys, rs);
    return reduce<REDUCTION_SIZE>(rs);
  }

  // return xs * ys with field operands
  // Adapts http://www.acsel-lab.com/arithmetic/arith23/data/1616a047.pdf to use IMAD.WIDE.
  static constexpr DEVICE_FORCEINLINE proth120 mul(const proth120 xs, const proth120 ys) {
    return mul_pick_reduction_size<1>(xs, ys);
  }

  template <u32 REDUCTION_SIZE = 1> static constexpr DEVICE_FORCEINLINE proth120 sqr_pick_reduction_size(const proth120 &xs) {
    // Forces us to think more carefully about the last carry bit if we use a modulus with fewer than 2 leading zeroes of slack
    static_assert(!(modulus.raw[LC - 1] >> 30));
    proth120_wide rs = {0};
    sqr_raw(xs, rs);
    redc_wide_inplace(rs); // after reduce_twopass, tmp's low LC limbs should represent a value in [0, 2*mod)
    return reduce<REDUCTION_SIZE>(proth120{rs.get_lo()});
  }

  // return xs^2 with field operands
  static constexpr DEVICE_FORCEINLINE proth120 sqr(const proth120 xs) {
    return sqr_pick_reduction_size<1>(xs);
  }

  static DEVICE_FORCEINLINE proth120 pow(proth120 x, const unsigned power) {
    proth120 result = ONE();
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

  // convert field to montgomery form
  template <u32 REDUCTION_SIZE = 1> static constexpr DEVICE_FORCEINLINE proth120 into_mont(const proth120 &xs) {
    constexpr proth120 r2 = R2();
    return mul<REDUCTION_SIZE>(xs, r2);
  }

  // convert field from montgomery form
  template <u32 REDUCTION_SIZE = 1> static constexpr DEVICE_FORCEINLINE proth120 from_mont(const proth120 &xs) { return mul<REDUCTION_SIZE>(xs, {1}); }

  // return 2*x with field operands
  template <u32 REDUCTION_SIZE = 1> static constexpr DEVICE_FORCEINLINE proth120 dbl(const proth120 &xs) {
    const u32 *x = xs.limbs.raw;
    proth120 rs = {};
    u32 *r = rs.limbs.raw;
    r[0] = x[0] << 1;
#pragma unroll
    for (u32 i = 1; i < LC; i++)
      r[i] = __funnelshift_r(x[i - 1], x[i], 31);
    return reduce<REDUCTION_SIZE>(rs);
  }

  // return x/2 with field operands
  template <u32 REDUCTION_SIZE = 1> static constexpr DEVICE_FORCEINLINE proth120 div2(const proth120 &xs) {
    const u32 *x = xs.limbs.raw;
    proth120 rs = {};
    u32 *r = rs.limbs.raw;
#pragma unroll
    for (u32 i = 0; i < LC - 1; i++)
      r[i] = __funnelshift_rc(x[i], x[i + 1], 1);
    r[LC - 1] = x[LC - 1] >> 1;
    return reduce<REDUCTION_SIZE>(rs);
  }

  // return -xs with field operand
  template <u32 MODULUS_SIZE = 1> static constexpr DEVICE_FORCEINLINE proth120 neg(const proth120 &xs) {
    const proth120 modulus = MODULUS<MODULUS_SIZE>();
    proth120 rs = {};
    sub_limbs<false>(modulus, xs, rs);
    return rs;
  }

  // extract a given count of bits at a given offset from the field
  static constexpr DEVICE_FORCEINLINE u32 extract_bits(const proth120 &xs, const u32 offset, const u32 count) {
    const u32 limb_index = offset / warpSize;
    const u32 *x = xs.limbs.raw;
    const u32 low_limb = x[limb_index];
    const u32 high_limb = limb_index < (LC - 1) ? x[limb_index + 1] : 0;
    u32 result = __funnelshift_r(low_limb, high_limb, offset);
    result &= (1 << count) - 1;
    return result;
  }

  template <u32 REDUCTION_SIZE = 1, u32 LAST_REDUCTION_SIZE = REDUCTION_SIZE>
  static constexpr DEVICE_FORCEINLINE proth120 mul(const u32 scalar, const proth120 &xs) {
    proth120 rs = {};
    proth120 temp = xs;
    u32 l = scalar;
    bool is_zero = true;
#pragma unroll
    for (u32 i = 0; i < 32; i++) {
      if (l & 1) {
        rs = is_zero ? temp : (l >> 1) ? add<REDUCTION_SIZE>(rs, temp) : add<LAST_REDUCTION_SIZE>(rs, temp);
        is_zero = false;
      }
      l >>= 1;
      if (l == 0)
        break;
      temp = dbl<REDUCTION_SIZE>(temp);
    }
    return rs;
  }

  static constexpr DEVICE_FORCEINLINE bool is_odd(const proth120 &xs) { return xs.limbs.raw[0] & 1; }

  static constexpr DEVICE_FORCEINLINE bool is_even(const proth120 &xs) { return ~xs.limbs.raw[0] & 1; }

  static constexpr DEVICE_FORCEINLINE bool lt(const proth120 &xs, const proth120 &ys) {
    proth120 dummy = {};
    u32 carry = sub_limbs<true>(xs, ys, dummy);
    return carry;
  }

  static constexpr DEVICE_FORCEINLINE proth120 inverse(const proth120 &xs) {
    if (is_zero(xs))
      return xs;
    constexpr proth120 one = {1};
    constexpr proth120 modulus = MODULUS<1>();
    proth120 u = xs;
    proth120 v = modulus;
    proth120 b = R2();
    proth120 c = {};
    while (!eq(u, one) && !eq(v, one)) {
      while (is_even(u)) {
        u = div2(u);
        if (is_odd(b))
          add_limbs<false>(b, modulus, b);
        b = div2(b);
      }
      while (is_even(v)) {
        v = div2(v);
        if (is_odd(c))
          add_limbs<false>(c, modulus, c);
        c = div2(c);
      }
      if (lt(v, u)) {
        sub_limbs<false>(u, v, u);
        b = sub(b, c);
      } else {
        sub_limbs<false>(v, u, v);
        c = sub(c, b);
      }
    }
    return eq(u, one) ? b : c;
  }
};

typedef proth120<inv_proth120> proth120_field;
typedef proth120_wide pr_wide;
using pr = proth120_field;

using namespace memory;

template <ld_modifier LD_MODIFIER = ld_modifier::none> struct pr_vector_getter : vector_getter<pr, LD_MODIFIER> {};

template <st_modifier ST_MODIFIER = st_modifier::none> struct pr_vector_setter : vector_setter<pr, ST_MODIFIER> {};

template <ld_modifier LD_MODIFIER = ld_modifier::none, st_modifier ST_MODIFIER = st_modifier::none>
struct pr_vector_getter_setter : vector_getter_setter<pr, LD_MODIFIER, ST_MODIFIER> {};

template <ld_modifier LD_MODIFIER = ld_modifier::none> struct pr_matrix_getter : matrix_getter<pr, LD_MODIFIER> {
  explicit pr_matrix_getter(size_t stride) : matrix_getter<pr, LD_MODIFIER>(stride) {}
};

template <st_modifier ST_MODIFIER = st_modifier::none> struct pr_matrix_setter : matrix_setter<pr, ST_MODIFIER> {
  explicit pr_matrix_setter(size_t stride) : matrix_setter<pr, ST_MODIFIER>(stride) {}
};

template <ld_modifier LD_MODIFIER = ld_modifier::none, st_modifier ST_MODIFIER = st_modifier::none>
struct pr_matrix_getter_setter : matrix_getter_setter<pr, LD_MODIFIER, ST_MODIFIER> {
  explicit pr_matrix_getter_setter(size_t stride) : matrix_getter_setter<pr, LD_MODIFIER, ST_MODIFIER>(stride) {}
};

#undef LIMBS_ALIGNMENT
#undef ALIGN
} // namespace airbender::primitives::field

