#include "primitives/proth120.cuh"
#include <cstddef>

namespace airbender::ops::proth120 {

using ::airbender::primitives::field::pr;
namespace field = ::airbender::primitives::field;
namespace detail = ::airbender::primitives::field::proth120_detail;
using namespace ::airbender::primitives::memory;

struct __align__(16) pr_probe_input {
  pr a;
  pr b;
  pr c;
  u32 exp_u32;
  u32 exp_le[4];
  u32 natural_le[4];
  u32 extract_offset;
  u32 extract_count;
  u32 _pad;
};

static_assert(sizeof(pr_probe_input) == 96 && alignof(pr_probe_input) == 16);
static_assert(offsetof(pr_probe_input, a) == 0);
static_assert(offsetof(pr_probe_input, b) == 16);
static_assert(offsetof(pr_probe_input, c) == 32);
static_assert(offsetof(pr_probe_input, exp_u32) == 48);
static_assert(offsetof(pr_probe_input, exp_le) == 52);
static_assert(offsetof(pr_probe_input, natural_le) == 68);
static_assert(offsetof(pr_probe_input, extract_offset) == 84);
static_assert(offsetof(pr_probe_input, extract_count) == 88);
static_assert(offsetof(pr_probe_input, _pad) == 92);

struct __align__(16) pr_probe_output {
  pr add;
  pr sub;
  pr mul;
  pr sqr;
  pr neg;
  pr dbl;
  pr inv;
  pr pow_u32;
  pr pow_u128;
  pr fma;
  pr fms;
  pr from_natural;
  pr pow_log2_8;
  pr scalar_mul;
  pr half;
  pr zero;
  pr one;
  pr two;
  u8 be_bytes[16];
  u32 eq;
  u32 is_zero;
  u32 extract;
  u32 operator_mismatch;
};

static_assert(sizeof(pr_probe_output) == 320 && alignof(pr_probe_output) == 16);
static_assert(offsetof(pr_probe_output, add) == 0);
static_assert(offsetof(pr_probe_output, sub) == 16);
static_assert(offsetof(pr_probe_output, mul) == 32);
static_assert(offsetof(pr_probe_output, sqr) == 48);
static_assert(offsetof(pr_probe_output, neg) == 64);
static_assert(offsetof(pr_probe_output, dbl) == 80);
static_assert(offsetof(pr_probe_output, inv) == 96);
static_assert(offsetof(pr_probe_output, pow_u32) == 112);
static_assert(offsetof(pr_probe_output, pow_u128) == 128);
static_assert(offsetof(pr_probe_output, fma) == 144);
static_assert(offsetof(pr_probe_output, fms) == 160);
static_assert(offsetof(pr_probe_output, from_natural) == 176);
static_assert(offsetof(pr_probe_output, pow_log2_8) == 192);
static_assert(offsetof(pr_probe_output, scalar_mul) == 208);
static_assert(offsetof(pr_probe_output, half) == 224);
static_assert(offsetof(pr_probe_output, zero) == 240);
static_assert(offsetof(pr_probe_output, one) == 256);
static_assert(offsetof(pr_probe_output, two) == 272);
static_assert(offsetof(pr_probe_output, be_bytes) == 288);
static_assert(offsetof(pr_probe_output, eq) == 304);
static_assert(offsetof(pr_probe_output, is_zero) == 308);
static_assert(offsetof(pr_probe_output, extract) == 312);
static_assert(offsetof(pr_probe_output, operator_mismatch) == 316);

struct __align__(16) pr_raw_probe_input {
  u32 a[8];
  u32 b[8];
  u32 op;
  u32 n;
  u32 width;
  u32 flags;
};

static_assert(sizeof(pr_raw_probe_input) == 80 && alignof(pr_raw_probe_input) == 16);
static_assert(offsetof(pr_raw_probe_input, a) == 0);
static_assert(offsetof(pr_raw_probe_input, b) == 32);
static_assert(offsetof(pr_raw_probe_input, op) == 64);
static_assert(offsetof(pr_raw_probe_input, n) == 68);
static_assert(offsetof(pr_raw_probe_input, width) == 72);
static_assert(offsetof(pr_raw_probe_input, flags) == 76);

struct __align__(16) pr_raw_probe_output {
  u32 r[8];
  u32 carry;
  u32 status;
  u32 _pad[2];
};

static_assert(sizeof(pr_raw_probe_output) == 48 && alignof(pr_raw_probe_output) == 16);
static_assert(offsetof(pr_raw_probe_output, r) == 0);
static_assert(offsetof(pr_raw_probe_output, carry) == 32);
static_assert(offsetof(pr_raw_probe_output, status) == 36);
static_assert(offsetof(pr_raw_probe_output, _pad) == 40);

static_assert(sizeof(field::pr_matrix_getter<>) == 16 && alignof(field::pr_matrix_getter<>) == 8);
static_assert(offsetof(field::pr_matrix_getter<>, ptr) == 0 && offsetof(field::pr_matrix_getter<>, stride) == 8);
static_assert(sizeof(field::pr_matrix_setter<>) == 16 && alignof(field::pr_matrix_setter<>) == 8);
static_assert(offsetof(field::pr_matrix_setter<>, ptr) == 0 && offsetof(field::pr_matrix_setter<>, stride) == 8);
static_assert(sizeof(field::pr_matrix_getter_setter<>) == 16 && alignof(field::pr_matrix_getter_setter<>) == 8);
static_assert(offsetof(field::pr_matrix_getter_setter<>, ptr) == 0 && offsetof(field::pr_matrix_getter_setter<>, stride) == 8);

EXTERN __global__ void ab_inv_pr_kernel(const pr *values, pr *result, const unsigned count) {
  const u64 i = u64(blockIdx.x) * blockDim.x + threadIdx.x;
  if (i < count)
    result[i] = pr::inv(values[i]);
}

EXTERN __global__ void ab_batch_inverse_pr_kernel(const pr *input, pr *output, pr *prefix, const unsigned count) {
  const u64 t = u64(blockIdx.x) * blockDim.x + threadIdx.x;
  const u64 offset = t * 256;
  if (offset >= count)
    return;
  const u32 chunk_count = count - offset < 256 ? u32(count - offset) : 256;
  pr::batch_inverse(input + offset, output + offset, prefix + offset, chunk_count);
}

EXTERN __global__ void ab_pr_field_probe_kernel(const pr_probe_input *input, pr_probe_output *output, const u32 count) {
  const u64 i = u64(blockIdx.x) * blockDim.x + threadIdx.x;
  if (i >= count)
    return;
  const pr_probe_input in = input[i];
  pr_probe_output out{};
  out.add = pr::add(in.a, in.b);
  out.sub = pr::sub(in.a, in.b);
  out.mul = pr::mul(in.a, in.b);
  out.sqr = pr::sqr(in.a);
  out.neg = pr::neg(in.a);
  out.dbl = pr::dbl(in.a);
  out.inv = pr::inv(in.a);
  out.pow_u32 = pr::pow(in.a, in.exp_u32);
  out.pow_u128 = pr::pow(in.a, in.exp_le);
  out.fma = pr::fma(in.a, in.b, in.c);
  out.fms = pr::fms(in.a, in.b, in.c);
  out.from_natural = pr::from_u128_with_reduction(in.natural_le);
  out.pow_log2_8 = pr::pow_log2_exp<8>(in.a);
  out.scalar_mul = detail::scalar_mul(in.exp_u32, in.a);
  out.half = detail::half(in.a);
  out.zero = pr::ZERO();
  out.one = pr::ONE();
  out.two = pr::TWO();
  pr::to_canonical_be_bytes(in.a, out.be_bytes);
  out.eq = pr::eq(in.a, in.b);
  out.is_zero = pr::is_zero(in.a);
  out.extract = detail::extract_bits(in.natural_le, in.extract_offset, in.extract_count);
  out.operator_mismatch |= u32(!pr::eq(-in.a, out.neg)) << 0;
  out.operator_mismatch |= u32(!pr::eq(in.a + in.b, out.add)) << 1;
  out.operator_mismatch |= u32(!pr::eq(in.a - in.b, out.sub)) << 2;
  out.operator_mismatch |= u32(!pr::eq(in.a * in.b, out.mul)) << 3;
  pr value = in.a;
  value += in.b;
  out.operator_mismatch |= u32(!pr::eq(value, out.add)) << 4;
  value = in.a;
  value -= in.b;
  out.operator_mismatch |= u32(!pr::eq(value, out.sub)) << 5;
  value = in.a;
  value *= in.b;
  out.operator_mismatch |= u32(!pr::eq(value, out.mul)) << 6;
  output[i] = out;
}

DEVICE_FORCEINLINE void raw_store(pr_raw_probe_output &out, const pr value) {
#pragma unroll
  for (u32 i = 0; i < 4; i++)
    out.r[i] = value.limbs[i];
}

DEVICE_FORCEINLINE void raw_store(pr_raw_probe_output &out, const detail::proth120_wide value) {
#pragma unroll
  for (u32 i = 0; i < 8; i++)
    out.r[i] = value.limbs[i];
}

template <bool SUBTRACT, bool CARRY_OUT, typename T> DEVICE_FORCEINLINE void raw_limbs(const T x, const T y, pr_raw_probe_output &out) {
  T r{};
  if constexpr (SUBTRACT)
    out.carry = detail::sub_limbs<CARRY_OUT>(x, y, r);
  else
    out.carry = detail::add_limbs<CARRY_OUT>(x, y, r);
  raw_store(out, r);
}

template <typename T> DEVICE_FORCEINLINE void raw_limb_flags(const T x, const T y, const u32 flags, pr_raw_probe_output &out) {
  switch (flags) {
  case 0:
    raw_limbs<false, false>(x, y, out);
    break;
  case 1:
    raw_limbs<true, false>(x, y, out);
    break;
  case 2:
    raw_limbs<false, true>(x, y, out);
    break;
  case 3:
    raw_limbs<true, true>(x, y, out);
    break;
  }
}

template <u32 N> DEVICE_FORCEINLINE void raw_probe(const pr_raw_probe_input &in, pr_raw_probe_output &out) {
  const pr x = {{in.a[0], in.a[1], in.a[2], in.a[3]}};
  const pr y = {{in.b[0], in.b[1], in.b[2], in.b[3]}};
  detail::proth120_wide wx{}, wy{}, r{};
  if (in.width == 8) {
#pragma unroll
    for (u32 i = 0; i < 8; i++) {
      wx.limbs[i] = in.a[i];
      wy.limbs[i] = in.b[i];
    }
  }
  switch (in.op) {
  case 0:
    if (in.width == 4)
      raw_limb_flags(x, y, in.flags, out);
    else
      raw_limb_flags(wx, wy, in.flags, out);
    break;
  case 1:
    raw_store(out, detail::MODULUS<N>());
    break;
  case 2:
    raw_store(out, detail::MODULUS_SQUARED<N>());
    break;
  case 3:
    raw_store(out, detail::reduce<N>(x));
    break;
  case 4:
    raw_store(out, detail::reduce_wide<N>(wx));
    break;
  case 5:
    raw_store(out, detail::add_pick_reduction_size<N>(x, y));
    break;
  case 6:
    raw_store(out, detail::sub_pick_reduction_size<N>(x, y));
    break;
  case 7:
    raw_store(out, detail::add_wide<N>(wx, wy));
    break;
  case 8:
    raw_store(out, detail::sub_wide<N>(wx, wy));
    break;
  case 9:
    detail::multiply_raw(x, y, r);
    raw_store(out, r);
    break;
  case 10:
    detail::sqr_raw(x, r);
    raw_store(out, r);
    break;
  case 11:
    raw_store(out, detail::mul_wide<N>(x, y));
    break;
  case 12: {
    pr r{};
    detail::montmul_raw(x, y, r);
    raw_store(out, r);
    break;
  }
  case 13:
    raw_store(out, detail::mul_pick_reduction_size<N>(x, y));
    break;
  case 14:
    raw_store(out, detail::sqr_pick_reduction_size<N>(x));
    break;
  case 15:
    detail::redc_wide_inplace(wx);
    raw_store(out, wx.get_lo());
    break;
  case 16:
    raw_store(out, detail::redc_wide<N>(wx));
    break;
  }
}

EXTERN __global__ void ab_pr_raw_probe_kernel(const pr_raw_probe_input *input, pr_raw_probe_output *output, const u32 count) {
  const u64 i = u64(blockIdx.x) * blockDim.x + threadIdx.x;
  if (i >= count)
    return;
  const pr_raw_probe_input in = input[i];
  pr_raw_probe_output out{};
  out.status = 0xffffffffu;
  const bool wide = in.op == 2 || in.op == 4 || in.op == 7 || in.op == 8 || in.op == 15 || in.op == 16;
  const bool n_zero = in.op == 0 || in.op == 9 || in.op == 10 || in.op == 12 || in.op == 15;
  if (in.op > 16 || (in.op == 0 ? (in.width != 4 && in.width != 8) : in.width != (wide ? 8 : 4)) || (in.n != 0 && in.n != 1 && in.n != 2 && in.n != 4) ||
      (n_zero && in.n != 0) || (in.op == 0 ? in.flags > 3 : in.flags != 0)) {
    output[i] = out;
    return;
  }
  out.status = 0;
  switch (in.n) {
  case 0:
    raw_probe<0>(in, out);
    break;
  case 1:
    raw_probe<1>(in, out);
    break;
  case 2:
    raw_probe<2>(in, out);
    break;
  case 4:
    raw_probe<4>(in, out);
    break;
  }
  output[i] = out;
}

EXTERN __global__ void ab_pr_access_probe_kernel(const pr *src, pr *dst, field::pr_matrix_getter<> src_matrix, field::pr_matrix_setter<> dst_matrix_setter,
                                                 field::pr_matrix_getter_setter<> dst_matrix_getter_setter, const unsigned rows) {
  const u64 i = u64(blockIdx.x) * blockDim.x + threadIdx.x;
  if (i >= rows)
    return;
  const u64 stride = src_matrix.stride;
  field::pr_vector_getter<ld_modifier::cs> getter{};
  getter.ptr = const_cast<pr *>(src);
  const pr value = getter.get(i);
  dst[i] = value;
  dst[stride + i] = src_matrix.get(i, 1);
#pragma unroll
  for (u32 k = 0; k < 5; k++)
    dst[(2 + k) * stride + i] = shfl_xor(0xffffffffu, value, 1 << k, 32);
  field::pr_vector_setter<st_modifier::cs> setter{};
  setter.ptr = dst + 7 * stride;
  setter.set(i, value);
  field::pr_vector_getter_setter<> getter_setter{};
  getter_setter.ptr = dst + 7 * stride;
  getter_setter.set(i, pr::add(getter_setter.get(i), pr::ONE()));
  dst_matrix_setter.set(i, 8, value);
  dst_matrix_getter_setter.set(i, 8, pr::add(dst_matrix_getter_setter.get(i, 8), pr::ONE()));
}

} // namespace airbender::ops::proth120
