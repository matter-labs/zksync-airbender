#pragma once
#include "ntt.cuh"

namespace airbender::ntt {

constexpr e2 W_1_8 = e2{bf{32768}, bf{2147450879}};
// constexpr e2 W_1_4 = e2{bf{0}, bf{2147483646}};
constexpr e2 W_3_8 = e2{bf{2147450879}, bf{2147450879}};

DEVICE_FORCEINLINE void size_8_fwd_dit(e2 *x) {
  // first stage
#pragma unroll
  for (unsigned i{0}; i < 4; i++) {
    const e2 tmp = x[i];
    x[i] = e2::add(tmp, x[i + 4]);
    x[i + 4] = e2::sub(tmp, x[i + 4]);
  }

  // second stage
#pragma unroll
  for (unsigned i{0}; i < 2; i++) {
    const e2 tmp = x[i];
    x[i] = e2::add(tmp, x[i + 2]);
    x[i + 2] = e2::sub(tmp, x[i + 2]);
  }
  // x[4] = x[4] + W_1_4 * (x[6].real + i * x[6].imag)
  //      = x[4] + (-i) * (x[6].real + i * x[6].imag)
  //      = x[4] + (x[6].imag - i * x[6].real)
  // x[6] = x[4] - W_1_4 * (x[6].real + i * x[6].imag)
  //      = x[4] - (-i) * (x[6].real + i * x[6].imag)
  //      = x[4] + (-x[6].imag + i * x[6].real)
#pragma unroll
  for (unsigned i{4}; i < 6; i++) {
    const e2 tmp0 = x[i];
    x[i][0] = bf::add(x[i][0], x[i + 2][1]);
    x[i][1] = bf::sub(x[i][1], x[i + 2][0]);
    const bf tmp1 = x[i + 2][0];
    x[i + 2][0] = bf::sub(tmp0[0], x[i + 2][1]);
    x[i + 2][1] = bf::add(tmp0[1], tmp1);
  }

  // third stage
  {
    // x[3] = W_1_4 * x[3]
    //      = -i * (x[3].real + i * x[3].imag)
    //      = x[3].imag - i * x[3].real
    const bf tmp = x[3][0];
    x[3][0] = x[3][1];
    x[3][1] = bf::neg(tmp);
  }
  x[5] = e2::mul(W_1_8, x[5]); // don't bother optimizing, marginal gains
  x[7] = e2::mul(W_3_8, x[7]); // don't bother optimizing, marginal gains
#pragma unroll
  for (unsigned i{0}; i < 8; i += 2) {
    const e2 tmp = x[i];
    x[i] = e2::add(tmp, x[i + 1]);
    x[i + 1] = e2::sub(tmp, x[i + 1]);
  }

  // undo bitrev
  const e2 tmp0 = x[1];
  x[1] = x[4];
  x[4] = tmp0;
  const e2 tmp1 = x[3];
  x[3] = x[6];
  x[6] = tmp1;
}

DEVICE_FORCEINLINE void size_8_inv_dit(e2 *x) {
  constexpr e2 W_1_8_INV = e2{bf{32768}, bf{32768}};
  // constexpr e2 W_1_4_INV = e2{bf{0}, bf{1}};
  constexpr e2 W_3_8_INV = e2{bf{2147450879}, bf{32768}};

  // first stage
#pragma unroll
  for (unsigned i{0}; i < 4; i++) {
    const e2 tmp = x[i];
    x[i] = e2::add(tmp, x[i + 4]);
    x[i + 4] = e2::sub(tmp, x[i + 4]);
  }

  // second stage
#pragma unroll
  for (unsigned i{0}; i < 2; i++) {
    const e2 tmp = x[i];
    x[i] = e2::add(tmp, x[i + 2]);
    x[i + 2] = e2::sub(tmp, x[i + 2]);
  }
  // x[4] = x[4] + W_1_4_INV * (x[6].real + i * x[6].imag)
  //      = x[4] + i * (x[6].real + i * x[6].imag)
  //      = x[4] + (-x[6].imag + i * x[6].real)
  // x[6] = x[4] - W_1_4_INV * (x[6].real + i * x[6].imag)
  //      = x[4] - i * (x[6].real + i * x[6].imag)
  //      = x[4] + (x[6].imag - i * x[6].real)
#pragma unroll
  for (unsigned i{4}; i < 6; i++) {
    const e2 tmp0 = x[i];
    x[i][0] = bf::sub(x[i][0], x[i + 2][1]);
    x[i][1] = bf::add(x[i][1], x[i + 2][0]);
    const bf tmp1 = x[i + 2][0];
    x[i + 2][0] = bf::add(tmp0[0], x[i + 2][1]);
    x[i + 2][1] = bf::sub(tmp0[1], tmp1);
  }

  // third stage
  {
    // x[3] = W_1_4_INV * x[3]
    //      = i * (x[3].real + i * x[3].imag)
    //      = -x[3].imag + i * x[3].real)
    const bf tmp = x[3][0];
    x[3][0] = bf::neg(x[3][1]);
    x[3][1] = tmp;
  }
  x[5] = e2::mul(W_1_8_INV, x[5]); // don't bother optimizing, marginal gains
  x[7] = e2::mul(W_3_8_INV, x[7]); // don't bother optimizing, marginal gains
#pragma unroll
  for (unsigned i{0}; i < 8; i += 2) {
    const e2 tmp = x[i];
    x[i] = e2::add(tmp, x[i + 1]);
    x[i + 1] = e2::sub(tmp, x[i + 1]);
  }

  // undo bitrev
  const e2 tmp0 = x[1];
  x[1] = x[4];
  x[4] = tmp0;
  const e2 tmp1 = x[3];
  x[3] = x[6];
  x[6] = tmp1;
}

template <unsigned LOG_RADIX> DEVICE_FORCEINLINE unsigned bitrev_by_radix(const unsigned idx, const unsigned bit_chunks) {
  constexpr unsigned RADIX_MASK = (1 << LOG_RADIX) - 1;
  unsigned out{0}, tmp_idx{idx};
  for (unsigned i{0}; i < bit_chunks; i++) {
    out <<= LOG_RADIX;
    out |= tmp_idx & RADIX_MASK;
    tmp_idx >>= LOG_RADIX;
  }
  return out;
}

template <unsigned LOG_RADIX>
DEVICE_FORCEINLINE void apply_twiddles_same_region(e2 *vals0, e2 *vals1, const unsigned exchg_region, const unsigned twiddle_stride,
                                                   const unsigned idx_bit_chunks, const e2 twiddle) {
  constexpr unsigned RADIX = 1 << LOG_RADIX;
  if (exchg_region > 0) {
    // const unsigned v = bitrev_by_radix<LOG_RADIX>(exchg_region, idx_bit_chunks);
    // const unsigned v = exchg_region;
    // const unsigned v = 7;
    // const auto twiddle_base = get_twiddle_with_direct_index<true>(v * twiddle_stride);
    // auto twiddle = twiddle_base;
#pragma unroll
    for (unsigned i{1}; i < RADIX - 1; i++) {
      // const auto twiddle = get_twiddle_with_direct_index<true>(v * i * twiddle_stride);
      vals0[i] = e2::mul(vals0[i], twiddle);
      vals1[i] = e2::mul(vals1[i], twiddle);
      // twiddle = e2::mul(twiddle, twiddle_base);
    }
    vals0[RADIX - 1] = e2::mul(vals0[RADIX - 1], twiddle);
    vals1[RADIX - 1] = e2::mul(vals1[RADIX - 1], twiddle);
  }
}

template <unsigned LOG_RADIX>
DEVICE_FORCEINLINE void apply_twiddles_distinct_regions(e2 *vals0, e2 *vals1, const unsigned exchg_region_0, const unsigned exchg_region_1,
                                                        const unsigned twiddle_stride, const unsigned idx_bit_chunks, const e2 twiddle) {
  constexpr unsigned RADIX = 1 << LOG_RADIX;
  if (exchg_region_0 > 0) {
    // const unsigned v = bitrev_by_radix<LOG_RADIX>(exchg_region_0, idx_bit_chunks);
    // const unsigned v = exchg_region_0;
    // const unsigned v = 7;
    // const auto twiddle_base = get_twiddle_with_direct_index<true>(v * twiddle_stride);
    // auto twiddle = twiddle_base;
#pragma unroll
    for (unsigned i{1}; i < RADIX - 1; i++) {
      // const auto twiddle = get_twiddle_with_direct_index<true>(v * i * twiddle_stride);
      vals0[i] = e2::mul(vals0[i], twiddle);
      // twiddle = e2::mul(twiddle, twiddle_base);
    }
    vals0[RADIX - 1] = e2::mul(vals0[RADIX - 1], twiddle);
  }
  // exchg_region_1 should never be 0
  // const unsigned v = bitrev_by_radix<LOG_RADIX>(exchg_region_1, idx_bit_chunks);
  // const unsigned v = exchg_region_1;
  // const unsigned v = 7;
  // const auto twiddle_base = get_twiddle_with_direct_index<true>(v * twiddle_stride);
  // auto twiddle = twiddle_base;
#pragma unroll
  for (unsigned i{1}; i < RADIX - 1; i++) {
    // const auto twiddle = get_twiddle_with_direct_index<true>(v * i * twiddle_stride);
    vals1[i] = e2::mul(vals1[i], twiddle);
    // twiddle = e2::mul(twiddle, twiddle_base);
  }
  vals1[RADIX - 1] = e2::mul(vals1[RADIX - 1], twiddle);
}

} // namespace airbender::ntt
