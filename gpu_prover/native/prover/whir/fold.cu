#include "../../common.cuh"
#include "../../primitives/field.cuh"
#include "../../primitives/memory.cuh"
#include "../../primitives/vectorized.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;
using namespace ::airbender::primitives::vectorized;

namespace airbender::prover::whir {

EXTERN __global__ void ab_whir_fold_monomial_e4_kernel(const e4 *src, const e4 *challenge, e4 *dst, const unsigned half_len) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= half_len)
    return;

  const e4 c0 = load<e4, ld_modifier::cs>(src, 2 * gid);
  const e4 c1 = load<e4, ld_modifier::cs>(src, 2 * gid + 1);
  const e4 folded = e4::fma(c1, *challenge, c0);
  store<e4, st_modifier::cs>(dst, folded, gid);
}

EXTERN __global__ void ab_whir_fold_split_half_vectorized_e4_kernel(vectorized_e4_matrix_getter<ld_modifier::cg> src,
                                                                    vectorized_e4_matrix_setter<st_modifier::cg> dst, const e4 *challenge,
                                                                    const unsigned half_len) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= half_len)
    return;

  const e4 c0 = src.get_at_row(gid);
  const e4 c1 = src.get_at_row(gid + half_len);
  const e4 folded = e4::add(c0, e4::mul(c1, *challenge));
  dst.set_at_row(gid, folded);
}

EXTERN __global__ void ab_whir_fold_split_half_e4_kernel(e4 *values, const e4 *challenge, const unsigned half_len) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= half_len)
    return;

  const e4 a = load<e4, ld_modifier::cs>(values, gid);
  const e4 b = load<e4, ld_modifier::cs>(values, half_len + gid);
  const e4 diff = e4::sub(b, a);
  const e4 folded = e4::fma(*challenge, diff, a);
  store<e4, st_modifier::cs>(values, folded, gid);
}

// Paired (eval_form, eq_poly) split-half fold sharing a single challenge.
EXTERN __global__ void ab_whir_fold_split_half_pair_e4_kernel(e4 *values_a, e4 *values_b, const e4 *challenge, const unsigned half_len) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= half_len)
    return;

  const e4 c = *challenge;
  const e4 a_lo = load<e4, ld_modifier::cs>(values_a, gid);
  const e4 a_hi = load<e4, ld_modifier::cs>(values_a, half_len + gid);
  store<e4, st_modifier::cs>(values_a, e4::fma(c, e4::sub(a_hi, a_lo), a_lo), gid);
  const e4 b_lo = load<e4, ld_modifier::cs>(values_b, gid);
  const e4 b_hi = load<e4, ld_modifier::cs>(values_b, half_len + gid);
  store<e4, st_modifier::cs>(values_b, e4::fma(c, e4::sub(b_hi, b_lo), b_lo), gid);
}

// WHIR sumcheck three-point partials. Each block stride-reduces its slice of
// [0, half) into three block-local sums; the finalize kernel sums across blocks.
//   p0 = sum_i eval[i] * eq[i]
//   p1 = sum_i eval[half+i] * eq[half+i]
//   p2 = sum_i (eval[i] + eval[half+i]) * (eq[i] + eq[half+i])
constexpr unsigned WHIR_THREE_POINT_BLOCK_THREADS = 256;

EXTERN __global__ void ab_whir_three_point_partials_e4_kernel(const e4 *__restrict__ eval, const e4 *__restrict__ eq, e4 *__restrict__ partials,
                                                              const unsigned half) {
  __shared__ e4 smem_p0[WHIR_THREE_POINT_BLOCK_THREADS];
  __shared__ e4 smem_p1[WHIR_THREE_POINT_BLOCK_THREADS];
  __shared__ e4 smem_p2[WHIR_THREE_POINT_BLOCK_THREADS];

  const unsigned tid = threadIdx.x;
  const unsigned stride = gridDim.x * blockDim.x;

  e4 acc0 = e4::ZERO();
  e4 acc1 = e4::ZERO();
  e4 acc2 = e4::ZERO();

  for (unsigned i = blockIdx.x * blockDim.x + tid; i < half; i += stride) {
    const e4 ev_lo = load<e4, ld_modifier::cs>(eval, i);
    const e4 ev_hi = load<e4, ld_modifier::cs>(eval, half + i);
    const e4 eq_lo = load<e4, ld_modifier::cs>(eq, i);
    const e4 eq_hi = load<e4, ld_modifier::cs>(eq, half + i);
    acc0 = e4::add(acc0, e4::mul(ev_lo, eq_lo));
    acc1 = e4::add(acc1, e4::mul(ev_hi, eq_hi));
    acc2 = e4::add(acc2, e4::mul(e4::add(ev_lo, ev_hi), e4::add(eq_lo, eq_hi)));
  }

  smem_p0[tid] = acc0;
  smem_p1[tid] = acc1;
  smem_p2[tid] = acc2;
  __syncthreads();

#pragma unroll
  for (unsigned offset = WHIR_THREE_POINT_BLOCK_THREADS / 2; offset > 0; offset >>= 1) {
    if (tid < offset) {
      smem_p0[tid] = e4::add(smem_p0[tid], smem_p0[tid + offset]);
      smem_p1[tid] = e4::add(smem_p1[tid], smem_p1[tid + offset]);
      smem_p2[tid] = e4::add(smem_p2[tid], smem_p2[tid + offset]);
    }
    __syncthreads();
  }

  if (tid == 0) {
    partials[blockIdx.x * 3u + 0u] = smem_p0[0];
    partials[blockIdx.x * 3u + 1u] = smem_p1[0];
    partials[blockIdx.x * 3u + 2u] = smem_p2[0];
  }
}

EXTERN __global__ void ab_whir_three_point_finalize_e4_kernel(const e4 *__restrict__ partials, const unsigned num_blocks, e4 *__restrict__ reduce_out) {
  __shared__ e4 smem_p0[WHIR_THREE_POINT_BLOCK_THREADS];
  __shared__ e4 smem_p1[WHIR_THREE_POINT_BLOCK_THREADS];
  __shared__ e4 smem_p2[WHIR_THREE_POINT_BLOCK_THREADS];

  const unsigned tid = threadIdx.x;

  e4 acc0 = e4::ZERO();
  e4 acc1 = e4::ZERO();
  e4 acc2 = e4::ZERO();
  for (unsigned b = tid; b < num_blocks; b += WHIR_THREE_POINT_BLOCK_THREADS) {
    acc0 = e4::add(acc0, partials[b * 3u + 0u]);
    acc1 = e4::add(acc1, partials[b * 3u + 1u]);
    acc2 = e4::add(acc2, partials[b * 3u + 2u]);
  }

  smem_p0[tid] = acc0;
  smem_p1[tid] = acc1;
  smem_p2[tid] = acc2;
  __syncthreads();

#pragma unroll
  for (unsigned offset = WHIR_THREE_POINT_BLOCK_THREADS / 2; offset > 0; offset >>= 1) {
    if (tid < offset) {
      smem_p0[tid] = e4::add(smem_p0[tid], smem_p0[tid + offset]);
      smem_p1[tid] = e4::add(smem_p1[tid], smem_p1[tid + offset]);
      smem_p2[tid] = e4::add(smem_p2[tid], smem_p2[tid + offset]);
    }
    __syncthreads();
  }

  if (tid == 0) {
    reduce_out[0] = smem_p0[0];
    reduce_out[1] = smem_p1[0];
    reduce_out[2] = smem_p2[0];
  }
}

// Single-launch path for tiny `half` (<= WHIR_THREE_POINT_BLOCK_THREADS):
// fuses partials + finalize into one block, no partials buffer.
EXTERN __global__ void ab_whir_three_point_combined_e4_kernel(const e4 *__restrict__ eval, const e4 *__restrict__ eq, e4 *__restrict__ reduce_out,
                                                              const unsigned half) {
  __shared__ e4 smem_p0[WHIR_THREE_POINT_BLOCK_THREADS];
  __shared__ e4 smem_p1[WHIR_THREE_POINT_BLOCK_THREADS];
  __shared__ e4 smem_p2[WHIR_THREE_POINT_BLOCK_THREADS];

  const unsigned tid = threadIdx.x;

  e4 acc0 = e4::ZERO();
  e4 acc1 = e4::ZERO();
  e4 acc2 = e4::ZERO();
  if (tid < half) {
    const e4 ev_lo = load<e4, ld_modifier::cs>(eval, tid);
    const e4 ev_hi = load<e4, ld_modifier::cs>(eval, half + tid);
    const e4 eq_lo = load<e4, ld_modifier::cs>(eq, tid);
    const e4 eq_hi = load<e4, ld_modifier::cs>(eq, half + tid);
    acc0 = e4::mul(ev_lo, eq_lo);
    acc1 = e4::mul(ev_hi, eq_hi);
    acc2 = e4::mul(e4::add(ev_lo, ev_hi), e4::add(eq_lo, eq_hi));
  }
  smem_p0[tid] = acc0;
  smem_p1[tid] = acc1;
  smem_p2[tid] = acc2;
  __syncthreads();

#pragma unroll
  for (unsigned offset = WHIR_THREE_POINT_BLOCK_THREADS / 2; offset > 0; offset >>= 1) {
    if (tid < offset) {
      smem_p0[tid] = e4::add(smem_p0[tid], smem_p0[tid + offset]);
      smem_p1[tid] = e4::add(smem_p1[tid], smem_p1[tid + offset]);
      smem_p2[tid] = e4::add(smem_p2[tid], smem_p2[tid + offset]);
    }
    __syncthreads();
  }

  if (tid == 0) {
    reduce_out[0] = smem_p0[0];
    reduce_out[1] = smem_p1[0];
    reduce_out[2] = smem_p2[0];
  }
}

DEVICE_FORCEINLINE unsigned bitreverse_low_bits(const unsigned value, const unsigned num_bits) { return __brev(value) >> (32 - num_bits); }

DEVICE_FORCEINLINE void partially_evaluate_monomial_form_small_impl(vectorized_e4_matrix_getter<ld_modifier::cg> src, e4 *dst, const e4 z,
                                                                    const unsigned log_count) {
  const int count = 1 << log_count;
  const int gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;

  e4 result{src.get_at_row(gid)};
  const unsigned power = bitreverse_low_bits(gid, log_count);
  const e4 adjustment = e4::pow(z, power);
  dst[gid] = e4::mul(result, adjustment);
}

EXTERN __global__ void ab_partially_evaluate_monomial_form_by_val_small_kernel(vectorized_e4_matrix_getter<ld_modifier::cg> src, e4 *dst, const e4 z,
                                                                               const unsigned log_count) {
  partially_evaluate_monomial_form_small_impl(src, dst, z, log_count);
}

EXTERN __global__ void ab_partially_evaluate_monomial_form_by_ref_small_kernel(vectorized_e4_matrix_getter<ld_modifier::cg> src, e4 *dst, const e4 *z,
                                                                               const unsigned log_count) {
  partially_evaluate_monomial_form_small_impl(src, dst, *z, log_count);
}

// Partially evaluates a polynomial at a single random point using Horner rule applied to bitreversed monomials.
// Output size will be count / VALS_PER_THREAD.
DEVICE_FORCEINLINE void partially_evaluate_monomial_form_impl(vectorized_e4_matrix_getter<ld_modifier::cg> src, e4 *dst, const e4 z,
                                                              const e4 z_chunk_adjustment, const unsigned log_count) {
  constexpr int VALS_PER_THREAD = 32;
  constexpr int BITREV_ORDER[VALS_PER_THREAD] = {0, 16, 8, 24, 4, 20, 12, 28, 2, 18, 10, 26, 6, 22, 14, 30,
                                                 1, 17, 9, 25, 5, 21, 13, 29, 3, 19, 11, 27, 7, 23, 15, 31};

  const int count = 1 << log_count;
  const int gid = blockIdx.x * blockDim.x + threadIdx.x;
  const int gmem_stride = gridDim.x * blockDim.x;

  src.add_row(gid);

  // Horner rule works backwards from highest powers
  e4 result{src.get_at_row(count - gmem_stride)};
#pragma unroll
  for (int i{1}; i < VALS_PER_THREAD; i++) {
    result = e4::mul(result, z);
    result = e4::add(result, src.get_at_row(gmem_stride * BITREV_ORDER[VALS_PER_THREAD - 1 - i]));
  }

  const unsigned power = bitreverse_low_bits(gid, log_count - 5);
  const e4 adjustment = e4::pow(z_chunk_adjustment, power);
  dst[gid] = e4::mul(result, adjustment);
}

EXTERN __global__ void ab_partially_evaluate_monomial_form_by_val_kernel(vectorized_e4_matrix_getter<ld_modifier::cg> src, e4 *dst, const e4 z,
                                                                         const e4 z_chunk_adjustment, const unsigned log_count) {
  partially_evaluate_monomial_form_impl(src, dst, z, z_chunk_adjustment, log_count);
}

EXTERN __global__ void ab_partially_evaluate_monomial_form_by_ref_kernel(vectorized_e4_matrix_getter<ld_modifier::cg> src, e4 *dst, const e4 *z_ref,
                                                                         const e4 *z_chunk_adjustment_ref, const unsigned log_count) {
  partially_evaluate_monomial_form_impl(src, dst, *z_ref, *z_chunk_adjustment_ref, log_count);
}

} // namespace airbender::prover::whir
