#include "common.cuh"
#include "primitives/field.cuh"
#include "primitives/memory.cuh"
#include "primitives/vectorized.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;
using namespace ::airbender::primitives::vectorized;

namespace airbender::whir {

// Monomial-form fold, LSB binding: the round eliminates variable 0, which is
// bit 0 of the NATURAL-order coefficient index, so the pair is ADJACENT
// (2*gid, 2*gid + 1) and the combination is `c0 + r * c1` -- CPU authority
// `fold_monomial_form`, prover/src/gkr/whir/mod.rs:2674-2714. Out of place:
// thread `gid` writes a cell thread `gid / 2` reads, so the overlap is
// cross-block.
EXTERN __global__ void ab_whir_fold_adjacent_vectorized_e4_kernel(vectorized_e4_matrix_getter<ld_modifier::cg> src,
                                                                  vectorized_e4_matrix_setter<st_modifier::cg> dst, const e4 *challenge,
                                                                  const unsigned half_len) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= half_len)
    return;

  const e4 c0 = src.get_at_row(2 * gid);
  const e4 c1 = src.get_at_row(2 * gid + 1);
  const e4 folded = e4::add(c0, e4::mul(c1, *challenge));
  dst.set_at_row(gid, folded);
}

// LSB binding: the round eliminates coordinate 0, so the pair is ADJACENT
// (2*gid, 2*gid + 1) -- `prover/src/gkr/whir/mod.rs` `fold_evaluation_form` /
// `fold_eq_poly`. The read range [0, 2*half_len) covers the write range
// [0, half_len), and thread `gid` writes a cell thread `gid / 2` reads, so the
// destination is a SEPARATE buffer (cross-block overlap admits no in-place
// form without a global barrier).
EXTERN __global__ void ab_whir_fold_adjacent_e4_kernel(const e4 *src, e4 *dst, const e4 *challenge, const unsigned half_len) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= half_len)
    return;

  const e4 a = load<e4, ld_modifier::cs>(src, 2 * gid);
  const e4 b = load<e4, ld_modifier::cs>(src, 2 * gid + 1);
  const e4 diff = e4::sub(b, a);
  const e4 folded = e4::fma(*challenge, diff, a);
  store<e4, st_modifier::cs>(dst, folded, gid);
}

// Paired (eval_form, eq_poly) adjacent-pair fold sharing a single challenge.
EXTERN __global__ void ab_whir_fold_adjacent_pair_e4_kernel(const e4 *src_a, e4 *dst_a, const e4 *src_b, e4 *dst_b, const e4 *challenge,
                                                            const unsigned half_len) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= half_len)
    return;

  const e4 c = *challenge;
  const e4 a_even = load<e4, ld_modifier::cs>(src_a, 2 * gid);
  const e4 a_odd = load<e4, ld_modifier::cs>(src_a, 2 * gid + 1);
  store<e4, st_modifier::cs>(dst_a, e4::fma(c, e4::sub(a_odd, a_even), a_even), gid);
  const e4 b_even = load<e4, ld_modifier::cs>(src_b, 2 * gid);
  const e4 b_odd = load<e4, ld_modifier::cs>(src_b, 2 * gid + 1);
  store<e4, st_modifier::cs>(dst_b, e4::fma(c, e4::sub(b_odd, b_even), b_even), gid);
}

// WHIR sumcheck three-point partials. Each block stride-reduces its slice of
// [0, half) into three block-local sums; the finalize kernel sums across blocks.
// LSB binding pairs ADJACENT entries, matching `three_point_partial` in
// `prover/src/gkr/whir/mod.rs` (`a.as_chunks::<2>()`):
//   p0 = sum_i eval[2i]   * eq[2i]
//   p1 = sum_i eval[2i+1] * eq[2i+1]
//   p2 = sum_i (eval[2i] + eval[2i+1]) * (eq[2i] + eq[2i+1])
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
    const e4 ev_even = load<e4, ld_modifier::cs>(eval, 2 * i);
    const e4 ev_odd = load<e4, ld_modifier::cs>(eval, 2 * i + 1);
    const e4 eq_even = load<e4, ld_modifier::cs>(eq, 2 * i);
    const e4 eq_odd = load<e4, ld_modifier::cs>(eq, 2 * i + 1);
    acc0 = e4::add(acc0, e4::mul(ev_even, eq_even));
    acc1 = e4::add(acc1, e4::mul(ev_odd, eq_odd));
    acc2 = e4::add(acc2, e4::mul(e4::add(ev_even, ev_odd), e4::add(eq_even, eq_odd)));
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
    const e4 ev_lo = load<e4, ld_modifier::cs>(eval, 2 * tid);
    const e4 ev_hi = load<e4, ld_modifier::cs>(eval, 2 * tid + 1);
    const e4 eq_lo = load<e4, ld_modifier::cs>(eq, 2 * tid);
    const e4 eq_hi = load<e4, ld_modifier::cs>(eq, 2 * tid + 1);
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

constexpr unsigned WHIR_SUM_BLOCK_THREADS = 256;

// One partial per block: out[blockIdx.x] = sum of this block's grid-stride
// slice. A second single-block launch over the partials completes the sum.
EXTERN __global__ void ab_whir_sum_e4_kernel(const e4 *__restrict__ values, const unsigned count, e4 *__restrict__ out) {
  __shared__ e4 smem[WHIR_SUM_BLOCK_THREADS];

  const unsigned tid = threadIdx.x;
  const unsigned stride = gridDim.x * blockDim.x;

  e4 acc = e4::ZERO();
  for (unsigned i = blockIdx.x * blockDim.x + tid; i < count; i += stride)
    acc = e4::add(acc, load<e4, ld_modifier::cs>(values, i));

  smem[tid] = acc;
  __syncthreads();

#pragma unroll
  for (unsigned offset = WHIR_SUM_BLOCK_THREADS / 2; offset > 0; offset >>= 1) {
    if (tid < offset)
      smem[tid] = e4::add(smem[tid], smem[tid + offset]);
    __syncthreads();
  }

  if (tid == 0)
    out[blockIdx.x] = smem[0];
}

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

EXTERN __global__ void ab_partially_evaluate_monomial_form_by_ref_kernel(vectorized_e4_matrix_getter<ld_modifier::cg> src, e4 *dst, const e4 *z_ref,
                                                                         const e4 *z_chunk_adjustment_ref, const unsigned log_count) {
  partially_evaluate_monomial_form_impl(src, dst, *z_ref, *z_chunk_adjustment_ref, log_count);
}

} // namespace airbender::whir
