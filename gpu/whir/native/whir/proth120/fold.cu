#include "common.cuh"
#include "primitives/proth120.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;

namespace airbender::whir {

EXTERN __global__ void ab_pr_whir_fold_adjacent_kernel(const pr *src, pr *dst, const pr *challenge, const unsigned half_len) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= half_len)
    return;

  const pr a = load<pr, ld_modifier::cs>(src, 2 * gid);
  const pr b = load<pr, ld_modifier::cs>(src, 2 * gid + 1);
  const pr folded = pr::fma(*challenge, b, a);
  store<pr, st_modifier::cs>(dst, folded, gid);
}

EXTERN __global__ void ab_pr_whir_fold_adjacent_pair_kernel(const pr *src_a, pr *dst_a, const pr *src_b, pr *dst_b, const pr *challenge,
                                                            const unsigned half_len) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= half_len)
    return;

  const pr c = *challenge;
  const pr a_even = load<pr, ld_modifier::cs>(src_a, 2 * gid);
  const pr a_odd = load<pr, ld_modifier::cs>(src_a, 2 * gid + 1);
  store<pr, st_modifier::cs>(dst_a, pr::fma(c, pr::sub(a_odd, a_even), a_even), gid);
  const pr b_even = load<pr, ld_modifier::cs>(src_b, 2 * gid);
  const pr b_odd = load<pr, ld_modifier::cs>(src_b, 2 * gid + 1);
  store<pr, st_modifier::cs>(dst_b, pr::fma(c, pr::sub(b_odd, b_even), b_even), gid);
}

constexpr unsigned WHIR_THREE_POINT_BLOCK_THREADS = 256;

EXTERN __global__ void ab_pr_whir_three_point_partials_kernel(const pr *__restrict__ eval, const pr *__restrict__ eq, pr *__restrict__ partials,
                                                              const unsigned half) {
  __shared__ pr smem_p0[WHIR_THREE_POINT_BLOCK_THREADS];
  __shared__ pr smem_p1[WHIR_THREE_POINT_BLOCK_THREADS];
  __shared__ pr smem_p2[WHIR_THREE_POINT_BLOCK_THREADS];

  const unsigned tid = threadIdx.x;
  const unsigned stride = gridDim.x * blockDim.x;

  pr acc0 = pr::ZERO();
  pr acc1 = pr::ZERO();
  pr acc2 = pr::ZERO();

  for (unsigned i = blockIdx.x * blockDim.x + tid; i < half; i += stride) {
    const pr ev_even = load<pr, ld_modifier::cs>(eval, 2 * i);
    const pr ev_odd = load<pr, ld_modifier::cs>(eval, 2 * i + 1);
    const pr eq_even = load<pr, ld_modifier::cs>(eq, 2 * i);
    const pr eq_odd = load<pr, ld_modifier::cs>(eq, 2 * i + 1);
    acc0 = pr::add(acc0, pr::mul(ev_even, eq_even));
    acc1 = pr::add(acc1, pr::mul(ev_odd, eq_odd));
    acc2 = pr::add(acc2, pr::mul(pr::add(ev_even, ev_odd), pr::add(eq_even, eq_odd)));
  }

  smem_p0[tid] = acc0;
  smem_p1[tid] = acc1;
  smem_p2[tid] = acc2;
  __syncthreads();

#pragma unroll
  for (unsigned offset = WHIR_THREE_POINT_BLOCK_THREADS / 2; offset > 0; offset >>= 1) {
    if (tid < offset) {
      smem_p0[tid] = pr::add(smem_p0[tid], smem_p0[tid + offset]);
      smem_p1[tid] = pr::add(smem_p1[tid], smem_p1[tid + offset]);
      smem_p2[tid] = pr::add(smem_p2[tid], smem_p2[tid + offset]);
    }
    __syncthreads();
  }

  if (tid == 0) {
    partials[blockIdx.x * 3u + 0u] = smem_p0[0];
    partials[blockIdx.x * 3u + 1u] = smem_p1[0];
    partials[blockIdx.x * 3u + 2u] = smem_p2[0];
  }
}

EXTERN __global__ void ab_pr_whir_three_point_finalize_kernel(const pr *__restrict__ partials, const unsigned num_blocks, pr *__restrict__ reduce_out) {
  __shared__ pr smem_p0[WHIR_THREE_POINT_BLOCK_THREADS];
  __shared__ pr smem_p1[WHIR_THREE_POINT_BLOCK_THREADS];
  __shared__ pr smem_p2[WHIR_THREE_POINT_BLOCK_THREADS];

  const unsigned tid = threadIdx.x;

  pr acc0 = pr::ZERO();
  pr acc1 = pr::ZERO();
  pr acc2 = pr::ZERO();
  for (unsigned b = tid; b < num_blocks; b += WHIR_THREE_POINT_BLOCK_THREADS) {
    acc0 = pr::add(acc0, partials[b * 3u + 0u]);
    acc1 = pr::add(acc1, partials[b * 3u + 1u]);
    acc2 = pr::add(acc2, partials[b * 3u + 2u]);
  }

  smem_p0[tid] = acc0;
  smem_p1[tid] = acc1;
  smem_p2[tid] = acc2;
  __syncthreads();

#pragma unroll
  for (unsigned offset = WHIR_THREE_POINT_BLOCK_THREADS / 2; offset > 0; offset >>= 1) {
    if (tid < offset) {
      smem_p0[tid] = pr::add(smem_p0[tid], smem_p0[tid + offset]);
      smem_p1[tid] = pr::add(smem_p1[tid], smem_p1[tid + offset]);
      smem_p2[tid] = pr::add(smem_p2[tid], smem_p2[tid + offset]);
    }
    __syncthreads();
  }

  if (tid == 0) {
    reduce_out[0] = smem_p0[0];
    reduce_out[1] = smem_p1[0];
    reduce_out[2] = smem_p2[0];
  }
}

EXTERN __global__ void ab_pr_whir_three_point_combined_kernel(const pr *__restrict__ eval, const pr *__restrict__ eq, pr *__restrict__ reduce_out,
                                                              const unsigned half) {
  __shared__ pr smem_p0[WHIR_THREE_POINT_BLOCK_THREADS];
  __shared__ pr smem_p1[WHIR_THREE_POINT_BLOCK_THREADS];
  __shared__ pr smem_p2[WHIR_THREE_POINT_BLOCK_THREADS];

  const unsigned tid = threadIdx.x;

  pr acc0 = pr::ZERO();
  pr acc1 = pr::ZERO();
  pr acc2 = pr::ZERO();
  if (tid < half) {
    const pr ev_lo = load<pr, ld_modifier::cs>(eval, 2 * tid);
    const pr ev_hi = load<pr, ld_modifier::cs>(eval, 2 * tid + 1);
    const pr eq_lo = load<pr, ld_modifier::cs>(eq, 2 * tid);
    const pr eq_hi = load<pr, ld_modifier::cs>(eq, 2 * tid + 1);
    acc0 = pr::mul(ev_lo, eq_lo);
    acc1 = pr::mul(ev_hi, eq_hi);
    acc2 = pr::mul(pr::add(ev_lo, ev_hi), pr::add(eq_lo, eq_hi));
  }
  smem_p0[tid] = acc0;
  smem_p1[tid] = acc1;
  smem_p2[tid] = acc2;
  __syncthreads();

#pragma unroll
  for (unsigned offset = WHIR_THREE_POINT_BLOCK_THREADS / 2; offset > 0; offset >>= 1) {
    if (tid < offset) {
      smem_p0[tid] = pr::add(smem_p0[tid], smem_p0[tid + offset]);
      smem_p1[tid] = pr::add(smem_p1[tid], smem_p1[tid + offset]);
      smem_p2[tid] = pr::add(smem_p2[tid], smem_p2[tid + offset]);
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

EXTERN __global__ void ab_pr_whir_sum_kernel(const pr *__restrict__ values, const unsigned count, pr *__restrict__ out) {
  __shared__ pr smem[WHIR_SUM_BLOCK_THREADS];

  const unsigned tid = threadIdx.x;
  const unsigned stride = gridDim.x * blockDim.x;

  pr acc = pr::ZERO();
  for (unsigned i = blockIdx.x * blockDim.x + tid; i < count; i += stride)
    acc = pr::add(acc, load<pr, ld_modifier::cs>(values, i));

  smem[tid] = acc;
  __syncthreads();

#pragma unroll
  for (unsigned offset = WHIR_SUM_BLOCK_THREADS / 2; offset > 0; offset >>= 1) {
    if (tid < offset)
      smem[tid] = pr::add(smem[tid], smem[tid + offset]);
    __syncthreads();
  }

  if (tid == 0)
    out[blockIdx.x] = smem[0];
}

DEVICE_FORCEINLINE void partially_evaluate_monomial_form_small_impl(const pr *src, pr *dst, const pr z, const unsigned log_count) {
  const int count = 1 << log_count;
  const int gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;

  pr result{load<pr, ld_modifier::cs>(src, gid)};
  const pr adjustment = pr::pow(z, gid);
  dst[gid] = pr::mul(result, adjustment);
}

EXTERN __global__ void ab_pr_whir_partially_evaluate_monomials_small_kernel(const pr *src, pr *dst, const pr *z, const unsigned log_count) {
  partially_evaluate_monomial_form_small_impl(src, dst, *z, log_count);
}

DEVICE_FORCEINLINE void partially_evaluate_monomial_form_impl(const pr *src, pr *dst, const pr z, const pr z_stride, const unsigned log_count) {
  constexpr int VALS_PER_THREAD = 32;

  const int count = 1 << log_count;
  const int gid = blockIdx.x * blockDim.x + threadIdx.x;
  const int gmem_stride = gridDim.x * blockDim.x;
  if (gid >= count / VALS_PER_THREAD)
    return;

  src += gid;

  pr result{load<pr, ld_modifier::cs>(src, gmem_stride * (VALS_PER_THREAD - 1))};
#pragma unroll
  for (int k{VALS_PER_THREAD - 2}; k >= 0; k--) {
    result = pr::mul(result, z_stride);
    result = pr::add(result, load<pr, ld_modifier::cs>(src, gmem_stride * k));
  }

  const pr adjustment = pr::pow(z, gid);
  dst[gid] = pr::mul(result, adjustment);
}

EXTERN __global__ void ab_pr_whir_partially_evaluate_monomials_kernel(const pr *src, pr *dst, const pr *z_ref, const pr *z_stride_ref,
                                                                      const unsigned log_count) {
  partially_evaluate_monomial_form_impl(src, dst, *z_ref, *z_stride_ref, log_count);
}

} // namespace airbender::whir
