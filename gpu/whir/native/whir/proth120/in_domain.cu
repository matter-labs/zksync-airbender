#include "common.cuh"
#include "primitives/memory.cuh"
#include "primitives/proth120.cuh"
#include "round.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;

namespace airbender::whir {

constexpr unsigned PR_WHIR_IN_DOMAIN_BLOCK_THREADS = 256;

EXTERN __global__ void ab_pr_whir_in_domain_add_terms_kernel(const u32 *indexes, const pr *challenges, const u32 query_domain_log2, const pr generator,
                                                             pr *weights, pr *points, u32 *exponents, const u32 count) {
  const u32 gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;
  const u32 index = indexes[gid];
  weights[gid] = challenges[gid];
  points[gid] = pr::pow(generator, index);
  exponents[gid] = query_domain_log2 == 0 ? 0u : index << (32 - query_domain_log2);
}

EXTERN __global__ void ab_pr_whir_in_domain_prepare_indexes_kernel(const u32 *exponents, const pr *points, const u32 domain_log2, const u32 log_v, u32 *indexes,
                                                                   pr *leaf_points, const u32 count) {
  const u32 gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;
  // exponents are fractions of 2^32; a 2^33 domain embeds them with one more bit
  const u64 e = domain_log2 == 0 ? 0 : (static_cast<u64>(exponents[gid]) << 32) >> (64 - domain_log2);
  const u32 leaves_log2 = domain_log2 - log_v;
  indexes[gid] = static_cast<u32>(e & ((u64{1} << leaves_log2) - 1));
  pr y = points[gid];
  for (u32 i = 0; i < log_v; i++)
    y = pr::sqr(y);
  leaf_points[gid] = y;
}

DEVICE_FORCEINLINE void pr_accumulate_term_corrections(const pr *leaves, const u32 leaf_stride, const u32 leaf_width, const pr *weights, const pr *points,
                                                       const u32 count, pr &acc0, pr &acc1, pr &acc2) {
  const u32 pairs = leaf_width >> 1;
  for (u32 t = threadIdx.x; t < count; t += PR_WHIR_IN_DOMAIN_BLOCK_THREADS) {
    const pr *leaf = leaves + static_cast<size_t>(t) * leaf_stride;
    const pr rho = points[t];
    const pr rho_sqr = pr::sqr(rho);
    pr even = leaf[2 * (pairs - 1)];
    pr odd = leaf[2 * (pairs - 1) + 1];
    for (u32 j = pairs - 1; j-- > 0;) {
      even = pr::fma(even, rho_sqr, leaf[2 * j]);
      odd = pr::fma(odd, rho_sqr, leaf[2 * j + 1]);
    }
    const pr w = weights[t];
    acc0 = pr::add(acc0, pr::mul(pr::mul(w, pr::sub(pr::ONE(), rho)), even));
    acc1 = pr::add(acc1, pr::mul(pr::mul(w, rho), pr::add(even, odd)));
    acc2 = pr::add(acc2, pr::mul(w, pr::add(pr::dbl(even), odd)));
  }
}

DEVICE_FORCEINLINE void pr_block_reduce_corrections(pr *smem_p0, pr *smem_p1, pr *smem_p2, const pr acc0, const pr acc1, const pr acc2) {
  const u32 tid = threadIdx.x;
  smem_p0[tid] = acc0;
  smem_p1[tid] = acc1;
  smem_p2[tid] = acc2;
  __syncthreads();
#pragma unroll
  for (u32 offset = PR_WHIR_IN_DOMAIN_BLOCK_THREADS / 2; offset > 0; offset >>= 1) {
    if (tid < offset) {
      smem_p0[tid] = pr::add(smem_p0[tid], smem_p0[tid + offset]);
      smem_p1[tid] = pr::add(smem_p1[tid], smem_p1[tid + offset]);
      smem_p2[tid] = pr::add(smem_p2[tid], smem_p2[tid + offset]);
    }
    __syncthreads();
  }
}

DEVICE_FORCEINLINE void pr_fold_term(pr *leaf, const u32 leaf_width, pr &weight, pr &point, u32 &exponent, const pr alpha) {
  const u32 pairs = leaf_width >> 1;
  for (u32 j = 0; j < pairs; j++) {
    const pr a = leaf[2 * j];
    const pr b = leaf[2 * j + 1];
    leaf[j] = pr::fma(alpha, b, a);
  }
  const pr rho = point;
  weight = pr::mul(weight, pr::fma(alpha, pr::sub(pr::dbl(rho), pr::ONE()), pr::sub(pr::ONE(), rho)));
  point = pr::sqr(rho);
  exponent <<= 1;
}

EXTERN __launch_bounds__(PR_WHIR_IN_DOMAIN_BLOCK_THREADS) __global__
    void ab_pr_whir_in_domain_correct_update_and_fold_kernel(pr *leaves, const u32 leaf_stride, const u32 leaf_width, pr *weights, pr *points, u32 *exponents,
                                                             pr *reductions, u8 *seed_io, pr *coeffs_out, pr *challenge_out, const u32 count) {
  __shared__ pr smem_p0[PR_WHIR_IN_DOMAIN_BLOCK_THREADS];
  __shared__ pr smem_p1[PR_WHIR_IN_DOMAIN_BLOCK_THREADS];
  __shared__ pr smem_p2[PR_WHIR_IN_DOMAIN_BLOCK_THREADS];
  __shared__ pr smem_alpha;
  const u32 tid = threadIdx.x;
  pr acc0 = pr::ZERO();
  pr acc1 = pr::ZERO();
  pr acc2 = pr::ZERO();
  pr_accumulate_term_corrections(leaves, leaf_stride, leaf_width, weights, points, count, acc0, acc1, acc2);
  pr_block_reduce_corrections(smem_p0, smem_p1, smem_p2, acc0, acc1, acc2);
  if (tid == 0) {
    reductions[0] = pr::add(reductions[0], smem_p0[0]);
    reductions[1] = pr::add(reductions[1], smem_p1[0]);
    reductions[2] = pr::add(reductions[2], smem_p2[0]);
    pr_whir_round_update_inline(reductions, seed_io, coeffs_out, challenge_out);
    smem_alpha = *challenge_out;
  }
  __syncthreads();
  const pr alpha = smem_alpha;
  for (u32 t = tid; t < count; t += PR_WHIR_IN_DOMAIN_BLOCK_THREADS)
    pr_fold_term(leaves + static_cast<size_t>(t) * leaf_stride, leaf_width, weights[t], points[t], exponents[t], alpha);
}

} // namespace airbender::whir
