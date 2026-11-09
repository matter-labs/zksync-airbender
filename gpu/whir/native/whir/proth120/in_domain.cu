#include "../in_domain_shared.cuh"
#include "common.cuh"
#include "primitives/memory.cuh"
#include "primitives/proth120.cuh"
#include "round.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;

namespace airbender::whir {

using namespace in_domain_detail;

constexpr unsigned PR_WHIR_IN_DOMAIN_BLOCK_THREADS = 256;

EXTERN __global__ void ab_pr_whir_in_domain_add_terms_kernel(const u32 *indexes, const pr *challenges, const u32 query_domain_log2, const pr generator,
                                                             pr *weights, pr *points, u32 *exponents, const u32 count) {
  add_terms(indexes, challenges, query_domain_log2, generator, weights, points, exponents, count);
}
EXTERN __global__ void ab_pr_whir_in_domain_prepare_indexes_kernel(const u32 *exponents, const pr *points, const u32 domain_log2, const u32 log_v, u32 *indexes,
                                                                   pr *leaf_points, const u32 count) {
  prepare_indexes<pr, true>(exponents, points, domain_log2, log_v, indexes, leaf_points, count);
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
  accumulate_term_corrections<pr, pr, PR_WHIR_IN_DOMAIN_BLOCK_THREADS>(leaves, leaf_stride, leaf_width, weights, points, count, acc0, acc1, acc2);
  block_reduce_corrections<pr, PR_WHIR_IN_DOMAIN_BLOCK_THREADS>(smem_p0, smem_p1, smem_p2, acc0, acc1, acc2);
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
    fold_term(leaves + static_cast<size_t>(t) * leaf_stride, leaf_width, weights[t], points[t], exponents[t], alpha);
}

} // namespace airbender::whir
