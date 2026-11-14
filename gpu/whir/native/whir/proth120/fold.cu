#include "../fold_shared.cuh"
#include "common.cuh"
#include "primitives/proth120.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;

namespace airbender::whir {

EXTERN __global__ void ab_pr_whir_fold_adjacent_kernel(const pr *src, pr *dst, const pr *challenge, const unsigned half_len) {
  whir_detail::fold_adjacent<pr, false>(src, dst, challenge, half_len);
}

EXTERN __global__ void ab_pr_whir_fold_adjacent_pair_kernel(const pr *src_a, pr *dst_a, const pr *src_b, pr *dst_b, const pr *challenge,
                                                            const unsigned half_len) {
  whir_detail::fold_adjacent_pair<pr>(src_a, dst_a, src_b, dst_b, challenge, half_len);
}

EXTERN __global__ void ab_pr_whir_three_point_partials_kernel(const pr *__restrict__ eval, const pr *__restrict__ eq, pr *__restrict__ partials,
                                                              const unsigned half) {
  __shared__ pr smem_p0[256];
  __shared__ pr smem_p1[256];
  __shared__ pr smem_p2[256];
  whir_detail::three_point_partials<pr>(eval, eq, partials, half, smem_p0, smem_p1, smem_p2);
}

EXTERN __global__ void ab_pr_whir_three_point_finalize_kernel(const pr *__restrict__ partials, const unsigned num_blocks, pr *__restrict__ reduce_out) {
  __shared__ pr smem_p0[256];
  __shared__ pr smem_p1[256];
  __shared__ pr smem_p2[256];
  whir_detail::three_point_finalize<pr>(partials, num_blocks, reduce_out, smem_p0, smem_p1, smem_p2);
}

EXTERN __global__ void ab_pr_whir_three_point_combined_kernel(const pr *__restrict__ eval, const pr *__restrict__ eq, pr *__restrict__ reduce_out,
                                                              const unsigned half) {
  __shared__ pr smem_p0[256];
  __shared__ pr smem_p1[256];
  __shared__ pr smem_p2[256];
  whir_detail::three_point_combined<pr>(eval, eq, reduce_out, half, smem_p0, smem_p1, smem_p2);
}

EXTERN __global__ void ab_pr_whir_sum_kernel(const pr *__restrict__ values, const unsigned count, pr *__restrict__ out) {
  __shared__ pr smem[256];
  whir_detail::sum<pr>(values, count, out, smem);
}

EXTERN __global__ void ab_pr_whir_partially_evaluate_monomials_small_kernel(const pr *src, pr *dst, const pr *z, const unsigned log_count) {
  whir_detail::evaluate_monomial_small(whir_detail::flat_coefficients<pr>{src}, dst, *z, log_count);
}

EXTERN __global__ void ab_pr_whir_partially_evaluate_monomials_kernel(const pr *src, pr *dst, const pr *z_ref, const pr *z_stride_ref,
                                                                      const unsigned log_count) {
  whir_detail::evaluate_monomial(whir_detail::flat_coefficients<pr>{src}, dst, *z_ref, *z_stride_ref, log_count);
}

} // namespace airbender::whir
