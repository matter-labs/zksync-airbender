#include "common.cuh"
#include "fold_shared.cuh"
#include "primitives/field.cuh"
#include "primitives/memory.cuh"
#include "primitives/vectorized.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;
using namespace ::airbender::primitives::vectorized;

namespace airbender::whir {

// LSB binding: variable 0 is bit 0 of the NATURAL-order coefficient index. Out
// of place -- thread `gid` writes a cell thread `gid / 2` reads, so no in-place
// form exists without a global barrier.
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

// Out of place -- thread `gid` writes a cell thread `gid / 2` reads
// (cross-block overlap).
EXTERN __global__ void ab_whir_fold_adjacent_e4_kernel(const e4 *src, e4 *dst, const e4 *challenge, const unsigned half_len) {
  whir_detail::fold_adjacent<e4, true>(src, dst, challenge, half_len);
}

// Paired (eval_form, eq_poly) adjacent-pair fold sharing a single challenge.
EXTERN __global__ void ab_whir_fold_adjacent_pair_e4_kernel(const e4 *src_a, e4 *dst_a, const e4 *src_b, e4 *dst_b, const e4 *challenge,
                                                            const unsigned half_len) {
  whir_detail::fold_adjacent_pair<e4>(src_a, dst_a, src_b, dst_b, challenge, half_len);
}

// WHIR sumcheck three-point partials. Each block stride-reduces its slice of
// [0, half) into three block-local sums; the finalize kernel sums across blocks:
//   p0 = sum_i eval[2i]   * eq[2i]
//   p1 = sum_i eval[2i+1] * eq[2i+1]
//   p2 = sum_i (eval[2i] + eval[2i+1]) * (eq[2i] + eq[2i+1])

EXTERN __global__ void ab_whir_three_point_partials_e4_kernel(const e4 *__restrict__ eval, const e4 *__restrict__ eq, e4 *__restrict__ partials,
                                                              const unsigned half) {
  __shared__ e4 smem_p0[256];
  __shared__ e4 smem_p1[256];
  __shared__ e4 smem_p2[256];
  whir_detail::three_point_partials<e4>(eval, eq, partials, half, smem_p0, smem_p1, smem_p2);
}

EXTERN __global__ void ab_whir_three_point_finalize_e4_kernel(const e4 *__restrict__ partials, const unsigned num_blocks, e4 *__restrict__ reduce_out) {
  __shared__ e4 smem_p0[256];
  __shared__ e4 smem_p1[256];
  __shared__ e4 smem_p2[256];
  whir_detail::three_point_finalize<e4>(partials, num_blocks, reduce_out, smem_p0, smem_p1, smem_p2);
}

// Single-launch path for tiny `half` (<= 256-thread block):
// fuses partials + finalize into one block, no partials buffer.
EXTERN __global__ void ab_whir_three_point_combined_e4_kernel(const e4 *__restrict__ eval, const e4 *__restrict__ eq, e4 *__restrict__ reduce_out,
                                                              const unsigned half) {
  __shared__ e4 smem_p0[256];
  __shared__ e4 smem_p1[256];
  __shared__ e4 smem_p2[256];
  whir_detail::three_point_combined<e4>(eval, eq, reduce_out, half, smem_p0, smem_p1, smem_p2);
}

// One partial per block: out[blockIdx.x] = sum of this block's grid-stride
// slice. A second single-block launch over the partials completes the sum.
EXTERN __global__ void ab_whir_sum_e4_kernel(const e4 *__restrict__ values, const unsigned count, e4 *__restrict__ out) {
  __shared__ e4 smem[256];
  whir_detail::sum<e4>(values, count, out, smem);
}

EXTERN __global__ void ab_partially_evaluate_monomial_form_by_ref_small_kernel(vectorized_e4_matrix_getter<ld_modifier::cg> src, e4 *dst, const e4 *z,
                                                                               const unsigned log_count) {
  whir_detail::evaluate_monomial_small(src, dst, *z, log_count);
}

// Thread `gid` owns the coefficients at `gid + k * gmem_stride` for k in
// [0, VALS_PER_THREAD), so its contribution is
// `z^gid * sum_k c_{gid + k * S} * (z^S)^k` -- a Horner rule in `z_stride =
// z^gmem_stride` walking k downwards, scaled by `z^gid`.
// Output size will be count / VALS_PER_THREAD.
EXTERN __global__ void ab_partially_evaluate_monomial_form_by_ref_kernel(vectorized_e4_matrix_getter<ld_modifier::cg> src, e4 *dst, const e4 *z_ref,
                                                                         const e4 *z_stride_ref, const unsigned log_count) {
  whir_detail::evaluate_monomial(src, dst, *z_ref, *z_stride_ref, log_count);
}

} // namespace airbender::whir
