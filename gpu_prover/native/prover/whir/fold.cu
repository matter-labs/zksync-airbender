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
                                                                    vectorized_e4_matrix_setter<st_modifier::cg> dst,
                                                                    const e4 *challenge,
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

DEVICE_FORCEINLINE unsigned bitreverse_low_bits(const unsigned value, const unsigned num_bits) { return __brev(value) >> (32 - num_bits); }

DEVICE_FORCEINLINE void partially_evaluate_monomial_form_small_impl(vectorized_e4_matrix_getter<ld_modifier::cg> src,
                                                                    e4 *dst,
                                                                    const e4 z,
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

EXTERN __global__ void ab_partially_evaluate_monomial_form_by_val_small_kernel(vectorized_e4_matrix_getter<ld_modifier::cg> src,
                                                                               e4 *dst,
                                                                               const e4 z,
                                                                               const unsigned log_count) {
  partially_evaluate_monomial_form_small_impl(src, dst, z, log_count);
}

EXTERN __global__ void ab_partially_evaluate_monomial_form_by_ref_small_kernel(vectorized_e4_matrix_getter<ld_modifier::cg> src,
                                                                               e4 *dst,
                                                                               const e4 *z,
                                                                               const unsigned log_count) {
  partially_evaluate_monomial_form_small_impl(src, dst, *z, log_count);
}

// Partially evaluates a polynomial at a single random point using Horner rule applied to bitreversed monomials.
// Output size will be count / VALS_PER_THREAD.
DEVICE_FORCEINLINE void partially_evaluate_monomial_form_impl(vectorized_e4_matrix_getter<ld_modifier::cg> src,
                                                              e4 *dst,
                                                              const e4 z,
                                                              const e4 z_chunk_adjustment,
                                                              const unsigned log_count) {
  constexpr int VALS_PER_THREAD = 32;
  constexpr int BITREV_ORDER[VALS_PER_THREAD] =
      {0, 16, 8, 24, 4, 20, 12, 28, 2, 18, 10, 26, 6, 22, 14, 30, 1, 17, 9, 25, 5, 21, 13, 29, 3, 19, 11, 27, 7, 23, 15, 31};

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

EXTERN __global__ void ab_partially_evaluate_monomial_form_by_val_kernel(vectorized_e4_matrix_getter<ld_modifier::cg> src,
                                                                         e4 *dst,
                                                                         const e4 z,
                                                                         const e4 z_chunk_adjustment,
                                                                         const unsigned log_count) {
  partially_evaluate_monomial_form_impl(src, dst, z, z_chunk_adjustment, log_count);
}

EXTERN __global__ void ab_partially_evaluate_monomial_form_by_ref_kernel(vectorized_e4_matrix_getter<ld_modifier::cg> src,
                                                                         e4 *dst,
                                                                         const e4 *z_ref,
                                                                         const e4 *z_chunk_adjustment_ref,
                                                                         const unsigned log_count) {
  partially_evaluate_monomial_form_impl(src, dst, *z_ref, *z_chunk_adjustment_ref, log_count);
}

} // namespace airbender::prover::whir
