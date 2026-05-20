// Warp-partial backward round-0 kernel — warp-reduce + full eq per row.
//
// Fuses the round-0 term compute + eq mul + per-warp reduce into a single
// kernel that writes one (c0, c1) partial per warp instead of one per acc
// row. The fused tail (`mega_finalize` over the per-warp partials)
// consumes `acc_size / 32` partial pairs.

#include "../support/eq_inline.cuh"
#include "../support/kernel_helpers.cuh"
#include "flat.cuh"

namespace airbender::prover::gkr::backward {

EXTERN __launch_bounds__(128, 8) __global__ void ab_gkr_main_round0_flat_constant_compact_warp_partial_e4_kernel(
    const __grid_constant__ flat_round0_static_desc_compact desc, const e4 *eq_low, const __grid_constant__ gkr_eq_sizes eq_sizes, e4 *__restrict__ partials,
    const unsigned acc_size) {
  const unsigned tid = threadIdx.x;
  const unsigned lane = tid & 31u;
  const unsigned warp_in_block = tid >> 5;
  const unsigned warps_per_block = blockDim.x / 32u;
  const unsigned gid = blockIdx.x * blockDim.x + tid;

  e4 c0 = e4::ZERO();
  e4 c1 = e4::ZERO();
  if (gid < acc_size) {
    flat_round0_compute_constant_compact_c0_c1<e4>(desc, acc_size, gid, c0, c1);
    const e4 eq = gkr_compute_eq_inline<e4>(eq_low, eq_sizes, gid);
    c0 = e4::mul(c0, eq);
    c1 = e4::mul(c1, eq);
  }

  // Warp shfl_xor reduce — 5 rounds collapse the 32 lanes' c0/c1 into lane 0.
  c0 = ::airbender::prover::gkr::gkr_trace_holder_partials_warp_reduce_sum<e4>(c0);
  c1 = ::airbender::prover::gkr::gkr_trace_holder_partials_warp_reduce_sum<e4>(c1);

  if (lane == 0) {
    const unsigned warp_global = blockIdx.x * warps_per_block + warp_in_block;
    partials[warp_global * 2u + 0u] = c0;
    partials[warp_global * 2u + 1u] = c1;
  }
}

} // namespace airbender::prover::gkr::backward
