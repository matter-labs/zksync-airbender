// Warp-partial backward continuation kernel, round 2.
// Same shape as `round1_flat_warp_partial.cu`; see comments there.

#include "continuation.cuh"

namespace airbender::prover::gkr::backward {

EXTERN __launch_bounds__(128, 8) __global__ void ab_gkr_main_round2_flat_constant_compact_unified_compact_warp_partial_e4_kernel(
    const __grid_constant__ flat_round2_unified_desc_compact desc, const unsigned fold_stride, const unsigned next_layer_size, const e4 *eq_low,
    const __grid_constant__ gkr_eq_sizes eq_sizes, e4 *partials, const unsigned acc_size) {
  constexpr unsigned NUM_WARPS = 4;
  const unsigned lane = threadIdx.x % 32;
  const unsigned warp_id = threadIdx.x / 32;
  const unsigned gid = blockIdx.x * 32 + lane;
  if (gid >= acc_size)
    return;

  e4 c0 = e4::ZERO();
  e4 c1 = e4::ZERO();
  flat_round2_accumulate_unified_compact<e4, NUM_WARPS>(desc, fold_stride, next_layer_size, gid, warp_id, c0, c1);

  __shared__ e4 smem[NUM_WARPS - 1][32];
  flat_store_unified_partials_warp_reduce<e4, NUM_WARPS>(smem, eq_low, eq_sizes, partials, gid, lane, warp_id, c0, c1);
}

} // namespace airbender::prover::gkr::backward
