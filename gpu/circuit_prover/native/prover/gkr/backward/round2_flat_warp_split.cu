#include "continuation.cuh"

__device__ __constant__ e4 ab_gkr_round2_challenges[3];

namespace airbender::prover::gkr::backward {

EXTERN __global__ void ab_gkr_round2_challenges_prelude(const e4 *folding_challenges, e4 *staging) { stage_round2_challenges(folding_challenges, staging); }

// Compact-source unified tiled warp-split round 2 kernel.
// Per-tile fold -> sync -> compute. All term types mixed in a single
// array sorted by source-group tile affinity. Grid covers acc_size / 32
// blocks (4 warps share 32 gids). Resolves source pointers via
// `desc.tables` instead of raw per-source structs.
EXTERN __launch_bounds__(128, 8) __global__
    void ab_gkr_main_round2_flat_constant_compact_unified_compact_e4_kernel(const __grid_constant__ flat_round2_unified_desc_compact desc,
                                                                            const unsigned fold_stride, const unsigned next_layer_size, const e4 *eq_low,
                                                                            const __grid_constant__ gkr_eq_sizes eq_sizes, e4 *contributions,
                                                                            const unsigned acc_size) {
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
  flat_store_unified_contributions<e4, NUM_WARPS>(smem, eq_low, eq_sizes, contributions, acc_size, gid, lane, warp_id, c0, c1);
}

} // namespace airbender::prover::gkr::backward
