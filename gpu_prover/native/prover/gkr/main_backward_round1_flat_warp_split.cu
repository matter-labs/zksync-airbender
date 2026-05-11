#include "flat_backward_continuation.cuh"

__device__ __constant__ e4 ab_gkr_main_layer_claim_point[airbender::prover::gkr::GKR_MAIN_LAYER_CLAIM_POINT_LEN];

namespace airbender::prover::gkr {

// Phase C compact-source unified tiled warp-split round 1 kernel.
// Resolves source pointers via `desc.tables` (per-launch base/log2_stride
// tables) instead of legacy raw per-source structs. The doubled `_compact_`
// in the name disambiguates from the older unified-tiled "compact"
// qualifier (unrelated to Phase C's u16 source encoding).
EXTERN __launch_bounds__(128, 8) __global__
    void ab_gkr_main_round1_flat_constant_compact_unified_compact_e4_kernel(const __grid_constant__ flat_round1_unified_desc_compact desc,
                                                                            const unsigned fold_stride, const unsigned next_layer_size, const e4 *eq_values,
                                                                            e4 *contributions, const unsigned acc_size) {
  constexpr unsigned NUM_WARPS = 4;
  const unsigned lane = threadIdx.x % 32;
  const unsigned warp_id = threadIdx.x / 32;
  const unsigned gid = blockIdx.x * 32 + lane;
  if (gid >= acc_size)
    return;

  e4 c0 = e4::ZERO();
  e4 c1 = e4::ZERO();

  // Constants: no sources involved, independent of tiles.
  flat_round1_compute_unified_compact<e4, false, NUM_WARPS>(desc, 0, desc.num_constant_terms, next_layer_size, gid, warp_id, c0, c1);

  // Per-tile: fold (with conditional sync inside) → compute.
  for (unsigned tile = 0; tile < desc.num_tiles; tile++) {
    flat_round1_tile_fold_compact<e4, NUM_WARPS>(desc, desc.tile_fold_offsets[tile], desc.tile_fold_offsets[tile + 1], fold_stride, next_layer_size, gid,
                                                 warp_id);
    flat_round1_compute_unified_compact<e4, false, NUM_WARPS>(desc, desc.tile_term_offsets[tile], desc.tile_term_offsets[tile + 1], next_layer_size, gid,
                                                              warp_id, c0, c1);
  }

  // Reduce partial c0/c1 across warps via shared memory, one coefficient at a time.
  const e4 eq = load<e4, ld_modifier::cs>(eq_values, gid);
  __shared__ e4 smem[NUM_WARPS - 1][32];

  if (warp_id != 0)
    smem[warp_id - 1][lane] = c0;
  __syncthreads();
  if (warp_id == 0) {
    e4 sum_c0 = c0;
    for (unsigned w = 0; w < NUM_WARPS - 1; w++)
      sum_c0 = e4::add(sum_c0, smem[w][lane]);
    store<e4, st_modifier::cs>(contributions, e4::mul(sum_c0, eq), gid);
  }

  __syncthreads();

  if (warp_id != 0)
    smem[warp_id - 1][lane] = c1;
  __syncthreads();
  if (warp_id == 0) {
    e4 sum_c1 = c1;
    for (unsigned w = 0; w < NUM_WARPS - 1; w++)
      sum_c1 = e4::add(sum_c1, smem[w][lane]);
    store<e4, st_modifier::cs>(contributions + acc_size, e4::mul(sum_c1, eq), gid);
  }
}

} // namespace airbender::prover::gkr
