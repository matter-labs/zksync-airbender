#include "flat_backward_continuation.cuh"

namespace airbender::prover::gkr {

// Phase C compact-source unified tiled warp-split round 3+ kernel
// (non-explicit form). Per-tile fold -> sync -> compute. All term types
// mixed in a single array sorted by source-group tile affinity. Grid
// covers acc_size / 32 blocks (4 warps share 32 gids). Resolves source
// pointers via `desc.tables` + per-step offsets baked into the compact
// descriptor instead of legacy raw pointers.
EXTERN __launch_bounds__(128, 8) __global__
    void ab_gkr_main_round3_flat_constant_unified_compact_e4_kernel(const __grid_constant__ flat_continuation_unified_desc_compact desc,
                                                                     const e4 *folding_challenge, const unsigned fold_stride, const unsigned next_layer_size,
                                                                     const e4 *eq_values, e4 *contributions, const unsigned acc_size) {
  constexpr unsigned NUM_WARPS = 4;
  const unsigned lane = threadIdx.x % 32;
  const unsigned warp_id = threadIdx.x / 32;
  const unsigned gid = blockIdx.x * 32 + lane;
  if (gid >= acc_size)
    return;

  const e4 challenge = load<e4, ld_modifier::ca>(folding_challenge, 0);
  e4 c0 = e4::ZERO();
  e4 c1 = e4::ZERO();

  flat_cont_compute_unified_compact<e4, false, NUM_WARPS>(desc, 0, desc.num_constant_terms, next_layer_size, gid, warp_id, c0, c1);

  for (unsigned tile = 0; tile < desc.num_tiles; tile++) {
    flat_cont_tile_fold_compact<e4, NUM_WARPS>(desc, desc.tile_fold_offsets[tile], desc.tile_fold_offsets[tile + 1], challenge, fold_stride, next_layer_size, gid,
                                                warp_id);
    flat_cont_compute_unified_compact<e4, false, NUM_WARPS>(desc, desc.tile_term_offsets[tile], desc.tile_term_offsets[tile + 1], next_layer_size, gid, warp_id,
                                                             c0, c1);
  }

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

// Phase C compact-source unified tiled warp-split round 3+ kernel (explicit form).
EXTERN __launch_bounds__(128, 8) __global__
    void ab_gkr_main_round3_flat_constant_explicit_unified_compact_e4_kernel(const __grid_constant__ flat_continuation_unified_desc_compact desc,
                                                                              const e4 *folding_challenge, const unsigned fold_stride,
                                                                              const unsigned next_layer_size, const e4 *eq_values, e4 *contributions,
                                                                              const unsigned acc_size) {
  constexpr unsigned NUM_WARPS = 4;
  const unsigned lane = threadIdx.x % 32;
  const unsigned warp_id = threadIdx.x / 32;
  const unsigned gid = blockIdx.x * 32 + lane;
  if (gid >= acc_size)
    return;

  const e4 challenge = load<e4, ld_modifier::ca>(folding_challenge, 0);
  e4 c0 = e4::ZERO();
  e4 c1 = e4::ZERO();

  flat_cont_compute_unified_compact<e4, true, NUM_WARPS>(desc, 0, desc.num_constant_terms, next_layer_size, gid, warp_id, c0, c1);

  for (unsigned tile = 0; tile < desc.num_tiles; tile++) {
    flat_cont_tile_fold_compact<e4, NUM_WARPS>(desc, desc.tile_fold_offsets[tile], desc.tile_fold_offsets[tile + 1], challenge, fold_stride, next_layer_size, gid,
                                                warp_id);
    flat_cont_compute_unified_compact<e4, true, NUM_WARPS>(desc, desc.tile_term_offsets[tile], desc.tile_term_offsets[tile + 1], next_layer_size, gid, warp_id,
                                                            c0, c1);
  }

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
