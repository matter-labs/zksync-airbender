#include "gkr/baby_bear/backward/window_dr/evaluate.cuh"
#include "gkr/backward/window_dr/continuation.cuh"

namespace airbender::gkr::backward {

static_assert(sizeof(dr_window_cell_pair<e4>) == 32 && alignof(dr_window_cell_pair<e4>) == 32, "DR continuation pair must be one aligned 256-bit transaction");

// Fold all three preceding coordinates before publishing the input pairs.
DEVICE_FORCEINLINE dr_window_cell_pair<e4> dr_window_fold_depth3_pair(const gkr_dr_cont_window3_desc &desc, const e4 *source, const size_t output_pair,
                                                                      const bool active) {
  const e4 c0 = active ? load<e4, ld_modifier::cs>(desc.claim_point, desc.start_round - 3u) : e4::ZERO();
  const e4 c1 = active ? load<e4, ld_modifier::cs>(desc.claim_point, desc.start_round - 2u) : e4::ZERO();
  const e4 c2 = active ? load<e4, ld_modifier::cs>(desc.claim_point, desc.start_round - 1u) : e4::ZERO();
  dr_window_cell_pair<e4> level1[4];
#pragma unroll
  for (u32 pair = 0; pair < 4; ++pair) {
    const size_t leaf_pair = (output_pair << 3) + 2u * pair;
    const auto zero = dr_window_load_pair_guarded(source, leaf_pair, active);
    const auto one = dr_window_load_pair_guarded(source, leaf_pair + 1u, active);
    level1[pair] = dr_window_pair_fold(zero, one, c0);
  }
  const auto level2_0 = dr_window_pair_fold(level1[0], level1[1], c1);
  const auto level2_1 = dr_window_pair_fold(level1[2], level1[3], c1);
  return dr_window_pair_fold(level2_0, level2_1, c2);
}

EXTERN __global__ __launch_bounds__(BWD_WINDOW_BLOCK_THREADS, 2) void ab_gkr_dr_cont_window3_kernel(const __grid_constant__ gkr_dr_cont_window3_desc desc) {
  const u32 slot = dr_cont_dense_slot(desc.batch.enabled_mask, blockIdx.y);
  dr_cont_selected_slot_prologue<e4>(desc, slot);
  __syncthreads();
  const size_t tile_slot = static_cast<size_t>(blockIdx.y) * gridDim.x + blockIdx.x;
  dr_window_evaluate(desc, 1u << slot, tile_slot);
}

} // namespace airbender::gkr::backward
