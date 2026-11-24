#include "gkr/backward/window_dr/continuation.cuh"
#include "gkr/proth120/backward/window_dr/evaluate_pr.cuh"

namespace airbender::gkr::proth120::backward {

static_assert(sizeof(pr_dr_bwd::dr_window_cell_pair<pr>) == 32 && alignof(pr_dr_bwd::dr_window_cell_pair<pr>) == 32,
              "Proth120 DR continuation pair must be one 256-bit transaction");

DEVICE_FORCEINLINE pr_dr_bwd::dr_window_cell_pair<pr> dr_window_fold_depth3_pair(const pr_dr_window_desc &desc, const pr *source, const size_t output_pair,
                                                                                 const bool active) {
  const pr c0 = active ? load<pr, ld_modifier::cs>(desc.claim_point, desc.start_round - 3u) : pr::ZERO();
  const pr c1 = active ? load<pr, ld_modifier::cs>(desc.claim_point, desc.start_round - 2u) : pr::ZERO();
  const pr c2 = active ? load<pr, ld_modifier::cs>(desc.claim_point, desc.start_round - 1u) : pr::ZERO();
  pr_dr_bwd::dr_window_cell_pair<pr> level2[2];
#pragma unroll
  for (u32 half = 0; half < 2; ++half) {
    const size_t leaf_pair = (output_pair << 3) + 4u * half;
    const auto first = pr_dr_bwd::dr_window_pair_fold(pr_dr_bwd::dr_window_load_pair_guarded(source, leaf_pair, active),
                                                      pr_dr_bwd::dr_window_load_pair_guarded(source, leaf_pair + 1u, active), c0);
    const auto second = pr_dr_bwd::dr_window_pair_fold(pr_dr_bwd::dr_window_load_pair_guarded(source, leaf_pair + 2u, active),
                                                       pr_dr_bwd::dr_window_load_pair_guarded(source, leaf_pair + 3u, active), c0);
    level2[half] = pr_dr_bwd::dr_window_pair_fold(first, second, c1);
  }
  return pr_dr_bwd::dr_window_pair_fold(level2[0], level2[1], c2);
}

EXTERN __global__ __launch_bounds__(pr_dr_bwd::BWD_WINDOW_BLOCK_THREADS,
                                    2) void ab_pr_gkr_bwd_dr_window_continuation_kernel(const __grid_constant__ pr_dr_window_desc desc) {
  const u32 slot = pr_dr_bwd::dr_cont_dense_slot(desc.batch.enabled_mask, blockIdx.y);
  pr_dr_bwd::dr_cont_selected_slot_prologue<pr>(desc, slot);
  __syncthreads();
  const size_t tile_slot = static_cast<size_t>(blockIdx.y) * gridDim.x + blockIdx.x;
  pr_dr_window_evaluate<true>(desc, 1u << slot, tile_slot);
}

} // namespace airbender::gkr::proth120::backward
