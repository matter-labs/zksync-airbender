#include "r0.cuh"

namespace airbender::gkr::proth120::backward {

template <u16 Shape> DEVICE_FORCEINLINE void pr_window_entry(const bwd_window_desc_pr &desc, const u32 scalar_seed, pr *equality_by_lane) {
  if (blockDim.x != PR_WINDOW_BLOCK_THREADS)
    return;
  pr_window_execute<Shape>(desc, scalar_seed, equality_by_lane);
}

EXTERN __global__ __launch_bounds__(PR_WINDOW_BLOCK_THREADS, PR_WINDOW_MIN_BLOCKS) void ab_pr_gkr_bwd_r0_kernel(const __grid_constant__ bwd_window_desc_pr desc,
                                                                                                                const u32 scalar_seed) {
  __shared__ pr equality_by_lane[PR_WINDOW_ROWS_PER_TILE];
  pr_window_entry<PR_WINDOW_SHAPE_GENERAL>(desc, scalar_seed, equality_by_lane);
}

EXTERN __global__ __launch_bounds__(PR_WINDOW_BLOCK_THREADS,
                                    PR_WINDOW_MIN_BLOCKS) void ab_pr_gkr_bwd_r0_unit_kernel(const __grid_constant__ bwd_window_desc_pr desc,
                                                                                            const u32 scalar_seed) {
  __shared__ pr equality_by_lane[PR_WINDOW_ROWS_PER_TILE];
  pr_window_entry<PR_WINDOW_SHAPE_UNIT>(desc, scalar_seed, equality_by_lane);
}

EXTERN __global__ __launch_bounds__(PR_WINDOW_BLOCK_THREADS,
                                    PR_WINDOW_MIN_BLOCKS) void ab_pr_gkr_bwd_r0_tails_kernel(const __grid_constant__ bwd_window_desc_pr desc,
                                                                                             const u32 scalar_seed) {
  __shared__ pr equality_by_lane[PR_WINDOW_ROWS_PER_TILE];
  pr_window_entry<PR_WINDOW_SHAPE_TAILS>(desc, scalar_seed, equality_by_lane);
}

} // namespace airbender::gkr::proth120::backward
