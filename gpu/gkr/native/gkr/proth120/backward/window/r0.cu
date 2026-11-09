#include "r0.cuh"

namespace airbender::gkr::proth120::backward {

template <u16 Shape> DEVICE_FORCEINLINE void pr_window_entry(const bwd_window_desc_pr &desc, const u32 scalar_seed, pr *equality_by_lane) {
  if (blockDim.x != PR_WINDOW_BLOCK_THREADS)
    return;
  pr_window_execute<Shape>(desc, scalar_seed, 0, desc.sections[BWD_WINDOW_SECTION_BF], 0, equality_by_lane);
}

template <u16 Shape>
DEVICE_FORCEINLINE void pr_window_partition_entry(const bwd_window_desc_pr &desc, const u32 scalar_seed, const bwd_window_partition_bounds_pr &bounds,
                                                  pr *equality_by_lane) {
  const u32 part = blockIdx.y;
  if (blockDim.x != PR_WINDOW_BLOCK_THREADS || part >= bounds.parts || part >= PR_WINDOW_MAX_PARTS)
    return;
  const u32 start = part == 0 ? 0 : bounds.ends[part - 1][PR_WINDOW_SECTION_WORDS - 1];
  pr_window_execute<Shape>(desc, scalar_seed, start, bounds.ends[part][BWD_WINDOW_SECTION_BF], part, equality_by_lane);
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

EXTERN __global__ __launch_bounds__(PR_WINDOW_BLOCK_THREADS, PR_WINDOW_MIN_BLOCKS) void ab_pr_gkr_bwd_r0_partition_kernel(
    const __grid_constant__ bwd_window_desc_pr desc, const u32 scalar_seed, const __grid_constant__ bwd_window_partition_bounds_pr bounds) {
  __shared__ pr equality_by_lane[PR_WINDOW_ROWS_PER_TILE];
  pr_window_partition_entry<PR_WINDOW_SHAPE_GENERAL>(desc, scalar_seed, bounds, equality_by_lane);
}

EXTERN __global__ __launch_bounds__(PR_WINDOW_BLOCK_THREADS, PR_WINDOW_MIN_BLOCKS) void ab_pr_gkr_bwd_r0_partition_unit_kernel(
    const __grid_constant__ bwd_window_desc_pr desc, const u32 scalar_seed, const __grid_constant__ bwd_window_partition_bounds_pr bounds) {
  __shared__ pr equality_by_lane[PR_WINDOW_ROWS_PER_TILE];
  pr_window_partition_entry<PR_WINDOW_SHAPE_UNIT>(desc, scalar_seed, bounds, equality_by_lane);
}

EXTERN __global__ __launch_bounds__(PR_WINDOW_BLOCK_THREADS, PR_WINDOW_MIN_BLOCKS) void ab_pr_gkr_bwd_r0_partition_tails_kernel(
    const __grid_constant__ bwd_window_desc_pr desc, const u32 scalar_seed, const __grid_constant__ bwd_window_partition_bounds_pr bounds) {
  __shared__ pr equality_by_lane[PR_WINDOW_ROWS_PER_TILE];
  pr_window_partition_entry<PR_WINDOW_SHAPE_TAILS>(desc, scalar_seed, bounds, equality_by_lane);
}

} // namespace airbender::gkr::proth120::backward
