#include "windowed_r0_executor.cuh"

namespace airbender::gkr_windowed_bench {

#if defined(GPU_GKR_WINDOWED_R0_CTA96_PARTITIONED_MIN_BLOCKS) && GPU_GKR_WINDOWED_R0_CTA96_PARTITIONED_MIN_BLOCKS > 0
#define AB_R0_LAUNCH_BOUNDS __launch_bounds__(96, GPU_GKR_WINDOWED_R0_CTA96_PARTITIONED_MIN_BLOCKS)
#else
#define AB_R0_LAUNCH_BOUNDS
#endif

EXTERN __global__ AB_R0_LAUNCH_BOUNDS void ab_gkr_windowed_r0_cta96_partitioned_kernel(const __grid_constant__ R0VmDesc desc) {
  const u32 warp = threadIdx.x >> 5;
  const u32 lane = threadIdx.x & 31;
  const u32 row_tile = blockIdx.x / 3;
  const u32 block_in_tile = blockIdx.x % 3;
  const u32 selector_id = 3 * block_in_tile + warp;
  const r0_selector_pair selector{selector_id / 3, selector_id % 3};
  const u32 row = row_tile * 32 + lane;
  const bool active = row < (1u << desc.log_rows);
  e4 accumulators[3];
  r0_execute_pair(desc, active ? row : 0, selector, accumulators);
  r0_publish_pair(desc, row_tile, selector_id, lane, active, accumulators);
}

#undef AB_R0_LAUNCH_BOUNDS

} // namespace airbender::gkr_windowed_bench
