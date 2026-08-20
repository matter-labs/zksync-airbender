#include "windowed_r0_executor.cuh"

namespace airbender::gkr_windowed_bench {

#if defined(GPU_GKR_WINDOWED_R0_CTA96_X2_MAJOR_MIN_BLOCKS) && GPU_GKR_WINDOWED_R0_CTA96_X2_MAJOR_MIN_BLOCKS > 0
#define AB_R0_LAUNCH_BOUNDS __launch_bounds__(96, GPU_GKR_WINDOWED_R0_CTA96_X2_MAJOR_MIN_BLOCKS)
#else
#define AB_R0_LAUNCH_BOUNDS
#endif

EXTERN __global__ AB_R0_LAUNCH_BOUNDS void ab_gkr_windowed_r0_cta96_x2_major_kernel(const __grid_constant__ R0VmDesc desc) {
  const u32 warp = threadIdx.x >> 5;
  const u32 lane = threadIdx.x & 31;
  const u32 row_tile = blockIdx.x;
  const u32 row = row_tile * 32 + lane;
  const bool active = row < (1u << desc.log_rows);
  e4 accumulators[9];
  r0_execute_axis_major<r0_axis::x2, r0_axis::x1, r0_axis::x0>(desc, active ? row : 0, warp, accumulators);
  r0_publish_axis_major<r0_axis::x2, r0_axis::x1, r0_axis::x0>(desc, row_tile, warp, lane, active, accumulators);
}

#undef AB_R0_LAUNCH_BOUNDS

} // namespace airbender::gkr_windowed_bench
