#include "r0.cuh"

namespace {
using airbender::gkr::backward::BWD_WINDOW_BLOCK_THREADS;
using airbender::gkr::backward::bwd_window_desc;
using airbender::gkr::backward::bwd_window_execute;
} // namespace

EXTERN __global__ __launch_bounds__(BWD_WINDOW_BLOCK_THREADS, 3) void ab_gkr_r0_b3(const __grid_constant__ bwd_window_desc desc, const u32 scalar_seed) {
  if (blockDim.x != BWD_WINDOW_BLOCK_THREADS)
    return;
  bwd_window_execute<0x7f7>(desc, scalar_seed);
}

EXTERN __global__ __launch_bounds__(BWD_WINDOW_BLOCK_THREADS, 4) void ab_gkr_r0_unit_b4(const __grid_constant__ bwd_window_desc desc, const u32 scalar_seed) {
  if (blockDim.x != BWD_WINDOW_BLOCK_THREADS)
    return;
  bwd_window_execute<0x771>(desc, scalar_seed);
}

EXTERN __global__ __launch_bounds__(BWD_WINDOW_BLOCK_THREADS, 4) void ab_gkr_r0_tails_b4(const __grid_constant__ bwd_window_desc desc, const u32 scalar_seed) {
  if (blockDim.x != BWD_WINDOW_BLOCK_THREADS)
    return;
  bwd_window_execute<0x7ff>(desc, scalar_seed);
}
