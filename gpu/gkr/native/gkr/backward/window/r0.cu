#include "r0.cuh"

namespace {
using airbender::gkr::backward::BWD_WINDOW_BLOCK_THREADS;
using airbender::gkr::backward::bwd_window_desc;
using airbender::gkr::backward::bwd_window_execute;
} // namespace

EXTERN __global__ __launch_bounds__(BWD_WINDOW_BLOCK_THREADS, 3) void ab_gkr_r0_b3(const __grid_constant__ bwd_window_desc desc, const u32 scalar_seed) {
  if (blockDim.x != BWD_WINDOW_BLOCK_THREADS)
    return;
  bwd_window_execute<0x7f7>(desc, scalar_seed, 0, desc.sections);
}

EXTERN __global__ __launch_bounds__(BWD_WINDOW_BLOCK_THREADS, 4) void ab_gkr_r0_unit_b4(const __grid_constant__ bwd_window_desc desc, const u32 scalar_seed) {
  if (blockDim.x != BWD_WINDOW_BLOCK_THREADS)
    return;
  bwd_window_execute<0x771>(desc, scalar_seed, 0, desc.sections);
}

EXTERN __global__ __launch_bounds__(BWD_WINDOW_BLOCK_THREADS, 4) void ab_gkr_r0_tails_b4(const __grid_constant__ bwd_window_desc desc, const u32 scalar_seed) {
  if (blockDim.x != BWD_WINDOW_BLOCK_THREADS)
    return;
  bwd_window_execute<0x7ff>(desc, scalar_seed, 0, desc.sections);
}

namespace {
// Matches PartitionBounds in src/backward/window/r0/partition.rs.
struct bwd_window_partition_bounds {
  u32 parts;
  u32 ends[16][4];
};
static_assert(sizeof(bwd_window_partition_bounds) == 260);
static_assert(alignof(bwd_window_partition_bounds) == 4);
static_assert(__builtin_offsetof(bwd_window_partition_bounds, ends) == 4);
static_assert(sizeof(bwd_window_desc) + sizeof(u32) + sizeof(bwd_window_partition_bounds) <= airbender::gkr::BWD_WINDOW_DESC_CAP);

template <u16 Shape> DEVICE_FORCEINLINE void execute_partition(const bwd_window_desc &desc, const u32 scalar_seed, const bwd_window_partition_bounds &bounds) {
  const u32 part = blockIdx.y;
  if (blockDim.x != BWD_WINDOW_BLOCK_THREADS || part >= bounds.parts)
    return;
  const u32 start = part == 0 ? 0 : bounds.ends[part - 1][3];
  bwd_window_execute<Shape>(desc, scalar_seed, start, bounds.ends[part], part);
}
} // namespace

EXTERN __global__ __launch_bounds__(BWD_WINDOW_BLOCK_THREADS, 3) void ab_gkr_r0_partition_b3(const __grid_constant__ bwd_window_desc desc,
                                                                                             const u32 scalar_seed,
                                                                                             const __grid_constant__ bwd_window_partition_bounds bounds) {
  execute_partition<0x7f7>(desc, scalar_seed, bounds);
}

EXTERN __global__ __launch_bounds__(BWD_WINDOW_BLOCK_THREADS, 4) void ab_gkr_r0_partition_unit_b4(const __grid_constant__ bwd_window_desc desc,
                                                                                                  const u32 scalar_seed,
                                                                                                  const __grid_constant__ bwd_window_partition_bounds bounds) {
  execute_partition<0x771>(desc, scalar_seed, bounds);
}

EXTERN __global__ __launch_bounds__(BWD_WINDOW_BLOCK_THREADS, 4) void ab_gkr_r0_partition_tails_b4(const __grid_constant__ bwd_window_desc desc,
                                                                                                   const u32 scalar_seed,
                                                                                                   const __grid_constant__ bwd_window_partition_bounds bounds) {
  execute_partition<0x7ff>(desc, scalar_seed, bounds);
}
