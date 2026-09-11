#pragma once

#include "fused_executor.cuh"

namespace airbender::gkr::backward {

// One corner per lane: retain the exact flattened arithmetic and input loads,
// but halve the inter-lane input stride. Eight lanes cover a suffix row.
DEVICE_FORCEINLINE void bwd_main_cont_fold_lane8(const bwd_main_cont_window_desc &desc, const u32 fold_warp, const u32 row, const bool active,
                                                 const u32 corner) {
  for (u32 position = desc.fold_list_offsets[fold_warp]; position < desc.fold_list_offsets[fold_warp + 1]; ++position) {
    const auto record = desc.source[desc.fold_sources[position]];
    const auto &input = desc.slot[bwd_main_cont_window_lane_slot(record.src)];
    const e4 value = bwd_main_cont_fold_output(desc, record, input, (row << 3) + corner);
    if (active)
      store<e4, st_modifier::wb>(bwd_main_cont_window_column_mut(desc, record.publish), value, (row << 3) + corner);
  }
}

DEVICE_FORCEINLINE void bwd_main_cont_lane8_prologue(const bwd_main_cont_window_desc &desc) {
  const u32 lane = threadIdx.x & 31;
  const u32 warp = threadIdx.x >> 5;
  const u32 logical_rows = bwd_main_cont_logical_rows(desc.eq_sizes);
  for (u32 subrow = 0; subrow < 8; ++subrow) {
    const u32 row = blockIdx.x * 32 + subrow * 4 + lane / 8;
    const bool active = row < logical_rows;
    bwd_main_cont_fold_lane8(desc, warp, active ? row : 0, active, lane % 8);
  }
  __syncthreads();
}

template <u16 Shape, bool StaticX0> DEVICE_FORCEINLINE void bwd_main_cont_lane8_execute(const bwd_main_cont_window_desc &desc) {
  bwd_main_cont_lane8_prologue(desc);
  switch ((threadIdx.x >> 5) / 3) {
  case 0:
    bwd_main_cont_fused_dispatch_x0<Shape, 0, StaticX0, true, StaticX0 ? 0 : 48, 1024>(desc);
    break;
  case 1:
    bwd_main_cont_fused_dispatch_x0<Shape, 1, StaticX0, true, StaticX0 ? 0 : 48, 1024>(desc);
    break;
  case 2:
    bwd_main_cont_fused_dispatch_x0<Shape, 2, StaticX0, true, StaticX0 ? 0 : 48, 1024>(desc);
    break;
  }
}

#define AB_GKR_MAIN_CONT_DEFINE_LANE8(Name, Shape, StaticX0)                                                                                                   \
  EXTERN __global__ __launch_bounds__(288, 2) void Name(const __grid_constant__ bwd_main_cont_window_desc desc) {                                              \
    if (blockDim.x != 288 || gridDim.x != desc.row_tiles || desc.publication_fold != 3)                                                                        \
      return;                                                                                                                                                  \
    bwd_main_cont_lane8_execute<Shape, StaticX0>(desc);                                                                                                        \
  }

EXTERN __global__ __launch_bounds__(96) void ab_gkr_main_cont_fold_lane8_publish(const __grid_constant__ bwd_main_cont_window_desc desc) {
  if (blockDim.x != 96 || gridDim.x != desc.row_tiles * 24)
    return;
  const u32 lane = threadIdx.x & 31;
  const u32 block_in_tile = blockIdx.x % 24;
  const u32 fold_warp = 3 * (block_in_tile / 8) + (threadIdx.x >> 5);
  const u32 row = (blockIdx.x / 24) * 32 + (block_in_tile % 8) * 4 + lane / 8;
  const bool active = row < bwd_main_cont_logical_rows(desc.eq_sizes);
  bwd_main_cont_fold_lane8(desc, fold_warp, active ? row : 0, active, lane % 8);
}

} // namespace airbender::gkr::backward
