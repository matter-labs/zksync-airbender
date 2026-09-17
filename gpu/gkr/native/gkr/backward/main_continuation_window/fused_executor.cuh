#pragma once

#include "executor.cuh"

namespace airbender::gkr::backward {

constexpr u32 BWD_MAIN_CONT_FUSED_THREADS = BWD_MAIN_CONT_WINDOW_WARPS * BWD_WINDOW_WARP_LANES;
static_assert(BWD_MAIN_CONT_FUSED_THREADS == 288, "one fused warp per selector pair");

// Each block owns a row tile, and each source has exactly one publishing warp.
DEVICE_FORCEINLINE void bwd_main_cont_fused_prologue(const bwd_main_cont_window_desc &desc) {
  const u32 lane = threadIdx.x & BWD_WINDOW_LANE_INDEX_MASK;
  const u32 warp = threadIdx.x >> BWD_WINDOW_WARP_SHIFT;
  const u32 logical_rows = bwd_main_cont_logical_rows(desc.eq_sizes);
  for (u32 subrow = 0; subrow < BWD_MAIN_CONT_WINDOW_PUBLICATION_SUBBLOCKS_PER_TILE; ++subrow) {
    const u32 row = blockIdx.x * BWD_MAIN_CONT_WINDOW_ROWS_PER_TILE + subrow * BWD_MAIN_CONT_WINDOW_PUBLICATION_ROWS_PER_BLOCK +
                    lane / BWD_MAIN_CONT_WINDOW_PUBLICATION_LANES_PER_ROW;
    const bool active = row < logical_rows;
    bwd_main_cont_fold_prologue_pair<true>(desc, warp, active ? row : 0, active, lane % BWD_MAIN_CONT_WINDOW_PUBLICATION_LANES_PER_ROW);
  }
  // Includes inactive rows. Publishes global stores before any selector warp
  // reads another warp's folded values; different blocks own disjoint tiles.
  __syncthreads();
}

template <u16 Shape, u32 X1, u32 X0, bool PairSources> DEVICE_FORCEINLINE void bwd_main_cont_fused_evaluate(const bwd_main_cont_window_desc &desc) {
  const u32 x1 = X1 == BWD_MAIN_CONT_WINDOW_BOOLEAN_X1 ? (threadIdx.x >> BWD_WINDOW_WARP_SHIFT) / 3 : X1;
  const u32 lane = threadIdx.x & BWD_WINDOW_LANE_INDEX_MASK;
  const u32 x0 = (threadIdx.x >> BWD_WINDOW_WARP_SHIFT) % 3;
  const u32 row = blockIdx.x * BWD_MAIN_CONT_WINDOW_ROWS_PER_TILE + lane;
  const bool active = row < bwd_main_cont_logical_rows(desc.eq_sizes);
  e4 values[3]{e4::ZERO(), e4::ZERO(), e4::ZERO()};
  if constexpr (X0 == BWD_MAIN_CONT_WINDOW_DYNAMIC_X0) {
    // Logical row counts are powers of two. A partial tile is therefore the
    // single block at row zero, whose own publication supplies these safe reads.
    bwd_main_cont_evaluate<Shape, X1, X0, true, PairSources>(desc, active ? row : 0, x0, values, x1);
    if (!active)
      for (u32 x2 = 0; x2 < 3; ++x2)
        values[x2] = e4::ZERO();
  }
  if (active) {
    if constexpr (X0 != BWD_MAIN_CONT_WINDOW_DYNAMIC_X0)
      bwd_main_cont_evaluate<Shape, X1, X0, false, PairSources>(desc, row, x0, values, x1);
    const e4 eq = gkr_compute_eq_inline<e4>(desc.eq_low, desc.eq_sizes, row);
#pragma unroll
    for (u32 x2 = 0; x2 < 3; ++x2)
      values[x2] = e4::mul(values[x2], eq);
  }
#pragma unroll
  for (u32 x2 = 0; x2 < 3; ++x2) {
    const e4 tile = ::airbender::gkr::gkr_trace_holder_partials_warp_reduce_sum<e4>(values[x2]);
    if (lane == 0)
      store<e4, st_modifier::cs>(desc.partials, tile, blockIdx.x * BWD_MAIN_CONT_WINDOW_TENSOR_CELLS + 9 * x2 + 3 * x1 + x0);
  }
}

template <u16 Shape, u32 X1, bool StaticX0, bool PairSources> DEVICE_FORCEINLINE void bwd_main_cont_fused_dispatch_x0(const bwd_main_cont_window_desc &desc) {
  if constexpr (StaticX0) {
    if ((threadIdx.x >> BWD_WINDOW_WARP_SHIFT) % 3 < 2)
      bwd_main_cont_fused_evaluate<Shape, X1, BWD_MAIN_CONT_WINDOW_BOOLEAN_X0, PairSources>(desc);
    else
      bwd_main_cont_fused_evaluate<Shape, X1, 2, PairSources>(desc);
  } else {
    bwd_main_cont_fused_evaluate<Shape, X1, BWD_MAIN_CONT_WINDOW_DYNAMIC_X0, PairSources>(desc);
  }
}

template <u16 Shape, bool StaticX0, bool PairSources> DEVICE_FORCEINLINE void bwd_main_cont_fused_execute(const bwd_main_cont_window_desc &desc) {
  static_assert((Shape & ~BWD_MAIN_CONT_WINDOW_SHAPE_DEFINED_BITS) == 0, "unsupported continuation shape");
  bwd_main_cont_fused_prologue(desc);
  if ((threadIdx.x >> BWD_WINDOW_WARP_SHIFT) / 3 < 2)
    bwd_main_cont_fused_dispatch_x0<Shape, BWD_MAIN_CONT_WINDOW_BOOLEAN_X1, StaticX0, PairSources>(desc);
  else
    bwd_main_cont_fused_dispatch_x0<Shape, 2, StaticX0, PairSources>(desc);
}

#define AB_GKR_MAIN_CONT_DEFINE_FUSED(Name, Shape, MinBlocks, StaticX0, PairSources)                                                                           \
  EXTERN __global__ __launch_bounds__(airbender::gkr::backward::BWD_MAIN_CONT_FUSED_THREADS,                                                                   \
                                      MinBlocks) void Name(const __grid_constant__ airbender::gkr::backward::bwd_main_cont_window_desc desc) {                 \
    using namespace airbender::gkr::backward;                                                                                                                  \
    if (blockDim.x != BWD_MAIN_CONT_FUSED_THREADS || gridDim.x != desc.row_tiles || desc.publication_fold != 3 ||                                              \
        desc.source_count > BWD_MAIN_CONT_WINDOW_MAX_SOURCES || desc.fold_list_offsets[BWD_MAIN_CONT_WINDOW_WARPS] > desc.source_count ||                      \
        desc.program_words > BWD_MAIN_CONT_WINDOW_PROGRAM_WORD_CAP || desc.program_words % BWD_CONTINUATION_WORDS_PER_TERM != 0)                               \
      return;                                                                                                                                                  \
    bwd_main_cont_fused_execute<Shape, StaticX0, PairSources>(desc);                                                                                           \
  }

} // namespace airbender::gkr::backward
