#pragma once

#include "executor.cuh"

namespace airbender::gkr::backward {

constexpr u32 BWD_MAIN_CONT_FUSED_THREADS = BWD_MAIN_CONT_WINDOW_WARPS * BWD_WINDOW_WARP_LANES;
static_assert(BWD_MAIN_CONT_FUSED_THREADS == 288, "one fused warp per selector pair");

// All publishers and consumers of a row tile belong to this block. Keep the
// existing four-lane corner-pair fold geometry, covering eight rows per step.
// Each semantic source occurs in one fold list, so every live corner has one
// writer. The existing fold helpers use seven precomputed challenge factors;
// they do not recursively fold or recompute factors in the evaluator.
template <bool WideFold = false> DEVICE_FORCEINLINE void bwd_main_cont_fused_prologue(const bwd_main_cont_window_desc &desc) {
  const u32 lane = threadIdx.x & BWD_WINDOW_LANE_INDEX_MASK;
  const u32 warp = threadIdx.x >> BWD_WINDOW_WARP_SHIFT;
  const u32 logical_rows = bwd_main_cont_logical_rows(desc.eq_sizes);
  for (u32 subrow = 0; subrow < BWD_MAIN_CONT_WINDOW_PUBLICATION_SUBBLOCKS_PER_TILE; ++subrow) {
    const u32 row = blockIdx.x * BWD_MAIN_CONT_WINDOW_ROWS_PER_TILE + subrow * BWD_MAIN_CONT_WINDOW_PUBLICATION_ROWS_PER_BLOCK +
                    lane / BWD_MAIN_CONT_WINDOW_PUBLICATION_LANES_PER_ROW;
    const bool active = row < logical_rows;
    bwd_main_cont_fold_prologue_pair<WideFold>(desc, warp, active ? row : 0, active, lane % BWD_MAIN_CONT_WINDOW_PUBLICATION_LANES_PER_ROW);
  }
  // Includes inactive rows. Publishes global stores before any selector warp
  // reads another warp's folded values; different blocks own disjoint tiles.
  __syncthreads();
}

template <u16 Shape, u32 X1, u32 X0, bool Packed, u32 PaceWords, u32 MinPaceWords>
DEVICE_FORCEINLINE void bwd_main_cont_fused_evaluate(const bwd_main_cont_window_desc &desc) {
  const u32 x1 = X1 == BWD_MAIN_CONT_WINDOW_BOOLEAN_X1 ? (threadIdx.x >> BWD_WINDOW_WARP_SHIFT) / 3 : X1;
  const u32 lane = threadIdx.x & BWD_WINDOW_LANE_INDEX_MASK;
  const u32 x0 = (threadIdx.x >> BWD_WINDOW_WARP_SHIFT) % 3;
  const u32 row = blockIdx.x * BWD_MAIN_CONT_WINDOW_ROWS_PER_TILE + lane;
  const bool active = row < bwd_main_cont_logical_rows(desc.eq_sizes);
  e4 values[3]{e4::ZERO(), e4::ZERO(), e4::ZERO()};
  if constexpr (PaceWords != 0) {
    // Logical row counts are powers of two. A partial tile is therefore the
    // single block at row zero, whose own publication supplies these safe reads.
    bwd_main_cont_evaluate<Shape, X1, X0, Packed, PaceWords, MinPaceWords>(desc, active ? row : 0, x0, values, x1);
    if (!active)
      for (u32 x2 = 0; x2 < 3; ++x2)
        values[x2] = e4::ZERO();
  }
  if (active) {
    if constexpr (PaceWords == 0)
      bwd_main_cont_evaluate<Shape, X1, X0, Packed>(desc, row, x0, values, x1);
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

template <u16 Shape, u32 X1, bool StaticX0, bool Packed, u32 PaceWords, u32 MinPaceWords, bool CompactX0 = false>
DEVICE_FORCEINLINE void bwd_main_cont_fused_dispatch_x0(const bwd_main_cont_window_desc &desc) {
  if constexpr (CompactX0) {
    if ((threadIdx.x >> BWD_WINDOW_WARP_SHIFT) % 3 < 2)
      bwd_main_cont_fused_evaluate<Shape, X1, BWD_MAIN_CONT_WINDOW_BOOLEAN_X0, Packed, PaceWords, MinPaceWords>(desc);
    else
      bwd_main_cont_fused_evaluate<Shape, X1, 2, Packed, PaceWords, MinPaceWords>(desc);
  } else if constexpr (!StaticX0) {
    bwd_main_cont_fused_evaluate<Shape, X1, BWD_MAIN_CONT_WINDOW_DYNAMIC_X0, Packed, PaceWords, MinPaceWords>(desc);
  } else {
    switch ((threadIdx.x >> BWD_WINDOW_WARP_SHIFT) % 3) {
    case 0:
      bwd_main_cont_fused_evaluate<Shape, X1, 0, Packed, PaceWords, MinPaceWords>(desc);
      break;
    case 1:
      bwd_main_cont_fused_evaluate<Shape, X1, 1, Packed, PaceWords, MinPaceWords>(desc);
      break;
    case 2:
      bwd_main_cont_fused_evaluate<Shape, X1, 2, Packed, PaceWords, MinPaceWords>(desc);
      break;
    }
  }
}

template <u16 Shape, bool StaticX0, bool Packed = false, u32 PaceWords = 0, u32 MinPaceWords = 0, bool WideFold = false, bool CompactX0 = false,
          bool CompactX1 = false>
DEVICE_FORCEINLINE void bwd_main_cont_fused_execute(const bwd_main_cont_window_desc &desc) {
  static_assert((Shape & ~BWD_MAIN_CONT_WINDOW_SHAPE_DEFINED_BITS) == 0, "unsupported continuation shape");
  bwd_main_cont_fused_prologue<WideFold>(desc);
  if constexpr (CompactX1) {
    if ((threadIdx.x >> BWD_WINDOW_WARP_SHIFT) / 3 < 2)
      bwd_main_cont_fused_dispatch_x0<Shape, BWD_MAIN_CONT_WINDOW_BOOLEAN_X1, StaticX0, Packed, PaceWords, MinPaceWords, CompactX0>(desc);
    else
      bwd_main_cont_fused_dispatch_x0<Shape, 2, StaticX0, Packed, PaceWords, MinPaceWords, CompactX0>(desc);
  } else {
    switch ((threadIdx.x >> BWD_WINDOW_WARP_SHIFT) / 3) {
    case 0:
      bwd_main_cont_fused_dispatch_x0<Shape, 0, StaticX0, Packed, PaceWords, MinPaceWords, CompactX0>(desc);
      break;
    case 1:
      bwd_main_cont_fused_dispatch_x0<Shape, 1, StaticX0, Packed, PaceWords, MinPaceWords, CompactX0>(desc);
      break;
    case 2:
      bwd_main_cont_fused_dispatch_x0<Shape, 2, StaticX0, Packed, PaceWords, MinPaceWords, CompactX0>(desc);
      break;
    }
  }
}

#define AB_GKR_MAIN_CONT_DEFINE_FUSED_SELECTORS_IMPL(Name, Shape, MinBlocks, StaticX0, Packed, PaceWords, MinPaceWords, WideFold, CompactX0, CompactX1)        \
  EXTERN __global__ __launch_bounds__(airbender::gkr::backward::BWD_MAIN_CONT_FUSED_THREADS,                                                                   \
                                      MinBlocks) void Name(const __grid_constant__ airbender::gkr::backward::bwd_main_cont_window_desc desc) {                 \
    using namespace airbender::gkr::backward;                                                                                                                  \
    if (blockDim.x != BWD_MAIN_CONT_FUSED_THREADS || gridDim.x != desc.row_tiles || desc.publication_fold != 3 ||                                              \
        desc.source_count > BWD_MAIN_CONT_WINDOW_MAX_SOURCES || desc.fold_list_offsets[BWD_MAIN_CONT_WINDOW_WARPS] != desc.source_count ||                     \
        desc.program_words > BWD_MAIN_CONT_WINDOW_PROGRAM_WORD_CAP || desc.program_words % BWD_CONTINUATION_WORDS_PER_TERM != 0)                               \
      return;                                                                                                                                                  \
    bwd_main_cont_fused_execute<Shape, StaticX0, Packed, PaceWords, MinPaceWords, WideFold, CompactX0, CompactX1>(desc);                                       \
  }

#define AB_GKR_MAIN_CONT_DEFINE_FUSED_EVAL_IMPL(Name, Shape, MinBlocks, StaticX0, Packed, PaceWords, MinPaceWords, WideFold, CompactX0)                        \
  AB_GKR_MAIN_CONT_DEFINE_FUSED_SELECTORS_IMPL(Name, Shape, MinBlocks, StaticX0, Packed, PaceWords, MinPaceWords, WideFold, CompactX0, false)

#define AB_GKR_MAIN_CONT_DEFINE_FUSED_FOLD_IMPL(Name, Shape, MinBlocks, StaticX0, Packed, PaceWords, MinPaceWords, WideFold)                                   \
  AB_GKR_MAIN_CONT_DEFINE_FUSED_EVAL_IMPL(Name, Shape, MinBlocks, StaticX0, Packed, PaceWords, MinPaceWords, WideFold, false)

// The diagnostic families retain narrow folding as their explicit reference.
#define AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(Name, Shape, MinBlocks, StaticX0, Packed, PaceWords, MinPaceWords)                                                  \
  AB_GKR_MAIN_CONT_DEFINE_FUSED_FOLD_IMPL(Name, Shape, MinBlocks, StaticX0, Packed, PaceWords, MinPaceWords, false)

#define AB_GKR_MAIN_CONT_DEFINE_FUSED(Name, Shape, MinBlocks, StaticX0) AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(Name, Shape, MinBlocks, StaticX0, false, 0, 0)
// Long dynamic-X0 programs benefit from keeping selectors near the same input
// records. This measured cutoff is a program-complexity policy, separate from
// the SM-scaled fused/split launch threshold. Static-X0 keeps its unpaced body.
// Only fused folding uses wide accumulators; standalone publication stays narrow.
#define AB_GKR_MAIN_CONT_DEFINE_FUSED_PACKED(Name, Shape, MinBlocks, StaticX0)                                                                                 \
  AB_GKR_MAIN_CONT_DEFINE_FUSED_SELECTORS_IMPL(Name, Shape, MinBlocks, StaticX0, true, (StaticX0 ? 0 : 48), 1024, true, StaticX0, true)

} // namespace airbender::gkr::backward
