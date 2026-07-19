#pragma once

#include "ntt.cuh"

// Tile / thread tunables for the two-pass and three-pass NTT kernels, shared
// across the forward, hypercube, and monomials-to-evals variants. Each phase
// has its own namespace; bring it into a kernel with `using namespace`.

namespace airbender::ntt::pass_config {

// Two-pass phase A: first / last 10-stage tile-exchange kernel.
namespace two_pass_phase_a {
constexpr int VALS_PER_THREAD = 32;
constexpr int LOG_DATA_TILE_SIZE = 4;
constexpr int TILE_SIZE = 1 << LOG_DATA_TILE_SIZE;
constexpr int LOG_DATA_TILES_PER_BLOCK = 10;
constexpr int THREAD_TILES_PER_BLOCK = 32;
constexpr int TILE_GMEM_STRIDE = 1 << (24 - LOG_DATA_TILES_PER_BLOCK);
constexpr int IL_GMEM_STRIDE = TILE_GMEM_STRIDE * THREAD_TILES_PER_BLOCK;
} // namespace two_pass_phase_a

// Two-pass phase B: 9-stage tile-exchange kernel.
namespace two_pass_phase_b {
constexpr int VALS_PER_THREAD = 32;
constexpr int LOG_DATA_TILE_SIZE = 5;
constexpr int TILE_SIZE = 1 << LOG_DATA_TILE_SIZE;
constexpr int LOG_DATA_TILES_PER_BLOCK = 9;
constexpr int THREAD_TILES_PER_BLOCK = 16;
constexpr int TILE_GMEM_STRIDE = 1 << (23 - LOG_DATA_TILES_PER_BLOCK);
constexpr int IL_GMEM_STRIDE = TILE_GMEM_STRIDE * THREAD_TILES_PER_BLOCK;
} // namespace two_pass_phase_b

// Two-pass phase C: 14-stage warp-exchange kernel.
namespace two_pass_phase_c {
constexpr int WARP_SIZE = 32;
constexpr int VALS_PER_THREAD = 32;
constexpr int WARPS_PER_BLOCK = 16;
constexpr int VALS_PER_BLOCK = WARPS_PER_BLOCK * WARP_SIZE * VALS_PER_THREAD; // 16384
} // namespace two_pass_phase_c

// Pipeline prefetch parameters used by the forward and hypercube two-pass
// phase-A and phase-B kernels. Not used by monomials-to-evals (no prefetch).
namespace pipeline_prefetch {
constexpr int PL_GROUP_SIZE = 4;
constexpr int PL_STRIDE = 8;
} // namespace pipeline_prefetch

// Three-pass phase A: 8-stage non-initial/non-final tile-exchange kernel.
namespace three_pass_phase_a {
constexpr int VALS_PER_THREAD = 16;
constexpr int LOG_DATA_TILE_SIZE = 5;
constexpr int TILE_SIZE = 1 << LOG_DATA_TILE_SIZE;
constexpr int LOG_DATA_TILES_PER_BLOCK = 8;
constexpr int THREAD_TILES_PER_BLOCK = 16;
} // namespace three_pass_phase_a

// Three-pass phase B: up-to-8-stage final / initial warp-exchange kernel.
// The derived `INITIAL_EXCHG_REGIONS_PER_WARP` / `OUTPUT_EXCHG_REGIONS_PER_WARP`
// values depend on the `STAGES` template parameter and stay local to each
// kernel body.
namespace three_pass_phase_b {
constexpr int WARP_SIZE = 32;
constexpr int VALS_PER_THREAD = 32;
constexpr int VALS_PER_WARP = WARP_SIZE * VALS_PER_THREAD;
constexpr int WARPS_PER_BLOCK = 8;
constexpr int VALS_PER_BLOCK = WARPS_PER_BLOCK * WARP_SIZE * VALS_PER_THREAD; // 8192
} // namespace three_pass_phase_b

} // namespace airbender::ntt::pass_config

// Shared device helpers factoring scaffolding idioms duplicated verbatim across
// the six *_pass.cu pass-kernel families. All are DEVICE_FORCEINLINE and
// semantics-preserving; they do not alter any EXTERN signature, launch bounds,
// or grid/block/smem geometry.
namespace airbender::ntt {

// Flat-block column offset: fold a decomposed FlatBlockIndex's coset + column
// indices into one column advance applied to both the input getter and the
// output setter (both share the same per-column offset). Used by every
// coset-folding pass kernel; kernels whose input and output take different
// column offsets, or that carry no per-coset column stride, keep their inline
// version.
DEVICE_FORCEINLINE void apply_flat_col_offset(const FlatBlockIndex &fi, const int num_cols_per_coset, bf_matrix_getter<ld_modifier::cg> &gmem_in,
                                              bf_matrix_setter<st_modifier::cg> &gmem_out) {
  const int col_offset = static_cast<int>(fi.coset) * num_cols_per_coset + static_cast<int>(fi.col);
  gmem_in.add_col(col_offset);
  gmem_out.add_col(col_offset);
}

// Per-thread consecutive-tile ("ct") / interleaved-tile ("il") gmem/smem start
// indices for the phase-A tile layout. Shared by the forward, inverse, and
// hypercube phase-A kernels (identical strides). Phase-B (doubled ct strides)
// and the three-pass kernels (runtime strides) compute their own.
struct ThreadTileStarts {
  int il_gmem_start;
  int ct_gmem_start;
  int il_smem_start;
  int ct_smem_start;
};

DEVICE_FORCEINLINE ThreadTileStarts thread_tile_starts(const int lane_in_tile, const int tile_id, const int tile_gmem_stride, const int il_gmem_stride,
                                                       const int tile_size, const int thread_tiles_per_block) {
  return {
      lane_in_tile + tile_id * tile_gmem_stride,
      lane_in_tile + tile_id * il_gmem_stride,
      lane_in_tile + tile_id * tile_size,
      lane_in_tile + tile_id * tile_size * thread_tiles_per_block,
  };
}

// Swizzled warp transpose: publish N per-lane registers to smem at the
// swizzled (lane, y) address, then read them back from the swizzled (x, lane)
// address, exchanging the register axis with the lane axis across the warp.
// The tile width is a template parameter so the "N == VALS_PER_THREAD == 32"
// invariant is compile-checked at every instantiation instead of living as a
// bare literal; call sites must state their width explicitly (no default) so
// a future non-32-wide caller fails to compile instead of silently taking the
// wrong tile width. The swizzle assumes a 32-wide warp tile, so the
// static_assert pins N to 32 -- widths other than 32 need the loop/lane logic
// reviewed before relaxing this. The mirror-direction transpose (store at
// (x, lane), load at (lane, y)) is a distinct idiom and stays inline.
template <unsigned N> DEVICE_FORCEINLINE void warp_transpose_swizzled(bf *smem_warp, bf *vals, const int lane) {
  static_assert(N == 32, "warp_transpose_swizzled assumes a 32-wide warp tile (VALS_PER_THREAD == 32)");
#pragma unroll
  for (int y = 0; y < static_cast<int>(N); y++)
    smem_warp[xy_to_swizzled(lane, y)] = vals[y];
  __syncwarp();
#pragma unroll
  for (int x = 0; x < static_cast<int>(N); x++)
    vals[x] = smem_warp[xy_to_swizzled(x, lane)];
}

// 8-group prefetch + exchange pipeline for the two-pass phase-A/B inverse
// kernels. `exchg` is a functor exposing a templated `apply<GROUP>(bf*)`; the two
// policies below bind the forward twiddle-exchange and the twiddle-free
// hypercube exchange. exchg_pipeline_group[_hypercube] stay in ntt.cuh so both
// remain visible here (see AGENTS: correctness of the shared factoring beats the
// single-consumer relocation nicety).
struct pipeline_exchg_forward {
  bf twiddle;
  template <int GROUP> DEVICE_FORCEINLINE void apply(bf *vals) const { exchg_pipeline_group<GROUP>(vals, twiddle); }
};

struct pipeline_exchg_hypercube {
  template <int GROUP> DEVICE_FORCEINLINE void apply(bf *vals) const { exchg_pipeline_group_hypercube<GROUP>(vals); }
};

template <int IL_GMEM_STRIDE, int PL_GROUP_SIZE, int PL_STRIDE, typename Exchg>
DEVICE_FORCEINLINE void prefetch_exchg_pipeline_8(bf *vals, const bf_matrix_getter<ld_modifier::cg> &gmem_in, const int thread_il_gmem_start,
                                                  const Exchg &exchg) {
  prefetch_pipeline_group<0, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg.template apply<0>(vals);
  prefetch_pipeline_group<1, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg.template apply<1>(vals);
  prefetch_pipeline_group<2, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg.template apply<2>(vals);
  prefetch_pipeline_group<3, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg.template apply<3>(vals);
  prefetch_pipeline_group<4, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg.template apply<4>(vals);
  prefetch_pipeline_group<5, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg.template apply<5>(vals);
  prefetch_pipeline_group<6, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg.template apply<6>(vals);
  prefetch_pipeline_group<7, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg.template apply<7>(vals);
}

} // namespace airbender::ntt
