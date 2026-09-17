#include "fold_prologue.cuh"

namespace airbender::gkr::backward {

EXTERN __global__
__launch_bounds__(BWD_MAIN_CONT_WINDOW_PUBLICATION_BLOCK_THREADS) void ab_gkr_main_cont_publish(const __grid_constant__ bwd_main_cont_window_desc desc) {
  if (blockDim.x != BWD_MAIN_CONT_WINDOW_PUBLICATION_BLOCK_THREADS || gridDim.x != desc.row_tiles * BWD_MAIN_CONT_WINDOW_PUBLICATION_BLOCKS_PER_TILE)
    return;
  const u32 lane = threadIdx.x & BWD_WINDOW_LANE_INDEX_MASK;
  const u32 warp_id = threadIdx.x >> BWD_WINDOW_WARP_SHIFT;
  const u32 block_in_tile = blockIdx.x % BWD_MAIN_CONT_WINDOW_PUBLICATION_BLOCKS_PER_TILE;
  const u32 publication_partition = block_in_tile / BWD_MAIN_CONT_WINDOW_PUBLICATION_SUBBLOCKS_PER_TILE;
  const u32 publication_subblock = block_in_tile % BWD_MAIN_CONT_WINDOW_PUBLICATION_SUBBLOCKS_PER_TILE;
  const u32 publication_row_tile = blockIdx.x / BWD_MAIN_CONT_WINDOW_PUBLICATION_BLOCKS_PER_TILE;
  const u32 fold_warp = BWD_MAIN_CONT_WINDOW_BLOCK_WARPS * publication_partition + warp_id;
  const u32 row_in_block = lane / BWD_MAIN_CONT_WINDOW_PUBLICATION_LANES_PER_ROW;
  const u32 corner_pair = lane % BWD_MAIN_CONT_WINDOW_PUBLICATION_LANES_PER_ROW;
  const u32 row =
      publication_row_tile * BWD_MAIN_CONT_WINDOW_ROWS_PER_TILE + publication_subblock * BWD_MAIN_CONT_WINDOW_PUBLICATION_ROWS_PER_BLOCK + row_in_block;
  const u32 logical_rows = 1u << (desc.eq_sizes.high[0] + desc.eq_sizes.high[1] + desc.eq_sizes.low);
  const bool active = row < logical_rows;
  bwd_main_cont_fold_prologue_pair(desc, fold_warp, active ? row : 0, active, corner_pair);
}

} // namespace airbender::gkr::backward
