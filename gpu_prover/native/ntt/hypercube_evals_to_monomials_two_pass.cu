#include "ntt.cuh"

namespace airbender::ntt {

// For log_n = 2^24 only. log_n argument is only present for API symmetry.
EXTERN __launch_bounds__(512, 1) __global__
    void ab_hypercube_evals_to_monomials_first_10_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out,
                                                                const int log_n, const int start_stage /*unused, for symmetry with three-pass API*/) {
  constexpr int VALS_PER_THREAD = 32;
  constexpr int LOG_DATA_TILE_SIZE = 4;
  constexpr int TILE_SIZE = 1 << LOG_DATA_TILE_SIZE;
  constexpr int LOG_DATA_TILES_PER_BLOCK = 10;
  constexpr int THREAD_TILES_PER_BLOCK = 32;
  constexpr int TILE_GMEM_STRIDE = 1 << (24 - LOG_DATA_TILES_PER_BLOCK);
  constexpr int IL_GMEM_STRIDE = TILE_GMEM_STRIDE * THREAD_TILES_PER_BLOCK;

  constexpr int PL_GROUP_SIZE = 4;
  constexpr int PL_STRIDE = 8;

  // TODO: make some of these kernel arguments
  const int lane_in_tile = threadIdx.x & 15;
  const int tile_id = threadIdx.x >> LOG_DATA_TILE_SIZE;
  const int gmem_block_offset = blockIdx.x << LOG_DATA_TILE_SIZE;
  gmem_in.add_row(gmem_block_offset);
  gmem_out.add_row(gmem_block_offset);

  extern __shared__ bf smem_block[]; // 16384 * 4 bytes

  bf vals[VALS_PER_THREAD];

  // "ct" = consecutive tile layout
  // "it" = interleaved tile layout
  const int thread_il_gmem_start = lane_in_tile + tile_id * TILE_GMEM_STRIDE;
  const int thread_ct_gmem_start = lane_in_tile + tile_id * IL_GMEM_STRIDE;
  const int thread_il_smem_start = lane_in_tile + tile_id * TILE_SIZE;
  const int thread_ct_smem_start = lane_in_tile + tile_id * TILE_SIZE * THREAD_TILES_PER_BLOCK;

  prefetch_pipeline_group<0, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg_pipeline_group_hypercube<0>(vals);
  prefetch_pipeline_group<1, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg_pipeline_group_hypercube<1>(vals);
  prefetch_pipeline_group<2, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg_pipeline_group_hypercube<2>(vals);
  prefetch_pipeline_group<3, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg_pipeline_group_hypercube<3>(vals);
  prefetch_pipeline_group<4, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg_pipeline_group_hypercube<4>(vals);
  prefetch_pipeline_group<5, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg_pipeline_group_hypercube<5>(vals);
  prefetch_pipeline_group<6, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg_pipeline_group_hypercube<6>(vals);
  prefetch_pipeline_group<7, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg_pipeline_group_hypercube<7>(vals);

  reg_exchg_hypercube_inv<4, 8, 4>(vals);
  reg_exchg_hypercube_inv<2, 4, 8>(vals);
  reg_exchg_hypercube_inv<1, 2, 16>(vals);

#pragma unroll
  for (int i{0}, addr{thread_il_smem_start}; i < 32; i++, addr += TILE_SIZE * THREAD_TILES_PER_BLOCK)
    smem_block[addr] = vals[i]; // write interleaved smem tiles

  __syncthreads();

#pragma unroll
  for (int i{0}, addr{thread_ct_smem_start}; i < 32; i++, addr += TILE_SIZE)
    vals[i] = smem_block[addr]; // read consecutive smem tiles

  reg_exchg_hypercube_inv<16, 32, 1>(vals);
  reg_exchg_hypercube_inv<8, 16, 2>(vals);
  reg_exchg_hypercube_inv<4, 8, 4>(vals);
  reg_exchg_hypercube_inv<2, 4, 8>(vals);
  reg_exchg_hypercube_inv<1, 2, 16>(vals);

#pragma unroll
  for (int i{0}, row{thread_ct_gmem_start}; i < 32; i++, row += TILE_GMEM_STRIDE)
    gmem_out.set_at_row(row, vals[i]); // write consecutive gmem tiles
}

// For log_n = 2^23 only. log_n argument is only present for API symmetry.
EXTERN __launch_bounds__(512, 1) __global__
    void ab_hypercube_evals_to_monomials_first_9_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out,
                                                               const int log_n, const int start_stage /*unused, for symmetry with three-pass API*/) {
  constexpr int VALS_PER_THREAD = 32;
  constexpr int LOG_DATA_TILE_SIZE = 5;
  constexpr int TILE_SIZE = 1 << LOG_DATA_TILE_SIZE;
  constexpr int LOG_DATA_TILES_PER_BLOCK = 9;
  constexpr int THREAD_TILES_PER_BLOCK = 16;
  constexpr int TILE_GMEM_STRIDE = 1 << (23 - LOG_DATA_TILES_PER_BLOCK);
  constexpr int IL_GMEM_STRIDE = TILE_GMEM_STRIDE * THREAD_TILES_PER_BLOCK;

  constexpr int PL_GROUP_SIZE = 4;
  constexpr int PL_STRIDE = 8;

  // TODO: make some of these kernel arguments
  const int lane_in_tile = threadIdx.x & 31;
  const int tile_id = threadIdx.x >> LOG_DATA_TILE_SIZE;
  const int gmem_block_offset = blockIdx.x << LOG_DATA_TILE_SIZE;
  gmem_in.add_row(gmem_block_offset);
  gmem_out.add_row(gmem_block_offset);

  extern __shared__ bf smem_block[]; // 16384 * 4 bytes

  bf vals[VALS_PER_THREAD];

  // "ct" = consecutive tile layout
  // "it" = interleaved tile layout
  const int thread_il_gmem_start = lane_in_tile + tile_id * TILE_GMEM_STRIDE;
  const int thread_ct_gmem_start = lane_in_tile + tile_id * 2 * IL_GMEM_STRIDE;
  const int thread_il_smem_start = lane_in_tile + tile_id * TILE_SIZE;
  const int thread_ct_smem_start = lane_in_tile + tile_id * TILE_SIZE * 2 * THREAD_TILES_PER_BLOCK;

  prefetch_pipeline_group<0, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg_pipeline_group_hypercube<0>(vals);
  prefetch_pipeline_group<1, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg_pipeline_group_hypercube<1>(vals);
  prefetch_pipeline_group<2, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg_pipeline_group_hypercube<2>(vals);
  prefetch_pipeline_group<3, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg_pipeline_group_hypercube<3>(vals);
  prefetch_pipeline_group<4, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg_pipeline_group_hypercube<4>(vals);
  prefetch_pipeline_group<5, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg_pipeline_group_hypercube<5>(vals);
  prefetch_pipeline_group<6, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg_pipeline_group_hypercube<6>(vals);
  prefetch_pipeline_group<7, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg_pipeline_group_hypercube<7>(vals);

  reg_exchg_hypercube_inv<4, 8, 4>(vals);
  reg_exchg_hypercube_inv<2, 4, 8>(vals);
  reg_exchg_hypercube_inv<1, 2, 16>(vals);

#pragma unroll
  for (int i{0}, addr{thread_il_smem_start}; i < 32; i++, addr += TILE_SIZE * THREAD_TILES_PER_BLOCK)
    smem_block[addr] = vals[i]; // write interleaved smem tiles

  __syncthreads();

#pragma unroll
  for (int i{0}, addr{thread_ct_smem_start}; i < 32; i++, addr += TILE_SIZE)
    vals[i] = smem_block[addr]; // read consecutive smem tiles

  reg_exchg_hypercube_inv<8, 16, 2>(vals);
  reg_exchg_hypercube_inv<4, 8, 4>(vals);
  reg_exchg_hypercube_inv<2, 4, 8>(vals);
  reg_exchg_hypercube_inv<1, 2, 16>(vals);

#pragma unroll
  for (int i{0}, row{thread_ct_gmem_start}; i < 32; i++, row += TILE_GMEM_STRIDE)
    gmem_out.set_at_row(row, vals[i]); // write consecutive gmem tiles
}

EXTERN __launch_bounds__(512, 1) __global__
    void ab_hypercube_evals_to_monomials_last_14_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out,
                                                               const bool transposed_monomials, const int log_n) {
  constexpr int WARP_SIZE = 32;
  constexpr int VALS_PER_THREAD = 32;
  constexpr int WARPS_PER_BLOCK = 16;
  constexpr int VALS_PER_BLOCK = WARPS_PER_BLOCK * WARP_SIZE * VALS_PER_THREAD; // 16384

  const int lane_id = threadIdx.x & 31;
  const int warp_id = threadIdx.x >> 5;
  const int tile_stride = VALS_PER_BLOCK >> 4;
  const int gmem_block_offset = blockIdx.x * VALS_PER_BLOCK;
  const int thread_start = 64 * warp_id + lane_id;
  gmem_in.add_row(gmem_block_offset);
  gmem_out.add_row(gmem_block_offset + warp_id * 1024);

  extern __shared__ bf smem_block[]; // 16384 vals
  bf *smem_warp = smem_block + warp_id * 1024;

  bf vals[VALS_PER_THREAD];

#pragma unroll
  for (int i{0}, row{thread_start}; i < 32; i += 2, row += tile_stride) {
    vals[i] = gmem_in.get_at_row(row);
    vals[i + 1] = gmem_in.get_at_row(row + 32);
  }

  reg_exchg_hypercube_inv<16, 32, 1>(vals);
  reg_exchg_hypercube_inv<8, 16, 2>(vals);
  reg_exchg_hypercube_inv<4, 8, 4>(vals);
  reg_exchg_hypercube_inv<2, 4, 8>(vals);

#pragma unroll
  for (int i{0}, row{thread_start}; i < 32; i += 2, row += tile_stride) {
    smem_block[row] = vals[i];
    smem_block[row + 32] = vals[i + 1];
  }

  __syncthreads(); // all-to-all, so ptx barriers are unlikely to help

#pragma unroll
  for (int i{0}, row{lane_id}; i < 32; i++, row += 32)
    vals[i] = smem_warp[row];

  reg_exchg_hypercube_inv<16, 32, 1>(vals);
  reg_exchg_hypercube_inv<8, 16, 2>(vals);
  reg_exchg_hypercube_inv<4, 8, 4>(vals);
  reg_exchg_hypercube_inv<2, 4, 8>(vals);
  reg_exchg_hypercube_inv<1, 2, 16>(vals);

  __syncwarp();
#pragma unroll
  for (int y = 0; y < 32; y++)
    smem_warp[xy_to_swizzled(lane_id, y)] = vals[y];
  __syncwarp();
#pragma unroll
  for (int x = 0; x < 32; x++)
    vals[x] = smem_warp[xy_to_swizzled(x, lane_id)];

  reg_exchg_hypercube_inv<16, 32, 1>(vals);
  reg_exchg_hypercube_inv<8, 16, 2>(vals);
  reg_exchg_hypercube_inv<4, 8, 4>(vals);
  reg_exchg_hypercube_inv<2, 4, 8>(vals);
  reg_exchg_hypercube_inv<1, 2, 16>(vals);

  if (transposed_monomials) {
#pragma unroll
    for (int i{0}, row{lane_id}; i < VALS_PER_THREAD; i++, row += WARP_SIZE)
      gmem_out.set_at_row(row, vals[i]);
  } else {
    // un-swizzling + coalesced stores performs better on 5090
    __syncwarp();
#pragma unroll
    for (int y = 0; y < 32; y++)
      smem_warp[xy_to_swizzled(lane_id, y)] = vals[y];
    __syncwarp();
#pragma unroll
    for (int x = 0; x < 32; x++)
      vals[x] = smem_warp[xy_to_swizzled(x, lane_id)];
#pragma unroll
    for (int i{0}, row{lane_id}; i < VALS_PER_THREAD; i++, row += WARP_SIZE)
      gmem_out.set_at_row(row, vals[i]);
  }
}

} // namespace airbender::ntt
