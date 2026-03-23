#include "ntt.cuh"

namespace airbender::ntt {

EXTERN __launch_bounds__(512, 2) __global__
    void ab_hypercube_evals_to_monomials_nonfinal_8_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out,
                                                                  const int log_n, const int start_stage) {
  constexpr int VALS_PER_THREAD = 16;
  constexpr int LOG_DATA_TILE_SIZE = 5;
  constexpr int TILE_SIZE = 1 << LOG_DATA_TILE_SIZE;
  constexpr int LOG_DATA_TILES_PER_BLOCK = 8;
  constexpr int THREAD_TILES_PER_BLOCK = 16;

  const int lane_in_tile = threadIdx.x & 31;
  const int tile_id = threadIdx.x >> LOG_DATA_TILE_SIZE;

  const int exchg_region_size = 1 << (log_n - start_stage);
  const int tile_gmem_stride = exchg_region_size >> LOG_DATA_TILES_PER_BLOCK;
  const int interleaved_gmem_stride = tile_gmem_stride * THREAD_TILES_PER_BLOCK;

  // Reversed block indexing for the middle kernel, to help L2 hits
  const int alternating_block_idx_x = (start_stage == 0) ? blockIdx.x : (gridDim.x - 1 - blockIdx.x);
  const int alternating_block_idx_y = (start_stage == 0) ? blockIdx.y : (gridDim.y - 1 - blockIdx.y);
  const int gmem_block_offset = alternating_block_idx_y * exchg_region_size + (alternating_block_idx_x << LOG_DATA_TILE_SIZE);
  gmem_in.add_row(gmem_block_offset);
  gmem_out.add_row(gmem_block_offset);

  __shared__ bf smem_block[8192];

  bf vals[VALS_PER_THREAD];

  // "ct" = consecutive tile layout
  // "it" = interleaved tile layout
  const int thread_il_gmem_start = lane_in_tile + tile_id * tile_gmem_stride;
  const int thread_ct_gmem_start = lane_in_tile + tile_id * interleaved_gmem_stride;
  const int thread_il_smem_start = lane_in_tile + tile_id * TILE_SIZE;
  const int thread_ct_smem_start = lane_in_tile + tile_id * TILE_SIZE * THREAD_TILES_PER_BLOCK;

#pragma unroll
  for (int i{0}, addr{thread_il_gmem_start}; i < VALS_PER_THREAD; i++, addr += interleaved_gmem_stride)
    vals[i] = gmem_in.get_at_row(addr);

  reg_exchg_hypercube_inv<8, 16, 1>(vals);
  reg_exchg_hypercube_inv<4, 8, 2>(vals);
  reg_exchg_hypercube_inv<2, 4, 4>(vals);
  reg_exchg_hypercube_inv<1, 2, 8>(vals);

#pragma unroll
  for (int i{0}, addr{thread_il_smem_start}; i < VALS_PER_THREAD; i++, addr += TILE_SIZE * THREAD_TILES_PER_BLOCK)
    smem_block[addr] = vals[i]; // write interleaved smem tiles

  __syncthreads();

#pragma unroll
  for (int i{0}, addr{thread_ct_smem_start}; i < VALS_PER_THREAD; i++, addr += TILE_SIZE)
    vals[i] = smem_block[addr]; // read consecutive smem tiles

  reg_exchg_hypercube_inv<8, 16, 1>(vals);
  reg_exchg_hypercube_inv<4, 8, 2>(vals);
  reg_exchg_hypercube_inv<2, 4, 4>(vals);
  reg_exchg_hypercube_inv<1, 2, 8>(vals);

#pragma unroll
  for (int i{0}, row{thread_ct_gmem_start}; i < VALS_PER_THREAD; i++, row += tile_gmem_stride)
    gmem_out.set_at_row(row, vals[i]); // write consecutive gmem tiles
}

template <int STAGES>
DEVICE_FORCEINLINE void hypercube_evals_to_monomials_final_up_to_8_stages(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out,
                                                                          const bool transposed_monomials, const int log_n) {
  constexpr int WARP_SIZE = 32;
  constexpr int VALS_PER_THREAD = 32;
  constexpr int VALS_PER_WARP = WARP_SIZE * VALS_PER_THREAD;
  constexpr int WARPS_PER_BLOCK = 8;
  constexpr int VALS_PER_BLOCK = WARPS_PER_BLOCK * WARP_SIZE * VALS_PER_THREAD; // 8192
  constexpr int INITIAL_EXCHG_REGIONS_PER_WARP = 1 << (10 - STAGES);

  const int lane_id = threadIdx.x & 31;
  const int warp_id = threadIdx.x >> 5;
  const int gmem_block_offset = blockIdx.x * VALS_PER_BLOCK;
  gmem_in.add_row(gmem_block_offset + warp_id * VALS_PER_WARP);
  gmem_out.add_row(gmem_block_offset + warp_id * VALS_PER_WARP);

  __shared__ bf smem_block[8192];
  bf *smem_warp = smem_block + warp_id * VALS_PER_WARP;

  bf vals[VALS_PER_THREAD];

#pragma unroll
  for (int i{0}, row{lane_id}; i < VALS_PER_THREAD; i++, row += WARP_SIZE)
    vals[i] = gmem_in.get_at_row(row);

  // Use pure cmem for warp-uniform twiddles
  if (STAGES >= 5) {
#pragma unroll
    for (int i{0}; i < INITIAL_EXCHG_REGIONS_PER_WARP; i++) {
      if (STAGES == 8) {
        bf *vals_this_region = vals + 8 * i;
        reg_exchg_hypercube_inv<4, 8, 1>(vals_this_region);
        reg_exchg_hypercube_inv<2, 4, 2>(vals_this_region);
        reg_exchg_hypercube_inv<1, 2, 4>(vals_this_region);
      }
      if (STAGES == 7) {
        bf *vals_this_region = vals + 4 * i;
        reg_exchg_hypercube_inv<2, 4, 1>(vals_this_region);
        reg_exchg_hypercube_inv<1, 2, 2>(vals_this_region);
      }
      if (STAGES == 6) {
        bf *vals_this_region = vals + 2 * i;
        reg_exchg_hypercube_inv<1, 2, 1>(vals_this_region);
      }
    }
  }

#pragma unroll
  for (int y = 0; y < VALS_PER_THREAD; y++)
    smem_warp[xy_to_swizzled(lane_id, y)] = vals[y];
  __syncwarp();
#pragma unroll
  for (int x = 0; x < VALS_PER_THREAD; x++)
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
#pragma unroll
    for (int x = 0; x < VALS_PER_THREAD; x++)
      smem_warp[xy_to_swizzled(x, lane_id)] = vals[x];
    __syncwarp();
#pragma unroll
    for (int y = 0; y < VALS_PER_THREAD; y++)
      vals[y] = smem_warp[xy_to_swizzled(lane_id, y)];

#pragma unroll
    for (int i{0}, row{lane_id}; i < VALS_PER_THREAD; i++, row += WARP_SIZE)
      gmem_out.set_at_row(row, vals[i]);
  }
}

EXTERN __launch_bounds__(256, 3) __global__
    void ab_hypercube_evals_to_monomials_final_8_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out,
                                                               const bool transposed_monomials, const int log_n) {
  hypercube_evals_to_monomials_final_up_to_8_stages<8>(gmem_in, gmem_out, transposed_monomials, log_n);
}

EXTERN __launch_bounds__(256, 3) __global__
    void ab_hypercube_evals_to_monomials_final_7_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out,
                                                               const bool transposed_monomials, const int log_n) {
  hypercube_evals_to_monomials_final_up_to_8_stages<7>(gmem_in, gmem_out, transposed_monomials, log_n);
}

EXTERN __launch_bounds__(256, 3) __global__
    void ab_hypercube_evals_to_monomials_final_6_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out,
                                                               const bool transposed_monomials, const int log_n) {
  hypercube_evals_to_monomials_final_up_to_8_stages<6>(gmem_in, gmem_out, transposed_monomials, log_n);
}

EXTERN __launch_bounds__(256, 3) __global__
    void ab_hypercube_evals_to_monomials_final_5_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out,
                                                               const bool transposed_monomials, const int log_n) {
  hypercube_evals_to_monomials_final_up_to_8_stages<5>(gmem_in, gmem_out, transposed_monomials, log_n);
}

} // namespace airbender::ntt
