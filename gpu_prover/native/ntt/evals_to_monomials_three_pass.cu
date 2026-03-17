#include "ntt.cuh"

namespace airbender::ntt {

EXTERN __launch_bounds__(512, 2) __global__
    void ab_evals_to_monomials_nonfinal_8_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out, const int log_n,
                                                        const int start_stage) {
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

  // __shared__ bf smem_block[49152];
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

  int block_exchg_region_offset = alternating_block_idx_y;
  if (start_stage == 0) {
    reg_exchg_inv<8, 16, 1>(vals, block_exchg_region_offset);
    block_exchg_region_offset <<= 1;
    reg_exchg_inv<4, 8, 2>(vals, block_exchg_region_offset);
    block_exchg_region_offset <<= 1;
    reg_exchg_inv<2, 4, 4>(vals, block_exchg_region_offset);
    block_exchg_region_offset <<= 1;
    reg_exchg_inv<1, 2, 8>(vals, block_exchg_region_offset);
    block_exchg_region_offset <<= 1;
  } else {
    reg_exchg_cmem_twiddles_inv<8, 16, 1>(vals, block_exchg_region_offset);
    block_exchg_region_offset <<= 1;
    reg_exchg_cmem_twiddles_inv<4, 8, 2>(vals, block_exchg_region_offset);
    block_exchg_region_offset <<= 1;
    reg_exchg_cmem_twiddles_inv<2, 4, 4>(vals, block_exchg_region_offset);
    block_exchg_region_offset <<= 1;
    reg_exchg_cmem_twiddles_inv<1, 2, 8>(vals, block_exchg_region_offset);
    block_exchg_region_offset <<= 1;
  }

#pragma unroll
  for (int i{0}, addr{thread_il_smem_start}; i < VALS_PER_THREAD; i++, addr += TILE_SIZE * THREAD_TILES_PER_BLOCK)
    smem_block[addr] = vals[i]; // write interleaved smem tiles

  __syncthreads();

#pragma unroll
  for (int i{0}, addr{thread_ct_smem_start}; i < VALS_PER_THREAD; i++, addr += TILE_SIZE)
    vals[i] = smem_block[addr]; // read consecutive smem tiles

  int tile_exchg_region_offset = block_exchg_region_offset + tile_id;
  if (start_stage == 0) {
    reg_exchg_inv<8, 16, 1>(vals, tile_exchg_region_offset);
    tile_exchg_region_offset <<= 1;
    reg_exchg_inv<4, 8, 2>(vals, tile_exchg_region_offset);
    tile_exchg_region_offset <<= 1;
    reg_exchg_inv<2, 4, 4>(vals, tile_exchg_region_offset);
    tile_exchg_region_offset <<= 1;
    reg_exchg_inv<1, 2, 8>(vals, tile_exchg_region_offset);
  } else {
    reg_exchg_cmem_twiddles_inv<8, 16, 1>(vals, tile_exchg_region_offset);
    tile_exchg_region_offset <<= 1;
    reg_exchg_cmem_twiddles_inv<4, 8, 2>(vals, tile_exchg_region_offset);
    tile_exchg_region_offset <<= 1;
    reg_exchg_cmem_twiddles_inv<2, 4, 4>(vals, tile_exchg_region_offset);
    tile_exchg_region_offset <<= 1;
    reg_exchg_cmem_twiddles_inv<1, 2, 8>(vals, tile_exchg_region_offset);
  }

#pragma unroll
  for (int i{0}, row{thread_ct_gmem_start}; i < VALS_PER_THREAD; i++, row += tile_gmem_stride)
    gmem_out.set_at_row(row, vals[i]); // write consecutive gmem tiles
}

template <int STAGES>
DEVICE_FORCEINLINE void evals_to_monomials_final_up_to_8_stages(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out,
                                                                const bool transposed_monomials, const int log_n) {
  constexpr int WARP_SIZE = 32;
  constexpr int VALS_PER_THREAD = 32;
  constexpr int VALS_PER_WARP = WARP_SIZE * VALS_PER_THREAD;
  constexpr int WARPS_PER_BLOCK = 8;
  constexpr int VALS_PER_BLOCK = WARPS_PER_BLOCK * WARP_SIZE * VALS_PER_THREAD; // 8192
  constexpr int INITIAL_EXCHG_REGIONS_PER_WARP = 1 << (10 - STAGES);

  const int lane_id = threadIdx.x & 31;
  const int warp_id = threadIdx.x >> 5;
  const int pipeline_memcpy_start = 4 * threadIdx.x;
  const int pipeline_memcpy_stride = 4 * blockDim.x;
  const int gmem_block_offset = blockIdx.x * VALS_PER_BLOCK;
  gmem_in.add_row(gmem_block_offset + warp_id * VALS_PER_WARP);
  gmem_out.add_row(gmem_block_offset + warp_id * VALS_PER_WARP);

  __shared__ bf smem_block[8192]; // 4096 vals, 4096 coarse twiddles
  bf *smem_warp = smem_block + (warp_id & 3) * VALS_PER_WARP;
  bf *smem_twiddles = smem_block + (VALS_PER_BLOCK >> 1);

  bf vals[VALS_PER_THREAD];

  // Cooperatively fetch coarse gmem twiddle powers used by last 5 stages.
  // The gmem layout is already swizzled, so it's a linear copy and we can vectorize :)
  // The cooperative twiddle fetch is actually the only reason this kernel needs a __syncthreads().
  // Unlike the 2-pass kernel, there's no compute overlap here, but gmem->smem is preferable to gmem->register->smem.
#pragma unroll
  for (int i{0}, addr{pipeline_memcpy_start}; i < 4; i++, addr += pipeline_memcpy_stride)
    __pipeline_memcpy_async(smem_twiddles + addr, ab_inv_gmem_twiddles_coarse + addr, 4 * sizeof(bf));
  __pipeline_commit();

#pragma unroll
  for (int i{0}, row{lane_id}; i < VALS_PER_THREAD; i++, row += WARP_SIZE)
    vals[i] = gmem_in.get_at_row(row);

  // Use pure cmem for warp-uniform twiddles
  if (STAGES >= 5) {
    int warp_exchg_region_offset = INITIAL_EXCHG_REGIONS_PER_WARP * (blockIdx.x * WARPS_PER_BLOCK + warp_id);
#pragma unroll
    for (int i{0}; i < INITIAL_EXCHG_REGIONS_PER_WARP; i++) {
      int exchg_region_offset = warp_exchg_region_offset + i;
      if (STAGES == 8) {
        bf *vals_this_region = vals + 8 * i;
        reg_exchg_cmem_twiddles_inv<4, 8, 1>(vals_this_region, exchg_region_offset);
        exchg_region_offset <<= 1;
        reg_exchg_cmem_twiddles_inv<2, 4, 2>(vals_this_region, exchg_region_offset);
        exchg_region_offset <<= 1;
        reg_exchg_cmem_twiddles_inv<1, 2, 4>(vals_this_region, exchg_region_offset);
      }
      if (STAGES == 7) {
        bf *vals_this_region = vals + 4 * i;
        reg_exchg_cmem_twiddles_inv<2, 4, 1>(vals_this_region, exchg_region_offset);
        exchg_region_offset <<= 1;
        reg_exchg_cmem_twiddles_inv<1, 2, 2>(vals_this_region, exchg_region_offset);
      }
      if (STAGES == 6) {
        bf *vals_this_region = vals + 2 * i;
        reg_exchg_cmem_twiddles_inv<1, 2, 1>(vals_this_region, exchg_region_offset);
      }
    }
  }

  // Register transpose from https://forums.developer.nvidia.com/t/transpose-2d-matrix-with-warp-shuffle-and-in-place-array/164045.
  // The problem is, it spills registers due to threadIdx.x being dynamic. I don't see an easy fix.
  // #pragma unroll
  //   for (int i = 1; i < 32; i++){
  //     int idx = i; // threadIdx.x ^ i;
  //     vals[idx].limb = __shfl_sync(0xffffffff, vals[idx].limb, idx);
  //   }

  if (warp_id & 4) {
#pragma unroll
    for (int y = 0; y < VALS_PER_THREAD; y++)
      smem_warp[xy_to_swizzled(lane_id, y)] = vals[y];
    __syncwarp();
#pragma unroll
    for (int x = 0; x < VALS_PER_THREAD; x++)
      vals[x] = smem_warp[xy_to_swizzled(x, lane_id)];
  }

  __pipeline_wait_prior(0);

  __syncthreads();

  if (!(warp_id & 4)) {
#pragma unroll
    for (int y = 0; y < VALS_PER_THREAD; y++)
      smem_warp[xy_to_swizzled(lane_id, y)] = vals[y];
    __syncwarp();
#pragma unroll
    for (int x = 0; x < VALS_PER_THREAD; x++)
      vals[x] = smem_warp[xy_to_swizzled(x, lane_id)];
  }

  int thread_exchg_region_offset = threadIdx.x + blockIdx.x * blockDim.x;
  constexpr bf *cmem_twiddles = ab_inv_cmem_twiddles_finest_11;
  reg_exchg_cmem_smem_twiddles_inv<EightStages, 16, 32, 1, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);
  thread_exchg_region_offset <<= 1;
  reg_exchg_cmem_smem_twiddles_inv<EightStages, 8, 16, 2, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);
  thread_exchg_region_offset <<= 1;
  reg_exchg_cmem_smem_twiddles_inv<EightStages, 4, 8, 4, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);
  thread_exchg_region_offset <<= 1;
  reg_exchg_cmem_smem_twiddles_inv<EightStages, 2, 4, 8, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);
  thread_exchg_region_offset <<= 1;
  reg_exchg_cmem_smem_twiddles_inv<EightStages, 1, 2, 16, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);

  const bf size_inv = ab_inv_sizes[log_n];
#pragma unroll
  for (int i = 0; i < 32; i++)
    vals[i] = bf::mul(vals[i], size_inv);

  if (transposed_monomials) {
#pragma unroll
    for (int i{0}, row{lane_id}; i < VALS_PER_THREAD; i++, row += WARP_SIZE)
      gmem_out.set_at_row(row, vals[i]);
  } else {
    // Simple option: uncoalesced, but vectorized and should fire off quickly.
    //     uint4 *gmem_monomials_out_ptr = reinterpret_cast<uint4 *>(gmem_out.ptr + VALS_PER_THREAD * lane_id);
    // #pragma unroll
    //     for (int i{0}; i < VALS_PER_THREAD; i += 4, gmem_monomials_out_ptr++)
    //       *gmem_monomials_out_ptr = {vals[i].limb, vals[i + 1].limb, vals[i + 2].limb, vals[i + 3].limb};

    // Unfortunately, 5090 seems to hate the uncoalesced stores. So instead we un-swizzle and store with coalescing.
    __syncthreads(); // Alternatively, we could try shuffle transpose to avoid the sync, or have some warps shuffle and some do smem swizzle.

    smem_warp = smem_block + warp_id * VALS_PER_WARP;
#pragma unroll
    for (int y = 0; y < VALS_PER_THREAD; y++)
      smem_warp[xy_to_swizzled(lane_id, y)] = vals[y];
    __syncwarp();
#pragma unroll
    for (int x = 0; x < VALS_PER_THREAD; x++)
      vals[x] = smem_warp[xy_to_swizzled(x, lane_id)];

#pragma unroll
    for (int i{0}, row{lane_id}; i < VALS_PER_THREAD; i++, row += WARP_SIZE)
      gmem_out.set_at_row(row, vals[i]);
  }
}

EXTERN __launch_bounds__(256, 3) __global__
    void ab_evals_to_monomials_final_8_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out,
                                                     const bool transposed_monomials, const int log_n) {
  evals_to_monomials_final_up_to_8_stages<8>(gmem_in, gmem_out, transposed_monomials, log_n);
}

EXTERN __launch_bounds__(256, 3) __global__
    void ab_evals_to_monomials_final_7_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out,
                                                     const bool transposed_monomials, const int log_n) {
  evals_to_monomials_final_up_to_8_stages<7>(gmem_in, gmem_out, transposed_monomials, log_n);
}

EXTERN __launch_bounds__(256, 3) __global__
    void ab_evals_to_monomials_final_6_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out,
                                                     const bool transposed_monomials, const int log_n) {
  evals_to_monomials_final_up_to_8_stages<6>(gmem_in, gmem_out, transposed_monomials, log_n);
}

EXTERN __launch_bounds__(256, 3) __global__
    void ab_evals_to_monomials_final_5_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out,
                                                     const bool transposed_monomials, const int log_n) {
  evals_to_monomials_final_up_to_8_stages<5>(gmem_in, gmem_out, transposed_monomials, log_n);
}

} // namespace airbender::ntt
