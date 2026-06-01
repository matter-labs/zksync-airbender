#include "ntt.cuh"
#include "pass_config.cuh"

namespace airbender::ntt {

EXTERN __launch_bounds__(512, 1) __global__
    void ab_evals_to_monomials_first_10_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out, const int log_n,
                                                      const int start_stage /*unused, for symmetry with three-pass API*/, const int num_cols_per_coset,
                                                      const int log_cosets_in_tile) {
  using namespace pass_config::two_pass_phase_a;
  using namespace pass_config::pipeline_prefetch;

  // Flat-blockIdx.x layout: gridDim.x packs blocks_per_ntt (= n / 16384 =
  // 1 << (log_n - 14)) blocks per NTT, then cosets in tile, then columns.
  const unsigned log_blocks_per_ntt = static_cast<unsigned>(log_n) - 14u;
  const FlatBlockIndex fi = decompose_flat_1d(log_blocks_per_ntt, static_cast<unsigned>(log_cosets_in_tile));
  const int col_offset = static_cast<int>(fi.coset) * num_cols_per_coset + static_cast<int>(fi.col);
  gmem_in.add_col(col_offset);
  gmem_out.add_col(col_offset);

  const int lane_in_tile = threadIdx.x & 15;
  const int tile_id = threadIdx.x >> LOG_DATA_TILE_SIZE;
  const int gmem_block_offset = static_cast<int>(fi.intra_x) << LOG_DATA_TILE_SIZE;
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

  const bf twiddle = ab_inv_cmem_twiddles_coarse[1];
  prefetch_pipeline_group<0, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg_pipeline_group<0>(vals, twiddle);
  prefetch_pipeline_group<1, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg_pipeline_group<1>(vals, twiddle);
  prefetch_pipeline_group<2, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg_pipeline_group<2>(vals, twiddle);
  prefetch_pipeline_group<3, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg_pipeline_group<3>(vals, twiddle);
  prefetch_pipeline_group<4, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg_pipeline_group<4>(vals, twiddle);
  prefetch_pipeline_group<5, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg_pipeline_group<5>(vals, twiddle);
  prefetch_pipeline_group<6, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg_pipeline_group<6>(vals, twiddle);
  prefetch_pipeline_group<7, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg_pipeline_group<7>(vals, twiddle);

  reg_exchg_inv<4, 8, 4>(vals, 0);
  reg_exchg_inv<2, 4, 8>(vals, 0);
  reg_exchg_inv<1, 2, 16>(vals, 0);

#pragma unroll
  for (int i{0}, addr{thread_il_smem_start}; i < 32; i++, addr += TILE_SIZE * THREAD_TILES_PER_BLOCK)
    smem_block[addr] = vals[i]; // write interleaved smem tiles

  __syncthreads();

#pragma unroll
  for (int i{0}, addr{thread_ct_smem_start}; i < 32; i++, addr += TILE_SIZE)
    vals[i] = smem_block[addr]; // read consecutive smem tiles

  int tile_exchg_region_offset = tile_id;
  reg_exchg_inv<16, 32, 1>(vals, tile_exchg_region_offset);
  tile_exchg_region_offset <<= 1;
  reg_exchg_inv<8, 16, 2>(vals, tile_exchg_region_offset);
  tile_exchg_region_offset <<= 1;
  reg_exchg_inv<4, 8, 4>(vals, tile_exchg_region_offset);
  tile_exchg_region_offset <<= 1;
  reg_exchg_inv<2, 4, 8>(vals, tile_exchg_region_offset);
  tile_exchg_region_offset <<= 1;
  reg_exchg_inv<1, 2, 16>(vals, tile_exchg_region_offset);

#pragma unroll
  for (int i{0}, row{thread_ct_gmem_start}; i < 32; i++, row += TILE_GMEM_STRIDE)
    gmem_out.set_at_row(row, vals[i]); // write consecutive gmem tiles
}

EXTERN __launch_bounds__(512, 1) __global__
    void ab_evals_to_monomials_first_9_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out, const int log_n,
                                                     const int start_stage /*unused, for symmetry with three-pass API*/, const int num_cols_per_coset,
                                                     const int log_cosets_in_tile) {
  using namespace pass_config::two_pass_phase_b;
  using namespace pass_config::pipeline_prefetch;

  // Flat-blockIdx.x layout: gridDim.x packs blocks_per_ntt (= n / 16384 =
  // 1 << (log_n - 14)) blocks per NTT, then cosets in tile, then columns.
  const unsigned log_blocks_per_ntt = static_cast<unsigned>(log_n) - 14u;
  const FlatBlockIndex fi = decompose_flat_1d(log_blocks_per_ntt, static_cast<unsigned>(log_cosets_in_tile));
  const int col_offset = static_cast<int>(fi.coset) * num_cols_per_coset + static_cast<int>(fi.col);
  gmem_in.add_col(col_offset);
  gmem_out.add_col(col_offset);

  const int lane_in_tile = threadIdx.x & 31;
  const int tile_id = threadIdx.x >> LOG_DATA_TILE_SIZE;
  const int gmem_block_offset = static_cast<int>(fi.intra_x) << LOG_DATA_TILE_SIZE;
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

  const bf twiddle = ab_inv_cmem_twiddles_coarse[1];
  prefetch_pipeline_group<0, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg_pipeline_group<0>(vals, twiddle);
  prefetch_pipeline_group<1, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg_pipeline_group<1>(vals, twiddle);
  prefetch_pipeline_group<2, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg_pipeline_group<2>(vals, twiddle);
  prefetch_pipeline_group<3, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg_pipeline_group<3>(vals, twiddle);
  prefetch_pipeline_group<4, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg_pipeline_group<4>(vals, twiddle);
  prefetch_pipeline_group<5, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg_pipeline_group<5>(vals, twiddle);
  prefetch_pipeline_group<6, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg_pipeline_group<6>(vals, twiddle);
  prefetch_pipeline_group<7, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  exchg_pipeline_group<7>(vals, twiddle);

  reg_exchg_inv<4, 8, 4>(vals, 0);
  reg_exchg_inv<2, 4, 8>(vals, 0);
  reg_exchg_inv<1, 2, 16>(vals, 0);

#pragma unroll
  for (int i{0}, addr{thread_il_smem_start}; i < 32; i++, addr += TILE_SIZE * THREAD_TILES_PER_BLOCK)
    smem_block[addr] = vals[i]; // write interleaved smem tiles

  __syncthreads();

#pragma unroll
  for (int i{0}, addr{thread_ct_smem_start}; i < 32; i++, addr += TILE_SIZE)
    vals[i] = smem_block[addr]; // read consecutive smem tiles

  int tile_exchg_region_offset = 2 * tile_id;
  // reg_exchg_inv<16, 32, 1>(vals, tile_exchg_region_offset); tile_exchg_region_offset <<= 1;
  reg_exchg_inv<8, 16, 2>(vals, tile_exchg_region_offset);
  tile_exchg_region_offset <<= 1;
  reg_exchg_inv<4, 8, 4>(vals, tile_exchg_region_offset);
  tile_exchg_region_offset <<= 1;
  reg_exchg_inv<2, 4, 8>(vals, tile_exchg_region_offset);
  tile_exchg_region_offset <<= 1;
  reg_exchg_inv<1, 2, 16>(vals, tile_exchg_region_offset);

#pragma unroll
  for (int i{0}, row{thread_ct_gmem_start}; i < 32; i++, row += TILE_GMEM_STRIDE)
    gmem_out.set_at_row(row, vals[i]); // write consecutive gmem tiles
}

EXTERN __launch_bounds__(512, 1) __global__
    void ab_evals_to_monomials_last_14_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out,
                                                     const bool transposed_monomials, const int log_n, const int num_cols_per_coset,
                                                     const int log_cosets_in_tile) {
  using namespace pass_config::two_pass_phase_c;

  // Flat-blockIdx.x layout: gridDim.x packs blocks_per_ntt (= n / VALS_PER_BLOCK
  // = 1 << (log_n - 14)) blocks per NTT, then cosets in tile, then columns.
  // `log_cosets_in_tile = 0` collapses to the original single-coset layout.
  const unsigned log_blocks_per_ntt = static_cast<unsigned>(log_n) - 14u;
  const FlatBlockIndex fi = decompose_flat_1d(log_blocks_per_ntt, static_cast<unsigned>(log_cosets_in_tile));
  const int col_offset = static_cast<int>(fi.coset) * num_cols_per_coset + static_cast<int>(fi.col);
  gmem_in.add_col(col_offset);
  gmem_out.add_col(col_offset);

  const int lane_id = threadIdx.x & 31;
  const int warp_id = threadIdx.x >> 5;
  const int tile_stride = VALS_PER_BLOCK >> 4;
  const int gmem_block_offset = static_cast<int>(fi.intra_x) * VALS_PER_BLOCK;
  const int thread_start = 64 * warp_id + lane_id;
  const int pipeline_memcpy_start = 4 * threadIdx.x;
  const int pipeline_memcpy_stride = 4 * blockDim.x;
  gmem_in.add_row(gmem_block_offset);
  gmem_out.add_row(gmem_block_offset + warp_id * 1024);

  extern __shared__ bf smem_block[]; // 16384 vals + 8192 twiddles
  bf *smem_warp = smem_block + warp_id * 1024;
  bf *smem_twiddles = smem_block + VALS_PER_BLOCK;
  constexpr bf *cmem_twiddles = ab_inv_cmem_twiddles_finest_10;

  bf vals[VALS_PER_THREAD];

#pragma unroll
  for (int i{0}, row{thread_start}; i < 32; i += 2, row += tile_stride) {
    vals[i] = gmem_in.get_at_row(row);
    vals[i + 1] = gmem_in.get_at_row(row + 32);
  }

  // Prefetch coarse gmem twiddle powers used by last 5 stages.
  // The gmem layout is already swizzled, so it's a linear copy and we can vectorize :)
#pragma unroll
  for (int i{0}, addr{pipeline_memcpy_start}; i < 4; i++, addr += pipeline_memcpy_stride)
    __pipeline_memcpy_async(smem_twiddles + addr, ab_inv_gmem_twiddles_coarse + addr, 4 * sizeof(bf));
  __pipeline_commit();

  int block_exchg_region_offset = static_cast<int>(fi.intra_x);
  reg_exchg_cmem_twiddles_inv<16, 32, 1>(vals, block_exchg_region_offset);
  block_exchg_region_offset <<= 1;
  reg_exchg_cmem_twiddles_inv<8, 16, 2>(vals, block_exchg_region_offset);
  block_exchg_region_offset <<= 1;
  reg_exchg_cmem_twiddles_inv<4, 8, 4>(vals, block_exchg_region_offset);
  block_exchg_region_offset <<= 1;
  reg_exchg_cmem_twiddles_inv<2, 4, 8>(vals, block_exchg_region_offset);
  block_exchg_region_offset <<= 1;

#pragma unroll
  for (int i{0}, row{thread_start}; i < 32; i += 2, row += tile_stride) {
    smem_block[row] = vals[i];
    smem_block[row + 32] = vals[i + 1];
  }

  __pipeline_wait_prior(0);

  __syncthreads(); // all-to-all, so ptx barriers are unlikely to help

#pragma unroll
  for (int i{0}, row{lane_id}; i < 32; i++, row += 32)
    vals[i] = smem_warp[row];

  int warp_exchg_region_offset = block_exchg_region_offset + warp_id;
  reg_exchg_cmem_twiddles_inv<16, 32, 1>(vals, warp_exchg_region_offset);
  warp_exchg_region_offset <<= 1;
  reg_exchg_cmem_twiddles_inv<8, 16, 2>(vals, warp_exchg_region_offset);
  warp_exchg_region_offset <<= 1;
  reg_exchg_cmem_twiddles_inv<4, 8, 4>(vals, warp_exchg_region_offset);
  warp_exchg_region_offset <<= 1;
  reg_exchg_cmem_twiddles_inv<2, 4, 8>(vals, warp_exchg_region_offset);
  warp_exchg_region_offset <<= 1;
  reg_exchg_cmem_twiddles_inv<1, 2, 16>(vals, warp_exchg_region_offset);
  warp_exchg_region_offset <<= 1;

  __syncwarp();
#pragma unroll
  for (int y = 0; y < 32; y++)
    smem_warp[xy_to_swizzled(lane_id, y)] = vals[y];
  __syncwarp();
#pragma unroll
  for (int x = 0; x < 32; x++)
    vals[x] = smem_warp[xy_to_swizzled(x, lane_id)];

  int thread_exchg_region_offset = warp_exchg_region_offset + lane_id;
  reg_exchg_cmem_smem_twiddles_inv<TenStages, 16, 32, 1, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);
  thread_exchg_region_offset <<= 1;
  reg_exchg_cmem_smem_twiddles_inv<TenStages, 8, 16, 2, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);
  thread_exchg_region_offset <<= 1;
  reg_exchg_cmem_smem_twiddles_inv<TenStages, 4, 8, 4, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);
  thread_exchg_region_offset <<= 1;
  reg_exchg_cmem_smem_twiddles_inv<TenStages, 2, 4, 8, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);
  thread_exchg_region_offset <<= 1;
  reg_exchg_cmem_smem_twiddles_inv<TenStages, 1, 2, 16, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);

  const bf size_inv = ab_inv_sizes[log_n];
#pragma unroll
  for (int i = 0; i < 32; i++)
    vals[i] = bf::mul(vals[i], size_inv);

  if (transposed_monomials) {
#pragma unroll
    for (int i{0}, row{lane_id}; i < VALS_PER_THREAD; i++, row += WARP_SIZE)
      gmem_out.set_at_row(row, vals[i]);
  } else {
    // uncoalesced, but vectorized and should fire off quickly
    //     uint4 *gmem_monomials_out_ptr = reinterpret_cast<uint4 *>(gmem_out.ptr + 32 * lane_id);
    // #pragma unroll
    //     for (int i{0}; i < 32; i += 4, gmem_monomials_out_ptr++)
    //       *gmem_monomials_out_ptr = {vals[i].limb, vals[i + 1].limb, vals[i + 2].limb, vals[i + 3].limb};

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
