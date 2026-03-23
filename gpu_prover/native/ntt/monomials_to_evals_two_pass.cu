#include "ntt.cuh"

namespace airbender::ntt {

EXTERN __launch_bounds__(512, 1) __global__
    void ab_monomials_to_evals_last_10_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out, const int log_n,
                                                     const int start_stage /*unused, for symmetry with three-pass*/) {
  constexpr int VALS_PER_THREAD = 32;
  constexpr int LOG_DATA_TILE_SIZE = 4;
  constexpr int TILE_SIZE = 1 << LOG_DATA_TILE_SIZE;
  constexpr int LOG_DATA_TILES_PER_BLOCK = 10;
  constexpr int THREAD_TILES_PER_BLOCK = 32;
  constexpr int TILE_GMEM_STRIDE = 1 << (24 - LOG_DATA_TILES_PER_BLOCK);
  constexpr int IL_GMEM_STRIDE = TILE_GMEM_STRIDE * THREAD_TILES_PER_BLOCK;

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

#pragma unroll
  for (int i{0}, row{thread_ct_gmem_start}; i < 32; i++, row += TILE_GMEM_STRIDE)
    vals[i] = gmem_in.get_at_row(row); // read consecutive gmem tiles

  int tile_exchg_region_offset = tile_id << 4;
  reg_exchg_fwd<1, 2, 16>(vals, tile_exchg_region_offset);
  tile_exchg_region_offset >>= 1;
  reg_exchg_fwd<2, 4, 8>(vals, tile_exchg_region_offset);
  tile_exchg_region_offset >>= 1;
  reg_exchg_fwd<4, 8, 4>(vals, tile_exchg_region_offset);
  tile_exchg_region_offset >>= 1;
  reg_exchg_fwd<8, 16, 2>(vals, tile_exchg_region_offset);
  tile_exchg_region_offset >>= 1;
  reg_exchg_fwd<16, 32, 1>(vals, tile_exchg_region_offset);

#pragma unroll
  for (int i{0}, addr{thread_ct_smem_start}; i < 32; i++, addr += TILE_SIZE)
    smem_block[addr] = vals[i]; // write consecutive smem tiles

  __syncthreads();

#pragma unroll
  for (int i{0}, addr{thread_il_smem_start}; i < 32; i++, addr += TILE_SIZE * THREAD_TILES_PER_BLOCK)
    vals[i] = smem_block[addr]; // read interleaved smem tiles

  reg_exchg_fwd<1, 2, 16>(vals);
  reg_exchg_fwd<2, 4, 8>(vals);
  reg_exchg_fwd<4, 8, 4>(vals);
  reg_exchg_fwd<8, 16, 2>(vals);
  reg_exchg_final_fwd<16>(vals);

  for (int i{0}, addr{thread_il_gmem_start}; i < 32; i++, addr += IL_GMEM_STRIDE)
    gmem_out.set_at_row(addr, vals[i]); // write interleaved gmem tiles
}

EXTERN __launch_bounds__(512, 1) __global__
    void ab_monomials_to_evals_last_9_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out, const int log_n,
                                                    const int start_stage /*unused, for symmetry with three-pass*/) {
  constexpr int VALS_PER_THREAD = 32;
  constexpr int LOG_DATA_TILE_SIZE = 5;
  constexpr int TILE_SIZE = 1 << LOG_DATA_TILE_SIZE;
  constexpr int LOG_DATA_TILES_PER_BLOCK = 9;
  constexpr int THREAD_TILES_PER_BLOCK = 16;
  constexpr int TILE_GMEM_STRIDE = 1 << (23 - LOG_DATA_TILES_PER_BLOCK);
  constexpr int IL_GMEM_STRIDE = TILE_GMEM_STRIDE * THREAD_TILES_PER_BLOCK;

  // TODO: make some of these kernel arguments
  const int lane_in_tile = threadIdx.x & 31;
  const int tile_id = threadIdx.x >> LOG_DATA_TILE_SIZE;
  const int tile_gmem_stride = 1 << (log_n - LOG_DATA_TILES_PER_BLOCK);
  const int gmem_block_offset = blockIdx.x << LOG_DATA_TILE_SIZE;
  gmem_in.add_row(gmem_block_offset);
  gmem_out.add_row(gmem_block_offset);

  extern __shared__ bf smem_block[]; // 16384 * 4 bytes

  bf vals[VALS_PER_THREAD];

  // "ct" = consecutive tile layout
  // "it" = interleaved tile layout
  const int thread_il_gmem_start = lane_in_tile + tile_id * TILE_GMEM_STRIDE;
  const int thread_ct_gmem_start = lane_in_tile + 2 * tile_id * IL_GMEM_STRIDE;
  const int thread_il_smem_start = lane_in_tile + tile_id * TILE_SIZE;
  const int thread_ct_smem_start = lane_in_tile + tile_id * TILE_SIZE * 2 * THREAD_TILES_PER_BLOCK;

#pragma unroll
  for (int i{0}, row{thread_ct_gmem_start}; i < 32; i++, row += tile_gmem_stride)
    vals[i] = gmem_in.get_at_row(row); // read consecutive gmem tiles

  int tile_exchg_region_offset = tile_id << 4;
  reg_exchg_fwd<1, 2, 16>(vals, tile_exchg_region_offset);
  tile_exchg_region_offset >>= 1;
  reg_exchg_fwd<2, 4, 8>(vals, tile_exchg_region_offset);
  tile_exchg_region_offset >>= 1;
  reg_exchg_fwd<4, 8, 4>(vals, tile_exchg_region_offset);
  tile_exchg_region_offset >>= 1;
  reg_exchg_fwd<8, 16, 2>(vals, tile_exchg_region_offset);
  // reg_exchg_fwd<16, 32, 1>(vals, tile_exchg_region_offset);

#pragma unroll
  for (int i{0}, addr{thread_ct_smem_start}; i < 32; i++, addr += TILE_SIZE)
    smem_block[addr] = vals[i]; // write consecutive smem tiles

  __syncthreads();

#pragma unroll
  for (int i{0}, addr{thread_il_smem_start}; i < 32; i++, addr += TILE_SIZE * THREAD_TILES_PER_BLOCK)
    vals[i] = smem_block[addr]; // read interleaved smem tiles

  reg_exchg_fwd<1, 2, 16>(vals, 0);
  reg_exchg_fwd<2, 4, 8>(vals, 0);
  reg_exchg_fwd<4, 8, 4>(vals, 0);
  reg_exchg_fwd<8, 16, 2>(vals, 0);
  reg_exchg_fwd<16, 32, 1>(vals, 0);

  for (int i{0}, addr{thread_il_gmem_start}; i < 32; i++, addr += IL_GMEM_STRIDE)
    gmem_out.set_at_row(addr, vals[i]); // write interleaved gmem tiles
}

EXTERN __launch_bounds__(512, 1) __global__
    void ab_monomials_to_evals_first_14_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out,
                                                      const bool transposed_monomials, const int log_n, const int coset_factor_power) {
  constexpr int WARP_SIZE = 32;
  constexpr int VALS_PER_THREAD = 32;
  constexpr int WARPS_PER_BLOCK = 16;
  constexpr int VALS_PER_BLOCK = WARPS_PER_BLOCK * WARP_SIZE * VALS_PER_THREAD; // 16384

  const int lane_id = threadIdx.x & 31;
  const int warp_id = threadIdx.x >> 5;
  const int tile_stride = VALS_PER_BLOCK >> 4;
  const int gmem_block_offset = blockIdx.x * VALS_PER_BLOCK;
  const int thread_start = 64 * warp_id + lane_id;
  const int pipeline_memcpy_start = 4 * threadIdx.x;
  const int pipeline_memcpy_stride = 4 * blockDim.x;
  gmem_in.add_row(gmem_block_offset + warp_id * 1024);
  gmem_out.add_row(gmem_block_offset);

  extern __shared__ bf smem_block[]; // 16384 vals + 8192 twiddles
  bf *smem_warp = smem_block + warp_id * 1024;
  bf *smem_twiddles = smem_block + VALS_PER_BLOCK;
  constexpr bf *cmem_twiddles = ab_fwd_cmem_twiddles_finest_10;

  bf vals[VALS_PER_THREAD];

  // Prefetch fine gmem twiddle powers used by last 5 stages.
  // The gmem layout is already swizzled, so it's a linear copy and we can vectorize :)
#pragma unroll
  for (int i{0}, addr{pipeline_memcpy_start}; i < 4; i++, addr += pipeline_memcpy_stride)
    __pipeline_memcpy_async(smem_twiddles + addr, ab_fwd_gmem_twiddles_coarse + addr, 4 * sizeof(bf));
  __pipeline_commit();

#pragma unroll
  for (int i{0}, row{lane_id}; i < VALS_PER_THREAD; i++, row += WARP_SIZE)
    vals[i] = gmem_in.get_at_row(row);

  // A separate adjustment loop performs better than interleaving adjustments with loads.
  if (coset_factor_power > 0) {
#pragma unroll
    for (int i{0}, global_row{lane_id + gmem_block_offset + warp_id * 1024}; i < VALS_PER_THREAD; i++, global_row += WARP_SIZE) {
      const int effective_row = transposed_monomials ? transposed_row_to_effective_row(global_row) : global_row;
      const bf coset_offset = get_power_from_layers(::ab_ntt_forward_powers, bitrev(effective_row, log_n) * coset_factor_power);
      vals[i] = bf::mul(vals[i], coset_offset);
    }
  }

  if (!transposed_monomials) {
    // transpose coalesced loads into registers
#pragma unroll
    for (int y = 0; y < 32; y++)
      smem_warp[xy_to_swizzled(lane_id, y)] = vals[y];
    __syncwarp();
#pragma unroll
    for (int x = 0; x < 32; x++)
      vals[x] = smem_warp[xy_to_swizzled(x, lane_id)];
  }

  __pipeline_wait_prior(0); // Unfortunately we use all the coarse twiddles in the first exchange, so we can't overlap this with compute.
  __syncthreads();

  int thread_exchg_region_offset = (threadIdx.x + blockIdx.x * blockDim.x) << 4;
  reg_exchg_cmem_smem_twiddles_fwd<TenStages, 1, 2, 16, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);
  thread_exchg_region_offset >>= 1;
  reg_exchg_cmem_smem_twiddles_fwd<TenStages, 2, 4, 8, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);
  thread_exchg_region_offset >>= 1;
  reg_exchg_cmem_smem_twiddles_fwd<TenStages, 4, 8, 4, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);
  thread_exchg_region_offset >>= 1;
  reg_exchg_cmem_smem_twiddles_fwd<TenStages, 8, 16, 2, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);
  thread_exchg_region_offset >>= 1;
  reg_exchg_cmem_smem_twiddles_fwd<TenStages, 16, 32, 1, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);

#pragma unroll
  for (int y = 0; y < 32; y++)
    smem_warp[xy_to_swizzled(lane_id, y)] = vals[y];
  __syncwarp();
#pragma unroll
  for (int x = 0; x < 32; x++)
    vals[x] = smem_warp[xy_to_swizzled(x, lane_id)];

  int warp_exchg_region_offset = (blockIdx.x * WARPS_PER_BLOCK + warp_id) << 4;
  reg_exchg_cmem_twiddles_fwd<1, 2, 16>(vals, warp_exchg_region_offset);
  warp_exchg_region_offset >>= 1;
  reg_exchg_cmem_twiddles_fwd<2, 4, 8>(vals, warp_exchg_region_offset);
  warp_exchg_region_offset >>= 1;
  reg_exchg_cmem_twiddles_fwd<4, 8, 4>(vals, warp_exchg_region_offset);
  warp_exchg_region_offset >>= 1;
  reg_exchg_cmem_twiddles_fwd<8, 16, 2>(vals, warp_exchg_region_offset);
  warp_exchg_region_offset >>= 1;
  reg_exchg_cmem_twiddles_fwd<16, 32, 1>(vals, warp_exchg_region_offset);

  __syncwarp();
#pragma unroll
  for (int i{0}, row{lane_id}; i < 32; i++, row += 32)
    smem_warp[row] = vals[i];

  __syncthreads(); // all-to-all, so ptx barriers are unlikely to help

#pragma unroll
  for (int i{0}, row{thread_start}; i < 32; i += 2, row += tile_stride) {
    vals[i] = smem_block[row];
    vals[i + 1] = smem_block[row + 32];
  }

  int block_exchg_region_offset = blockIdx.x << 3;
  reg_exchg_cmem_twiddles_fwd<2, 4, 8>(vals, block_exchg_region_offset);
  block_exchg_region_offset >>= 1;
  reg_exchg_cmem_twiddles_fwd<4, 8, 4>(vals, block_exchg_region_offset);
  block_exchg_region_offset >>= 1;
  reg_exchg_cmem_twiddles_fwd<8, 16, 2>(vals, block_exchg_region_offset);
  block_exchg_region_offset >>= 1;
  reg_exchg_cmem_twiddles_fwd<16, 32, 1>(vals, block_exchg_region_offset);

#pragma unroll
  for (int i{0}, row{thread_start}; i < 32; i += 2, row += tile_stride) {
    gmem_out.set_at_row(row, vals[i]);
    gmem_out.set_at_row(row + 32, vals[i + 1]);
  }
}

} // namespace airbender::ntt
