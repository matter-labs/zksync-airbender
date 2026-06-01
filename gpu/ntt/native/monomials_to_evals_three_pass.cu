#include "ntt.cuh"
#include "pass_config.cuh"

namespace airbender::ntt {

EXTERN __launch_bounds__(512, 2) __global__
    void ab_monomials_to_evals_noninitial_8_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out,
                                                          const int log_n, const int start_stage, const int num_cols_per_coset, const int log_cosets_in_tile) {
  using namespace pass_config::three_pass_phase_a;

  const int lane_in_tile = threadIdx.x & 31;
  const int tile_id = threadIdx.x >> LOG_DATA_TILE_SIZE;

  const int exchg_region_size = 1 << (start_stage + 8);
  const int tile_gmem_stride = exchg_region_size >> LOG_DATA_TILES_PER_BLOCK;
  const int interleaved_gmem_stride = tile_gmem_stride * THREAD_TILES_PER_BLOCK;

  // Flat-blockIdx.x layout (2-D intra-NTT), cosets as the outer axis. With
  // `log_cosets_in_tile = 0` the coset bits vanish and the column offset
  // reduces to fi.col, preserving the single-coset behavior.
  //   log_blocks_x = (start_stage + 8) - 13 = start_stage - 5 (blocks per exchg region)
  //   log_blocks_y = log_n - (start_stage + 8)                (num exchg regions)
  // The alternating-block-index L2 hint applies to the decomposed intra-NTT
  // axes -- reversing the raw flat blockIdx.x would scramble the column factor.
  const unsigned log_blocks_x = static_cast<unsigned>(start_stage - 5);
  const unsigned log_blocks_y = static_cast<unsigned>(log_n - start_stage - 8);
  const FlatBlockIndex fi = decompose_flat_2d(log_blocks_x, log_blocks_y, static_cast<unsigned>(log_cosets_in_tile));
  const int col_offset = static_cast<int>(fi.coset) * num_cols_per_coset + static_cast<int>(fi.col);
  gmem_in.add_col(col_offset);
  gmem_out.add_col(col_offset);
  const unsigned blocks_per_exchg_region = 1u << log_blocks_x;
  const unsigned num_exchg_regions = 1u << log_blocks_y;

  // Reversed block indexing for the middle kernel, to help L2 hits.
  const int alternating_block_idx_x =
      (start_stage == 0) ? static_cast<int>(fi.intra_x) : (static_cast<int>(blocks_per_exchg_region) - 1 - static_cast<int>(fi.intra_x));
  const int alternating_block_idx_y =
      (start_stage == 0) ? static_cast<int>(fi.intra_y) : (static_cast<int>(num_exchg_regions) - 1 - static_cast<int>(fi.intra_y));
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
  for (int i{0}, row{thread_ct_gmem_start}; i < VALS_PER_THREAD; i++, row += tile_gmem_stride)
    vals[i] = gmem_in.get_at_row(row); // read consecutive gmem tiles

  int tile_exchg_region_offset = (alternating_block_idx_y * THREAD_TILES_PER_BLOCK + tile_id) << 3;
  if (start_stage == log_n - 8) {
    reg_exchg_fwd<1, 2, 8>(vals, tile_exchg_region_offset);
    tile_exchg_region_offset >>= 1;
    reg_exchg_fwd<2, 4, 4>(vals, tile_exchg_region_offset);
    tile_exchg_region_offset >>= 1;
    reg_exchg_fwd<4, 8, 2>(vals, tile_exchg_region_offset);
    tile_exchg_region_offset >>= 1;
    reg_exchg_fwd<8, 16, 1>(vals, tile_exchg_region_offset);
  } else {
    reg_exchg_cmem_twiddles_fwd<1, 2, 8>(vals, tile_exchg_region_offset);
    tile_exchg_region_offset >>= 1;
    reg_exchg_cmem_twiddles_fwd<2, 4, 4>(vals, tile_exchg_region_offset);
    tile_exchg_region_offset >>= 1;
    reg_exchg_cmem_twiddles_fwd<4, 8, 2>(vals, tile_exchg_region_offset);
    tile_exchg_region_offset >>= 1;
    reg_exchg_cmem_twiddles_fwd<8, 16, 1>(vals, tile_exchg_region_offset);
  }

#pragma unroll
  for (int i{0}, addr{thread_ct_smem_start}; i < VALS_PER_THREAD; i++, addr += TILE_SIZE)
    smem_block[addr] = vals[i]; // write consecutive smem tiles

  __syncthreads();

#pragma unroll
  for (int i{0}, addr{thread_il_smem_start}; i < VALS_PER_THREAD; i++, addr += TILE_SIZE * THREAD_TILES_PER_BLOCK)
    vals[i] = smem_block[addr]; // read interleaved smem tiles

  if (start_stage == log_n - 8) {
    reg_exchg_fwd<1, 2, 8>(vals);
    reg_exchg_fwd<2, 4, 4>(vals);
    reg_exchg_fwd<4, 8, 2>(vals);
    reg_exchg_final_fwd<8>(vals);
  } else {
    int block_exchg_region_offset = alternating_block_idx_y << 3;
    reg_exchg_cmem_twiddles_fwd<1, 2, 8>(vals, block_exchg_region_offset);
    block_exchg_region_offset >>= 1;
    reg_exchg_cmem_twiddles_fwd<2, 4, 4>(vals, block_exchg_region_offset);
    block_exchg_region_offset >>= 1;
    reg_exchg_cmem_twiddles_fwd<4, 8, 2>(vals, block_exchg_region_offset);
    block_exchg_region_offset >>= 1;
    reg_exchg_cmem_twiddles_fwd<8, 16, 1>(vals, block_exchg_region_offset);
  }

#pragma unroll
  for (int i{0}, addr{thread_il_gmem_start}; i < VALS_PER_THREAD; i++, addr += interleaved_gmem_stride)
    gmem_out.set_at_row(addr, vals[i]);
}

template <int STAGES>
DEVICE_FORCEINLINE void monomials_to_evals_initial_up_to_8_stages(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out,
                                                                  const bool transposed_monomials, const int log_n, const int coset_index_base,
                                                                  const int coset_factor_shift, const int num_cols_per_coset, const int log_cosets_in_tile) {
  using namespace pass_config::three_pass_phase_b;
  constexpr int OUTPUT_EXCHG_REGIONS_PER_WARP = 1 << (10 - STAGES);

  // Flat-blockIdx.x layout: gridDim.x packs blocks_per_ntt (= n / VALS_PER_BLOCK
  // = 1 << (log_n - 13)) blocks per NTT, then cosets in tile, then columns.
  // Inputs are shared across cosets; outputs are coset-major with per-coset
  // stride `num_cols_per_coset`. `log_cosets_in_tile = 0` collapses cleanly.
  const unsigned log_blocks_per_ntt = static_cast<unsigned>(log_n) - 13u; // VALS_PER_BLOCK = 1 << 13
  const FlatBlockIndex fi = decompose_flat_1d(log_blocks_per_ntt, static_cast<unsigned>(log_cosets_in_tile));
  gmem_in.add_col(fi.col);
  gmem_out.add_col(static_cast<int>(fi.coset) * num_cols_per_coset + static_cast<int>(fi.col));
  const int coset_factor_power = (coset_index_base + static_cast<int>(fi.coset)) << coset_factor_shift;

  const int lane_id = threadIdx.x & 31;
  const int warp_id = threadIdx.x >> 5;
  const int pipeline_memcpy_start = 4 * threadIdx.x;
  const int pipeline_memcpy_stride = 4 * blockDim.x;
  const int gmem_block_offset = static_cast<int>(fi.intra_x) * VALS_PER_BLOCK;
  gmem_in.add_row(gmem_block_offset + warp_id * VALS_PER_WARP);
  gmem_out.add_row(gmem_block_offset + warp_id * VALS_PER_WARP);

  __shared__ bf smem_block[8192]; // 4096 vals, 4096 coarse twiddles
  bf *smem_warp = smem_block + (warp_id & 3) * VALS_PER_WARP;
  bf *smem_twiddles = smem_block + (VALS_PER_BLOCK >> 1);

  bf vals[VALS_PER_THREAD];

  // Cooperatively fetch fine gmem twiddle powers used by last 5 stages.
  // The gmem layout is already swizzled, so it's a linear copy and we can vectorize :)
#pragma unroll
  for (int i{0}, addr{pipeline_memcpy_start}; i < 4; i++, addr += pipeline_memcpy_stride)
    __pipeline_memcpy_async(smem_twiddles + addr, ab_fwd_gmem_twiddles_coarse + addr, 4 * sizeof(bf));
  __pipeline_commit();

#pragma unroll
  for (int i{0}, row{lane_id}; i < VALS_PER_THREAD; i++, row += WARP_SIZE)
    vals[i] = gmem_in.get_at_row(row);

  // A separate coset adjustment loop performs better than interleaving adjustments with loads.
  if (coset_factor_power > 0) {
#pragma unroll
    for (int i{0}, global_row{lane_id + gmem_block_offset + warp_id * VALS_PER_WARP}; i < VALS_PER_THREAD; i++, global_row += WARP_SIZE) {
      const int effective_row = transposed_monomials ? transposed_row_to_effective_row(global_row) : global_row;
      const bf coset_offset = get_power_from_layers(::ab_ntt_forward_powers, bitrev(effective_row, log_n) * coset_factor_power);
      vals[i] = bf::mul(vals[i], coset_offset);
    }
  }

  if (transposed_monomials) {
    __pipeline_wait_prior(0); // Unfortunately we use all the coarse twiddles in the first exchange, so we can't overlap this with compute.
    __syncthreads();
  } else {
    // transpose coalesced loads into registers
    if (warp_id & 4) {
#pragma unroll
      for (int y = 0; y < VALS_PER_THREAD; y++)
        smem_warp[xy_to_swizzled(lane_id, y)] = vals[y];
      __syncwarp();
#pragma unroll
      for (int x = 0; x < VALS_PER_THREAD; x++)
        vals[x] = smem_warp[xy_to_swizzled(x, lane_id)];
    }

    __pipeline_wait_prior(0); // might as well also use this sync to ensure twiddles are ready
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
  }

  int thread_exchg_region_offset = (threadIdx.x + static_cast<int>(fi.intra_x) * blockDim.x) << 4;
  constexpr bf *cmem_twiddles = ab_fwd_cmem_twiddles_finest_11;
  reg_exchg_cmem_smem_twiddles_fwd<EightStages, 1, 2, 16, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);
  thread_exchg_region_offset >>= 1;
  reg_exchg_cmem_smem_twiddles_fwd<EightStages, 2, 4, 8, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);
  thread_exchg_region_offset >>= 1;
  reg_exchg_cmem_smem_twiddles_fwd<EightStages, 4, 8, 4, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);
  thread_exchg_region_offset >>= 1;
  reg_exchg_cmem_smem_twiddles_fwd<EightStages, 8, 16, 2, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);
  thread_exchg_region_offset >>= 1;
  reg_exchg_cmem_smem_twiddles_fwd<EightStages, 16, 32, 1, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);

  __syncthreads();

  smem_warp = smem_block + warp_id * VALS_PER_WARP;
#pragma unroll
  for (int y = 0; y < VALS_PER_THREAD; y++)
    smem_warp[xy_to_swizzled(lane_id, y)] = vals[y];
  __syncwarp();
#pragma unroll
  for (int x = 0; x < VALS_PER_THREAD; x++)
    vals[x] = smem_warp[xy_to_swizzled(x, lane_id)];

  // Use pure cmem for warp-uniform twiddles
  if (STAGES >= 5) {
    int warp_exchg_region_offset = (static_cast<int>(fi.intra_x) * WARPS_PER_BLOCK + warp_id) << 4;
#pragma unroll
    for (int i{0}; i < OUTPUT_EXCHG_REGIONS_PER_WARP; i++) {
      if (STAGES == 8) {
        int exchg_region_offset = warp_exchg_region_offset + i * 4;
        bf *vals_this_region = vals + 8 * i;
        reg_exchg_cmem_twiddles_fwd<1, 2, 4>(vals_this_region, exchg_region_offset);
        exchg_region_offset >>= 1;
        reg_exchg_cmem_twiddles_fwd<2, 4, 2>(vals_this_region, exchg_region_offset);
        exchg_region_offset >>= 1;
        reg_exchg_cmem_twiddles_fwd<4, 8, 1>(vals_this_region, exchg_region_offset);
      }
      if (STAGES == 7) {
        int exchg_region_offset = warp_exchg_region_offset + i * 2;
        bf *vals_this_region = vals + 4 * i;
        reg_exchg_cmem_twiddles_fwd<1, 2, 2>(vals_this_region, exchg_region_offset);
        exchg_region_offset >>= 1;
        reg_exchg_cmem_twiddles_fwd<2, 4, 1>(vals_this_region, exchg_region_offset);
      }
      if (STAGES == 6) {
        int exchg_region_offset = warp_exchg_region_offset + i;
        bf *vals_this_region = vals + 2 * i;
        reg_exchg_cmem_twiddles_fwd<1, 2, 1>(vals_this_region, exchg_region_offset);
      }
    }
  }

#pragma unroll
  for (int i{0}, row{lane_id}; i < VALS_PER_THREAD; i++, row += WARP_SIZE)
    gmem_out.set_at_row(row, vals[i]);
}

#define DEFINE_INITIAL_KERNEL(STAGES)                                                                                                                          \
  EXTERN __launch_bounds__(256, 3) __global__ void ab_monomials_to_evals_initial_##STAGES##_stages_kernel(                                                     \
      bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out, const bool transposed_monomials, const int log_n,                 \
      const int coset_index_base, const int coset_factor_shift, const int num_cols_per_coset, const int log_cosets_in_tile) {                                  \
    monomials_to_evals_initial_up_to_8_stages<STAGES>(gmem_in, gmem_out, transposed_monomials, log_n, coset_index_base, coset_factor_shift,                    \
                                                      num_cols_per_coset, log_cosets_in_tile);                                                                 \
  }

DEFINE_INITIAL_KERNEL(5)
DEFINE_INITIAL_KERNEL(6)
DEFINE_INITIAL_KERNEL(7)
DEFINE_INITIAL_KERNEL(8)

#undef DEFINE_INITIAL_KERNEL

} // namespace airbender::ntt
