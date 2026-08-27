#include "ntt.cuh"
#include "pass_config.cuh"

namespace airbender::ntt {

// Natural-order monomials -> bitreversed-order evaluations, two-pass regime
// (log_n in [23, 24], one column >= device L2): out_k[p] = f(g_k * omega^rev_n(p)).
// Descending-stride DIT network (pass structure cloned from
// evals_to_monomials_two_pass.cu) over FORWARD twiddles, with no 1/N
// normalization. Pass 1 carries the multi-coset shape: one shared input column
// feeds every coset's output slab, with the coset pre-scale g_k^row applied on
// the full global row.

// Pass 1 for log_n = 24: stages 0..9 (five register stages, tile exchange,
// five more).
EXTERN __launch_bounds__(512, 1) __global__
    void ab_natural_monomials_to_bitrev_evals_first_10_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out,
                                                                     const bool transposed_monomials, const int log_n, const int coset_index_base,
                                                                     const int coset_factor_shift, const int num_cols_per_coset, const int log_cosets_in_tile) {
  using namespace pass_config::two_pass_phase_a;
  using namespace pass_config::pipeline_prefetch;

  // Flat-blockIdx.x layout: gridDim.x packs blocks_per_ntt (= n / 16384 =
  // 1 << (log_n - 14)) blocks per NTT, then cosets in tile, then columns.
  // Inputs are shared across cosets; outputs are coset-major with per-coset
  // stride `num_cols_per_coset`.
  const unsigned log_blocks_per_ntt = static_cast<unsigned>(log_n) - 14u;
  const FlatBlockIndex fi = decompose_flat_1d(log_blocks_per_ntt, static_cast<unsigned>(log_cosets_in_tile));
  gmem_in.add_col(static_cast<int>(fi.col));
  gmem_out.add_col(static_cast<int>(fi.coset) * num_cols_per_coset + static_cast<int>(fi.col));
  const unsigned coset_factor_power = static_cast<unsigned>((coset_index_base + static_cast<int>(fi.coset)) << coset_factor_shift);

  const int lane_in_tile = threadIdx.x & 15;
  const int tile_id = threadIdx.x >> LOG_DATA_TILE_SIZE;
  // Full global physical row = block offset + tile/lane/iteration offsets, so
  // the coset exponent and the transposed-layout mapping see absolute rows.
  const int gmem_block_offset = static_cast<int>(fi.intra_x) << LOG_DATA_TILE_SIZE;

  extern __shared__ bf smem_block[]; // 16384 * 4 bytes

  bf vals[VALS_PER_THREAD];

  // "ct" = consecutive tile layout
  // "il" = interleaved tile layout
  const ThreadTileStarts starts = thread_tile_starts(lane_in_tile, tile_id, TILE_GMEM_STRIDE, IL_GMEM_STRIDE, TILE_SIZE, THREAD_TILES_PER_BLOCK);
  const int thread_il_gmem_start = gmem_block_offset + starts.il_gmem_start;
  const int thread_ct_gmem_start = gmem_block_offset + starts.ct_gmem_start;

  // Correctness form of the donor's prefetch/exchange pipeline: all eight
  // register groups are loaded and coset-scaled from their full global rows
  // first, then the donor's exchg_pipeline_group<0..7> sequence runs unchanged
  // over the forward twiddles.
  prefetch_pipeline_group<0, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  prefetch_pipeline_group<1, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  prefetch_pipeline_group<2, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  prefetch_pipeline_group<3, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  prefetch_pipeline_group<4, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  prefetch_pipeline_group<5, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  prefetch_pipeline_group<6, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  prefetch_pipeline_group<7, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);

  // The natural labeling IS the exponent, so no bitrev here;
  // `transposed_row_to_effective_row` resolves the physical row of the
  // transposed-monomial layout to its logical row.
  if (coset_factor_power != 0) {
#pragma unroll
    for (int i{0}, row{thread_il_gmem_start}; i < VALS_PER_THREAD; i++, row += IL_GMEM_STRIDE) {
      const int effective_row = transposed_monomials ? transposed_row_to_effective_row(row) : row;
      vals[i] = bf::mul(vals[i], get_forward_twiddle_power(static_cast<unsigned>(effective_row) * coset_factor_power));
    }
  }

  const bf pipeline_twiddle = ab_fwd_cmem_twiddles_coarse[1];
  exchg_pipeline_group<0>(vals, pipeline_twiddle);
  exchg_pipeline_group<1>(vals, pipeline_twiddle);
  exchg_pipeline_group<2>(vals, pipeline_twiddle);
  exchg_pipeline_group<3>(vals, pipeline_twiddle);
  exchg_pipeline_group<4>(vals, pipeline_twiddle);
  exchg_pipeline_group<5>(vals, pipeline_twiddle);
  exchg_pipeline_group<6>(vals, pipeline_twiddle);
  exchg_pipeline_group<7>(vals, pipeline_twiddle);

  reg_exchg_fwd_dit<4, 8, 4>(vals, 0);
  reg_exchg_fwd_dit<2, 4, 8>(vals, 0);
  reg_exchg_fwd_dit<1, 2, 16>(vals, 0);

#pragma unroll
  for (int i{0}, addr{starts.il_smem_start}; i < 32; i++, addr += TILE_SIZE * THREAD_TILES_PER_BLOCK)
    smem_block[addr] = vals[i]; // write interleaved smem tiles

  __syncthreads();

#pragma unroll
  for (int i{0}, addr{starts.ct_smem_start}; i < 32; i++, addr += TILE_SIZE)
    vals[i] = smem_block[addr]; // read consecutive smem tiles

  int tile_exchg_region_offset = tile_id;
  reg_exchg_fwd_dit<16, 32, 1>(vals, tile_exchg_region_offset);
  tile_exchg_region_offset <<= 1;
  reg_exchg_fwd_dit<8, 16, 2>(vals, tile_exchg_region_offset);
  tile_exchg_region_offset <<= 1;
  reg_exchg_fwd_dit<4, 8, 4>(vals, tile_exchg_region_offset);
  tile_exchg_region_offset <<= 1;
  reg_exchg_fwd_dit<2, 4, 8>(vals, tile_exchg_region_offset);
  tile_exchg_region_offset <<= 1;
  reg_exchg_fwd_dit<1, 2, 16>(vals, tile_exchg_region_offset);

  // Un-transpose on the way out: pass 1's strides are all multiples of the
  // 1024-row transposition chunk (so the layout does not disturb its
  // butterflies or twiddle groups), but pass 2 exchanges rows WITHIN a chunk
  // and requires natural row order.
#pragma unroll
  for (int i{0}, row{thread_ct_gmem_start}; i < 32; i++, row += TILE_GMEM_STRIDE)
    gmem_out.set_at_row(transposed_monomials ? transposed_row_to_effective_row(row) : row, vals[i]);
}

// Pass 1 for log_n = 23: stages 0..8.
EXTERN __launch_bounds__(512, 1) __global__
    void ab_natural_monomials_to_bitrev_evals_first_9_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out,
                                                                    const bool transposed_monomials, const int log_n, const int coset_index_base,
                                                                    const int coset_factor_shift, const int num_cols_per_coset, const int log_cosets_in_tile) {
  using namespace pass_config::two_pass_phase_b;
  using namespace pass_config::pipeline_prefetch;

  const unsigned log_blocks_per_ntt = static_cast<unsigned>(log_n) - 14u;
  const FlatBlockIndex fi = decompose_flat_1d(log_blocks_per_ntt, static_cast<unsigned>(log_cosets_in_tile));
  gmem_in.add_col(static_cast<int>(fi.col));
  gmem_out.add_col(static_cast<int>(fi.coset) * num_cols_per_coset + static_cast<int>(fi.col));
  const unsigned coset_factor_power = static_cast<unsigned>((coset_index_base + static_cast<int>(fi.coset)) << coset_factor_shift);

  const int lane_in_tile = threadIdx.x & 31;
  const int tile_id = threadIdx.x >> LOG_DATA_TILE_SIZE;
  const int gmem_block_offset = static_cast<int>(fi.intra_x) << LOG_DATA_TILE_SIZE;

  extern __shared__ bf smem_block[]; // 16384 * 4 bytes

  bf vals[VALS_PER_THREAD];

  const int thread_il_gmem_start = gmem_block_offset + lane_in_tile + tile_id * TILE_GMEM_STRIDE;
  const int thread_ct_gmem_start = gmem_block_offset + lane_in_tile + tile_id * 2 * IL_GMEM_STRIDE;
  const int thread_il_smem_start = lane_in_tile + tile_id * TILE_SIZE;
  const int thread_ct_smem_start = lane_in_tile + tile_id * TILE_SIZE * 2 * THREAD_TILES_PER_BLOCK;

  prefetch_pipeline_group<0, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  prefetch_pipeline_group<1, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  prefetch_pipeline_group<2, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  prefetch_pipeline_group<3, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  prefetch_pipeline_group<4, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  prefetch_pipeline_group<5, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  prefetch_pipeline_group<6, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);
  prefetch_pipeline_group<7, IL_GMEM_STRIDE, PL_GROUP_SIZE, PL_STRIDE>(vals, gmem_in, thread_il_gmem_start);

  if (coset_factor_power != 0) {
#pragma unroll
    for (int i{0}, row{thread_il_gmem_start}; i < VALS_PER_THREAD; i++, row += IL_GMEM_STRIDE) {
      const int effective_row = transposed_monomials ? transposed_row_to_effective_row(row) : row;
      vals[i] = bf::mul(vals[i], get_forward_twiddle_power(static_cast<unsigned>(effective_row) * coset_factor_power));
    }
  }

  const bf pipeline_twiddle = ab_fwd_cmem_twiddles_coarse[1];
  exchg_pipeline_group<0>(vals, pipeline_twiddle);
  exchg_pipeline_group<1>(vals, pipeline_twiddle);
  exchg_pipeline_group<2>(vals, pipeline_twiddle);
  exchg_pipeline_group<3>(vals, pipeline_twiddle);
  exchg_pipeline_group<4>(vals, pipeline_twiddle);
  exchg_pipeline_group<5>(vals, pipeline_twiddle);
  exchg_pipeline_group<6>(vals, pipeline_twiddle);
  exchg_pipeline_group<7>(vals, pipeline_twiddle);

  reg_exchg_fwd_dit<4, 8, 4>(vals, 0);
  reg_exchg_fwd_dit<2, 4, 8>(vals, 0);
  reg_exchg_fwd_dit<1, 2, 16>(vals, 0);

#pragma unroll
  for (int i{0}, addr{thread_il_smem_start}; i < 32; i++, addr += TILE_SIZE * THREAD_TILES_PER_BLOCK)
    smem_block[addr] = vals[i]; // write interleaved smem tiles

  __syncthreads();

#pragma unroll
  for (int i{0}, addr{thread_ct_smem_start}; i < 32; i++, addr += TILE_SIZE)
    vals[i] = smem_block[addr]; // read consecutive smem tiles

  int tile_exchg_region_offset = 2 * tile_id;
  reg_exchg_fwd_dit<8, 16, 2>(vals, tile_exchg_region_offset);
  tile_exchg_region_offset <<= 1;
  reg_exchg_fwd_dit<4, 8, 4>(vals, tile_exchg_region_offset);
  tile_exchg_region_offset <<= 1;
  reg_exchg_fwd_dit<2, 4, 8>(vals, tile_exchg_region_offset);
  tile_exchg_region_offset <<= 1;
  reg_exchg_fwd_dit<1, 2, 16>(vals, tile_exchg_region_offset);

#pragma unroll
  for (int i{0}, row{thread_ct_gmem_start}; i < 32; i++, row += TILE_GMEM_STRIDE)
    gmem_out.set_at_row(transposed_monomials ? transposed_row_to_effective_row(row) : row, vals[i]);
}

// Pass 2: the last 14 stages, in place per coset slab. Outputs are always
// written in plain (non-transposed) row order: the bitreversed codeword is what
// the tree layer consumes.
EXTERN __launch_bounds__(512, 1) __global__
    void ab_natural_monomials_to_bitrev_evals_last_14_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out,
                                                                    const int log_n, const int num_cols_per_coset, const int log_cosets_in_tile) {
  using namespace pass_config::two_pass_phase_c;

  const unsigned log_blocks_per_ntt = static_cast<unsigned>(log_n) - 14u;
  const FlatBlockIndex fi = decompose_flat_1d(log_blocks_per_ntt, static_cast<unsigned>(log_cosets_in_tile));
  apply_flat_col_offset(fi, num_cols_per_coset, gmem_in, gmem_out);

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
  constexpr bf *cmem_twiddles = ab_fwd_cmem_twiddles_finest_10;

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
    __pipeline_memcpy_async(smem_twiddles + addr, ab_fwd_gmem_twiddles_coarse + addr, 4 * sizeof(bf));
  __pipeline_commit();

  int block_exchg_region_offset = static_cast<int>(fi.intra_x);
  reg_exchg_cmem_twiddles_fwd_dit<16, 32, 1>(vals, block_exchg_region_offset);
  block_exchg_region_offset <<= 1;
  reg_exchg_cmem_twiddles_fwd_dit<8, 16, 2>(vals, block_exchg_region_offset);
  block_exchg_region_offset <<= 1;
  reg_exchg_cmem_twiddles_fwd_dit<4, 8, 4>(vals, block_exchg_region_offset);
  block_exchg_region_offset <<= 1;
  reg_exchg_cmem_twiddles_fwd_dit<2, 4, 8>(vals, block_exchg_region_offset);
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
  reg_exchg_cmem_twiddles_fwd_dit<16, 32, 1>(vals, warp_exchg_region_offset);
  warp_exchg_region_offset <<= 1;
  reg_exchg_cmem_twiddles_fwd_dit<8, 16, 2>(vals, warp_exchg_region_offset);
  warp_exchg_region_offset <<= 1;
  reg_exchg_cmem_twiddles_fwd_dit<4, 8, 4>(vals, warp_exchg_region_offset);
  warp_exchg_region_offset <<= 1;
  reg_exchg_cmem_twiddles_fwd_dit<2, 4, 8>(vals, warp_exchg_region_offset);
  warp_exchg_region_offset <<= 1;
  reg_exchg_cmem_twiddles_fwd_dit<1, 2, 16>(vals, warp_exchg_region_offset);
  warp_exchg_region_offset <<= 1;

  __syncwarp();
  warp_transpose_swizzled<VALS_PER_THREAD>(smem_warp, vals, lane_id);

  int thread_exchg_region_offset = warp_exchg_region_offset + lane_id;
  reg_exchg_cmem_smem_twiddles_fwd_dit<TenStages, 16, 32, 1, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);
  thread_exchg_region_offset <<= 1;
  reg_exchg_cmem_smem_twiddles_fwd_dit<TenStages, 8, 16, 2, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);
  thread_exchg_region_offset <<= 1;
  reg_exchg_cmem_smem_twiddles_fwd_dit<TenStages, 4, 8, 4, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);
  thread_exchg_region_offset <<= 1;
  reg_exchg_cmem_smem_twiddles_fwd_dit<TenStages, 2, 4, 8, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);
  thread_exchg_region_offset <<= 1;
  reg_exchg_cmem_smem_twiddles_fwd_dit<TenStages, 1, 2, 16, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);

  // un-swizzling + coalesced stores performs better on 5090
  __syncwarp();
  warp_transpose_swizzled<VALS_PER_THREAD>(smem_warp, vals, lane_id);
#pragma unroll
  for (int i{0}, row{lane_id}; i < VALS_PER_THREAD; i++, row += WARP_SIZE)
    gmem_out.set_at_row(row, vals[i]);
}

} // namespace airbender::ntt
