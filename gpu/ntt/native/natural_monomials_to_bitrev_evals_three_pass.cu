#include "ntt.cuh"
#include "pass_config.cuh"

namespace airbender::ntt {

// Natural-order monomials -> bitreversed-order evaluations, three-pass regime
// (log_n in [21, 24]): out_k[p] = f(g_k * omega^rev_n(p)). Descending-stride
// DIT network (pass structure cloned from evals_to_monomials_three_pass.cu)
// over FORWARD twiddles, with no 1/N normalization. Pass 1 also carries the
// multi-coset shape: one shared input column feeds every coset's output slab,
// with the coset pre-scale g_k^row fused into the load.

// Pass 1: stages 0..7 (exchange region = the whole NTT).
EXTERN __launch_bounds__(256, 3) __global__
    void ab_natural_monomials_to_bitrev_evals_initial_8_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out,
                                                                      const bool transposed_monomials, const int log_n, const int coset_index_base,
                                                                      const int coset_factor_shift, const int num_cols_per_coset,
                                                                      const int log_cosets_in_tile) {
  using namespace pass_config::three_pass_phase_a;
  constexpr int ROLES = 2;
  constexpr int ROLE_TILE_STRIDE = THREAD_TILES_PER_BLOCK / ROLES;

  const int lane_in_tile = threadIdx.x & 31;

  const int exchg_region_size = 1 << log_n; // start_stage == 0
  const int tile_gmem_stride = exchg_region_size >> LOG_DATA_TILES_PER_BLOCK;
  const int interleaved_gmem_stride = tile_gmem_stride * THREAD_TILES_PER_BLOCK;

  // Flat-blockIdx.x layout: log_blocks_x = log_n - 13 blocks per (single)
  // exchange region, no intra-NTT y axis, then cosets, then columns. Inputs
  // are shared across cosets; outputs are coset-major with per-coset stride
  // `num_cols_per_coset`.
  const unsigned log_blocks_x = static_cast<unsigned>(log_n - 13);
  const FlatBlockIndex fi = decompose_flat_2d(log_blocks_x, 0u, static_cast<unsigned>(log_cosets_in_tile));
  gmem_in.add_col(static_cast<int>(fi.col));
  gmem_out.add_col(static_cast<int>(fi.coset) * num_cols_per_coset + static_cast<int>(fi.col));
  const unsigned coset_factor_power = static_cast<unsigned>((coset_index_base + static_cast<int>(fi.coset)) << coset_factor_shift);

  // Full global physical row = block offset + tile/lane/iteration offsets, so
  // the coset exponent and the transposed-layout mapping see absolute rows.
  const int gmem_block_offset = static_cast<int>(fi.intra_x) << LOG_DATA_TILE_SIZE;

  __shared__ bf smem_block[8192];

#pragma unroll
  for (int role = 0; role < ROLES; role++) {
    const int tile_id = (threadIdx.x >> LOG_DATA_TILE_SIZE) + role * ROLE_TILE_STRIDE;
    const int thread_il_gmem_start = gmem_block_offset + lane_in_tile + tile_id * tile_gmem_stride;
    const int thread_il_smem_start = lane_in_tile + tile_id * TILE_SIZE;

    bf vals[VALS_PER_THREAD];

#pragma unroll
    for (int i{0}, row{thread_il_gmem_start}; i < VALS_PER_THREAD; i++, row += interleaved_gmem_stride)
      vals[i] = gmem_in.get_at_row(row);

    // A separate coset adjustment loop performs better than interleaving
    // adjustments with loads. The natural labeling IS the exponent, so no
    // bitrev here; `transposed_row_to_effective_row` resolves the physical
    // row of the transposed-monomial layout to its logical row.
    if (coset_factor_power != 0) {
#pragma unroll
      for (int i{0}, row{thread_il_gmem_start}; i < VALS_PER_THREAD; i++, row += interleaved_gmem_stride) {
        const int effective_row = transposed_monomials ? transposed_row_to_effective_row(row) : row;
        vals[i] = bf::mul(vals[i], get_forward_twiddle_power(static_cast<unsigned>(effective_row) * coset_factor_power));
      }
    }

    int block_exchg_region_offset = 0; // start_stage == 0: one exchange region
    reg_exchg_fwd_dit<8, 16, 1>(vals, block_exchg_region_offset);
    block_exchg_region_offset <<= 1;
    reg_exchg_fwd_dit<4, 8, 2>(vals, block_exchg_region_offset);
    block_exchg_region_offset <<= 1;
    reg_exchg_fwd_dit<2, 4, 4>(vals, block_exchg_region_offset);
    block_exchg_region_offset <<= 1;
    reg_exchg_fwd_dit<1, 2, 8>(vals, block_exchg_region_offset);

#pragma unroll
    for (int i{0}, addr{thread_il_smem_start}; i < VALS_PER_THREAD; i++, addr += TILE_SIZE * THREAD_TILES_PER_BLOCK)
      smem_block[addr] = vals[i]; // write interleaved smem tiles
  }

  __syncthreads();

#pragma unroll
  for (int role = 0; role < ROLES; role++) {
    const int tile_id = (threadIdx.x >> LOG_DATA_TILE_SIZE) + role * ROLE_TILE_STRIDE;
    const int thread_ct_gmem_start = gmem_block_offset + lane_in_tile + tile_id * interleaved_gmem_stride;
    const int thread_ct_smem_start = lane_in_tile + tile_id * TILE_SIZE * THREAD_TILES_PER_BLOCK;

    bf vals[VALS_PER_THREAD];

#pragma unroll
    for (int i{0}, addr{thread_ct_smem_start}; i < VALS_PER_THREAD; i++, addr += TILE_SIZE)
      vals[i] = smem_block[addr]; // read consecutive smem tiles

    int tile_exchg_region_offset = tile_id;
    reg_exchg_fwd_dit<8, 16, 1>(vals, tile_exchg_region_offset);
    tile_exchg_region_offset <<= 1;
    reg_exchg_fwd_dit<4, 8, 2>(vals, tile_exchg_region_offset);
    tile_exchg_region_offset <<= 1;
    reg_exchg_fwd_dit<2, 4, 4>(vals, tile_exchg_region_offset);
    tile_exchg_region_offset <<= 1;
    reg_exchg_fwd_dit<1, 2, 8>(vals, tile_exchg_region_offset);

    // Un-transpose on the way out: pass 1's strides are all multiples of the
    // 1024-row transposition chunk (so the layout does not disturb its
    // butterflies or twiddle groups), but passes 2 and 3 exchange rows WITHIN
    // a chunk and require natural row order.
#pragma unroll
    for (int i{0}, row{thread_ct_gmem_start}; i < VALS_PER_THREAD; i++, row += tile_gmem_stride)
      gmem_out.set_at_row(transposed_monomials ? transposed_row_to_effective_row(row) : row, vals[i]);
  }
}

// Pass 2: 8 in-place stages per coset starting at `start_stage` (8 in the
// three-pass plan). Same tile exchange as the inverse nonfinal kernel, always
// on the two-level cmem twiddle lookup (correct for any start_stage).
EXTERN __launch_bounds__(256, 3) __global__
    void ab_natural_monomials_to_bitrev_evals_middle_8_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out,
                                                                     const int log_n, const int start_stage, const int num_cols_per_coset,
                                                                     const int log_cosets_in_tile) {
  using namespace pass_config::three_pass_phase_a;
  constexpr int ROLES = 2;
  constexpr int ROLE_TILE_STRIDE = THREAD_TILES_PER_BLOCK / ROLES;

  const int lane_in_tile = threadIdx.x & 31;

  const int exchg_region_size = 1 << (log_n - start_stage);
  const int tile_gmem_stride = exchg_region_size >> LOG_DATA_TILES_PER_BLOCK;
  const int interleaved_gmem_stride = tile_gmem_stride * THREAD_TILES_PER_BLOCK;

  //   log_blocks_x = log_n - start_stage - 13 (blocks per exchg region)
  //   log_blocks_y = start_stage              (num exchg regions)
  const unsigned log_blocks_x = static_cast<unsigned>(log_n - start_stage - 13);
  const unsigned log_blocks_y = static_cast<unsigned>(start_stage);
  const FlatBlockIndex fi = decompose_flat_2d(log_blocks_x, log_blocks_y, static_cast<unsigned>(log_cosets_in_tile));
  apply_flat_col_offset(fi, num_cols_per_coset, gmem_in, gmem_out);
  const unsigned blocks_per_exchg_region = 1u << log_blocks_x;
  const unsigned num_exchg_regions = 1u << log_blocks_y;

  // Reversed block indexing, to help L2 hits.
  const int alternating_block_idx_x = static_cast<int>(blocks_per_exchg_region) - 1 - static_cast<int>(fi.intra_x);
  const int alternating_block_idx_y = static_cast<int>(num_exchg_regions) - 1 - static_cast<int>(fi.intra_y);
  const int gmem_block_offset = alternating_block_idx_y * exchg_region_size + (alternating_block_idx_x << LOG_DATA_TILE_SIZE);
  gmem_in.add_row(gmem_block_offset);
  gmem_out.add_row(gmem_block_offset);

  __shared__ bf smem_block[8192];

#pragma unroll
  for (int role = 0; role < ROLES; role++) {
    const int tile_id = (threadIdx.x >> LOG_DATA_TILE_SIZE) + role * ROLE_TILE_STRIDE;
    const int thread_il_gmem_start = lane_in_tile + tile_id * tile_gmem_stride;
    const int thread_il_smem_start = lane_in_tile + tile_id * TILE_SIZE;

    bf vals[VALS_PER_THREAD];

#pragma unroll
    for (int i{0}, addr{thread_il_gmem_start}; i < VALS_PER_THREAD; i++, addr += interleaved_gmem_stride)
      vals[i] = gmem_in.get_at_row(addr);

    int block_exchg_region_offset = alternating_block_idx_y;
    reg_exchg_cmem_twiddles_fwd_dit<8, 16, 1>(vals, block_exchg_region_offset);
    block_exchg_region_offset <<= 1;
    reg_exchg_cmem_twiddles_fwd_dit<4, 8, 2>(vals, block_exchg_region_offset);
    block_exchg_region_offset <<= 1;
    reg_exchg_cmem_twiddles_fwd_dit<2, 4, 4>(vals, block_exchg_region_offset);
    block_exchg_region_offset <<= 1;
    reg_exchg_cmem_twiddles_fwd_dit<1, 2, 8>(vals, block_exchg_region_offset);

#pragma unroll
    for (int i{0}, addr{thread_il_smem_start}; i < VALS_PER_THREAD; i++, addr += TILE_SIZE * THREAD_TILES_PER_BLOCK)
      smem_block[addr] = vals[i]; // write interleaved smem tiles
  }

  __syncthreads();

#pragma unroll
  for (int role = 0; role < ROLES; role++) {
    const int tile_id = (threadIdx.x >> LOG_DATA_TILE_SIZE) + role * ROLE_TILE_STRIDE;
    const int thread_ct_gmem_start = lane_in_tile + tile_id * interleaved_gmem_stride;
    const int thread_ct_smem_start = lane_in_tile + tile_id * TILE_SIZE * THREAD_TILES_PER_BLOCK;

    bf vals[VALS_PER_THREAD];

#pragma unroll
    for (int i{0}, addr{thread_ct_smem_start}; i < VALS_PER_THREAD; i++, addr += TILE_SIZE)
      vals[i] = smem_block[addr]; // read consecutive smem tiles

    int tile_exchg_region_offset = (alternating_block_idx_y << 4) + tile_id;
    reg_exchg_cmem_twiddles_fwd_dit<8, 16, 1>(vals, tile_exchg_region_offset);
    tile_exchg_region_offset <<= 1;
    reg_exchg_cmem_twiddles_fwd_dit<4, 8, 2>(vals, tile_exchg_region_offset);
    tile_exchg_region_offset <<= 1;
    reg_exchg_cmem_twiddles_fwd_dit<2, 4, 4>(vals, tile_exchg_region_offset);
    tile_exchg_region_offset <<= 1;
    reg_exchg_cmem_twiddles_fwd_dit<1, 2, 8>(vals, tile_exchg_region_offset);

#pragma unroll
    for (int i{0}, row{thread_ct_gmem_start}; i < VALS_PER_THREAD; i++, row += tile_gmem_stride)
      gmem_out.set_at_row(row, vals[i]); // write consecutive gmem tiles
  }
}

// Pass 3: the final STAGES (= log_n - 16) finest stages, in place per coset.
// Outputs are always written in plain (non-transposed) row order: the
// bitreversed codeword is what the tree layer consumes.
template <int STAGES>
DEVICE_FORCEINLINE void natural_monomials_to_bitrev_evals_final_up_to_8_stages(bf_matrix_getter<ld_modifier::cg> gmem_in,
                                                                               bf_matrix_setter<st_modifier::cg> gmem_out, const int log_n,
                                                                               const int num_cols_per_coset, const int log_cosets_in_tile) {
  using namespace pass_config::three_pass_phase_b;
  constexpr int INITIAL_EXCHG_REGIONS_PER_WARP = 1 << (10 - STAGES);

  const unsigned log_blocks_per_ntt = static_cast<unsigned>(log_n) - 13u;
  const FlatBlockIndex fi = decompose_flat_1d(log_blocks_per_ntt, static_cast<unsigned>(log_cosets_in_tile));
  apply_flat_col_offset(fi, num_cols_per_coset, gmem_in, gmem_out);

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

  // Cooperatively fetch the coarse gmem twiddle powers used by the last 5
  // stages. The gmem layout is already swizzled, so it's a linear copy.
#pragma unroll
  for (int i{0}, addr{pipeline_memcpy_start}; i < 4; i++, addr += pipeline_memcpy_stride)
    __pipeline_memcpy_async(smem_twiddles + addr, ab_fwd_gmem_twiddles_coarse + addr, 4 * sizeof(bf));
  __pipeline_commit();

#pragma unroll
  for (int i{0}, row{lane_id}; i < VALS_PER_THREAD; i++, row += WARP_SIZE)
    vals[i] = gmem_in.get_at_row(row);

  // Use pure cmem for warp-uniform twiddles
  if (STAGES >= 5) {
    int warp_exchg_region_offset = INITIAL_EXCHG_REGIONS_PER_WARP * (static_cast<int>(fi.intra_x) * WARPS_PER_BLOCK + warp_id);
#pragma unroll
    for (int i{0}; i < INITIAL_EXCHG_REGIONS_PER_WARP; i++) {
      int exchg_region_offset = warp_exchg_region_offset + i;
      if (STAGES == 8) {
        bf *vals_this_region = vals + 8 * i;
        reg_exchg_cmem_twiddles_fwd_dit<4, 8, 1>(vals_this_region, exchg_region_offset);
        exchg_region_offset <<= 1;
        reg_exchg_cmem_twiddles_fwd_dit<2, 4, 2>(vals_this_region, exchg_region_offset);
        exchg_region_offset <<= 1;
        reg_exchg_cmem_twiddles_fwd_dit<1, 2, 4>(vals_this_region, exchg_region_offset);
      }
      if (STAGES == 7) {
        bf *vals_this_region = vals + 4 * i;
        reg_exchg_cmem_twiddles_fwd_dit<2, 4, 1>(vals_this_region, exchg_region_offset);
        exchg_region_offset <<= 1;
        reg_exchg_cmem_twiddles_fwd_dit<1, 2, 2>(vals_this_region, exchg_region_offset);
      }
      if (STAGES == 6) {
        bf *vals_this_region = vals + 2 * i;
        reg_exchg_cmem_twiddles_fwd_dit<1, 2, 1>(vals_this_region, exchg_region_offset);
      }
    }
  }

  if (warp_id & 4) {
    warp_transpose_swizzled<VALS_PER_THREAD>(smem_warp, vals, lane_id);
  }

  __pipeline_wait_prior(0);

  __syncthreads();

  if (!(warp_id & 4)) {
    warp_transpose_swizzled<VALS_PER_THREAD>(smem_warp, vals, lane_id);
  }

  int thread_exchg_region_offset = threadIdx.x + static_cast<int>(fi.intra_x) * blockDim.x;
  constexpr bf *cmem_twiddles = ab_fwd_cmem_twiddles_finest_11;
  reg_exchg_cmem_smem_twiddles_fwd_dit<EightStages, 16, 32, 1, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);
  thread_exchg_region_offset <<= 1;
  reg_exchg_cmem_smem_twiddles_fwd_dit<EightStages, 8, 16, 2, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);
  thread_exchg_region_offset <<= 1;
  reg_exchg_cmem_smem_twiddles_fwd_dit<EightStages, 4, 8, 4, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);
  thread_exchg_region_offset <<= 1;
  reg_exchg_cmem_smem_twiddles_fwd_dit<EightStages, 2, 4, 8, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);
  thread_exchg_region_offset <<= 1;
  reg_exchg_cmem_smem_twiddles_fwd_dit<EightStages, 1, 2, 16, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);

  // Un-swizzle and store with coalescing.
  __syncthreads();

  smem_warp = smem_block + warp_id * VALS_PER_WARP;
  warp_transpose_swizzled<VALS_PER_THREAD>(smem_warp, vals, lane_id);

#pragma unroll
  for (int i{0}, row{lane_id}; i < VALS_PER_THREAD; i++, row += WARP_SIZE)
    gmem_out.set_at_row(row, vals[i]);
}

#define DEFINE_FINAL_KERNEL(STAGES)                                                                                                                            \
  EXTERN __launch_bounds__(256, 3) __global__ void ab_natural_monomials_to_bitrev_evals_final_##STAGES##_stages_kernel(                                        \
      bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out, const int log_n, const int num_cols_per_coset,                    \
      const int log_cosets_in_tile) {                                                                                                                          \
    natural_monomials_to_bitrev_evals_final_up_to_8_stages<STAGES>(gmem_in, gmem_out, log_n, num_cols_per_coset, log_cosets_in_tile);                          \
  }

DEFINE_FINAL_KERNEL(5)
DEFINE_FINAL_KERNEL(6)
DEFINE_FINAL_KERNEL(7)
DEFINE_FINAL_KERNEL(8)

#undef DEFINE_FINAL_KERNEL

} // namespace airbender::ntt
