#include "ntt.cuh"
#include "pass_config.cuh"

namespace airbender::ntt {

// Two tile roles per thread at 256 threads / 3 blocks-per-SM (see the forward
// noninitial body for the shape rationale).
EXTERN __launch_bounds__(256, 3) __global__
    void ab_hypercube_evals_to_monomials_nonfinal_8_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out,
                                                                  const int log_n, const int start_stage) {
  using namespace pass_config::three_pass_phase_a;
  constexpr int ROLES = 2;
  constexpr int ROLE_TILE_STRIDE = THREAD_TILES_PER_BLOCK / ROLES;

  const int lane_in_tile = threadIdx.x & 31;

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

#pragma unroll
  for (int role = 0; role < ROLES; role++) {
    const int tile_id = (threadIdx.x >> LOG_DATA_TILE_SIZE) + role * ROLE_TILE_STRIDE;
    const int thread_il_gmem_start = lane_in_tile + tile_id * tile_gmem_stride;
    const int thread_il_smem_start = lane_in_tile + tile_id * TILE_SIZE;

    bf vals[VALS_PER_THREAD];

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

    reg_exchg_hypercube_inv<8, 16, 1>(vals);
    reg_exchg_hypercube_inv<4, 8, 2>(vals);
    reg_exchg_hypercube_inv<2, 4, 4>(vals);
    reg_exchg_hypercube_inv<1, 2, 8>(vals);

#pragma unroll
    for (int i{0}, row{thread_ct_gmem_start}; i < VALS_PER_THREAD; i++, row += tile_gmem_stride)
      gmem_out.set_at_row(row, vals[i]); // write consecutive gmem tiles
  }
}

// Fused LDE boundary for a column's FIRST coset (transposed layout only):
// iNTT final stages + in-place monomial writeback + coset scale +
// forward-initial stages. In-place contract: each block rewrites exactly the
// scratch window it read; only later launches read the writeback, so
// same-stream order suffices. The coarse-twiddle staging must wait for the
// hypercube warp transpose (they share smem's upper half).
template <int STAGES>
DEVICE_FORCEINLINE void lde_fused_boundary_writeback_up_to_8_stages(bf_matrix_getter_setter<ld_modifier::cg, st_modifier::cg> gmem_scratch,
                                                                    bf_matrix_setter<st_modifier::cg> gmem_out, const int log_n, const int coset_index_base,
                                                                    const int coset_factor_shift, const int num_cols_per_coset, const int log_cosets_in_tile) {
  using namespace pass_config::three_pass_phase_b;
  constexpr int REGIONS_PER_WARP = 1 << (10 - STAGES);

  const unsigned log_blocks_per_ntt = static_cast<unsigned>(log_n) - 13u;
  const FlatBlockIndex fi = decompose_flat_1d(log_blocks_per_ntt, static_cast<unsigned>(log_cosets_in_tile));
  gmem_scratch.add_col(fi.col);
  gmem_out.add_col(static_cast<int>(fi.coset) * num_cols_per_coset + static_cast<int>(fi.col));
  const int coset_factor_power = (coset_index_base + static_cast<int>(fi.coset)) << coset_factor_shift;

  const int lane_id = threadIdx.x & 31;
  const int warp_id = threadIdx.x >> 5;
  const int pipeline_memcpy_start = 4 * threadIdx.x;
  const int pipeline_memcpy_stride = 4 * blockDim.x;
  const int gmem_block_offset = static_cast<int>(fi.intra_x) * VALS_PER_BLOCK;
  gmem_scratch.add_row(gmem_block_offset + warp_id * VALS_PER_WARP);
  gmem_out.add_row(gmem_block_offset + warp_id * VALS_PER_WARP);

  __shared__ bf smem_block[8192]; // warp transposes; [4096..8192) doubles as coarse twiddles
  bf *smem_warp = smem_block + warp_id * VALS_PER_WARP;
  bf *smem_twiddles = smem_block + (VALS_PER_BLOCK >> 1);

  bf vals[VALS_PER_THREAD];

#pragma unroll
  for (int i{0}, row{lane_id}; i < VALS_PER_THREAD; i++, row += WARP_SIZE)
    vals[i] = gmem_scratch.get_at_row(row);

  // Hypercube iNTT final STAGES stages (mirrors the standalone final kernel).
  if (STAGES >= 5) {
#pragma unroll
    for (int i{0}; i < REGIONS_PER_WARP; i++) {
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

  warp_transpose_swizzled<VALS_PER_THREAD>(smem_warp, vals, lane_id);

  reg_exchg_hypercube_inv<16, 32, 1>(vals);
  reg_exchg_hypercube_inv<8, 16, 2>(vals);
  reg_exchg_hypercube_inv<4, 8, 4>(vals);
  reg_exchg_hypercube_inv<2, 4, 8>(vals);
  reg_exchg_hypercube_inv<1, 2, 16>(vals);

  // Warps 4-7's transposes must retire before the twiddle staging overwrites
  // smem's upper half.
  __syncthreads();

#pragma unroll
  for (int i{0}, addr{pipeline_memcpy_start}; i < 4; i++, addr += pipeline_memcpy_stride)
    __pipeline_memcpy_async(smem_twiddles + addr, ab_fwd_gmem_twiddles_coarse + addr, 4 * sizeof(bf));
  __pipeline_commit();

  // Materialize the monomials (pre-scale); overlaps the twiddle copy.
#pragma unroll
  for (int i{0}, row{lane_id}; i < VALS_PER_THREAD; i++, row += WARP_SIZE)
    gmem_scratch.set_at_row(row, vals[i]);

  // Coset scale on the logical monomial rows, also overlapping the copy.
  if (coset_factor_power > 0) {
#pragma unroll
    for (int i{0}, global_row{lane_id + gmem_block_offset + warp_id * VALS_PER_WARP}; i < VALS_PER_THREAD; i++, global_row += WARP_SIZE) {
      const int effective_row = transposed_row_to_effective_row(global_row);
      const bf coset_offset = get_power_from_layers(::ab_ntt_forward_powers, bitrev(effective_row, log_n) * coset_factor_power);
      vals[i] = bf::mul(vals[i], coset_offset);
    }
  }

  __pipeline_wait_prior(0);
  __syncthreads();

  // Forward NTT initial STAGES stages, transposed path (mirrors
  // monomials_to_evals_three_pass.cu's initial body).
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

  warp_transpose_swizzled<VALS_PER_THREAD>(smem_warp, vals, lane_id);

  if (STAGES >= 5) {
    int warp_exchg_region_offset = (static_cast<int>(fi.intra_x) * WARPS_PER_BLOCK + warp_id) << 4;
#pragma unroll
    for (int i{0}; i < REGIONS_PER_WARP; i++) {
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

#define DEFINE_LDE_FUSED_WRITEBACK_KERNEL(STAGES)                                                                                                              \
  EXTERN __launch_bounds__(256, 3) __global__ void ab_lde_fused_boundary_writeback_##STAGES##_stages_kernel(                                                   \
      bf_matrix_getter_setter<ld_modifier::cg, st_modifier::cg> gmem_scratch, bf_matrix_setter<st_modifier::cg> gmem_out, const int log_n,                     \
      const int coset_index_base, const int coset_factor_shift, const int num_cols_per_coset, const int log_cosets_in_tile) {                                  \
    lde_fused_boundary_writeback_up_to_8_stages<STAGES>(gmem_scratch, gmem_out, log_n, coset_index_base, coset_factor_shift, num_cols_per_coset,               \
                                                        log_cosets_in_tile);                                                                                   \
  }

DEFINE_LDE_FUSED_WRITEBACK_KERNEL(5)
DEFINE_LDE_FUSED_WRITEBACK_KERNEL(6)
DEFINE_LDE_FUSED_WRITEBACK_KERNEL(7)
DEFINE_LDE_FUSED_WRITEBACK_KERNEL(8)

#undef DEFINE_LDE_FUSED_WRITEBACK_KERNEL

template <int STAGES>
DEVICE_FORCEINLINE void hypercube_evals_to_monomials_final_up_to_8_stages(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out,
                                                                          const bool transposed_monomials, const int log_n) {
  using namespace pass_config::three_pass_phase_b;
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

  warp_transpose_swizzled<VALS_PER_THREAD>(smem_warp, vals, lane_id);

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
