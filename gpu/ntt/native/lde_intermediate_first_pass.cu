#include "ntt.cuh"

namespace airbender::ntt {

DEVICE_FORCEINLINE void shfl_for_exchange(bf *vals, const unsigned lane_mask) {
  constexpr unsigned WARP_MASK = 0xffffffff;
  // The following non-divergent shfl pattern avoids deadlocks on architectures
  // with a program counter shared across the warp (Pascal and earlier):
  const bool is_odd = threadIdx.x & lane_mask;
  const unsigned val_to_publish = is_odd ? vals[0].limb : vals[1].limb;
  const unsigned val_received = __shfl_xor_sync(WARP_MASK, val_to_publish, lane_mask);
  if (is_odd)
    vals[0].limb = val_received;
  else
    vals[1].limb = val_received;
  // For Volta and later, with independent PCs per thread, the following would also be fine:
  // if (threadIdx.x & lane_mask)
  //   vals[0] = __shfl_xor_sync(WARP_MASK, vals[0], lane_mask);
  // else
  //   vals[1] = __shfl_xor_sync(WARP_MASK, vals[1], lane_mask);
}

// First-K-stages LDE for intermediate sizes.
// Reuses twiddles, monomials, and coset adjustments across cosets.
template <unsigned THREADS_PER_BLOCK, unsigned STAGES>
DEVICE_FORCEINLINE void lde_first_k_stages_impl(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out_base,
                                                const unsigned log_n, const unsigned coset_index_base, const unsigned coset_factor_shift,
                                                const unsigned num_cols_per_coset, const unsigned num_cosets_in_tile) {
  constexpr unsigned VALS_PER_THREAD = 2;
  constexpr unsigned VALS_PER_WARP = 64;
  constexpr unsigned VALS_PER_BLOCK = THREADS_PER_BLOCK * VALS_PER_THREAD;

  const unsigned gid = threadIdx.x + blockIdx.x * blockDim.x;

  const unsigned gmem_block_offset = blockIdx.x * VALS_PER_BLOCK;
  gmem_in.add_row(gmem_block_offset);
  gmem_out_base.add_row(gmem_block_offset);

  __shared__ bf smem[VALS_PER_BLOCK + THREADS_PER_BLOCK];
  bf *twiddles = smem + VALS_PER_BLOCK;
  const bf first_twiddle = ab_fully_precomputed_bitrev_twiddles[gid];
  // Cooperatively loads THREADS_PER_BLOCK - 1 twiddles for remaining stages with minimal divergence. Pain.
  // Stages are ordered in reverse in the shared memory chunk, ie
  // [...[twiddles for stage 8] [twiddles for stage 9] [ twiddles for stage 10]]
  {
    const unsigned lz = __clz(threadIdx.x);    // ranges from 32 to 32 - (STAGES - 1) inclusive
    const unsigned stage = STAGES - (32 - lz); // ranges from STAGES to 1 inclusive
    const unsigned exchg_region_offset = blockIdx.x * (VALS_PER_BLOCK >> (stage + 1));
    const unsigned global_bitrev_exchg_region = (threadIdx.x ^ (1 << (31 - lz))) + exchg_region_offset;
    if (threadIdx.x > 0)
      twiddles[threadIdx.x] = ab_fully_precomputed_bitrev_twiddles[global_bitrev_exchg_region];
  }

  __syncthreads();

  const unsigned base_coset_this_block = coset_index_base + blockIdx.z;
  bf coset_deltas[2];
  bf initial_adjustments[2];
  const unsigned global_bitrev_idx = (VALS_PER_THREAD * threadIdx.x) + blockIdx.x * VALS_PER_BLOCK;
#pragma unroll
  for (unsigned i = 0; i < 2; i++) {
    const unsigned global_natural_idx = bitrev(global_bitrev_idx + i, log_n);
    coset_deltas[i] = get_power_from_layers(::ab_ntt_forward_powers, gridDim.z * (global_natural_idx << coset_factor_shift));
    if (base_coset_this_block > 0)
      initial_adjustments[i] = get_forward_twiddle_power((global_natural_idx << coset_factor_shift) * base_coset_this_block);
  }

  // inter-warp reshuffling helpers
  const unsigned warp_id = threadIdx.x >> 5;
  const unsigned lane_id = threadIdx.x & 31;

  gmem_in.add_col(blockIdx.y);
  gmem_out_base.add_col(blockIdx.y + num_cols_per_coset * blockIdx.z);

  // This loop lets the caller balance occupancy and twiddle/adjustment amortization by playing with gridDim.y.
#pragma unroll 1
  for (unsigned monomial_col = blockIdx.y; monomial_col < num_cols_per_coset;
       monomial_col += gridDim.y, gmem_in.add_col(gridDim.y), gmem_out_base.add_col(gridDim.y)) {
    auto gmem_out = gmem_out_base.copy();

    const uint2 monomials_data = *(reinterpret_cast<uint2 *>(gmem_in.ptr) + threadIdx.x);
    bf monomials[2] = {bf{monomials_data.x}, bf{monomials_data.y}};

    if (base_coset_this_block > 0) {
      monomials[0] = bf::mul(initial_adjustments[0], monomials[0]);
      monomials[1] = bf::mul(initial_adjustments[1], monomials[1]);
    }

#pragma unroll 1
    for (unsigned coset = blockIdx.z; coset < num_cosets_in_tile; coset += gridDim.z) {
      bf vals[2] = {monomials[0], monomials[1]};

      exchg_dif(vals[0], vals[1], first_twiddle);

      const bf *twiddles_this_stage = twiddles + THREADS_PER_BLOCK;

      // 5 intrawarp exchanges
      unsigned lane_mask = 1;
#pragma unroll
      // for (unsigned stage = 1; stage < 6; stage++, lane_mask <<= 1) {
      for (unsigned stage = 1; stage < 6; stage++, lane_mask <<= 1) {
        shfl_for_exchange(vals, lane_mask);
        twiddles_this_stage -= THREADS_PER_BLOCK >> stage;
        const unsigned exchg_region = threadIdx.x >> stage;
        const bf twiddle = twiddles_this_stage[exchg_region];
        exchg_dif(vals[0], vals[1], twiddle);
      }

      // Reshuffle data between warps
      smem[VALS_PER_WARP * warp_id + lane_id] = vals[0];
      smem[VALS_PER_WARP * warp_id + lane_id + 32] = vals[1];
      __syncthreads();

      // We could use intrawarp tiling and shuffles to avoid some __syncthreads here,
      // but the pattern is simple and good enough.
#pragma unroll
      for (unsigned stage = 6; stage < STAGES - 1; stage++) {
        twiddles_this_stage -= THREADS_PER_BLOCK >> stage;
        const unsigned exchg_region = threadIdx.x >> stage;
        const unsigned exchg_stride = 1 << stage;
        const unsigned lane_in_region = threadIdx.x & (exchg_stride - 1);
        const unsigned idx0 = 2 * exchg_region * exchg_stride + lane_in_region;
        const unsigned idx1 = idx0 + exchg_stride;
        vals[0] = smem[idx0];
        vals[1] = smem[idx1];
        const bf twiddle = twiddles_this_stage[exchg_region];
        exchg_dif(vals[0], vals[1], twiddle);
        smem[idx0] = vals[0];
        smem[idx1] = vals[1];
        __syncthreads();
      }

      // Final stage
      vals[0] = smem[threadIdx.x];
      vals[1] = smem[threadIdx.x + blockDim.x];
      // Protect reads from the next coset iteration
      if ((monomial_col + gridDim.y < num_cols_per_coset) || (coset + gridDim.z < num_cosets_in_tile))
        __syncthreads();

      exchg_dif(vals[0], vals[1], twiddles[1]);

      gmem_out.set_at_row(threadIdx.x, vals[0]);
      gmem_out.set_at_row(threadIdx.x + blockDim.x, vals[1]);

      if (coset + gridDim.z < num_cosets_in_tile) {
        gmem_out.add_col(num_cols_per_coset * gridDim.z);

#pragma unroll
        for (unsigned j = 0; j < 2; j++)
          monomials[j] = bf::mul(coset_deltas[j], monomials[j]);
      }
    }
  }
}

EXTERN __launch_bounds__(512, 3) __global__
    void ab_lde_first_10_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out, const unsigned log_n,
                                       const unsigned coset_index_base, const unsigned coset_factor_shift, const unsigned num_cols_per_coset,
                                       const unsigned num_cosets_in_tile) {
  lde_first_k_stages_impl<512, 10>(gmem_in, gmem_out, log_n, coset_index_base, coset_factor_shift, num_cols_per_coset, num_cosets_in_tile);
}

EXTERN __launch_bounds__(256, 6) __global__
    void ab_lde_first_9_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out, const unsigned log_n,
                                      const unsigned coset_index_base, const unsigned coset_factor_shift, const unsigned num_cols_per_coset,
                                      const unsigned num_cosets_in_tile) {
  lde_first_k_stages_impl<256, 9>(gmem_in, gmem_out, log_n, coset_index_base, coset_factor_shift, num_cols_per_coset, num_cosets_in_tile);
}

EXTERN __launch_bounds__(128, 12) __global__
    void ab_lde_first_8_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out, const unsigned log_n,
                                      const unsigned coset_index_base, const unsigned coset_factor_shift, const unsigned num_cols_per_coset,
                                      const unsigned num_cosets_in_tile) {
  lde_first_k_stages_impl<128, 8>(gmem_in, gmem_out, log_n, coset_index_base, coset_factor_shift, num_cols_per_coset, num_cosets_in_tile);
}

EXTERN __launch_bounds__(64, 24) __global__
    void ab_lde_first_7_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out, const unsigned log_n,
                                      const unsigned coset_index_base, const unsigned coset_factor_shift, const unsigned num_cols_per_coset,
                                      const unsigned num_cosets_in_tile) {
  lde_first_k_stages_impl<64, 7>(gmem_in, gmem_out, log_n, coset_index_base, coset_factor_shift, num_cols_per_coset, num_cosets_in_tile);
}

// First-K-stages LDE for intermediate sizes.
// Reuses twiddles, monomials, and coset adjustments across cosets.
EXTERN __launch_bounds__(128, 12) __global__
    void ab_lde_first_6_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out_base, const unsigned log_n,
                                      const unsigned coset_index_base, const unsigned coset_factor_shift, const unsigned num_cols_per_coset,
                                      const unsigned num_cosets_in_tile) {
  constexpr unsigned WARPS_PER_BLOCK = 4;
  constexpr unsigned THREADS_PER_BLOCK = WARPS_PER_BLOCK * 32;
  constexpr unsigned STAGES = 6;
  constexpr unsigned VALS_PER_THREAD = 2;
  constexpr unsigned VALS_PER_WARP = 64;

  const unsigned lane_id = threadIdx.x & 31;
  const unsigned warp_id = threadIdx.x >> 5;
  const unsigned warp_gid = blockIdx.x * WARPS_PER_BLOCK + warp_id;

  const unsigned gid = threadIdx.x + blockIdx.x * blockDim.x;

  const unsigned gmem_warp_offset = warp_gid * VALS_PER_WARP;
  gmem_in.add_row(gmem_warp_offset);
  gmem_out_base.add_row(gmem_warp_offset);

  __shared__ bf smem[THREADS_PER_BLOCK];
  bf *twiddles = smem + 32 * warp_id;
  const bf first_twiddle = ab_fully_precomputed_bitrev_twiddles[gid];
  // Cooperatively loads 31 twiddles for remaining stages with minimal divergence. Pain.
  // Stages are ordered in reverse in the shared memory chunk, ie
  // [...[twiddles for stage 8] [twiddles for stage 9] [ twiddles for stage 10]]
  {
    const unsigned lz = __clz(lane_id);        // ranges from 32 to 32 - (STAGES - 1) inclusive
    const unsigned stage = STAGES - (32 - lz); // ranges from STAGES to 1 inclusive
    const unsigned exchg_region_offset = warp_gid * (VALS_PER_WARP >> (stage + 1));
    const unsigned global_bitrev_exchg_region = (lane_id ^ (1 << (31 - lz))) + exchg_region_offset;
    if (lane_id > 0)
      twiddles[lane_id] = ab_fully_precomputed_bitrev_twiddles[global_bitrev_exchg_region];
  }

  __syncwarp();

  const unsigned base_coset_this_block = coset_index_base + blockIdx.z;
  bf coset_deltas[2];
  bf initial_adjustments[2];
  const unsigned global_bitrev_idx = VALS_PER_THREAD * lane_id + warp_gid * VALS_PER_WARP;
#pragma unroll
  for (unsigned i = 0; i < 2; i++) {
    const unsigned global_natural_idx = bitrev(global_bitrev_idx + i, log_n);
    coset_deltas[i] = get_power_from_layers(::ab_ntt_forward_powers, gridDim.z * (global_natural_idx << coset_factor_shift));
    if (base_coset_this_block > 0)
      initial_adjustments[i] = get_forward_twiddle_power((global_natural_idx << coset_factor_shift) * base_coset_this_block);
  }

  gmem_in.add_col(blockIdx.y);
  gmem_out_base.add_col(blockIdx.y + num_cols_per_coset * blockIdx.z);

  // This loop lets the caller balance occupancy and twiddle/adjustment amortization by playing with gridDim.y.
#pragma unroll 1
  for (unsigned monomial_col = blockIdx.y; monomial_col < num_cols_per_coset;
       monomial_col += gridDim.y, gmem_in.add_col(gridDim.y), gmem_out_base.add_col(gridDim.y)) {
    auto gmem_out = gmem_out_base.copy();

    const uint2 monomials_data = *(reinterpret_cast<uint2 *>(gmem_in.ptr) + lane_id);
    bf monomials[2] = {bf{monomials_data.x}, bf{monomials_data.y}};

    if (base_coset_this_block > 0) {
      monomials[0] = bf::mul(initial_adjustments[0], monomials[0]);
      monomials[1] = bf::mul(initial_adjustments[1], monomials[1]);
    }

#pragma unroll 1
    for (unsigned coset = blockIdx.z; coset < num_cosets_in_tile; coset += gridDim.z) {
      bf vals[2] = {monomials[0], monomials[1]};

      exchg_dif(vals[0], vals[1], first_twiddle);

      const bf *twiddles_this_stage = twiddles + 32;

      // 5 intrawarp exchanges
      unsigned lane_mask = 1;
#pragma unroll
      for (unsigned stage = 1; stage < 6; stage++, lane_mask <<= 1) {
        shfl_for_exchange(vals, lane_mask);
        twiddles_this_stage -= 32 >> stage;
        const unsigned exchg_region = lane_id >> stage;
        const bf twiddle = twiddles_this_stage[exchg_region];
        exchg_dif(vals[0], vals[1], twiddle);
      }

      gmem_out.set_at_row(lane_id, vals[0]);
      gmem_out.set_at_row(lane_id + 32, vals[1]);

      if (coset + gridDim.z < num_cosets_in_tile) {
        gmem_out.add_col(num_cols_per_coset * gridDim.z);

#pragma unroll
        for (unsigned j = 0; j < 2; j++)
          monomials[j] = bf::mul(coset_deltas[j], monomials[j]);
      }
    }
  }
}

} // namespace airbender::ntt
