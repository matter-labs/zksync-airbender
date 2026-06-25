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

// First-10-stages LDE.
// Reuses twiddles, monomials, and 
DEVICE_FORCEINLINE void lde_first_10_stages_impl(bf_matrix_getter<ld_modifier::cg> gmem_in,
                                                 bf_matrix_setter<st_modifier::cg> gmem_out,
                                                 const unsigned log_n,
                                                 const unsigned coset_index_base,
                                                 const unsigned coset_factor_shift,
                                                 const unsigned num_cols_per_coset,
                                                 const unsigned num_cosets_in_tile) {
  constexpr unsigned THREADS_PER_BLOCK = 512;
  constexpr unsigned VALS_PER_THREAD = 2;
  constexpr unsigned VALS_PER_WARP = 64;
  constexpr unsigned VALS_PER_BLOCK = THREADS_PER_BLOCK * VALS_PER_THREAD;

  const unsigned gid = threadIdx.x + blockIdx.x * blockDim.x;

  gmem_in.add_col(blockIdx.y);
  gmem_out.add_col(blockIdx.y);

  const unsigned gmem_block_offset = blockIdx.x * VALS_PER_BLOCK;
  gmem_in.add_row(gmem_block_offset);
  gmem_out.add_row(gmem_block_offset);

  __shared__ bf smem[VALS_PER_BLOCK];
  bf *twiddles = smem + VALS_PER_BLOCK;
  const bf first_twiddle = get_forward_twiddle_power(bitrev(gid, log_n - 1) << (OMEGA_LOG_ORDER - log_n));
  // Cooperatively loads 511 twiddles for remaining stages with minimal divergence. Pain.
  // Stages are ordered in reverse in the shared memory chunk, ie
  // [...[twiddles for stage 8] [twiddles for stage 9] [ twiddles for stage 10]]
  {
    const unsigned lz = __clz(threadIdx.x);
    const unsigned stage = 10 - (32 - lz);
    const unsigned exchg_region_offset = blockIdx.x * (VALS_PER_BLOCK >> (stage+ 1));
    const unsigned global_bitrev_exchg_region = (threadIdx.x ^ (1 << lz)) + exchg_region_offset;
    const unsigned global_natural_exchg_region = bitrev(global_bitrev_exchg_region, log_n - stage - 1);
    if (threadIdx.x > 0)
      twiddles[threadIdx.x] = get_forward_twiddle_power(global_natural_exchg_region << (OMEGA_LOG_ORDER - log_n - stage));
  }

  __syncthreads();

  const uint2 monomials_data = *(reinterpret_cast<uint2 *>(gmem_in.ptr) + threadIdx.x);
  bf monomials[2] = {bf{monomials_data.x}, bf{monomials_data.y}};

  bf coset_deltas[2];
  const unsigned global_bitrev_idx = (VALS_PER_THREAD * threadIdx.x) + blockIdx.x * VALS_PER_BLOCK;
#pragma unroll
  for (unsigned i = 0; i < 2; i++) {
    const unsigned global_natural_idx = bitrev(global_bitrev_idx + i, log_n);
    coset_deltas[i] = get_power_from_layers(::ab_ntt_forward_powers, global_natural_idx * coset_factor_shift);
    if (coset_index_base > 0) {
      const bf initial_adjustment = get_forward_twiddle_power(global_natural_idx * coset_factor_shift * coset_index_base);
      monomials[i] = bf::mul(initial_adjustment, monomials[i]);
    }
  }

  // inter-warp reshuffling helpers
  const unsigned warp_id = threadIdx.x >> 5;
  const unsigned lane_id = threadIdx.x & 31;
  constexpr unsigned LOG_TILE_SIZE = 2;
  constexpr unsigned TILE_SIZE = 1 << LOG_TILE_SIZE;
  const unsigned tile_in_warp = lane_id >> LOG_TILE_SIZE;
  const unsigned lane_in_tile = lane_id & (TILE_SIZE - 1);
  const unsigned reshuffle_write_idx_0 = linear_to_swizzled(lane_id + VALS_PER_WARP * warp_id);
  const unsigned reshuffle_write_idx_1 = linear_to_swizzled(lane_id + VALS_PER_WARP * warp_id + 32);
  const unsigned reshuffle_read_idx_0 = linear_to_swizzled(lane_in_tile + TILE_SIZE * warp_id + VALS_PER_WARP * 2 * tile_in_warp);
  const unsigned reshuffle_read_idx_1 = linear_to_swizzled(lane_in_tile + TILE_SIZE * warp_id + VALS_PER_WARP * (2 * tile_in_warp + 1));

#pragma unroll 1
  for (unsigned i = 0; i < num_cosets_in_tile; i++) {
    bf vals[2] = {monomials[0], monomials[1]};

    exchg_dif(vals[0], vals[1], first_twiddle);

    const bf *twiddles_this_stage = twiddles + THREADS_PER_BLOCK;

    // 5 intrawarp exchanges
    unsigned lane_mask = 1;
#pragma unroll
    for (unsigned stage = 1; stage < 6; stage++, lane_mask <<= 1) {
      shfl_for_exchange(vals, lane_mask);
      twiddles_this_stage -= THREADS_PER_BLOCK >> stage;
      const unsigned exchg_region = threadIdx.x >> stage;
      const bf twiddle = twiddles_this_stage[exchg_region];
      exchg_dif(vals[0], vals[1], twiddle);
    }

    // Reshuffle data between warps
    smem[reshuffle_write_idx_0] = vals[0];
    smem[reshuffle_write_idx_1] = vals[1];
    __syncthreads();
    vals[0] = smem[reshuffle_read_idx_0];
    vals[1] = smem[reshuffle_read_idx_1];
    // we need read-protection in this case. A barrier arrive here, with a wait before the writes above, would work too.
    __syncthreads();

    twiddles_this_stage -= THREADS_PER_BLOCK >> 6;
    exchg_dif(vals[0], vals[1], twiddles_this_stage[tile_in_warp]);

    // 3 intrawarp exchanges
    lane_mask = TILE_SIZE;
#pragma unroll
    for (unsigned stage = 7; stage < 10; stage++, lane_mask <<= 1) {
      shfl_for_exchange(vals, lane_mask);
      twiddles_this_stage -= THREADS_PER_BLOCK >> stage;
      const unsigned exchg_region = tile_in_warp >> (stage - 6);
      const bf twiddle = twiddles_this_stage[exchg_region];
      exchg_dif(vals[0], vals[1], twiddle);
    }

    gmem_out.set_at_row(threadIdx.x, vals[0]);
    gmem_out.set_at_row(threadIdx.x, vals[1]);

    if (i < num_cosets_in_tile - 1) {
      gmem_out.add_col(num_cols_per_coset);

#pragma unroll
      for (unsigned j = 0; j < 2; j++)
        monomials[j] = bf::mul(coset_deltas[j], monomials[j]);
    }
  }
}

EXTERN __launch_bounds__(512, 3) 
__global__ void ab_lde_first_10_stages(bf_matrix_getter<ld_modifier::cg> gmem_in,
                                       bf_matrix_setter<st_modifier::cg> gmem_out,
                                       const unsigned log_n,
                                       const unsigned coset_index_base,
                                       const unsigned coset_factor_shift,
                                       const unsigned num_cols_per_coset,
                                       const unsigned num_cosets_in_tile) {
  lde_first_10_stages_impl(gmem_in, gmem_out, log_n, coset_index_base, coset_factor_shift, num_cols_per_coset, num_cosets_in_tile);
}

} // namespace airbender::ntt
