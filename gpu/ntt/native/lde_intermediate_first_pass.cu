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

// One-shot LDE for log_n <= 13. Design goals:
//  - Up to 13 stages in one pass
//  - Between 64 and 512 threads per block
//  - At least 1024 resident threads / SM
// This means at most 64 registers per thread, so the approach is different from kernels above.
// We assumes monomials are small enough to easily persist in L2.
// Instead of reusing monomials, we prioritize reusing twiddles and coset adjustments
// across monomials within each coset.
template <unsigned LOG_WARPS_PER_BLOCK, unsigned STAGES>
DEVICE_FORCEINLINE void lde_oneshot_k_stages_impl(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out,
                                                  const unsigned log_n, const unsigned coset_index_base, const unsigned coset_factor_shift,
                                                  const unsigned num_cols_per_coset, const unsigned num_cosets_in_tile) {
  constexpr unsigned WARPS_PER_BLOCK = 1 << LOG_WARPS_PER_BLOCK;
  constexpr unsigned LOG_VALS_PER_THREAD = 4;
  constexpr unsigned VALS_PER_THREAD = 1 << LOG_VALS_PER_THREAD;
  constexpr unsigned PAIRS_PER_THREAD = VALS_PER_THREAD >> 1;
  constexpr unsigned LOG_VALS_PER_WARP = LOG_VALS_PER_THREAD + 5;
  constexpr unsigned VALS_PER_WARP = VALS_PER_THREAD * 32;
  constexpr unsigned PAIRS_PER_WARP = VALS_PER_WARP >> 1;
  constexpr unsigned VALS_PER_BLOCK = VALS_PER_WARP * WARPS_PER_BLOCK;
  constexpr unsigned PAIRS_PER_BLOCK = VALS_PER_BLOCK >> 1;

  const unsigned lane_id = threadIdx.x & 31;
  const unsigned warp_id = threadIdx.x >> 5;

  // For this kernel, 1 block covers all rows.
  gmem_in.add_row(warp_id * VALS_PER_WARP);
  gmem_out.add_row(32 * warp_id);

  // Because one block covers all rows, blockIdx.x isn't used for row indexing.
  // Instead, we use it to specify this block's target coset.
  gmem_out.add_col(num_cols_per_coset * blockIdx.x);

  __shared__ bf smem[VALS_PER_BLOCK + PAIRS_PER_BLOCK];
  bf *twiddles = smem + VALS_PER_BLOCK;

  // The whole block uses all the twiddles, so we can load them non-divergently (much simpler than multi-pass kernels)
#pragma unroll
  for (unsigned i = threadIdx.x; i < PAIRS_PER_BLOCK; i += blockDim.x)
    twiddles[i] = ab_fully_precomputed_bitrev_twiddles[i];

  __syncthreads();

  const unsigned coset = coset_index_base + blockIdx.x;
  bf coset_adjustments[VALS_PER_THREAD];
  if (coset > 0) {
#pragma unroll
    for (unsigned i{0}; i < PAIRS_PER_THREAD; i++) {
      const unsigned global_bitrev_idx = warp_id * VALS_PER_WARP + 2 * lane_id + 64 * i;
#pragma unroll
      for (unsigned j{0}; j < 2; j++) {
        const unsigned global_natural_idx = bitrev(global_bitrev_idx + j, log_n);
        coset_adjustments[2 * i + j] = get_forward_twiddle_power((global_natural_idx << coset_factor_shift) * coset);
      }
    }
  }

#pragma unroll 1
  for (unsigned monomial_col = 0;
       monomial_col < num_cols_per_coset;
       monomial_col++, gmem_in.add_col(1), gmem_out.add_col(1)) {
    bf *smem_warp = smem + warp_id * VALS_PER_WARP;

    // 5 + log(VALS_PER_THREAD) stages are handled within each warp
#pragma unroll
    for (unsigned initial_warp_region = 0; initial_warp_region < PAIRS_PER_THREAD; initial_warp_region++) {
      const uint2 monomials_data = *(reinterpret_cast<uint2 *>(gmem_in.ptr) + 32 * initial_warp_region + lane_id);
      bf vals[2] = {bf{monomials_data.x}, bf{monomials_data.y}};
      // bf vals[2] = {bf::ONE(), bf::ONE()};

      if (coset > 0) {
        vals[0] = bf::mul(coset_adjustments[2 * initial_warp_region], vals[0]);
        vals[1] = bf::mul(coset_adjustments[2 * initial_warp_region + 1], vals[1]);
      }

      unsigned exchg_region = PAIRS_PER_WARP * warp_id + 32 * initial_warp_region + lane_id;

      exchg_dif(vals[0], vals[1], twiddles[exchg_region]);

      // 5 intrawarp shuffle exchanges
      unsigned lane_mask = 1;
#pragma unroll 1
      for (unsigned stage = 1; stage < 6; stage++, lane_mask <<= 1) {
        shfl_for_exchange(vals, lane_mask);
        exchg_region >>= 1;
        exchg_dif(vals[0], vals[1], twiddles[exchg_region]);
      }

      // post results to this warp's smem chunk
      smem_warp[64 * initial_warp_region + lane_id] = vals[0];
      smem_warp[64 * initial_warp_region + lane_id + 32] = vals[1];
    }

    // log(VALS_PER_THREAD) - 1 intrawarp smem exchanges
#pragma unroll 1
    for (unsigned stage = 0; stage < LOG_VALS_PER_THREAD - 1; stage++) {
      __syncwarp();
      const unsigned regions_per_warp = PAIRS_PER_THREAD >> (stage + 1);
      const unsigned exchg_stride = 64 << stage;
      const unsigned global_region_offset = regions_per_warp * warp_id;
      for (unsigned global_region{global_region_offset}, region_start{0};
           region_start < VALS_PER_WARP;
           global_region++, region_start += 2 * exchg_stride) {
        const bf twiddle = twiddles[global_region];
        for (unsigned lane_in_region = lane_id; lane_in_region < exchg_stride; lane_in_region += 32) {
          bf a = smem_warp[region_start + lane_in_region];
          bf b = smem_warp[region_start + lane_in_region + exchg_stride];
          exchg_dif(a, b, twiddle);
          smem_warp[region_start + lane_in_region] = a;
          smem_warp[region_start + lane_in_region + exchg_stride] = b;
        }
      }
    }

    __syncthreads();

    // Remaining exchanges, intrawarp again but with larger stride
    smem_warp = smem + 32 * warp_id;
#pragma unroll 1
    for (unsigned stage = 0; stage < STAGES - LOG_VALS_PER_WARP; stage++) {
      const unsigned exchg_stride = VALS_PER_WARP << stage;
      for (unsigned region{0}, region_start{0};
           region_start < VALS_PER_BLOCK;
           region++, region_start += 2 * exchg_stride) {
        const bf twiddle = twiddles[region];
        for (unsigned lane_in_region = lane_id; lane_in_region < exchg_stride; lane_in_region += 32 * WARPS_PER_BLOCK) {
          const unsigned base_lane = region_start + lane_in_region;
          bf a = smem_warp[base_lane];
          bf b = smem_warp[base_lane + exchg_stride];
          exchg_dif(a, b, twiddle);
          smem_warp[base_lane] = a;
          smem_warp[base_lane + exchg_stride] = b;
        }
      }
      __syncwarp();
    }

#pragma unroll
    for (unsigned output_lane = lane_id; output_lane < VALS_PER_BLOCK; output_lane += 32 * WARPS_PER_BLOCK)
      gmem_out.set_at_row(output_lane, smem_warp[output_lane]);

    // protect reads from next iteration's writes
    if (monomial_col < num_cols_per_coset - 1)
      __syncthreads();
  }
}

EXTERN __launch_bounds__(512, 2) __global__
    void ab_lde_oneshot_13_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out, const unsigned log_n,
                                         const unsigned coset_index_base, const unsigned coset_factor_shift, const unsigned num_cols_per_coset,
                                         const unsigned num_cosets_in_tile) {
  lde_oneshot_k_stages_impl<4, 13>(gmem_in, gmem_out, log_n, coset_index_base, coset_factor_shift, num_cols_per_coset, num_cosets_in_tile);
}

EXTERN __launch_bounds__(256, 4) __global__
    void ab_lde_oneshot_12_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out, const unsigned log_n,
                                         const unsigned coset_index_base, const unsigned coset_factor_shift, const unsigned num_cols_per_coset,
                                         const unsigned num_cosets_in_tile) {
  lde_oneshot_k_stages_impl<3, 12>(gmem_in, gmem_out, log_n, coset_index_base, coset_factor_shift, num_cols_per_coset, num_cosets_in_tile);
}

EXTERN __launch_bounds__(128, 8) __global__
    void ab_lde_oneshot_11_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out, const unsigned log_n,
                                         const unsigned coset_index_base, const unsigned coset_factor_shift, const unsigned num_cols_per_coset,
                                         const unsigned num_cosets_in_tile) {
  lde_oneshot_k_stages_impl<2, 11>(gmem_in, gmem_out, log_n, coset_index_base, coset_factor_shift, num_cols_per_coset, num_cosets_in_tile);
}

EXTERN __launch_bounds__(64, 16) __global__
    void ab_lde_oneshot_10_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out, const unsigned log_n,
                                         const unsigned coset_index_base, const unsigned coset_factor_shift, const unsigned num_cols_per_coset,
                                         const unsigned num_cosets_in_tile) {
  lde_oneshot_k_stages_impl<1, 10>(gmem_in, gmem_out, log_n, coset_index_base, coset_factor_shift, num_cols_per_coset, num_cosets_in_tile);
}

} // namespace airbender::ntt
