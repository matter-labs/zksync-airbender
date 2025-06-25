#include "ntt.cuh"

namespace ntt {

template <unsigned LOG_VALS_PER_THREAD>
DEVICE_FORCEINLINE void bitrev_Z_to_natural_coset_evals_initial_stages_warp(vectorized_e2_matrix_getter<ld_modifier::cg> gmem_in,
                                                                            vectorized_e2_matrix_setter<st_modifier::cg> gmem_out, const unsigned start_stage,
                                                                            const unsigned stages_this_launch, const unsigned log_n, const unsigned num_Z_cols,
                                                                            const unsigned log_extension_degree, const unsigned coset_idx,
                                                                            const unsigned grid_offset) {
  constexpr unsigned COL_PAIRS_PER_BLOCK = COLS_PER_BLOCK<e2f>::VAL;
  constexpr unsigned VALS_PER_THREAD = 1u << LOG_VALS_PER_THREAD;
  constexpr unsigned PAIRS_PER_THREAD = VALS_PER_THREAD >> 1;
  constexpr unsigned VALS_PER_WARP = 32 * VALS_PER_THREAD;
  constexpr unsigned LOG_VALS_PER_BLOCK = 5 + LOG_VALS_PER_THREAD + 2;
  constexpr unsigned VALS_PER_BLOCK = 1u << LOG_VALS_PER_BLOCK;

  __shared__ e2f smem[VALS_PER_BLOCK];

  const unsigned effective_block_idx_x = blockIdx.x + grid_offset;
  const unsigned lane_id{threadIdx.x & 31};
  const unsigned warp_id{threadIdx.x >> 5};
  const unsigned gmem_offset = VALS_PER_BLOCK * effective_block_idx_x + VALS_PER_WARP * warp_id;
  gmem_in.add_row(gmem_offset);
  gmem_in.add_col(COL_PAIRS_PER_BLOCK * blockIdx.y);
  gmem_out.add_row(gmem_offset);
  gmem_out.add_col(COL_PAIRS_PER_BLOCK * blockIdx.y);

  auto twiddle_cache = smem + VALS_PER_WARP * warp_id;

  load_initial_twiddles_warp<VALS_PER_WARP, LOG_VALS_PER_THREAD, false>(twiddle_cache, lane_id, gmem_offset);

  const unsigned bound = std::min(COL_PAIRS_PER_BLOCK, num_Z_cols - COL_PAIRS_PER_BLOCK * blockIdx.y);
  for (unsigned ntt_idx = 0; ntt_idx < bound; ntt_idx++, gmem_in.add_col(1), gmem_out.add_col(1)) {
    e2f vals[VALS_PER_THREAD];

#pragma unroll
    for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
      // const auto in = memory::load_cg(reinterpret_cast<const uint4 *>(gmem_in + 64 * i + 2 * lane_id));
      // vals[2 * i][0].limb = in.x;
      // vals[2 * i][1].limb = in.y;
      // vals[2 * i + 1][0].limb = in.z;
      // vals[2 * i + 1][1].limb = in.w;
      gmem_in.get_two_adjacent(64 * i + 2 * lane_id, vals[2 * i], vals[2 * i + 1]);
    }

#pragma unroll 1
    for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
      const unsigned mem_idx = gmem_offset + 64 * i + 2 * lane_id;
      const unsigned idx0 = bitrev(mem_idx, log_n);
      const unsigned idx1 = bitrev(mem_idx + 1, log_n);
      vals[2 * i] = lde_scale_and_shift(vals[2 * i], idx0, log_extension_degree, coset_idx, log_n);
      vals[2 * i + 1] = lde_scale_and_shift(vals[2 * i + 1], idx1, log_extension_degree, coset_idx, log_n);
    }

    unsigned lane_mask = 1;
    e2f *twiddles_this_stage = twiddle_cache;
    unsigned num_twiddles_this_stage = VALS_PER_WARP >> 1;
    for (unsigned stage = 0; stage < 6; stage++) {
#pragma unroll
      for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
        const auto twiddle = twiddles_this_stage[(32 * i + lane_id) >> stage];
        exchg_dif(vals[2 * i], vals[2 * i + 1], twiddle);
        if (stage < 5)
          shfl_xor_e2f(vals, i, lane_id, lane_mask);
      }
      lane_mask <<= 1;
      twiddles_this_stage += num_twiddles_this_stage;
      num_twiddles_this_stage >>= 1;
    }

    for (unsigned i = 1; i < LOG_VALS_PER_THREAD; i++) {
#pragma unroll
      for (unsigned j = 0; j < PAIRS_PER_THREAD >> i; j++) {
        const unsigned exchg_tile_sz = 2u << i;
        const unsigned half_exchg_tile_sz = 1u << i;
        const auto twiddle = twiddles_this_stage[j];
#pragma unroll
        for (unsigned k = 0; k < half_exchg_tile_sz; k++) {
          exchg_dif(vals[exchg_tile_sz * j + k], vals[exchg_tile_sz * j + k + half_exchg_tile_sz], twiddle);
        }
      }
      twiddles_this_stage += num_twiddles_this_stage;
      num_twiddles_this_stage >>= 1;
    }

#pragma unroll
    for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
      // This output pattern (resulting from the above shfls) is nice, but not obvious.
      // To see why it works, sketch the shfl stages on paper.
      // memory::store_cg(gmem_out + 64 * i + lane_id, vals[2 * i]);
      // memory::store_cg(gmem_out + 64 * i + lane_id + 32, vals[2 * i + 1]);
      gmem_out.set_at_row(64 * i + lane_id, vals[2 * i]);
      gmem_out.set_at_row(64 * i + lane_id + 32, vals[2 * i + 1]);
    }
  }
}

extern "C" __launch_bounds__(128, 8) __global__
    void bitrev_Z_to_natural_coset_evals_initial_8_stages_warp(vectorized_e2_matrix_getter<ld_modifier::cg> gmem_in,
                                                               vectorized_e2_matrix_setter<st_modifier::cg> gmem_out, const unsigned start_stage,
                                                               const unsigned stages_this_launch, const unsigned log_n, const unsigned num_Z_cols,
                                                               const unsigned log_extension_degree, const unsigned coset_idx, const unsigned grid_offset) {
  bitrev_Z_to_natural_coset_evals_initial_stages_warp<3>(gmem_in, gmem_out, start_stage, stages_this_launch, log_n, num_Z_cols, log_extension_degree, coset_idx,
                                                         grid_offset);
}

extern "C" __launch_bounds__(128, 8) __global__
    void bitrev_Z_to_natural_coset_evals_initial_7_stages_warp(vectorized_e2_matrix_getter<ld_modifier::cg> gmem_in,
                                                               vectorized_e2_matrix_setter<st_modifier::cg> gmem_out, const unsigned start_stage,
                                                               const unsigned stages_this_launch, const unsigned log_n, const unsigned num_Z_cols,
                                                               const unsigned log_extension_degree, const unsigned coset_idx, const unsigned grid_offset) {
  bitrev_Z_to_natural_coset_evals_initial_stages_warp<2>(gmem_in, gmem_out, start_stage, stages_this_launch, log_n, num_Z_cols, log_extension_degree, coset_idx,
                                                         grid_offset);
}

template <unsigned LOG_VALS_PER_THREAD>
DEVICE_FORCEINLINE void bitrev_Z_to_natural_coset_evals_initial_stages_block(vectorized_e2_matrix_getter<ld_modifier::cg> gmem_in,
                                                                             vectorized_e2_matrix_setter<st_modifier::cg> gmem_out, const unsigned start_stage,
                                                                             const unsigned stages_this_launch, const unsigned log_n, const unsigned num_Z_cols,
                                                                             const unsigned log_extension_degree, const unsigned coset_idx,
                                                                             const unsigned grid_offset) {
  constexpr unsigned COL_PAIRS_PER_BLOCK = COLS_PER_BLOCK<e2f>::VAL;
  constexpr unsigned VALS_PER_THREAD = 1u << LOG_VALS_PER_THREAD;
  constexpr unsigned PAIRS_PER_THREAD = VALS_PER_THREAD >> 1;
  constexpr unsigned VALS_PER_WARP = 32 * VALS_PER_THREAD;
  constexpr unsigned WARPS_PER_BLOCK = VALS_PER_WARP >> 4;
  constexpr unsigned LOG_VALS_PER_BLOCK = 2 * (LOG_VALS_PER_THREAD + 5) - 4;
  constexpr unsigned VALS_PER_BLOCK = 1u << LOG_VALS_PER_BLOCK;

  __shared__ e2f smem[VALS_PER_BLOCK];

  const unsigned effective_block_idx_x = blockIdx.x + grid_offset;
  const unsigned lane_id{threadIdx.x & 31};
  const unsigned warp_id{threadIdx.x >> 5};
  const unsigned gmem_block_offset = VALS_PER_BLOCK * effective_block_idx_x;
  const unsigned gmem_offset = gmem_block_offset + VALS_PER_WARP * warp_id;
  gmem_in.add_row(gmem_offset);
  gmem_in.add_col(COL_PAIRS_PER_BLOCK * blockIdx.y);
  // annoyingly scrambled, but should be coalesced overall
  const unsigned gmem_out_thread_offset = 16 * warp_id + VALS_PER_WARP * (lane_id >> 4) + 2 * (lane_id & 7) + ((lane_id >> 3) & 1);
  gmem_out.add_row(gmem_block_offset + gmem_out_thread_offset);
  gmem_out.add_col(COL_PAIRS_PER_BLOCK * blockIdx.y);

  auto twiddle_cache = smem + VALS_PER_WARP * warp_id;

  load_initial_twiddles_warp<VALS_PER_WARP, LOG_VALS_PER_THREAD, false>(twiddle_cache, lane_id, gmem_offset);

  const unsigned bound = std::min(COL_PAIRS_PER_BLOCK, num_Z_cols - COL_PAIRS_PER_BLOCK * blockIdx.y);
  for (unsigned ntt_idx = 0; ntt_idx < bound; ntt_idx++, gmem_in.add_col(1), gmem_out.add_col(1)) {
    e2f vals[VALS_PER_THREAD];

#pragma unroll
    for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
      // const auto pair = memory::load_cg(reinterpret_cast<const uint4 *>(gmem_in + 64 * i + 2 * lane_id));
      // vals[2 * i][0].limb = pair.x;
      // vals[2 * i][1].limb = pair.y;
      // vals[2 * i + 1][0].limb = pair.z;
      // vals[2 * i + 1][1].limb = pair.w;
      gmem_in.get_two_adjacent(64 * i + 2 * lane_id, vals[2 * i], vals[2 * i + 1]);
    }

#pragma unroll 1
    for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
      const unsigned mem_idx = gmem_offset + 64 * i + 2 * lane_id;
      const unsigned idx0 = bitrev(mem_idx, log_n);
      const unsigned idx1 = bitrev(mem_idx + 1, log_n);
      vals[2 * i] = lde_scale_and_shift(vals[2 * i], idx0, log_extension_degree, coset_idx, log_n);
      vals[2 * i + 1] = lde_scale_and_shift(vals[2 * i + 1], idx1, log_extension_degree, coset_idx, log_n);
    }

    unsigned lane_mask = 1;
    e2f *twiddles_this_stage = twiddle_cache;
    unsigned num_twiddles_this_stage = VALS_PER_WARP >> 1;
    for (unsigned stage = 0; stage < 6; stage++) {
#pragma unroll
      for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
        const auto twiddle = twiddles_this_stage[(32 * i + lane_id) >> stage];
        exchg_dif(vals[2 * i], vals[2 * i + 1], twiddle);
        if (stage < 5)
          shfl_xor_e2f(vals, i, lane_id, lane_mask);
      }
      lane_mask <<= 1;
      twiddles_this_stage += num_twiddles_this_stage;
      num_twiddles_this_stage >>= 1;
    }

    for (unsigned i = 1; i < LOG_VALS_PER_THREAD; i++) {
#pragma unroll
      for (unsigned j = 0; j < PAIRS_PER_THREAD >> i; j++) {
        const unsigned exchg_tile_sz = 2u << i;
        const unsigned half_exchg_tile_sz = 1u << i;
        const auto twiddle = twiddles_this_stage[j];
#pragma unroll
        for (unsigned k = 0; k < half_exchg_tile_sz; k++)
          exchg_dif(vals[exchg_tile_sz * j + k], vals[exchg_tile_sz * j + k + half_exchg_tile_sz], twiddle);
      }
      twiddles_this_stage += num_twiddles_this_stage;
      num_twiddles_this_stage >>= 1;
    }

    __syncwarp();

    if (ntt_idx < num_Z_cols - 1) {
#pragma unroll
      for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
        // juggle twiddles in registers while we use smem to communicate values
        const auto tmp0 = twiddle_cache[64 * i + lane_id];
        const auto tmp1 = twiddle_cache[64 * i + lane_id + 32];
        twiddle_cache[64 * i + lane_id] = vals[2 * i];
        twiddle_cache[64 * i + lane_id + 32] = vals[2 * i + 1];
        vals[2 * i] = tmp0;
        vals[2 * i + 1] = tmp1;
      }
    } else {
#pragma unroll
      for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
        twiddle_cache[64 * i + lane_id] = vals[2 * i];
        twiddle_cache[64 * i + lane_id + 32] = vals[2 * i + 1];
      }
    }

    __syncthreads();

    auto pair_addr = smem + 16 * warp_id + VALS_PER_WARP * (lane_id >> 3) + 2 * (threadIdx.x & 7);
    if (ntt_idx < num_Z_cols - 1) {
      // juggle twiddles back into smem
      // In theory, we could avoid the full-size stashing and extra syncthreads by
      // "switching" each warp's twiddle region from contiguous to strided-chunks each iteration,
      // but that's a lot of trouble. Let's try the simple approach first.
      e2f tmp[VALS_PER_THREAD];
#pragma unroll
      for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
        tmp[2 * i] = vals[2 * i];
        tmp[2 * i + 1] = vals[2 * i + 1];
      }

#pragma unroll
      for (unsigned i = 0; i < PAIRS_PER_THREAD; i++, pair_addr += 4 * VALS_PER_WARP) {
        const auto pair = *reinterpret_cast<const uint4 *>(pair_addr);
        vals[2 * i][0].limb = pair.x;
        vals[2 * i][1].limb = pair.y;
        vals[2 * i + 1][0].limb = pair.z;
        vals[2 * i + 1][1].limb = pair.w;
      }

      __syncthreads();

#pragma unroll
      for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
        twiddle_cache[64 * i + lane_id] = tmp[2 * i];
        twiddle_cache[64 * i + lane_id + 32] = tmp[2 * i + 1];
      }

      __syncwarp(); // maybe unnecessary due to shfls below
      // __syncthreads();
    } else {
#pragma unroll
      for (unsigned i = 0; i < PAIRS_PER_THREAD; i++, pair_addr += 4 * VALS_PER_WARP) {
        const auto pair = *reinterpret_cast<const uint4 *>(pair_addr);
        vals[2 * i][0].limb = pair.x;
        vals[2 * i][1].limb = pair.y;
        vals[2 * i + 1][0].limb = pair.z;
        vals[2 * i + 1][1].limb = pair.w;
      }
    }

    const unsigned stages_so_far = 6 + LOG_VALS_PER_THREAD - 1;
    lane_mask = 8;
    unsigned exchg_region_offset = effective_block_idx_x * (WARPS_PER_BLOCK >> 1) + (lane_id >> 4);
    for (unsigned s = 0; s < 2; s++) {
      if (s + stages_so_far < stages_this_launch) {
#pragma unroll
        for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
          // TODO: Handle these cooperatively?
          const auto twiddle = get_twiddle<false>(exchg_region_offset + ((2 * i) >> s));
          shfl_xor_e2f(vals, i, lane_id, lane_mask);
          exchg_dif(vals[2 * i], vals[2 * i + 1], twiddle);
        }
      } else {
#pragma unroll
        for (unsigned i = 0; i < PAIRS_PER_THREAD; i++)
          shfl_xor_e2f(vals, i, lane_id, lane_mask);
      }
      lane_mask <<= 1;
      exchg_region_offset >>= 1;
    }

    exchg_region_offset = effective_block_idx_x * (PAIRS_PER_THREAD >> 1);
    for (unsigned i = 1; i < LOG_VALS_PER_THREAD; i++) {
      if (i + 2 + stages_so_far <= stages_this_launch) {
#pragma unroll
        for (unsigned j = 0; j < PAIRS_PER_THREAD >> i; j++) {
          const unsigned exchg_tile_sz = 2u << i;
          const unsigned half_exchg_tile_sz = 1u << i;
          const auto twiddle = get_twiddle<false>(exchg_region_offset + (j >> (i - 1)));
#pragma unroll
          for (unsigned k = 0; k < half_exchg_tile_sz; k++)
            exchg_dif(vals[exchg_tile_sz * j + k], vals[exchg_tile_sz * j + k + half_exchg_tile_sz], twiddle);
        }
      }
      exchg_region_offset >>= 1;
    }
#pragma unroll
    for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
      // memory::store_cg(gmem_out + 4 * i * VALS_PER_WARP, vals[2 * i]);
      // memory::store_cg(gmem_out + (4 * i + 2) * VALS_PER_WARP, vals[2 * i + 1]);
      gmem_out.set_at_row(4 * i * VALS_PER_WARP, vals[2 * i]);
      gmem_out.set_at_row((4 * i + 2) * VALS_PER_WARP, vals[2 * i + 1]);
    }
  }
}

// Bizarrely, on cuda 12.2 and 12.3:
// With launch bounds it uses 64 registers per thread AND spills registers.
// Without launch bounds it still uses 64 registers per thread but DOES NOT spill registers.
// #justnvccthings
extern "C" __launch_bounds__(512, 2) __global__
    void bitrev_Z_to_natural_coset_evals_initial_9_to_12_stages_block(vectorized_e2_matrix_getter<ld_modifier::cg> gmem_in,
                                                                      vectorized_e2_matrix_setter<st_modifier::cg> gmem_out, const unsigned start_stage,
                                                                      const unsigned stages_this_launch, const unsigned log_n, const unsigned num_Z_cols,
                                                                      const unsigned log_extension_degree, const unsigned coset_idx,
                                                                      const unsigned grid_offset) {
  bitrev_Z_to_natural_coset_evals_initial_stages_block<3>(gmem_in, gmem_out, start_stage, stages_this_launch, log_n, num_Z_cols, log_extension_degree,
                                                          coset_idx, grid_offset);
}

template <unsigned LOG_VALS_PER_THREAD>
DEVICE_FORCEINLINE void bitrev_Z_to_natural_coset_evals_noninitial_stages_block(vectorized_e2_matrix_getter<ld_modifier::cg> gmem_in,
                                                                                vectorized_e2_matrix_setter<st_modifier::cg> gmem_out,
                                                                                const unsigned start_stage, const bool skip_first_stage, const unsigned log_n,
                                                                                const unsigned num_Z_cols, const unsigned log_extension_degree,
                                                                                const unsigned grid_offset) {
  constexpr unsigned COL_PAIRS_PER_BLOCK = COLS_PER_BLOCK<e2f>::VAL;
  constexpr unsigned VALS_PER_THREAD = 1u << LOG_VALS_PER_THREAD;
  constexpr unsigned PAIRS_PER_THREAD = VALS_PER_THREAD >> 1;
  constexpr unsigned VALS_PER_WARP = 32 * VALS_PER_THREAD;
  constexpr unsigned TILES_PER_WARP = VALS_PER_WARP >> 4;
  constexpr unsigned WARPS_PER_BLOCK = VALS_PER_WARP >> 4;
  constexpr unsigned LOG_VALS_PER_BLOCK = 2 * (LOG_VALS_PER_THREAD + 5) - 4;
  constexpr unsigned VALS_PER_BLOCK = 1u << LOG_VALS_PER_BLOCK;
  constexpr unsigned TILES_PER_BLOCK = VALS_PER_BLOCK >> 4;
  constexpr unsigned EXCHG_REGIONS_PER_BLOCK = TILES_PER_BLOCK >> 1;

  __shared__ e2f smem[VALS_PER_BLOCK];

  const unsigned effective_block_idx_x = blockIdx.x + grid_offset;
  const unsigned lane_id{threadIdx.x & 31};
  const unsigned warp_id{threadIdx.x >> 5};
  const unsigned log_tile_stride = skip_first_stage ? start_stage - 1 : start_stage;
  const unsigned tile_stride = 1u << log_tile_stride;
  const unsigned log_blocks_per_region = log_tile_stride - 4; // tile size is always 16
  const unsigned block_bfly_region_size = TILES_PER_BLOCK * tile_stride;
  const unsigned block_bfly_region = effective_block_idx_x >> log_blocks_per_region;
  const unsigned block_exchg_region_offset = block_bfly_region * EXCHG_REGIONS_PER_BLOCK;
  const unsigned block_bfly_region_start = block_bfly_region * block_bfly_region_size;
  const unsigned block_start_in_bfly_region = 16 * (effective_block_idx_x & ((1u << log_blocks_per_region) - 1));
  gmem_in.add_row(block_bfly_region_start + block_start_in_bfly_region);
  gmem_in.add_col(COL_PAIRS_PER_BLOCK * blockIdx.y);
  // annoyingly scrambled, but should be coalesced overall
  const unsigned gmem_out_thread_offset = tile_stride * warp_id + tile_stride * WARPS_PER_BLOCK * (lane_id >> 4) + 2 * (lane_id & 7) + ((lane_id >> 3) & 1);
  const unsigned gmem_out_offset = block_bfly_region_start + block_start_in_bfly_region + gmem_out_thread_offset;
  gmem_out.add_row(gmem_out_offset);
  gmem_out.add_col(COL_PAIRS_PER_BLOCK * blockIdx.y);

  auto twiddle_cache = smem + VALS_PER_WARP * warp_id;

  load_noninitial_twiddles_warp<LOG_VALS_PER_THREAD, false>(twiddle_cache, lane_id, warp_id, block_exchg_region_offset);

  const unsigned bound = std::min(COL_PAIRS_PER_BLOCK, num_Z_cols - COL_PAIRS_PER_BLOCK * blockIdx.y);
  for (unsigned ntt_idx = 0; ntt_idx < bound; ntt_idx++, gmem_in.add_col(1), gmem_out.add_col(1)) {
    e2f vals[VALS_PER_THREAD];

    if (skip_first_stage) {
      auto val0_offset = TILES_PER_WARP * tile_stride * warp_id + 2 * tile_stride * (lane_id >> 4) + 2 * (threadIdx.x & 7) + (lane_id >> 3 & 1);
#pragma unroll
      for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
        vals[2 * i] = gmem_in.get_at_row(val0_offset);
        vals[2 * i + 1] = gmem_in.get_at_row(val0_offset + tile_stride);
        val0_offset += 4 * tile_stride;
      }
    } else {
      auto pair_offset = TILES_PER_WARP * tile_stride * warp_id + tile_stride * (lane_id >> 3) + 2 * (threadIdx.x & 7);
#pragma unroll
      for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
        // const auto pair = memory::load_cg(reinterpret_cast<const uint4 *>(pair_addr));
        // vals[2 * i][0].limb = pair.x;
        // vals[2 * i][1].limb = pair.y;
        // vals[2 * i + 1][0].limb = pair.z;
        // vals[2 * i + 1][1].limb = pair.w;
        gmem_in.get_two_adjacent(pair_offset, vals[2 * i], vals[2 * i + 1]);
        pair_offset += 4 * tile_stride;
      }
    }

    unsigned lane_mask = 8;
    e2f *twiddles_this_stage = twiddle_cache;
    unsigned num_twiddles_this_stage = 1u << LOG_VALS_PER_THREAD;
    for (unsigned s = 4; s < LOG_VALS_PER_THREAD + 3; s++) {
      if (!skip_first_stage || s > 4) {
#pragma unroll
        for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
          const auto twiddle = twiddles_this_stage[(32 * i + lane_id) >> s];
          shfl_xor_e2f(vals, i, lane_id, lane_mask);
          exchg_dif(vals[2 * i], vals[2 * i + 1], twiddle);
        }
      }
      lane_mask <<= 1;
      twiddles_this_stage += num_twiddles_this_stage;
      num_twiddles_this_stage >>= 1;
    }

    for (unsigned i = 1; i < LOG_VALS_PER_THREAD; i++) {
#pragma unroll
      for (unsigned j = 0; j < PAIRS_PER_THREAD >> i; j++) {
        const unsigned exchg_tile_sz = 2u << i;
        const unsigned half_exchg_tile_sz = 1 << i;
        const auto twiddle = twiddles_this_stage[j];
#pragma unroll
        for (unsigned k = 0; k < half_exchg_tile_sz; k++)
          exchg_dif(vals[exchg_tile_sz * j + k], vals[exchg_tile_sz * j + k + half_exchg_tile_sz], twiddle);
      }
      twiddles_this_stage += num_twiddles_this_stage;
      num_twiddles_this_stage >>= 1;
    }

    __syncwarp();

    // there are at most 31 per-warp twiddles, so we only need 1 temporary per thread to stash them
    e2f tmp{};
    if (ntt_idx < num_Z_cols - 1)
      tmp = twiddle_cache[lane_id];

    // annoyingly scrambled but should be bank-conflict-free
    const unsigned smem_thread_offset = 16 * (lane_id >> 4) + 2 * (lane_id & 7) + ((lane_id >> 3) & 1);
#pragma unroll
    for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
      twiddle_cache[64 * i + smem_thread_offset] = vals[2 * i];
      twiddle_cache[64 * i + smem_thread_offset + 32] = vals[2 * i + 1];
    }

    __syncthreads();

    auto smem_pair_addr = smem + 16 * warp_id + VALS_PER_WARP * (lane_id >> 3) + 2 * (threadIdx.x & 7);
#pragma unroll
    for (unsigned i = 0; i < PAIRS_PER_THREAD; i++, smem_pair_addr += 4 * VALS_PER_WARP) {
      const auto pair = *reinterpret_cast<const uint4 *>(smem_pair_addr);
      vals[2 * i][0].limb = pair.x;
      vals[2 * i][1].limb = pair.y;
      vals[2 * i + 1][0].limb = pair.z;
      vals[2 * i + 1][1].limb = pair.w;
    }

    if (ntt_idx < num_Z_cols - 1) {
      __syncthreads();
      twiddle_cache[lane_id] = tmp;
      __syncwarp(); // maybe unnecessary due to shfls below
      // __syncthreads();
    }

    lane_mask = 8;
    unsigned exchg_region_offset = (block_exchg_region_offset >> (LOG_VALS_PER_THREAD + 1)) + (lane_id >> 4);
    for (unsigned s = 0; s < 2; s++) {
#pragma unroll
      for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
        // TODO: Handle these cooperatively?
        const auto twiddle = get_twiddle<false>(exchg_region_offset + ((2 * i) >> s));
        shfl_xor_e2f(vals, i, lane_id, lane_mask);
        exchg_dif(vals[2 * i], vals[2 * i + 1], twiddle);
      }
      lane_mask <<= 1;
      exchg_region_offset >>= 1;
    }

    for (unsigned i = 1; i < LOG_VALS_PER_THREAD; i++) {
#pragma unroll
      for (unsigned j = 0; j < PAIRS_PER_THREAD >> i; j++) {
        const unsigned exchg_tile_sz = 2 << i;
        const unsigned half_exchg_tile_sz = 1 << i;
        const auto twiddle = get_twiddle<false>(exchg_region_offset + (j >> (i - 1)));
#pragma unroll
        for (unsigned k = 0; k < half_exchg_tile_sz; k++)
          exchg_dif(vals[exchg_tile_sz * j + k], vals[exchg_tile_sz * j + k + half_exchg_tile_sz], twiddle);
      }
      exchg_region_offset >>= 1;
    }

#pragma unroll
    for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
      // memory::store_cg(gmem_out + 4 * i * tile_stride * WARPS_PER_BLOCK, vals[2 * i]);
      // memory::store_cg(gmem_out + (4 * i + 2) * tile_stride * WARPS_PER_BLOCK, vals[2 * i + 1]);
      gmem_out.set_at_row(4 * i * tile_stride * WARPS_PER_BLOCK, vals[2 * i]);
      gmem_out.set_at_row((4 * i + 2) * tile_stride * WARPS_PER_BLOCK, vals[2 * i + 1]);
    }
  }
}

extern "C" __launch_bounds__(512, 2) __global__
    void bitrev_Z_to_natural_coset_evals_noninitial_7_or_8_stages_block(vectorized_e2_matrix_getter<ld_modifier::cg> gmem_in,
                                                                        vectorized_e2_matrix_setter<st_modifier::cg> gmem_out, const unsigned start_stage,
                                                                        const unsigned stages_this_launch, const unsigned log_n, const unsigned num_Z_cols,
                                                                        const unsigned log_extension_degree, const unsigned coset_idx,
                                                                        const unsigned grid_offset) {
  bitrev_Z_to_natural_coset_evals_noninitial_stages_block<3>(gmem_in, gmem_out, start_stage, stages_this_launch == 7, log_n, num_Z_cols, log_extension_degree,
                                                             grid_offset);
}

// Simple, non-optimized kernel used for log_n < 16, to unblock debugging small proofs.
extern "C" __launch_bounds__(512, 2) __global__
    void bitrev_Z_to_natural_coset_evals_one_stage(vectorized_e2_matrix_getter<ld_modifier::cg> gmem_in, vectorized_e2_matrix_setter<st_modifier::cg> gmem_out,
                                                   const unsigned start_stage, const unsigned log_n, const unsigned blocks_per_ntt,
                                                   const unsigned log_extension_degree, const unsigned coset_idx) {
  const unsigned col_pair = blockIdx.x / blocks_per_ntt;
  const unsigned bid_in_ntt = blockIdx.x - col_pair * blocks_per_ntt;
  const unsigned tid_in_ntt = threadIdx.x + bid_in_ntt * blockDim.x;
  if (tid_in_ntt >= (1u << (log_n - 1)))
    return;
  const unsigned log_exchg_region_sz = start_stage + 1;
  const unsigned exchg_region = tid_in_ntt >> (log_exchg_region_sz - 1);
  const unsigned tid_in_exchg_region = tid_in_ntt - (exchg_region << (log_exchg_region_sz - 1));
  const unsigned exchg_stride = 1 << (log_exchg_region_sz - 1);
  const unsigned a_idx = tid_in_exchg_region + exchg_region * (1u << log_exchg_region_sz);
  const unsigned b_idx = a_idx + exchg_stride;
  gmem_in.add_col(col_pair);
  gmem_out.add_col(col_pair);

  const auto twiddle = get_twiddle<false>(exchg_region);
  auto a = gmem_in.get_at_row(a_idx);
  auto b = gmem_in.get_at_row(b_idx);

  if (start_stage == 0) {
    // a = a_idx == 0 ? e2f{bf{0}, bf{0}} : lde_scale_and_shift(a, a_idx, log_extension_degree, coset_idx, log_n);
    a = lde_scale_and_shift(a, bitrev(a_idx, log_n), log_extension_degree, coset_idx, log_n);
    b = lde_scale_and_shift(b, bitrev(b_idx, log_n), log_extension_degree, coset_idx, log_n);
  }

  exchg_dif(a, b, twiddle);

  gmem_out.set_at_row(a_idx, a);
  gmem_out.set_at_row(b_idx, b);
}

} // namespace ntt
