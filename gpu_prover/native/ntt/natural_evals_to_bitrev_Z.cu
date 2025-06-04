#include "ntt.cuh"

namespace ntt {

template <unsigned LOG_VALS_PER_THREAD, bool evals_are_coset>
DEVICE_FORCEINLINE void evals_to_Z_final_stages_warp(vectorized_e2_matrix_getter<ld_modifier::cg> gmem_in,
                                                     vectorized_e2_matrix_setter<st_modifier::cg> gmem_out, const unsigned start_stage,
                                                     const unsigned stages_this_launch, const unsigned log_n, const unsigned num_Z_cols,
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

  e2f vals[VALS_PER_THREAD];

  load_initial_twiddles_warp<VALS_PER_WARP, LOG_VALS_PER_THREAD, true>(twiddle_cache, lane_id, gmem_offset);

  const unsigned bound = std::min(COL_PAIRS_PER_BLOCK, num_Z_cols - COL_PAIRS_PER_BLOCK * blockIdx.y);
  for (unsigned ntt_idx = 0; ntt_idx < bound; ntt_idx++, gmem_in.add_col(1), gmem_out.add_col(1)) {
#pragma unroll
    for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
      vals[2 * i] = gmem_in.get_at_row(64 * i + lane_id);
      vals[2 * i + 1] = gmem_in.get_at_row(64 * i + lane_id + 32);
    }

    e2f *twiddles_this_stage = twiddle_cache + VALS_PER_WARP - 2;
    unsigned num_twiddles_this_stage = 1;
    for (unsigned i = 0; i < LOG_VALS_PER_THREAD - 1; i++) {
#pragma unroll
      for (unsigned j = 0; j < (1u << i); j++) {
        const unsigned exchg_tile_sz = VALS_PER_THREAD >> i;
        const unsigned half_exchg_tile_sz = exchg_tile_sz >> 1;
        const auto twiddle = twiddles_this_stage[j];
#pragma unroll
        for (unsigned k = 0; k < half_exchg_tile_sz; k++) {
          exchg_dit(vals[exchg_tile_sz * j + k], vals[exchg_tile_sz * j + k + half_exchg_tile_sz], twiddle);
        }
      }
      num_twiddles_this_stage <<= 1;
      twiddles_this_stage -= num_twiddles_this_stage;
    }

    unsigned lane_mask = 16;
    for (unsigned stage = 0, s = 5; stage < 6; stage++, s--) {
#pragma unroll
      for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
        const auto twiddle = twiddles_this_stage[(32 * i + lane_id) >> s];
        exchg_dit(vals[2 * i], vals[2 * i + 1], twiddle);
        if (stage < 5)
          shfl_xor_e2f(vals, i, lane_id, lane_mask);
      }
      lane_mask >>= 1;
      num_twiddles_this_stage <<= 1;
      twiddles_this_stage -= num_twiddles_this_stage;
    }

#pragma unroll
    for (unsigned i = 0; i < VALS_PER_THREAD; i++)
      vals[i] = e2f::mul(vals[i], inv_sizes[log_n]);

    if (evals_are_coset) {
#pragma unroll 1
      for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
        const unsigned mem_idx = gmem_offset + 64 * i + 2 * lane_id;
        const unsigned idx0 = bitrev(mem_idx, log_n);
        const unsigned idx1 = bitrev(mem_idx + 1, log_n);
        vals[2 * i] = lde_scale<true>(vals[2 * i], idx0, 1, 1, log_n);
        vals[2 * i + 1] = lde_scale<true>(vals[2 * i + 1], idx1, 1, 1, log_n);
      }
    }

    for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
      // gmem_out.set_at_row(64 * i + 2 * lane_id, vals[2 * i]);
      // gmem_out.set_at_row(64 * i + 2 * lane_id + 1, vals[2 * i + 1]);
      gmem_out.set_two_adjacent(64 * i + 2 * lane_id, vals[2 * i], vals[2 * i + 1]);
    }
  }
}

extern "C" __launch_bounds__(128, 8) __global__
    void main_domain_evals_to_Z_final_8_stages_warp(vectorized_e2_matrix_getter<ld_modifier::cg> gmem_in, vectorized_e2_matrix_setter<st_modifier::cg> gmem_out,
                                                    const unsigned start_stage, const unsigned stages_this_launch, const unsigned log_n,
                                                    const unsigned num_Z_cols, const unsigned grid_offset) {
  evals_to_Z_final_stages_warp<3, false>(gmem_in, gmem_out, start_stage, stages_this_launch, log_n, num_Z_cols, grid_offset);
}

extern "C" __launch_bounds__(128, 8) __global__
    void main_domain_evals_to_Z_final_7_stages_warp(vectorized_e2_matrix_getter<ld_modifier::cg> gmem_in, vectorized_e2_matrix_setter<st_modifier::cg> gmem_out,
                                                    const unsigned start_stage, const unsigned stages_this_launch, const unsigned log_n,
                                                    const unsigned num_Z_cols, const unsigned grid_offset) {
  evals_to_Z_final_stages_warp<2, false>(gmem_in, gmem_out, start_stage, stages_this_launch, log_n, num_Z_cols, grid_offset);
}

extern "C" __launch_bounds__(128, 8) __global__
    void coset_evals_to_Z_final_8_stages_warp(vectorized_e2_matrix_getter<ld_modifier::cg> gmem_in, vectorized_e2_matrix_setter<st_modifier::cg> gmem_out,
                                              const unsigned start_stage, const unsigned stages_this_launch, const unsigned log_n, const unsigned num_Z_cols,
                                              const unsigned grid_offset) {
  evals_to_Z_final_stages_warp<3, true>(gmem_in, gmem_out, start_stage, stages_this_launch, log_n, num_Z_cols, grid_offset);
}

extern "C" __launch_bounds__(128, 8) __global__
    void coset_evals_to_Z_final_7_stages_warp(vectorized_e2_matrix_getter<ld_modifier::cg> gmem_in, vectorized_e2_matrix_setter<st_modifier::cg> gmem_out,
                                              const unsigned start_stage, const unsigned stages_this_launch, const unsigned log_n, const unsigned num_Z_cols,
                                              const unsigned grid_offset) {
  evals_to_Z_final_stages_warp<2, true>(gmem_in, gmem_out, start_stage, stages_this_launch, log_n, num_Z_cols, grid_offset);
}

template <unsigned LOG_VALS_PER_THREAD, bool evals_are_coset>
DEVICE_FORCEINLINE void evals_to_Z_final_stages_block(vectorized_e2_matrix_getter<ld_modifier::cg> gmem_in,
                                                      vectorized_e2_matrix_setter<st_modifier::cg> gmem_out, const unsigned start_stage,
                                                      const unsigned stages_this_launch, const unsigned log_n, const unsigned num_Z_cols,
                                                      const unsigned grid_offset) {
  constexpr unsigned COL_PAIRS_PER_BLOCK = COLS_PER_BLOCK<e2f>::VAL;
  constexpr unsigned VALS_PER_THREAD = 1u << LOG_VALS_PER_THREAD;
  constexpr unsigned PAIRS_PER_THREAD = VALS_PER_THREAD >> 1;
  constexpr unsigned VALS_PER_WARP = 32 * VALS_PER_THREAD;
  constexpr unsigned WARPS_PER_BLOCK = VALS_PER_WARP >> 4;
  constexpr unsigned VALS_PER_BLOCK = 32 * VALS_PER_THREAD * WARPS_PER_BLOCK;
  constexpr unsigned MAX_STAGES_THIS_LAUNCH = 2 * (LOG_VALS_PER_THREAD + 5) - 4;

  __shared__ e2f smem[VALS_PER_BLOCK];

  const unsigned effective_block_idx_x = blockIdx.x + grid_offset;
  const unsigned lane_id{threadIdx.x & 31};
  const unsigned warp_id{threadIdx.x >> 5};
  const unsigned gmem_block_offset = VALS_PER_BLOCK * effective_block_idx_x;
  const unsigned gmem_offset = gmem_block_offset + VALS_PER_WARP * warp_id;
  // annoyingly scrambled, but should be coalesced overall
  const unsigned gmem_in_thread_offset = 16 * warp_id + VALS_PER_WARP * (lane_id >> 4) + 2 * (lane_id & 7) + ((lane_id >> 3) & 1);
  gmem_in.add_row(gmem_block_offset + gmem_in_thread_offset);
  gmem_in.add_col(COL_PAIRS_PER_BLOCK * blockIdx.y);
  gmem_out.add_row(gmem_offset);
  gmem_out.add_col(COL_PAIRS_PER_BLOCK * blockIdx.y);

  auto twiddle_cache = smem + VALS_PER_WARP * warp_id;

  const unsigned bound = std::min(COL_PAIRS_PER_BLOCK, num_Z_cols - COL_PAIRS_PER_BLOCK * blockIdx.y);
  for (unsigned ntt_idx = 0; ntt_idx < bound; ntt_idx++, gmem_in.add_col(1), gmem_out.add_col(1)) {
    e2f vals[VALS_PER_THREAD];

#pragma unroll
    for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
      vals[2 * i] = gmem_in.get_at_row(4 * i * VALS_PER_WARP);
      vals[2 * i + 1] = gmem_in.get_at_row((4 * i + 2) * VALS_PER_WARP);
    }

    const unsigned stages_to_skip = MAX_STAGES_THIS_LAUNCH - stages_this_launch;
    unsigned exchg_region_offset = effective_block_idx_x;
    for (unsigned i = 0; i < LOG_VALS_PER_THREAD - 1; i++) {
      if (i >= stages_to_skip) {
#pragma unroll
        for (unsigned j = 0; j < (1u << i); j++) {
          const unsigned exchg_tile_sz = VALS_PER_THREAD >> i;
          const unsigned half_exchg_tile_sz = exchg_tile_sz >> 1;
          const auto twiddle = get_twiddle<true>(exchg_region_offset + j);
#pragma unroll
          for (unsigned k = 0; k < half_exchg_tile_sz; k++)
            exchg_dit(vals[exchg_tile_sz * j + k], vals[exchg_tile_sz * j + k + half_exchg_tile_sz], twiddle);
        }
      }
      exchg_region_offset <<= 1;
    }

    unsigned lane_mask = 16;
    unsigned halfwarp_id = lane_id >> 4;
    for (unsigned s = 0; s < 2; s++) {
      if ((s + LOG_VALS_PER_THREAD - 1) >= stages_to_skip) {
#pragma unroll
        for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
          // TODO: Handle these cooperatively?
          const auto twiddle = get_twiddle<true>(exchg_region_offset + ((2 * i + halfwarp_id) >> (1 - s)));
          exchg_dit(vals[2 * i], vals[2 * i + 1], twiddle);
          shfl_xor_e2f(vals, i, lane_id, lane_mask);
        }
      } else {
#pragma unroll
        for (unsigned i = 0; i < PAIRS_PER_THREAD; i++)
          shfl_xor_e2f(vals, i, lane_id, lane_mask);
      }
      lane_mask >>= 1;
      exchg_region_offset <<= 1;
    }

    __syncwarp(); // maybe unnecessary but can't hurt

    {
      e2f tmp[VALS_PER_THREAD];
      auto pair_addr = smem + 16 * warp_id + VALS_PER_WARP * (lane_id >> 3) + 2 * (threadIdx.x & 7);
      if (ntt_idx > 0) {
#pragma unroll
        for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
          tmp[2 * i] = twiddle_cache[64 * i + lane_id];
          tmp[2 * i + 1] = twiddle_cache[64 * i + lane_id + 32];
        }

        __syncthreads();

#pragma unroll
        for (unsigned i = 0; i < PAIRS_PER_THREAD; i++, pair_addr += 4 * VALS_PER_WARP) {
          uint4 *pair = reinterpret_cast<uint4 *>(pair_addr);
          const uint4 out{vals[2 * i][0].limb, vals[2 * i][1].limb, vals[2 * i + 1][0].limb, vals[2 * i + 1][1].limb};
          *pair = out;
        }
      } else {
#pragma unroll
        for (unsigned i = 0; i < PAIRS_PER_THREAD; i++, pair_addr += 4 * VALS_PER_WARP) {
          uint4 *pair = reinterpret_cast<uint4 *>(pair_addr);
          const uint4 out{vals[2 * i][0].limb, vals[2 * i][1].limb, vals[2 * i + 1][0].limb, vals[2 * i + 1][1].limb};
          *pair = out;
        }
      }

      __syncthreads();

      if (ntt_idx > 0) {
#pragma unroll
        for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
          vals[2 * i] = twiddle_cache[64 * i + lane_id];
          vals[2 * i + 1] = twiddle_cache[64 * i + lane_id + 32];
          twiddle_cache[64 * i + lane_id] = tmp[2 * i];
          twiddle_cache[64 * i + lane_id + 32] = tmp[2 * i + 1];
        }

        __syncwarp();
      } else {
#pragma unroll
        for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
          vals[2 * i] = twiddle_cache[64 * i + lane_id];
          vals[2 * i + 1] = twiddle_cache[64 * i + lane_id + 32];
        }

        __syncwarp();

        load_initial_twiddles_warp<VALS_PER_WARP, LOG_VALS_PER_THREAD, true>(twiddle_cache, lane_id, gmem_offset);
      }
    }

    e2f *twiddles_this_stage = twiddle_cache + VALS_PER_WARP - 2;
    unsigned num_twiddles_this_stage = 1;
    for (unsigned i = 0; i < LOG_VALS_PER_THREAD - 1; i++) {
#pragma unroll
      for (unsigned j = 0; j < (1u << i); j++) {
        const unsigned exchg_tile_sz = VALS_PER_THREAD >> i;
        const unsigned half_exchg_tile_sz = exchg_tile_sz >> 1;
        const auto twiddle = twiddles_this_stage[j];
#pragma unroll
        for (unsigned k = 0; k < half_exchg_tile_sz; k++) {
          exchg_dit(vals[exchg_tile_sz * j + k], vals[exchg_tile_sz * j + k + half_exchg_tile_sz], twiddle);
        }
      }
      num_twiddles_this_stage <<= 1;
      twiddles_this_stage -= num_twiddles_this_stage;
    }

    lane_mask = 16;
    for (unsigned stage = 0, s = 5; stage < 6; stage++, s--) {
#pragma unroll
      for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
        const auto twiddle = twiddles_this_stage[(32 * i + lane_id) >> s];
        exchg_dit(vals[2 * i], vals[2 * i + 1], twiddle);
        if (stage < 5)
          shfl_xor_e2f(vals, i, lane_id, lane_mask);
      }
      lane_mask >>= 1;
      num_twiddles_this_stage <<= 1;
      twiddles_this_stage -= num_twiddles_this_stage;
    }

#pragma unroll
    for (unsigned i = 0; i < VALS_PER_THREAD; i++)
      vals[i] = e2f::mul(vals[i], inv_sizes[log_n]);

    if (evals_are_coset) {
#pragma unroll 1
      for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
        const unsigned mem_idx = gmem_offset + 64 * i + 2 * lane_id;
        const unsigned idx0 = bitrev(mem_idx, log_n);
        const unsigned idx1 = bitrev(mem_idx + 1, log_n);
        vals[2 * i] = lde_scale<true>(vals[2 * i], idx0, 1, 1, log_n);
        vals[2 * i + 1] = lde_scale<true>(vals[2 * i + 1], idx1, 1, 1, log_n);
      }
    }

#pragma unroll
    for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
      // gmem_out.set_at_row(64 * i + 2 * lane_id, vals[2 * i]);
      // gmem_out.set_at_row(64 * i + 2 * lane_id + 1, vals[2 * i + 1]);
      gmem_out.set_two_adjacent(64 * i + 2 * lane_id, vals[2 * i], vals[2 * i + 1]);
    }
  }
}

extern "C" __launch_bounds__(512, 2) __global__
    void main_domain_evals_to_Z_final_9_to_12_stages_block(vectorized_e2_matrix_getter<ld_modifier::cg> gmem_in,
                                                           vectorized_e2_matrix_setter<st_modifier::cg> gmem_out, const unsigned start_stage,
                                                           const unsigned stages_this_launch, const unsigned log_n, const unsigned num_Z_cols,
                                                           const unsigned grid_offset) {
  evals_to_Z_final_stages_block<3, false>(gmem_in, gmem_out, start_stage, stages_this_launch, log_n, num_Z_cols, grid_offset);
}

extern "C" __launch_bounds__(512, 2) __global__
    void coset_evals_to_Z_final_9_to_12_stages_block(vectorized_e2_matrix_getter<ld_modifier::cg> gmem_in,
                                                     vectorized_e2_matrix_setter<st_modifier::cg> gmem_out, const unsigned start_stage,
                                                     const unsigned stages_this_launch, const unsigned log_n, const unsigned num_Z_cols,
                                                     const unsigned grid_offset) {
  evals_to_Z_final_stages_block<3, true>(gmem_in, gmem_out, start_stage, stages_this_launch, log_n, num_Z_cols, grid_offset);
}

// This kernel basically reverses the pattern of the b2n_noninitial_stages_block kernel.
template <unsigned LOG_VALS_PER_THREAD>
DEVICE_FORCEINLINE void evals_to_Z_nonfinal_stages_block(vectorized_e2_matrix_getter<ld_modifier::cg> gmem_in,
                                                         vectorized_e2_matrix_setter<st_modifier::cg> gmem_out, const unsigned start_stage,
                                                         const bool skip_last_stage, const unsigned log_n, const unsigned num_Z_cols,
                                                         const unsigned grid_offset) {
  constexpr unsigned COL_PAIRS_PER_BLOCK = COLS_PER_BLOCK<e2f>::VAL;
  constexpr unsigned VALS_PER_THREAD = 1u << LOG_VALS_PER_THREAD;
  constexpr unsigned PAIRS_PER_THREAD = VALS_PER_THREAD >> 1;
  constexpr unsigned VALS_PER_WARP = 32 * VALS_PER_THREAD;
  constexpr unsigned TILES_PER_WARP = VALS_PER_WARP >> 4;
  constexpr unsigned WARPS_PER_BLOCK = VALS_PER_WARP >> 4;
  constexpr unsigned VALS_PER_BLOCK = VALS_PER_WARP * WARPS_PER_BLOCK;
  constexpr unsigned TILES_PER_BLOCK = VALS_PER_BLOCK >> 4;
  constexpr unsigned EXCHG_REGIONS_PER_BLOCK = TILES_PER_BLOCK >> 1;
  constexpr unsigned MAX_STAGES_THIS_LAUNCH = 2 * (LOG_VALS_PER_THREAD + 5) - 8;

  __shared__ e2f smem[VALS_PER_BLOCK];

  const unsigned effective_block_idx_x = blockIdx.x + grid_offset;
  const unsigned lane_id{threadIdx.x & 31};
  const unsigned warp_id{threadIdx.x >> 5};
  const unsigned log_tile_stride = log_n - start_stage - MAX_STAGES_THIS_LAUNCH;
  const unsigned tile_stride = 1u << log_tile_stride;
  const unsigned log_blocks_per_region = log_tile_stride - 4; // tile size is always 16
  const unsigned block_bfly_region_size = TILES_PER_BLOCK * tile_stride;
  const unsigned block_bfly_region = effective_block_idx_x >> log_blocks_per_region;
  const unsigned block_bfly_region_start = block_bfly_region * block_bfly_region_size;
  const unsigned block_start_in_bfly_region = 16 * (effective_block_idx_x & ((1u << log_blocks_per_region) - 1));
  // annoyingly scrambled, but should be coalesced overall
  const unsigned gmem_in_thread_offset = tile_stride * warp_id + tile_stride * WARPS_PER_BLOCK * (lane_id >> 4) + 2 * (lane_id & 7) + ((lane_id >> 3) & 1);
  const unsigned gmem_in_offset = block_bfly_region_start + block_start_in_bfly_region + gmem_in_thread_offset;
  gmem_in.add_row(gmem_in_offset);
  gmem_in.add_col(COL_PAIRS_PER_BLOCK * blockIdx.y);
  gmem_out.add_row(block_bfly_region_start + block_start_in_bfly_region);
  gmem_out.add_col(COL_PAIRS_PER_BLOCK * blockIdx.y);

  auto twiddle_cache = smem + VALS_PER_WARP * warp_id;

  const unsigned bound = std::min(COL_PAIRS_PER_BLOCK, num_Z_cols - COL_PAIRS_PER_BLOCK * blockIdx.y);
  for (unsigned ntt_idx = 0; ntt_idx < bound; ntt_idx++, gmem_in.add_col(1), gmem_out.add_col(1)) {
    e2f vals[VALS_PER_THREAD];

#pragma unroll
    for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
      vals[2 * i] = gmem_in.get_at_row(4 * i * tile_stride * WARPS_PER_BLOCK);
      vals[2 * i + 1] = gmem_in.get_at_row((4 * i + 2) * tile_stride * WARPS_PER_BLOCK);
    }

    unsigned block_exchg_region_offset = block_bfly_region;
    for (unsigned i = 0; i < LOG_VALS_PER_THREAD - 1; i++) {
#pragma unroll
      for (unsigned j = 0; j < (1u << i); j++) {
        const unsigned exchg_tile_sz = VALS_PER_THREAD >> i;
        const unsigned half_exchg_tile_sz = exchg_tile_sz >> 1;
        const auto twiddle = get_twiddle<true>(block_exchg_region_offset + j);
#pragma unroll
        for (unsigned k = 0; k < half_exchg_tile_sz; k++)
          exchg_dit(vals[exchg_tile_sz * j + k], vals[exchg_tile_sz * j + k + half_exchg_tile_sz], twiddle);
      }
      block_exchg_region_offset <<= 1;
    }

    unsigned lane_mask = 16;
    unsigned halfwarp_id = lane_id >> 4;
    for (unsigned s = 0; s < 2; s++) {
#pragma unroll
      for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
        // TODO: Handle these cooperatively?
        const auto twiddle = get_twiddle<true>(block_exchg_region_offset + ((2 * i + halfwarp_id) >> (1 - s)));
        exchg_dit(vals[2 * i], vals[2 * i + 1], twiddle);
        shfl_xor_e2f(vals, i, lane_id, lane_mask);
      }
      lane_mask >>= 1;
      block_exchg_region_offset <<= 1;
    }

    __syncwarp(); // maybe unnecessary but can't hurt

    // there are at most 31 per-warp twiddles, so we only need 1 temporary per thread to stash them
    e2f tmp;
    if (ntt_idx > 0) {
      tmp = twiddle_cache[lane_id];
      __syncthreads();
    }

    auto smem_pair_addr = smem + 16 * warp_id + VALS_PER_WARP * (lane_id >> 3) + 2 * (threadIdx.x & 7);
#pragma unroll
    for (unsigned i = 0; i < PAIRS_PER_THREAD; i++, smem_pair_addr += 4 * VALS_PER_WARP) {
      uint4 *pair = reinterpret_cast<uint4 *>(smem_pair_addr);
      const uint4 out{vals[2 * i][0].limb, vals[2 * i][1].limb, vals[2 * i + 1][0].limb, vals[2 * i + 1][1].limb};
      *pair = out;
    }

    __syncthreads();

    // annoyingly scrambled but should be bank-conflict-free
    const unsigned smem_thread_offset = 16 * (lane_id >> 4) + 2 * (lane_id & 7) + ((lane_id >> 3) & 1);
#pragma unroll
    for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
      vals[2 * i] = twiddle_cache[64 * i + smem_thread_offset];
      vals[2 * i + 1] = twiddle_cache[64 * i + smem_thread_offset + 32];
    }

    __syncwarp();

    if (ntt_idx > 0) {
      twiddle_cache[lane_id] = tmp;
      __syncwarp();
    } else {
      load_noninitial_twiddles_warp<LOG_VALS_PER_THREAD, true>(twiddle_cache, lane_id, warp_id, block_bfly_region * EXCHG_REGIONS_PER_BLOCK);
    }

    e2f *twiddles_this_stage = twiddle_cache + 2 * VALS_PER_THREAD - 2;
    unsigned num_twiddles_this_stage = 1;
    for (unsigned i = 0; i < LOG_VALS_PER_THREAD - 1; i++) {
#pragma unroll
      for (unsigned j = 0; j < (1u << i); j++) {
        const unsigned exchg_tile_sz = VALS_PER_THREAD >> i;
        const unsigned half_exchg_tile_sz = exchg_tile_sz >> 1;
        const auto twiddle = twiddles_this_stage[j];
#pragma unroll
        for (unsigned k = 0; k < half_exchg_tile_sz; k++) {
          exchg_dit(vals[exchg_tile_sz * j + k], vals[exchg_tile_sz * j + k + half_exchg_tile_sz], twiddle);
        }
      }
      num_twiddles_this_stage <<= 1;
      twiddles_this_stage -= num_twiddles_this_stage;
    }

    lane_mask = 16;
    for (unsigned s = 0; s < 2; s++) {
      if (!skip_last_stage || s < 1) {
#pragma unroll
        for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
          // TODO: Handle these cooperatively?
          const auto twiddle = twiddles_this_stage[(2 * i + halfwarp_id) >> (1 - s)];
          exchg_dit(vals[2 * i], vals[2 * i + 1], twiddle);
          shfl_xor_e2f(vals, i, lane_id, lane_mask);
        }
        lane_mask >>= 1;
        num_twiddles_this_stage <<= 1;
        twiddles_this_stage -= num_twiddles_this_stage;
      }
    }

    if (skip_last_stage) {
      auto val0_offset = TILES_PER_WARP * tile_stride * warp_id + 2 * tile_stride * (lane_id >> 4) + 2 * (threadIdx.x & 7) + (lane_id >> 3 & 1);
#pragma unroll
      for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
        gmem_out.set_at_row(val0_offset, vals[2 * i]);
        gmem_out.set_at_row(val0_offset + tile_stride, vals[2 * i + 1]);
        val0_offset += 4 * tile_stride;
      }
    } else {
      auto pair_offset = TILES_PER_WARP * tile_stride * warp_id + tile_stride * (lane_id >> 3) + 2 * (threadIdx.x & 7);
#pragma unroll
      for (unsigned i = 0; i < PAIRS_PER_THREAD; i++) {
        // gmem_out.set_at_row(pair_offset, vals[2 * i]);
        // gmem_out.set_at_row(pair_offset + 1, vals[2 * i + 1]);
        gmem_out.set_two_adjacent(pair_offset, vals[2 * i], vals[2 * i + 1]);
        pair_offset += 4 * tile_stride;
      }
    }
  }
}

extern "C" __launch_bounds__(512, 2) __global__
    void evals_to_Z_nonfinal_7_or_8_stages_block(vectorized_e2_matrix_getter<ld_modifier::cg> gmem_in, vectorized_e2_matrix_setter<st_modifier::cg> gmem_out,
                                                 const unsigned start_stage, const unsigned stages_this_launch, const unsigned log_n, const unsigned num_Z_cols,
                                                 const unsigned grid_offset) {
  evals_to_Z_nonfinal_stages_block<3>(gmem_in, gmem_out, start_stage, stages_this_launch == 7, log_n, num_Z_cols, grid_offset);
}

// Simple, non-optimized kernel used for log_n < 16, to unblock debugging small proofs.
extern "C" __launch_bounds__(512, 2) __global__
    void evals_to_Z_one_stage(vectorized_e2_matrix_getter<ld_modifier::cg> gmem_in, vectorized_e2_matrix_setter<st_modifier::cg> gmem_out,
                              const unsigned start_stage, const unsigned log_n, const unsigned blocks_per_ntt, const bool evals_are_coset) {
  const unsigned col_pair = blockIdx.x / blocks_per_ntt;
  const unsigned bid_in_ntt = blockIdx.x % blocks_per_ntt;
  const unsigned tid_in_ntt = threadIdx.x + bid_in_ntt * blockDim.x;
  if (tid_in_ntt >= (1u << (log_n - 1)))
    return;
  const unsigned log_exchg_region_sz = log_n - start_stage;
  const unsigned exchg_region = tid_in_ntt >> (log_exchg_region_sz - 1);
  const unsigned tid_in_exchg_region = tid_in_ntt - (exchg_region << (log_exchg_region_sz - 1));
  const unsigned exchg_stride = 1 << (log_exchg_region_sz - 1);
  const unsigned a_idx = tid_in_exchg_region + exchg_region * (1u << log_exchg_region_sz);
  const unsigned b_idx = a_idx + exchg_stride;
  gmem_in.add_col(col_pair);
  gmem_out.add_col(col_pair);

  const auto twiddle = get_twiddle<true>(exchg_region);

  auto a = gmem_in.get_at_row(a_idx);
  auto b = gmem_in.get_at_row(b_idx);

  exchg_dit(a, b, twiddle);

  if (start_stage + 1 == log_n) {
    a = e2f::mul(a, inv_sizes[log_n]);
    b = e2f::mul(b, inv_sizes[log_n]);
    if (evals_are_coset) {
      a = lde_scale<true>(a, bitrev(a_idx, log_n), 1, 1, log_n);
      b = lde_scale<true>(b, bitrev(b_idx, log_n), 1, 1, log_n);
    }
  }

  gmem_out.set_at_row(a_idx, a);
  gmem_out.set_at_row(b_idx, b);
}

} // namespace ntt
