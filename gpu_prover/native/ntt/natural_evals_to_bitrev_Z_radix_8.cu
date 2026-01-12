#include "radix_8_utils.cuh"

namespace airbender::ntt {

EXTERN __launch_bounds__(256, 3) __global__
    void ab_radix_8_main_domain_evals_to_Z_nonfinal_6_stages_warp(vectorized_e2_matrix_getter<ld_modifier::cg> gmem_in,
                                                                  vectorized_e2_matrix_setter<st_modifier::cg> gmem_out, const unsigned start_stage,
                                                                  unsigned exchg_region_bit_chunks, const unsigned log_exchg_region_size,
                                                                  const unsigned tile_gmem_stride, const unsigned log_n, const unsigned grid_offset) {
  constexpr unsigned WARP_SIZE = 32u;
  constexpr unsigned LOG_RADIX = 3u;
  constexpr unsigned RADIX = 1 << LOG_RADIX;
  constexpr unsigned LOG_WARPS_PER_BLOCK = 3;
  constexpr unsigned LOG_VALS_PER_THREAD = 4;
  constexpr unsigned VALS_PER_BLOCK = WARP_SIZE << (LOG_WARPS_PER_BLOCK + LOG_VALS_PER_THREAD);
  constexpr unsigned LOG_TILE_SIZE = 3;
  constexpr unsigned TILES_PER_WARP = 32 >> LOG_TILE_SIZE;
  constexpr unsigned TILE_SIZE = 1 << LOG_TILE_SIZE;
  constexpr unsigned TILE_MASK = TILE_SIZE - 1;

  __shared__ e2 static_smem[VALS_PER_BLOCK];

  const unsigned effective_block_idx_x = blockIdx.x + grid_offset;
  const unsigned warp_id = threadIdx.x >> 5;
  e2 *smem = static_smem + warp_id * (WARP_SIZE << LOG_VALS_PER_THREAD);
  const unsigned lane_id = threadIdx.x & 31;
  const unsigned tile_id = lane_id >> LOG_TILE_SIZE;
  const unsigned lane_in_tile = lane_id & TILE_MASK;
  const unsigned block_exchg_region = blockIdx.x;    // effective_block_idx_x >> log_blocks_per_exchg_region;
  const unsigned block_in_exchg_region = blockIdx.y; // effective_block_idx_x & ((1 << log_blocks_per_exchg_region) - 1);
  const unsigned gmem_block_offset = block_exchg_region << log_exchg_region_size;
  const unsigned gmem_warp_offset = ((block_in_exchg_region << LOG_WARPS_PER_BLOCK) + warp_id) << LOG_TILE_SIZE;
  gmem_in.add_row(gmem_block_offset + gmem_warp_offset);
  gmem_out.add_row(gmem_block_offset + gmem_warp_offset);

  e2 vals0[RADIX];
  e2 vals1[RADIX];

  unsigned twiddle_stride = 1 << (OMEGA_LOG_ORDER - LOG_RADIX * (start_stage + 1));

  const auto twiddle = get_twiddle_with_direct_index<true>(log_n);

  // First three stages
  {
    const unsigned thread_offset = lane_in_tile + tile_id * tile_gmem_stride;
#pragma unroll
    for (unsigned i{0}, addr{thread_offset}; i < RADIX; i++, addr += RADIX * tile_gmem_stride) {
      vals0[i] = gmem_in.get_at_row(addr);
      vals1[i] = gmem_in.get_at_row(addr + TILES_PER_WARP * tile_gmem_stride);
    }

    if (start_stage > 0)
      apply_twiddles_same_region<LOG_RADIX>(vals0, vals1, block_exchg_region, twiddle_stride, exchg_region_bit_chunks, twiddle);

    size_8_inv_dit(vals0);
    size_8_inv_dit(vals1);

#pragma unroll
    for (unsigned i{0}, addr{lane_id}; i < RADIX; i++, addr += 2 * WARP_SIZE) {
      smem[addr] = vals0[i];
      smem[addr + WARP_SIZE] = vals1[i];
    }
    // #pragma unroll
    //     for (unsigned i{0}, addr{thread_offset}; i < RADIX; i++, addr += RADIX * tile_gmem_stride) {
    //       gmem_out.set_at_row(addr, vals0[i]);
    //       gmem_out.set_at_row(addr + TILES_PER_WARP * tile_gmem_stride, vals1[i]);
    //     }

    __syncwarp();
  }

  // Second three stages
  {
    const unsigned thread_offset = lane_in_tile + tile_id * 2 * RADIX * TILE_SIZE;
#pragma unroll
    for (unsigned i{0}, addr{thread_offset}; i < RADIX; i++, addr += RADIX) {
      vals0[i] = smem[addr];
      vals1[i] = smem[addr + 64];
    }

    const unsigned exchg_region_0 = block_exchg_region * RADIX + 2 * tile_id;
    const unsigned exchg_region_1 = exchg_region_0 + 1;
    twiddle_stride >>= LOG_RADIX;
    apply_twiddles_distinct_regions<LOG_RADIX>(vals0, vals1, exchg_region_0, exchg_region_1, twiddle_stride, ++exchg_region_bit_chunks,
                                               twiddle);

    size_8_inv_dit(vals0);
    size_8_inv_dit(vals1);

    const unsigned gmem_write_offset = lane_in_tile + tile_id * 2 * RADIX * tile_gmem_stride;
#pragma unroll
    for (unsigned i{0}, addr{gmem_write_offset}; i < RADIX; i++, addr += tile_gmem_stride) {
      gmem_out.set_at_row(addr, vals0[i]);
      gmem_out.set_at_row(addr + RADIX * tile_gmem_stride, vals1[i]);
    }
  }
}

EXTERN __launch_bounds__(256, 3) __global__
    void ab_radix_8_main_domain_evals_to_Z_final_12_stages_block(vectorized_e2_matrix_getter<ld_modifier::cg> gmem_in,
                                                                 vectorized_e2_matrix_setter<st_modifier::cg> gmem_out, const unsigned start_stage,
                                                                 unsigned exchg_region_bit_chunks, const unsigned log_n, const unsigned grid_offset) {
  constexpr unsigned WARP_SIZE = 32u;
  constexpr unsigned LOG_RADIX = 3u;
  constexpr unsigned RADIX = 1 << LOG_RADIX;
  constexpr unsigned VALS_PER_BLOCK = 4096;

  __shared__ e2 static_smem[VALS_PER_BLOCK];
  e2 *smem = static_smem;

  const unsigned effective_block_idx_x = blockIdx.x + grid_offset;
  const unsigned warp_id{threadIdx.x >> 5};
  const unsigned lane_id{threadIdx.x & 31};
  const unsigned gmem_block_offset = VALS_PER_BLOCK * effective_block_idx_x;
  gmem_in.add_row(gmem_block_offset);
  gmem_out.add_row(gmem_block_offset);

  e2 vals0[RADIX];
  e2 vals1[RADIX];

  unsigned twiddle_stride = 1 << (OMEGA_LOG_ORDER - LOG_RADIX * (start_stage + 1));

  const auto twiddle = get_twiddle_with_direct_index<true>(log_n);

  // First three stages
  {
#pragma unroll
    for (unsigned i{0}, addr{threadIdx.x}; i < RADIX; i++, addr += 2 * blockDim.x) {
      vals0[i] = gmem_in.get_at_row(addr);
      vals1[i] = gmem_in.get_at_row(addr + blockDim.x);
    }

    if (start_stage > 0)
      apply_twiddles_same_region<LOG_RADIX>(vals0, vals1, effective_block_idx_x, twiddle_stride, exchg_region_bit_chunks, twiddle);

    size_8_inv_dit(vals0);
    size_8_inv_dit(vals1);

#pragma unroll
    for (unsigned i{0}, addr{threadIdx.x}; i < RADIX; i++, addr += 2 * blockDim.x) {
      smem[addr] = vals0[i];
      smem[addr + blockDim.x] = vals1[i];
      // gmem_out.set_at_row(addr, vals0[i]);
      // gmem_out.set_at_row(addr + blockDim.x, vals1[i]);
    }

    __syncthreads();
  }

  // The remaining stages will be processed within each warp.
  const unsigned warp_offset = warp_id * 512;
  smem += warp_offset;
  gmem_out.add_row(warp_offset);
  unsigned warp_exchg_region_offset = effective_block_idx_x * RADIX + warp_id;

  // Second three stages
  {
#pragma unroll
    for (unsigned i{0}, addr{lane_id}; i < RADIX; i++, addr += 2 * WARP_SIZE) {
      vals0[i] = smem[addr];
      vals1[i] = smem[addr + WARP_SIZE];
    }

    twiddle_stride >>= LOG_RADIX;
    apply_twiddles_same_region<LOG_RADIX>(vals0, vals1, warp_exchg_region_offset, twiddle_stride, ++exchg_region_bit_chunks, twiddle);

    size_8_inv_dit(vals0);
    size_8_inv_dit(vals1);

#pragma unroll
    for (unsigned i{0}, addr{lane_id}; i < RADIX; i++, addr += 2 * WARP_SIZE) {
      smem[addr] = vals0[i];
      smem[addr + WARP_SIZE] = vals1[i];
      // gmem_out.set_at_row(addr, vals0[i]);
      // gmem_out.set_at_row(addr + WARP_SIZE, vals1[i]);
    }

    __syncwarp();
  }

  // Third three stages
  {
    const unsigned tile_id{lane_id >> 3};
    const unsigned thread_offset = (lane_id & 7) + tile_id * 128;
    // I could swizzle access order across tiles to avoid bank conflicts, but swizzling logic
    // would probably add more instructions than the bank conflict replays. Seems marginal.
#pragma unroll
    for (unsigned i{0}, addr{thread_offset}; i < RADIX; i++, addr += RADIX) {
      vals0[i] = smem[addr];
      vals1[i] = smem[addr + 64];
    }

    warp_exchg_region_offset *= RADIX;
    const unsigned exchg_region_0 = warp_exchg_region_offset + tile_id * 2;
    const unsigned exchg_region_1 = exchg_region_0 + 1;
    twiddle_stride >>= LOG_RADIX;
    apply_twiddles_distinct_regions<LOG_RADIX>(vals0, vals1, exchg_region_0, exchg_region_1, twiddle_stride, ++exchg_region_bit_chunks,
                                               twiddle);

    size_8_inv_dit(vals0);
    size_8_inv_dit(vals1);

#pragma unroll
    for (unsigned i{0}, addr{thread_offset}; i < RADIX; i++, addr += RADIX) {
      smem[addr] = vals0[i];
      smem[addr + 64] = vals1[i];
      // gmem_out.set_at_row(addr, vals0[i]);
      // gmem_out.set_at_row(addr + 64, vals1[i]);
    }

    __syncwarp();
  }

  // Fourth three stages
  {
    const unsigned thread_offset = lane_id * 8;
#pragma unroll
    for (unsigned i{0}; i < RADIX; i++) {
      vals0[i] = smem[i + thread_offset];
      vals1[i] = smem[i + thread_offset + 256];
    }

    warp_exchg_region_offset *= RADIX;
    const unsigned exchg_region_0 = warp_exchg_region_offset + lane_id;
    const unsigned exchg_region_1 = exchg_region_0 + 32;
    twiddle_stride >>= LOG_RADIX;
    apply_twiddles_distinct_regions<LOG_RADIX>(vals0, vals1, exchg_region_0, exchg_region_1, twiddle_stride, ++exchg_region_bit_chunks,
                                               twiddle);

    size_8_inv_dit(vals0);
    size_8_inv_dit(vals1);

#pragma unroll
    for (unsigned i{0}; i < RADIX; i++) {
      vals0[i] = e2::mul(vals0[i], ab_inv_sizes[log_n]);
      vals1[i] = e2::mul(vals1[i], ab_inv_sizes[log_n]);
    }

    gmem_out.set_four_adjacent(thread_offset, vals0[0], vals0[1], vals0[2], vals0[3]);
    gmem_out.set_four_adjacent(thread_offset + 4, vals0[4], vals0[5], vals0[6], vals0[7]);
    gmem_out.set_four_adjacent(thread_offset + 256, vals1[0], vals1[1], vals1[2], vals1[3]);
    gmem_out.set_four_adjacent(thread_offset + 260, vals1[4], vals1[5], vals1[6], vals1[7]);
  }
}

} // namespace airbender::ntt
