#pragma once
#include "../support/eq_inline.cuh"
#include "../support/kernel_helpers.cuh"

namespace airbender::gkr {
// The single-column row stride must preserve the low and middle
// coordinates, so their factors can be applied after the thread's row sum.
DEVICE_FORCEINLINE void gkr_trace_holder_deferred_eq(const bf *raw_values, const e4 *eq_low, const gkr_eq_sizes sizes, e4 *block_partials,
                                                     const unsigned trace_len, const unsigned blocks_count) {
  const unsigned tid = threadIdx.x;
  const unsigned packed_gid = blockIdx.x * blockDim.x + tid;
  const unsigned packed_stride = gridDim.x * blockDim.x;
  const unsigned shift0 = sizes.low + sizes.high[1];
  const unsigned lo_mask = (1u << sizes.low) - 1u;
  const unsigned hi1_mask = (1u << sizes.high[1]) - 1u;
  const unsigned hi0_mask = (1u << sizes.high[0]) - 1u;
  // Launch contract is checked by the caller; all branches here are uniform.
  if (blockDim.x != GKR_TRACE_HOLDER_PARTIALS_THREADS_PER_BLOCK || gridDim.x != blocks_count || sizes.low < 2 ||
      ((packed_stride << 2) & ((1u << shift0) - 1u)) != 0)
    return;
  e4 acc[4] = {e4::ZERO(), e4::ZERO(), e4::ZERO(), e4::ZERO()};
  for (unsigned packed_row = packed_gid; packed_row < (trace_len >> 2); packed_row += packed_stride) {
    const unsigned row = packed_row << 2;
    const auto high = load<e4, ld_modifier::ca>(&ab_gkr_eq_high[0][0], (row >> shift0) & hi0_mask);
    const auto values = load<gkr_trace_holder_bf4, ld_modifier::cs>(reinterpret_cast<const gkr_trace_holder_bf4 *>(raw_values), packed_row);
#pragma unroll
    for (unsigned i = 0; i < 4; ++i)
      acc[i] = e4::fma(high, values.values[i], acc[i]);
  }
  const unsigned first_row = packed_gid << 2;
  const unsigned lo = first_row & lo_mask;
  e4 sum = e4::ZERO();
#pragma unroll
  for (unsigned i = 0; i < 4; ++i)
    sum = e4::add(sum, e4::mul(acc[i], load<e4, ld_modifier::cs>(eq_low, lo + i)));
  sum = e4::mul(sum, load<e4, ld_modifier::ca>(&ab_gkr_eq_high[1][0], (first_row >> sizes.low) & hi1_mask));
  sum = gkr_trace_holder_partials_warp_reduce_sum(sum);
  __shared__ e4 warp_partials[GKR_TRACE_HOLDER_PARTIALS_WARPS_PER_BLOCK];
  const unsigned lane = tid & 31;
  const unsigned warp = tid >> 5;
  if (lane == 0)
    warp_partials[warp] = sum;
  __syncthreads();
  if (warp == 0) {
    sum = lane < GKR_TRACE_HOLDER_PARTIALS_WARPS_PER_BLOCK ? warp_partials[lane] : e4::ZERO();
    sum = gkr_trace_holder_partials_warp_reduce_sum(sum);
    if (lane == 0)
      store<e4, st_modifier::cs>(block_partials, sum, blockIdx.x);
  }
}
} // namespace airbender::gkr
