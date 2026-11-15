#pragma once

#include "gkr/baby_bear/support/descriptors.cuh"
#include "gkr/support/kernel_helpers.cuh"

namespace airbender::gkr {

DEVICE_FORCEINLINE bf gkr_virtual_base_value(const gkr_base_source_kind kind, const unsigned row) {
  switch (kind) {
  case GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_16_BITS:
    return row < (1u << 16) ? bf::from_u32_unchecked(row) : bf::ZERO();
  case GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_TIMESTAMP:
    return row < (1u << GKR_TIMESTAMP_COLUMNS_NUM_BITS) ? bf::from_u32_unchecked(row) : bf::ZERO();
  case GKR_BASE_SOURCE_VIRTUAL_INITS_AND_TEARDOWNS_LOW:
    return bf::from_u32_unchecked((row << 2) & 0xffffu);
  case GKR_BASE_SOURCE_VIRTUAL_INITS_AND_TEARDOWNS_HIGH:
    return bf::from_u32_unchecked(row >> 14);
  case GKR_BASE_SOURCE_EMPTY:
  case GKR_BASE_SOURCE_REAL:
  default:
    return bf::ZERO();
  }
}

template <unsigned PACK_LOG2> struct alignas(sizeof(bf) << PACK_LOG2) gkr_trace_holder_bf_pack {
  bf values[1u << PACK_LOG2];
};
using gkr_trace_holder_bf4 = gkr_trace_holder_bf_pack<2>;

template <unsigned PACK_LOG2 = 2, typename E, typename EqFn>
DEVICE_FORCEINLINE void gkr_trace_holder_block_partials(const bf *raw_values, const EqFn eq_fn, E *block_partials, const unsigned trace_len,
                                                        const unsigned column_start, const unsigned chunk_cols, const unsigned blocks_count) {
  static_assert(GKR_TRACE_HOLDER_PARTIALS_THREADS_PER_BLOCK % GKR_TRACE_HOLDER_PARTIALS_WARP_SIZE == 0);
  static_assert(PACK_LOG2 == 2 || PACK_LOG2 == 3);
  using TracePack = gkr_trace_holder_bf_pack<PACK_LOG2>;
  static_assert(sizeof(TracePack) == (sizeof(bf) << PACK_LOG2));
  static_assert(alignof(TracePack) == (sizeof(bf) << PACK_LOG2));

  const unsigned tid = threadIdx.x;
  const unsigned lane_id = tid & (GKR_TRACE_HOLDER_PARTIALS_WARP_SIZE - 1);
  const unsigned warp_id = tid / GKR_TRACE_HOLDER_PARTIALS_WARP_SIZE;
  const unsigned packed_trace_len = trace_len >> PACK_LOG2;
  const unsigned packed_gid = blockIdx.x * blockDim.x + tid;
  const unsigned packed_stride = gridDim.x * blockDim.x;
  E accumulators[GKR_TRACE_HOLDER_PARTIALS_COLUMNS_PER_CHUNK] = {
      E::ZERO(),
      E::ZERO(),
      E::ZERO(),
      E::ZERO(),
  };

  for (unsigned packed_row = packed_gid; packed_row < packed_trace_len; packed_row += packed_stride) {
    const unsigned row = packed_row << PACK_LOG2;
    E eq[1u << PACK_LOG2];
    eq_fn.template load_pack<PACK_LOG2>(row, eq);
#pragma unroll
    for (unsigned local_col = 0; local_col < GKR_TRACE_HOLDER_PARTIALS_COLUMNS_PER_CHUNK; ++local_col) {
      if (local_col >= chunk_cols)
        break;
      const unsigned column = column_start + local_col;
      const size_t row_offset = static_cast<size_t>(column) * trace_len + row;
      const auto values = load<TracePack, ld_modifier::cs>(reinterpret_cast<const TracePack *>(raw_values), row_offset >> PACK_LOG2);
      E partial = E::mul(values.values[0], eq[0]);
      partial = E::fma(eq[1], values.values[1], partial);
      partial = E::fma(eq[2], values.values[2], partial);
      partial = E::fma(eq[3], values.values[3], partial);
      if constexpr (PACK_LOG2 == 3) {
        partial = E::fma(eq[4], values.values[4], partial);
        partial = E::fma(eq[5], values.values[5], partial);
        partial = E::fma(eq[6], values.values[6], partial);
        partial = E::fma(eq[7], values.values[7], partial);
      }
      accumulators[local_col] = E::add(accumulators[local_col], partial);
    }
  }

  __shared__ E warp_partials[GKR_TRACE_HOLDER_PARTIALS_COLUMNS_PER_CHUNK][GKR_TRACE_HOLDER_PARTIALS_WARPS_PER_BLOCK];
#pragma unroll
  for (unsigned local_col = 0; local_col < GKR_TRACE_HOLDER_PARTIALS_COLUMNS_PER_CHUNK; ++local_col) {
    if (local_col >= chunk_cols)
      break;
    const E warp_sum = gkr_trace_holder_partials_warp_reduce_sum(accumulators[local_col]);
    if (lane_id == 0)
      warp_partials[local_col][warp_id] = warp_sum;
  }
  __syncthreads();

  if (warp_id != 0)
    return;

#pragma unroll
  for (unsigned local_col = 0; local_col < GKR_TRACE_HOLDER_PARTIALS_COLUMNS_PER_CHUNK; ++local_col) {
    if (local_col >= chunk_cols)
      break;
    E block_sum = lane_id < GKR_TRACE_HOLDER_PARTIALS_WARPS_PER_BLOCK ? warp_partials[local_col][lane_id] : E::ZERO();
    block_sum = gkr_trace_holder_partials_warp_reduce_sum(block_sum);
    if (lane_id == 0) {
      const size_t partial_offset = static_cast<size_t>(column_start + local_col) * blocks_count + blockIdx.x;
      store<E, st_modifier::cs>(block_partials, block_sum, partial_offset);
    }
  }
}

} // namespace airbender::gkr
