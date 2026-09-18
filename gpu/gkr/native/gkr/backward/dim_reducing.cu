#include "../support/eq_inline.cuh"
#include "../support/lookup_helpers.cuh"

__device__ __constant__ e4 ab_gkr_dim_reducing_batch_challenge_table[airbender::gkr::GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN];
__device__ __constant__ e4 ab_gkr_dim_reducing_layer_claim_point[airbender::gkr::GKR_DIM_REDUCING_LAYER_CLAIM_POINT_LEN];

namespace airbender::gkr::backward {

EXTERN __global__ void ab_gkr_dim_reducing_build_eq_group_tables_from_point_e4_kernel(const e4 *claim_point, const unsigned challenge_offset,
                                                                                      const unsigned challenge_count, e4 *eq_group_tables) {
  gkr_build_eq_group_tables_from_point(claim_point, challenge_offset, challenge_count, eq_group_tables);
}

template <typename E> struct gkr_independent_eq_group_writer {
  E *destination;
  unsigned source_offset;

  DEVICE_FORCEINLINE void operator()(const unsigned index, const E &value) const { store<E, st_modifier::cs>(destination, value, index - source_offset); }
};

// Builds the factored eq representation directly from a claim point into the
// strict 3-slot layout. Each slot has an independent owner so DR continuation
// layers can retain only their exact maximum table size; the R0 caller still
// passes its two contiguous `__constant__` high slots.
//
// To support the strict 3-slot read in `gkr_compute_eq_inline` for small
// `challenge_count` (where some high slabs are not active), thread 0 of
// every block writes `e4::ONE()` to its slot's [0] entry before the group
// build runs. Active slots overwrite the sentinel with real data; unused
// slots retain the identity so the inline-eq read returns 1. Launch must
// be sized `max(groups_count, GKR_EQ_HIGH_SLOTS)` blocks for this to
// initialize every high slab.
EXTERN __global__ void ab_gkr_dim_reducing_build_eq_high_low_from_point_e4_kernel(const e4 *claim_point, const unsigned challenge_offset,
                                                                                  const unsigned challenge_count, e4 *high_0, e4 *high_1, e4 *low_buffer) {
  if (threadIdx.x == 0) {
    if (blockIdx.x == 0)
      high_0[0] = e4::ONE();
    else if (blockIdx.x == 1)
      high_1[0] = e4::ONE();
  }
  const unsigned groups_count = gkr_eq_group_count(challenge_count);
  if (blockIdx.x >= groups_count)
    return;
  e4 *destination = low_buffer;
  if (blockIdx.x + 1u != groups_count)
    destination = blockIdx.x == 0 ? high_0 : high_1;
  const gkr_independent_eq_group_writer<e4> write_destination{destination, blockIdx.x * GKR_EQ_GROUP_TABLE_LEN};
  gkr_build_eq_group_table_from_point<e4>(claim_point, challenge_offset, challenge_count, blockIdx.x, write_destination);
}

EXTERN __global__ void ab_gkr_dim_reducing_build_eq_values_from_group_tables_e4_kernel(const e4 *eq_group_tables, const unsigned challenge_count, e4 *eq_values,
                                                                                       const unsigned acc_size) {
  gkr_build_eq_values_from_group_tables(eq_group_tables, challenge_count, eq_values, acc_size);
}

EXTERN __global__ void ab_gkr_dim_reducing_trace_holder_block_partials_e4_kernel(const bf *raw_values, const e4 *eq_values, e4 *block_partials,
                                                                                 const unsigned trace_len, const unsigned column_start,
                                                                                 const unsigned chunk_cols, const unsigned blocks_count) {
  gkr_trace_holder_block_partials(raw_values, gkr_trace_holder_eq_dense<e4>{eq_values}, block_partials, trace_len, column_start, chunk_cols, blocks_count);
}

EXTERN __global__ void ab_gkr_dim_reducing_trace_holder_block_partials_eq_inline_e4_kernel(const bf *raw_values, const e4 *eq_low, const gkr_eq_sizes sizes,
                                                                                           e4 *block_partials, const unsigned trace_len,
                                                                                           const unsigned column_start, const unsigned chunk_cols,
                                                                                           const unsigned blocks_count) {
  gkr_trace_holder_block_partials(raw_values, gkr_eq_inline_reader<e4>{eq_low, sizes}, block_partials, trace_len, column_start, chunk_cols, blocks_count);
}

// Each thread accumulates four rows with fixed low/middle Eq coordinates.
static constexpr unsigned GKR_EXTRAS_DEFERRED_THREADS_PER_BLOCK = 128;
static constexpr unsigned GKR_EXTRAS_DEFERRED_WARPS_PER_BLOCK = GKR_EXTRAS_DEFERRED_THREADS_PER_BLOCK / 32;
EXTERN __global__ __launch_bounds__(GKR_EXTRAS_DEFERRED_THREADS_PER_BLOCK) void ab_gkr_extras_deferred_eq_kernel(const bf *raw_values, const e4 *eq_low,
                                                                                                                 const gkr_eq_sizes sizes, e4 *block_partials,
                                                                                                                 const unsigned trace_len) {
  const unsigned tid = threadIdx.x;
  const unsigned packed_gid = blockIdx.x * blockDim.x + tid;
  const unsigned packed_stride = gridDim.x * blockDim.x;
  const unsigned shift0 = sizes.low + sizes.high[1];
  const unsigned lo_mask = (1u << sizes.low) - 1u;
  const unsigned hi1_mask = (1u << sizes.high[1]) - 1u;
  const unsigned hi0_mask = (1u << sizes.high[0]) - 1u;
  // Launch contract is checked by the caller; all branches here are uniform.
  if (blockDim.x != GKR_EXTRAS_DEFERRED_THREADS_PER_BLOCK || sizes.low < 2 || ((packed_stride << 2) & ((1u << shift0) - 1u)) != 0)
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
  __shared__ e4 warp_partials[GKR_EXTRAS_DEFERRED_WARPS_PER_BLOCK];
  const unsigned lane = tid & 31;
  const unsigned warp = tid >> 5;
  if (lane == 0)
    warp_partials[warp] = sum;
  __syncthreads();
  if (warp == 0) {
    sum = lane < GKR_EXTRAS_DEFERRED_WARPS_PER_BLOCK ? warp_partials[lane] : e4::ZERO();
    sum = gkr_trace_holder_partials_warp_reduce_sum(sum);
    if (lane == 0)
      store<e4, st_modifier::cs>(block_partials, sum, blockIdx.x);
  }
}

EXTERN __global__ void ab_gkr_dim_reducing_trace_holder_column_sums_e4_kernel(const e4 *block_partials, e4 *column_sums, const unsigned blocks_count) {
  gkr_trace_holder_column_sums(block_partials, column_sums, blocks_count);
}

} // namespace airbender::gkr::backward
