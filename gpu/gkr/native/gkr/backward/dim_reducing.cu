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

EXTERN __global__ void ab_gkr_dim_reducing_trace_holder_column_sums_e4_kernel(const e4 *block_partials, e4 *column_sums, const unsigned blocks_count) {
  gkr_trace_holder_column_sums(block_partials, column_sums, blocks_count);
}

EXTERN __global__ void ab_gkr_dim_reducing_round0_batched_compact_e4_kernel(const __grid_constant__ gkr_dim_reducing_batch<e4> batch, const unsigned acc_size) {
  gkr_dim_reducing_round0_batched_compact(batch, acc_size);
}

EXTERN __global__ void ab_gkr_dim_reducing_continuation_batched_compact_e4_kernel(const __grid_constant__ gkr_dim_reducing_batch<e4> batch,
                                                                                  const unsigned acc_size, const unsigned step) {
  gkr_dim_reducing_continuation_batched_compact_inner<e4>(batch, acc_size, step);
}

} // namespace airbender::gkr::backward
