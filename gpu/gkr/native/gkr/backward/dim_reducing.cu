#include "../support/eq_inline.cuh"
#include "../support/lookup_helpers.cuh"

__device__ __constant__ e4 ab_gkr_dim_reducing_batch_challenge_table[airbender::gkr::GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN];
__device__ __constant__ e4 ab_gkr_dim_reducing_layer_claim_point[airbender::gkr::GKR_DIM_REDUCING_LAYER_CLAIM_POINT_LEN];

namespace airbender::gkr::backward {

EXTERN __global__ void ab_gkr_dim_reducing_build_eq_group_tables_from_point_e4_kernel(const e4 *claim_point, const unsigned challenge_offset,
                                                                                      const unsigned challenge_count, e4 *eq_group_tables) {
  gkr_build_eq_group_tables_from_point(claim_point, challenge_offset, challenge_count, eq_group_tables);
}

// Builds the factored eq representation directly from a claim point into the
// strict 3-slot layout: high slabs (slots 0..GKR_EQ_HIGH_SLOTS-1) live in the
// `__constant__` symbol via `high_slab` (the device pointer obtained from
// `cudaGetSymbolAddress`), and the lane-varying low slab in regular global
// memory via `low_buffer`. Group 0..(G-2) populate slot 0..(G-2); the last
// group (G-1) populates `low_buffer` via the negative-offset trick (the inner
// helper stores at `dst + blockIdx.x * stride`).
//
// To support the strict 3-slot read in `gkr_compute_eq_inline` for small
// `challenge_count` (where some high slabs are not active), thread 0 of
// every block writes `e4::ONE()` to its slot's [0] entry before the group
// build runs. Active slots overwrite the sentinel with real data; unused
// slots retain the identity so the inline-eq read returns 1. Launch must
// be sized `max(groups_count, GKR_EQ_HIGH_SLOTS)` blocks for this to
// initialize every high slab.
EXTERN __global__ void ab_gkr_dim_reducing_build_eq_high_low_from_point_e4_kernel(const e4 *claim_point, const unsigned challenge_offset,
                                                                                  const unsigned challenge_count, e4 *high_slab, e4 *low_buffer) {
  if (blockIdx.x < GKR_EQ_HIGH_SLOTS && threadIdx.x == 0) {
    high_slab[static_cast<size_t>(blockIdx.x) * GKR_EQ_GROUP_TABLE_LEN] = e4::ONE();
  }
  const unsigned groups_count = gkr_eq_group_count(challenge_count);
  if (blockIdx.x >= groups_count)
    return;
  e4 *dst;
  if (blockIdx.x + 1u == groups_count) {
    dst = low_buffer - static_cast<size_t>(blockIdx.x) * GKR_EQ_GROUP_TABLE_LEN;
  } else {
    dst = high_slab;
  }
  gkr_build_eq_group_tables_from_point(claim_point, challenge_offset, challenge_count, dst);
}

EXTERN __global__ void ab_gkr_dim_reducing_build_eq_values_from_group_tables_e4_kernel(const e4 *eq_group_tables, const unsigned challenge_count, e4 *eq_values,
                                                                                       const unsigned acc_size) {
  gkr_build_eq_values_from_group_tables(eq_group_tables, challenge_count, eq_values, acc_size);
}

EXTERN __global__ void ab_gkr_dim_reducing_trace_holder_block_partials_e4_kernel(const bf *raw_values, const e4 *eq_values, e4 *block_partials,
                                                                                 const unsigned trace_len, const unsigned column_start,
                                                                                 const unsigned chunk_cols, const unsigned blocks_count) {
  gkr_trace_holder_block_partials(raw_values, eq_values, block_partials, trace_len, column_start, chunk_cols, blocks_count);
}

EXTERN __global__ void ab_gkr_dim_reducing_round0_batched_compact_e4_kernel(const __grid_constant__ gkr_dim_reducing_round0_batch_compact<e4> batch,
                                                                            const unsigned acc_size) {
  gkr_dim_reducing_round0_batched_compact(batch, acc_size);
}

EXTERN __global__ void ab_gkr_dim_reducing_round1_batched_compact_e4_kernel(const __grid_constant__ gkr_dim_reducing_continuation_batch_compact<e4> batch,
                                                                            const unsigned acc_size) {
  gkr_dim_reducing_round1_batched_compact_inner<e4>(batch, acc_size);
}

EXTERN __global__ void ab_gkr_dim_reducing_continuation_batched_compact_e4_kernel(const __grid_constant__ gkr_dim_reducing_continuation_batch_compact<e4> batch,
                                                                                  const unsigned acc_size, const unsigned step) {
  gkr_dim_reducing_continuation_batched_compact_inner<e4>(batch, acc_size, step);
}

} // namespace airbender::gkr::backward
