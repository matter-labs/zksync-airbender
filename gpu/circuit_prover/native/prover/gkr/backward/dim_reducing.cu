#include "../support/eq_inline.cuh"
#include "../support/lookup_helpers.cuh"

__device__ __constant__ e4 ab_gkr_dim_reducing_batch_challenge_table[airbender::prover::gkr::GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN];
__device__ __constant__ e4 ab_gkr_dim_reducing_layer_claim_point[airbender::prover::gkr::GKR_DIM_REDUCING_LAYER_CLAIM_POINT_LEN];

namespace airbender::prover::gkr::backward {

EXTERN __global__ void ab_gkr_dim_reducing_pairwise_round0_e4_kernel(const gkr_ext_initial_source<e4> *inputs, const gkr_ext_initial_source<e4> *outputs,
                                                                     const e4 *batch_challenges, e4 *contributions, const unsigned acc_size) {
  gkr_pairwise_round0(inputs, outputs, batch_challenges, contributions, acc_size);
}

EXTERN __global__ void ab_gkr_dim_reducing_lookup_round0_e4_kernel(const gkr_ext_initial_source<e4> *inputs, const gkr_ext_initial_source<e4> *outputs,
                                                                   const e4 *batch_challenges, e4 *contributions, const unsigned acc_size) {
  gkr_lookup_round0(inputs, outputs, batch_challenges, contributions, acc_size);
}

EXTERN __global__ void ab_gkr_dim_reducing_pairwise_continuation_e4_kernel(const gkr_ext_continuing_source<e4> *inputs, const e4 *folding_challenge,
                                                                           const e4 *batch_challenges, const bool explicit_form, e4 *contributions,
                                                                           const unsigned acc_size) {
  if (explicit_form)
    gkr_pairwise_continuation<e4, true>(inputs, folding_challenge, batch_challenges, contributions, acc_size);
  else
    gkr_pairwise_continuation<e4, false>(inputs, folding_challenge, batch_challenges, contributions, acc_size);
}

EXTERN __global__ void ab_gkr_dim_reducing_lookup_continuation_e4_kernel(const gkr_ext_continuing_source<e4> *inputs, const e4 *folding_challenge,
                                                                         const e4 *batch_challenges, const bool explicit_form, e4 *contributions,
                                                                         const unsigned acc_size) {
  if (explicit_form)
    gkr_lookup_continuation<e4, true>(inputs, folding_challenge, batch_challenges, contributions, acc_size);
  else
    gkr_lookup_continuation<e4, false>(inputs, folding_challenge, batch_challenges, contributions, acc_size);
}

EXTERN __global__ void ab_gkr_dim_reducing_build_eq_group_tables_from_pairs_e4_kernel(const e4 *eq_pair_values, const unsigned challenge_count,
                                                                                      e4 *eq_group_tables) {
  gkr_build_eq_group_tables_from_pairs(eq_pair_values, challenge_count, eq_group_tables);
}

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

EXTERN __global__ void ab_gkr_dim_reducing_fold_eq_values_e4_kernel(e4 *eq_values, const unsigned half_len) {
  gkr_fold_eq_values_in_place(eq_values, half_len);
}

// Single pointer-driven fold kernel for the factored-eq high slab. The Rust
// launcher offsets `high_slab_group_base` to the slot to fold, so this kernel
// is layer-kind agnostic (works for both main-layer and dim-reducing slabs).
EXTERN __global__ void ab_gkr_dim_reducing_fold_eq_high_group_in_place_e4_kernel(e4 *high_slab_group_base, const unsigned new_g_len) {
  gkr_fold_eq_high_group_in_place(high_slab_group_base, new_g_len);
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
  if (batch.explicit_form)
    gkr_dim_reducing_round1_batched_compact_inner<e4, true>(batch, acc_size);
  else
    gkr_dim_reducing_round1_batched_compact_inner<e4, false>(batch, acc_size);
}

EXTERN __global__ void ab_gkr_dim_reducing_continuation_batched_compact_e4_kernel(const __grid_constant__ gkr_dim_reducing_continuation_batch_compact<e4> batch,
                                                                                  const unsigned acc_size, const unsigned step) {
  if (batch.explicit_form)
    gkr_dim_reducing_continuation_batched_compact_inner<e4, true>(batch, acc_size, step);
  else
    gkr_dim_reducing_continuation_batched_compact_inner<e4, false>(batch, acc_size, step);
}

// Microbench / parity-test kernel: materializes dense `eq_values[gid] =
// gkr_compute_eq_inline(eq_low, sizes, gid)` for gid in 0..acc_size.
// High slabs are read from the `ab_gkr_eq_high` __constant__ symbol; the
// caller must have populated it before launching (via the build / fold path).
EXTERN __global__ void ab_gkr_eq_inline_materialize_for_test_e4_kernel(const e4 *eq_low, const gkr_eq_sizes sizes, e4 *eq_values, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;
  eq_values[gid] = gkr_compute_eq_inline<e4>(eq_low, sizes, gid);
}

} // namespace airbender::prover::gkr::backward
