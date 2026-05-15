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

EXTERN __global__ void ab_gkr_dim_reducing_build_eq_values_from_group_tables_e4_kernel(const e4 *eq_group_tables, const unsigned challenge_count, e4 *eq_values,
                                                                                       const unsigned acc_size) {
  gkr_build_eq_values_from_group_tables(eq_group_tables, challenge_count, eq_values, acc_size);
}

EXTERN __global__ void ab_gkr_dim_reducing_fold_eq_values_e4_kernel(e4 *eq_values, const unsigned half_len) {
  gkr_fold_eq_values_in_place(eq_values, half_len);
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

} // namespace airbender::prover::gkr::backward
