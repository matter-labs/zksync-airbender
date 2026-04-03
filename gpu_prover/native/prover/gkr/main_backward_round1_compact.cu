#include "common.cuh"

namespace airbender::prover::gkr {

EXTERN __global__ void
ab_gkr_main_round1_compact_e4_kernel(const unsigned kind, const gkr_base_after_one_source<bf, e4> *base_inputs, const gkr_ext_continuing_source<e4> *ext_inputs,
                                     const e4 *batch_challenges, const e4 *folding_challenge, const e4 *aux_challenge,
                                     const gkr_main_constraint_quadratic_term<e4> *constraint_quadratic_terms, const unsigned constraint_quadratic_terms_count,
                                     const gkr_main_constraint_linear_term<e4> *constraint_linear_terms, const unsigned constraint_linear_terms_count,
                                     const e4 *constraint_constant_offset, e4 *contributions, const unsigned acc_size) {
  gkr_main_round1<e4, false>(kind, base_inputs, ext_inputs, batch_challenges, folding_challenge, aux_challenge, constraint_quadratic_terms,
                             constraint_quadratic_terms_count, constraint_linear_terms, constraint_linear_terms_count, constraint_constant_offset,
                             contributions, acc_size);
}

EXTERN __global__ void ab_gkr_main_round1_batched_compact_e4_kernel(const __grid_constant__ gkr_main_round1_batch<e4> batch, const unsigned acc_size) {
  gkr_main_round1_batched<e4, false>(batch, acc_size);
}

} // namespace airbender::prover::gkr
