#include "common.cuh"

namespace airbender::prover::gkr {

EXTERN __global__ void
ab_gkr_main_round0_e4_kernel(const unsigned kind, const gkr_base_initial_source<bf> *base_inputs, const gkr_ext_initial_source<e4> *ext_inputs,
                             const gkr_base_initial_source<bf> *base_outputs, const gkr_ext_initial_source<e4> *ext_outputs, const e4 *batch_challenges,
                             const e4 *aux_challenge, const gkr_main_constraint_quadratic_term<e4> *constraint_quadratic_terms,
                             const unsigned constraint_quadratic_terms_count, const gkr_main_constraint_linear_term<e4> *constraint_linear_terms,
                             const unsigned constraint_linear_terms_count, const e4 *constraint_constant_offset, e4 *contributions, const unsigned acc_size) {
  gkr_main_round0(kind, base_inputs, ext_inputs, base_outputs, ext_outputs, batch_challenges, aux_challenge, constraint_quadratic_terms,
                  constraint_quadratic_terms_count, constraint_linear_terms, constraint_linear_terms_count, constraint_constant_offset, contributions,
                  acc_size);
}

EXTERN __global__ void
ab_gkr_main_round0_batched_e4_kernel(const __grid_constant__ gkr_main_round0_batch_static<e4> batch_static,
                                     const gkr_main_round0_batch_runtime<e4> batch_runtime, const unsigned acc_size) {
  gkr_main_round0_batched(batch_static, batch_runtime, acc_size);
}

} // namespace airbender::prover::gkr
