#include "common.cuh"

namespace airbender::prover::gkr {

#define GKR_MAIN_LAYER_KERNELS(arg_t)                                                                                                                          \
  EXTERN __global__ void ab_gkr_main_round0_##arg_t##_kernel(                                                                                                  \
      const unsigned kind, const gkr_base_initial_source<bf> *base_inputs, const gkr_ext_initial_source<arg_t> *ext_inputs,                                    \
      const gkr_base_initial_source<bf> *base_outputs, const gkr_ext_initial_source<arg_t> *ext_outputs, const arg_t *batch_challenges,                        \
      const arg_t *aux_challenge, const gkr_main_constraint_quadratic_term<arg_t> *constraint_quadratic_terms,                                                 \
      const unsigned constraint_quadratic_terms_count, const gkr_main_constraint_linear_term<arg_t> *constraint_linear_terms,                                  \
      const unsigned constraint_linear_terms_count, const arg_t *constraint_constant_offset, arg_t *contributions, const unsigned acc_size) {                  \
    gkr_main_round0(kind, base_inputs, ext_inputs, base_outputs, ext_outputs, batch_challenges, aux_challenge, constraint_quadratic_terms,                     \
                    constraint_quadratic_terms_count, constraint_linear_terms, constraint_linear_terms_count, constraint_constant_offset, contributions,       \
                    acc_size);                                                                                                                                 \
  }                                                                                                                                                            \
  EXTERN __global__ void ab_gkr_main_round1_##arg_t##_kernel(                                                                                                  \
      const unsigned kind, const gkr_base_after_one_source<bf, arg_t> *base_inputs, const gkr_ext_continuing_source<arg_t> *ext_inputs,                        \
      const arg_t *batch_challenges, const arg_t *folding_challenge, const arg_t *aux_challenge,                                                               \
      const gkr_main_constraint_quadratic_term<arg_t> *constraint_quadratic_terms, const unsigned constraint_quadratic_terms_count,                            \
      const gkr_main_constraint_linear_term<arg_t> *constraint_linear_terms, const unsigned constraint_linear_terms_count,                                     \
      const arg_t *constraint_constant_offset, const bool explicit_form, arg_t *contributions, const unsigned acc_size) {                                      \
    if (explicit_form)                                                                                                                                         \
      gkr_main_round1<arg_t, true>(kind, base_inputs, ext_inputs, batch_challenges, folding_challenge, aux_challenge, constraint_quadratic_terms,              \
                                   constraint_quadratic_terms_count, constraint_linear_terms, constraint_linear_terms_count, constraint_constant_offset,       \
                                   contributions, acc_size);                                                                                                   \
    else                                                                                                                                                       \
      gkr_main_round1<arg_t, false>(kind, base_inputs, ext_inputs, batch_challenges, folding_challenge, aux_challenge, constraint_quadratic_terms,             \
                                    constraint_quadratic_terms_count, constraint_linear_terms, constraint_linear_terms_count, constraint_constant_offset,      \
                                    contributions, acc_size);                                                                                                  \
  }                                                                                                                                                            \
  EXTERN __global__ void ab_gkr_main_round2_##arg_t##_kernel(                                                                                                  \
      const unsigned kind, const gkr_base_after_two_source<bf, arg_t> *base_inputs, const gkr_ext_continuing_source<arg_t> *ext_inputs,                        \
      const arg_t *batch_challenges, const arg_t *folding_challenges, const arg_t *aux_challenge,                                                              \
      const gkr_main_constraint_quadratic_term<arg_t> *constraint_quadratic_terms, const unsigned constraint_quadratic_terms_count,                            \
      const gkr_main_constraint_linear_term<arg_t> *constraint_linear_terms, const unsigned constraint_linear_terms_count,                                     \
      const arg_t *constraint_constant_offset, const bool explicit_form, arg_t *contributions, const unsigned acc_size) {                                      \
    if (explicit_form)                                                                                                                                         \
      gkr_main_round2<arg_t, true>(kind, base_inputs, ext_inputs, batch_challenges, folding_challenges, aux_challenge, constraint_quadratic_terms,             \
                                   constraint_quadratic_terms_count, constraint_linear_terms, constraint_linear_terms_count, constraint_constant_offset,       \
                                   contributions, acc_size);                                                                                                   \
    else                                                                                                                                                       \
      gkr_main_round2<arg_t, false>(kind, base_inputs, ext_inputs, batch_challenges, folding_challenges, aux_challenge, constraint_quadratic_terms,            \
                                    constraint_quadratic_terms_count, constraint_linear_terms, constraint_linear_terms_count, constraint_constant_offset,      \
                                    contributions, acc_size);                                                                                                  \
  }                                                                                                                                                            \
  EXTERN __global__ void ab_gkr_main_round3_##arg_t##_kernel(                                                                                                  \
      const unsigned kind, const gkr_ext_continuing_source<arg_t> *base_inputs, const gkr_ext_continuing_source<arg_t> *ext_inputs,                            \
      const arg_t *batch_challenges, const arg_t *folding_challenge, const arg_t *aux_challenge,                                                               \
      const gkr_main_constraint_quadratic_term<arg_t> *constraint_quadratic_terms, const unsigned constraint_quadratic_terms_count,                            \
      const gkr_main_constraint_linear_term<arg_t> *constraint_linear_terms, const unsigned constraint_linear_terms_count,                                     \
      const arg_t *constraint_constant_offset, const bool explicit_form, arg_t *contributions, const unsigned acc_size) {                                      \
    if (explicit_form)                                                                                                                                         \
      gkr_main_round3<arg_t, true>(kind, base_inputs, ext_inputs, batch_challenges, folding_challenge, aux_challenge, constraint_quadratic_terms,              \
                                   constraint_quadratic_terms_count, constraint_linear_terms, constraint_linear_terms_count, constraint_constant_offset,       \
                                   contributions, acc_size);                                                                                                   \
    else                                                                                                                                                       \
      gkr_main_round3<arg_t, false>(kind, base_inputs, ext_inputs, batch_challenges, folding_challenge, aux_challenge, constraint_quadratic_terms,             \
                                    constraint_quadratic_terms_count, constraint_linear_terms, constraint_linear_terms_count, constraint_constant_offset,      \
                                    contributions, acc_size);                                                                                                  \
  }                                                                                                                                                            \
  EXTERN __global__ void ab_gkr_main_round0_batched_##arg_t##_kernel(const __grid_constant__ gkr_main_round0_batch<arg_t> batch, const unsigned acc_size) {    \
    gkr_main_round0_batched(batch, acc_size);                                                                                                                  \
  }                                                                                                                                                            \
  EXTERN __global__ void ab_gkr_main_round1_batched_##arg_t##_kernel(const __grid_constant__ gkr_main_round1_batch<arg_t> batch, const unsigned acc_size) {    \
    if (batch.explicit_form)                                                                                                                                   \
      gkr_main_round1_batched<arg_t, true>(batch, acc_size);                                                                                                   \
    else                                                                                                                                                       \
      gkr_main_round1_batched<arg_t, false>(batch, acc_size);                                                                                                  \
  }                                                                                                                                                            \
  EXTERN __global__ void ab_gkr_main_round2_batched_##arg_t##_kernel(const __grid_constant__ gkr_main_round2_batch<arg_t> batch, const unsigned acc_size) {    \
    if (batch.explicit_form)                                                                                                                                   \
      gkr_main_round2_batched<arg_t, true>(batch, acc_size);                                                                                                   \
    else                                                                                                                                                       \
      gkr_main_round2_batched<arg_t, false>(batch, acc_size);                                                                                                  \
  }                                                                                                                                                            \
  EXTERN __global__ void ab_gkr_main_round3_batched_##arg_t##_kernel(const __grid_constant__ gkr_main_round3_batch<arg_t> batch, const unsigned acc_size) {    \
    if (batch.explicit_form)                                                                                                                                   \
      gkr_main_round3_batched<arg_t, true>(batch, acc_size);                                                                                                   \
    else                                                                                                                                                       \
      gkr_main_round3_batched<arg_t, false>(batch, acc_size);                                                                                                  \
  }

GKR_MAIN_LAYER_KERNELS(e2);
GKR_MAIN_LAYER_KERNELS(e4);
GKR_MAIN_LAYER_KERNELS(e6);

} // namespace airbender::prover::gkr
