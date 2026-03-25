#include "common.cuh"

namespace airbender::prover::gkr {

#define GKR_DIM_REDUCING_KERNELS(arg_t)                                                                                                                        \
  EXTERN __global__ void ab_gkr_dim_reducing_pairwise_round0_##arg_t##_kernel(const gkr_ext_initial_source<arg_t> *inputs,                                     \
                                                                              const gkr_ext_initial_source<arg_t> *outputs, const arg_t *batch_challenges,     \
                                                                              arg_t *contributions, const unsigned acc_size) {                                 \
    gkr_pairwise_round0(inputs, outputs, batch_challenges, contributions, acc_size);                                                                           \
  }                                                                                                                                                            \
  EXTERN __global__ void ab_gkr_dim_reducing_lookup_round0_##arg_t##_kernel(const gkr_ext_initial_source<arg_t> *inputs,                                       \
                                                                            const gkr_ext_initial_source<arg_t> *outputs, const arg_t *batch_challenges,       \
                                                                            arg_t *contributions, const unsigned acc_size) {                                   \
    gkr_lookup_round0(inputs, outputs, batch_challenges, contributions, acc_size);                                                                             \
  }                                                                                                                                                            \
  EXTERN __global__ void ab_gkr_dim_reducing_pairwise_continuation_##arg_t##_kernel(const gkr_ext_continuing_source<arg_t> *inputs,                            \
                                                                                    const arg_t *folding_challenge, const arg_t *batch_challenges,             \
                                                                                    const bool explicit_form, arg_t *contributions, const unsigned acc_size) { \
    if (explicit_form)                                                                                                                                         \
      gkr_pairwise_continuation<arg_t, true>(inputs, folding_challenge, batch_challenges, contributions, acc_size);                                            \
    else                                                                                                                                                       \
      gkr_pairwise_continuation<arg_t, false>(inputs, folding_challenge, batch_challenges, contributions, acc_size);                                           \
  }                                                                                                                                                            \
  EXTERN __global__ void ab_gkr_dim_reducing_lookup_continuation_##arg_t##_kernel(const gkr_ext_continuing_source<arg_t> *inputs,                              \
                                                                                  const arg_t *folding_challenge, const arg_t *batch_challenges,               \
                                                                                  const bool explicit_form, arg_t *contributions, const unsigned acc_size) {   \
    if (explicit_form)                                                                                                                                         \
      gkr_lookup_continuation<arg_t, true>(inputs, folding_challenge, batch_challenges, contributions, acc_size);                                              \
    else                                                                                                                                                       \
      gkr_lookup_continuation<arg_t, false>(inputs, folding_challenge, batch_challenges, contributions, acc_size);                                             \
  }                                                                                                                                                            \
  EXTERN __global__ void ab_gkr_dim_reducing_build_eq_##arg_t##_kernel(const arg_t *claim_point, const unsigned challenge_offset,                              \
                                                                       const unsigned challenge_count, arg_t *eq_values, const unsigned acc_size) {            \
    gkr_build_eq_values(claim_point, challenge_offset, challenge_count, eq_values, acc_size);                                                                  \
  }                                                                                                                                                            \
  EXTERN __global__ void ab_gkr_dim_reducing_round0_batched_##arg_t##_kernel(const __grid_constant__ gkr_dim_reducing_round0_batch<arg_t> batch,               \
                                                                             const unsigned acc_size) {                                                        \
    gkr_dim_reducing_round0_batched(batch, acc_size);                                                                                                          \
  }                                                                                                                                                            \
  EXTERN __global__ void ab_gkr_dim_reducing_round1_batched_##arg_t##_kernel(const __grid_constant__ gkr_dim_reducing_round1_batch<arg_t> batch,               \
                                                                             const unsigned acc_size) {                                                        \
    if (batch.explicit_form)                                                                                                                                   \
      gkr_dim_reducing_continuation_batched<arg_t, true>(batch, acc_size);                                                                                     \
    else                                                                                                                                                       \
      gkr_dim_reducing_continuation_batched<arg_t, false>(batch, acc_size);                                                                                    \
  }                                                                                                                                                            \
  EXTERN __global__ void ab_gkr_dim_reducing_round2_batched_##arg_t##_kernel(const __grid_constant__ gkr_dim_reducing_round2_batch<arg_t> batch,               \
                                                                             const unsigned acc_size) {                                                        \
    if (batch.explicit_form)                                                                                                                                   \
      gkr_dim_reducing_continuation_batched<arg_t, true>(batch, acc_size);                                                                                     \
    else                                                                                                                                                       \
      gkr_dim_reducing_continuation_batched<arg_t, false>(batch, acc_size);                                                                                    \
  }                                                                                                                                                            \
  EXTERN __global__ void ab_gkr_dim_reducing_round3_batched_##arg_t##_kernel(const __grid_constant__ gkr_dim_reducing_round3_batch<arg_t> batch,               \
                                                                             const unsigned acc_size) {                                                        \
    if (batch.explicit_form)                                                                                                                                   \
      gkr_dim_reducing_continuation_batched<arg_t, true>(batch, acc_size);                                                                                     \
    else                                                                                                                                                       \
      gkr_dim_reducing_continuation_batched<arg_t, false>(batch, acc_size);                                                                                    \
  }

GKR_DIM_REDUCING_KERNELS(e2);
GKR_DIM_REDUCING_KERNELS(e4);
GKR_DIM_REDUCING_KERNELS(e6);

} // namespace airbender::prover::gkr
