#include "flat_backward_continuation.cuh"

namespace airbender::prover::gkr {

EXTERN __launch_bounds__(128, 8) __global__
    void ab_gkr_main_round2_flat_compact_e4_kernel(const __grid_constant__ flat_round2_static_desc<bf, e4> static_desc, const e4 *coefficients,
                                                   const e4 *folding_challenges, const unsigned fold_stride, const unsigned next_layer_size,
                                                   const e4 *eq_values, e4 *contributions, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;
  const e4 first_challenge = load<e4, ld_modifier::ca>(folding_challenges, 0);
  const e4 second_challenge = load<e4, ld_modifier::ca>(folding_challenges, 1);
  flat_round2_compute<e4, false>(static_desc, coefficients, first_challenge, second_challenge, fold_stride, next_layer_size, eq_values, contributions, acc_size,
                                 gid);
}

EXTERN __launch_bounds__(128, 8) __global__
    void ab_gkr_main_round2_flat_constant_compact_e4_kernel(const __grid_constant__ flat_round2_static_desc<bf, e4> static_desc,
                                                            const e4 *folding_challenges, const unsigned fold_stride, const unsigned next_layer_size,
                                                            const e4 *eq_values, e4 *contributions, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;
  const e4 first_challenge = load<e4, ld_modifier::ca>(folding_challenges, 0);
  const e4 second_challenge = load<e4, ld_modifier::ca>(folding_challenges, 1);
  flat_round2_compute_constant<e4, false>(static_desc, first_challenge, second_challenge, fold_stride, next_layer_size, eq_values, contributions, acc_size, gid);
}

} // namespace airbender::prover::gkr
