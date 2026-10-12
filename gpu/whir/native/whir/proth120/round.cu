#include "round.cuh"

namespace airbender::whir {

EXTERN __global__ void ab_pr_whir_fold_round_update_kernel(pr *reductions, u8 *seed_io, pr *coeffs_out, pr *challenge_out) {
  if (blockIdx.x == 0 && threadIdx.x == 0)
    pr_whir_round_update_inline(reductions, seed_io, coeffs_out, challenge_out);
}

} // namespace airbender::whir
