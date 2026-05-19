#include "coeff.cuh"
#include "continuation.cuh"

__device__ __constant__ e4 ab_gkr_flat_coefficients[airbender::prover::gkr::FLAT_CONST_MAX];

namespace airbender::prover::gkr::backward {

EXTERN __launch_bounds__(128, 8) __global__
    void ab_gkr_flat_continuation_eval_recipes_e4_kernel(const e4 *batch_base, const e4 *lookup_mul, const e4 *lookup_add, const e4 *ext_challenges,
                                                         __grid_constant__ const gpu_flat_recipe_eval_desc desc, e4 *coefficients, const unsigned num_recipes) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= num_recipes)
    return;
  coefficients[gid] = eval_single_recipe(desc.headers[gid], desc, *batch_base, *lookup_mul, *lookup_add, ext_challenges);
}

} // namespace airbender::prover::gkr::backward
