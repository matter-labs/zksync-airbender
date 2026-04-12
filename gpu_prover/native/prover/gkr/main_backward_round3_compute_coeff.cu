#include "flat_backward_coeff.cuh"
#include "flat_backward_continuation.cuh"

__device__ __constant__ e4 ab_gkr_flat_continuation_coefficients[airbender::prover::gkr::FLAT_CONT_CONST_MAX];

namespace airbender::prover::gkr {

// challenges layout: [batch_base, lookup_mul, lookup_add, constraint_batch]
EXTERN __launch_bounds__(128, 8) __global__
    void ab_gkr_flat_continuation_eval_recipes_e4_kernel(const e4 *challenges, const gpu_recipe_header *recipes, const gpu_prefactor_term *terms,
                                                         e4 *coefficients, const unsigned num_recipes) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= num_recipes)
    return;
  const e4 batch_base = challenges[0];
  const e4 lookup_mul = challenges[1];
  const e4 lookup_add = challenges[2];
  const e4 constraint_batch = challenges[3];
  coefficients[gid] = eval_single_recipe(recipes[gid], terms, batch_base, lookup_mul, lookup_add, constraint_batch);
}

} // namespace airbender::prover::gkr
