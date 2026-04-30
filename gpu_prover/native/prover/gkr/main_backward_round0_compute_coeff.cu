#include "flat_backward_coeff.cuh"

namespace airbender::prover::gkr {

// Read each challenge from its own pointer rather than from a packed
// 4-element buffer. The previous packed layout was
// [batch_base, lookup_mul, lookup_add, constraint_batch], populated by 2
// per-layer D2Ds into a 3-element scratch allocation; constraint_batch was
// read past-the-end and is never produced by the recipe builder
// (`compile_recipes_for_device` only emits term.source ∈ {0, 1}). Pass
// e4::ZERO() to eval_single_recipe so the unreachable default branch sees
// a defined value.
EXTERN __launch_bounds__(128, 8) __global__
    void ab_gkr_flat_round0_eval_recipes_e4_kernel(const e4 *batch_base, const e4 *lookup_mul, const e4 *lookup_add,
                                                   const gpu_recipe_header *recipes, const gpu_prefactor_term *terms, e4 *coefficients,
                                                   const unsigned num_recipes) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= num_recipes)
    return;
  const e4 constraint_batch = e4::ZERO();
  coefficients[gid] = eval_single_recipe(recipes[gid], terms, *batch_base, *lookup_mul, *lookup_add, constraint_batch);
}

} // namespace airbender::prover::gkr
