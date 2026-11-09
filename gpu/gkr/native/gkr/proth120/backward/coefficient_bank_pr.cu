#include "coefficient_bank_pr.cuh"

namespace airbender::gkr::proth120::backward {

EXTERN __launch_bounds__(PR_COEFF_FILL_BLOCK_THREADS) __global__
    void ab_pr_gkr_bwd_eval_coefficients_kernel(const __grid_constant__ bwd_coeff_fill_desc_pr desc) {
  if (blockDim.x != PR_COEFF_FILL_BLOCK_THREADS)
    return;
  const u32 lane = threadIdx.x & 31u;
  const u32 local = blockIdx.x * PR_COEFF_FILL_WARPS + (threadIdx.x >> 5);
  if (local >= desc.recipe_count)
    return;
  const u32 slot = desc.recipe_first + local;
  const bwd_coeff_recipe_pr recipe = desc.recipes[slot];
  const pr batch_base = *desc.claim_batching;
  pr acc = pr::ZERO();
  for (u32 i = lane; i < recipe.monomial_count; i += 32u) {
    const u32 index = recipe.monomial_offset + i;
    const bwd_coeff_monomial_pr monomial = desc.monomials[index];
    pr term = desc.monomial_coeffs[index];
    if (monomial.batch_power != 0)
      term = pr::mul(term, pr::pow(batch_base, monomial.batch_power));
    if (monomial.challenge_idx_0 != PR_COEFF_CHALLENGE_ABSENT)
      term = pr::mul(term, pr::pow(desc.challenges[monomial.challenge_idx_0], monomial.power_0));
    if (monomial.challenge_idx_1 != PR_COEFF_CHALLENGE_ABSENT)
      term = pr::mul(term, pr::pow(desc.challenges[monomial.challenge_idx_1], monomial.power_1));
    acc = pr::add(acc, term);
  }
  acc = gkr_trace_holder_partials_warp_reduce_sum(acc);
  if (lane == 0) {
    if (recipe.kind == PR_COEFF_PLAN_SCALED)
      acc = pr::mul(acc, desc.scalars[recipe.scalar_index]);
    desc.coefficients[local] = acc;
  }
}

} // namespace airbender::gkr::proth120::backward
