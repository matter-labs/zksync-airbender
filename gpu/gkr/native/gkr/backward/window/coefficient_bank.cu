#include "../../support/kernel_helpers.cuh"
#include "coefficient_bank.cuh"

namespace airbender::gkr::backward {

// Fill one contiguous coefficient-bank range: one warp per bank slot,
// reading the round's device-resident challenge slab and writing E4 values the
// window executors index directly.
//
// The chunk's recipes and monomials ride the launch parameter space by value —
// no host staging, no device table buffer, no H2D copy. `challenges` is round
// state the transcript squeezed on the device.
//
// `coefficients` is the `ab_gkr_bwd_coeff_bank` symbol's device address.
//
// The reserved literals occupy bank slots 0 and 1 and are filled here like any
// other slot (constant plans, no factors), so the chunk sequence produces the
// whole reserved-inclusive payload.
// Every live warp participates in the canonical field sum, including lanes
// with no monomial. Reassociation preserves the serial recipe value exactly.
EXTERN __launch_bounds__(128, 8) __global__
    void ab_gkr_bwd_eval_coefficients_kernel(__grid_constant__ const bwd_coeff_chunk_desc desc, const e4 *challenges, e4 *coefficients) {
  if (blockDim.x != 128)
    return;
  const unsigned lane = threadIdx.x & 31u;
  const unsigned gid = blockIdx.x * 4u + (threadIdx.x >> 5);
  if (gid >= desc.bank_count)
    return;
  const bwd_coeff_recipe recipe = desc.recipes[gid];
  const bwd_coeff_monomial *monomials = desc.monomials + recipe.monomial_offset;
  const e4 batch_base = challenges[BWD_COEFF_CHALLENGE_CLAIM_BATCHING];
  e4 acc = e4::ZERO();
  for (unsigned i = lane; i < recipe.monomial_count; i += 32u) {
    const bwd_coeff_monomial mon = monomials[i];
    e4 term = e4::from_scalar(mon.coeff);
    if (mon.batch_power != 0)
      term = e4::mul(term, e4::pow(batch_base, mon.batch_power));
    if (mon.challenge_idx_0 != BWD_COEFF_CHALLENGE_ABSENT)
      term = e4::mul(term, e4::pow(challenges[mon.challenge_idx_0], mon.power_0));
    if (mon.challenge_idx_1 != BWD_COEFF_CHALLENGE_ABSENT)
      term = e4::mul(term, e4::pow(challenges[mon.challenge_idx_1], mon.power_1));
    acc = e4::add(acc, term);
  }
  acc = gkr_trace_holder_partials_warp_reduce_sum(acc);
  if (lane == 0) {
    if (recipe.kind == BWD_COEFF_PLAN_SCALED)
      acc = e4::mul(acc, recipe.scalar);
    else if (recipe.kind == BWD_COEFF_PLAN_LINEAR_BASIS) {
      bf basis[4] = {bf::ZERO(), bf::ZERO(), bf::ZERO(), bf::ZERO()};
      basis[recipe.limb] = bf::ONE();
      acc = e4::mul(acc, e4(basis));
    }
    coefficients[desc.bank_first + gid] = acc;
  }
}

} // namespace airbender::gkr::backward
