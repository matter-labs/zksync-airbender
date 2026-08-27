#include "coefficient_bank.cuh"

namespace airbender::gkr::backward {

// Fill one contiguous coefficient-bank range: one thread per bank slot,
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
EXTERN __launch_bounds__(128, 8) __global__
    void ab_gkr_bwd_eval_coefficients_kernel(__grid_constant__ const bwd_coeff_chunk_desc desc, const e4 *challenges, e4 *coefficients) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= desc.bank_count)
    return;
  coefficients[desc.bank_first + gid] = bwd_eval_coefficient(desc, gid, challenges);
}

} // namespace airbender::gkr::backward
