#include "seg_coeff_eval.cuh"

namespace airbender::prover::gkr::backward {

// Fill one coefficient bank: one thread per bank slot, reading the round's
// challenge slab and writing E4 values the segmented executors index raw.
//
// The tables ride the parameter space BY VALUE — they are a pure function of the
// compiled layer, so they are scheduling-time known, exactly like `bwd_seg_desc`.
// Only `challenges` is round state the transcript squeezed on the device, and only
// it is a pointer.
//
// `coefficients` is the write target — the `ab_gkr_bwd_seg_coeff_bank`
// `__constant__` symbol's own device address under the `const` loader, or the
// descriptor's device buffer under the `ptr` loader. Writing a `__constant__`
// symbol through its address is the same mechanism the flat lineage's
// `eval_recipes` kernels use for `ab_gkr_flat_coefficients`; the constant cache is
// invalidated between launches, so a later kernel's `__constant__` reads see it.
//
// The reserved literals occupy bank slots 0 and 1 and are filled here like any
// other slot (constant recipes, no factors), so ONE launch produces the whole
// reserved-inclusive payload and the host stages nothing.
EXTERN __launch_bounds__(128, 8) __global__
    void ab_gkr_bwd_seg_eval_coefficients_kernel(__grid_constant__ const bwd_seg_coeff_eval_desc desc, const e4 *challenges, e4 *coefficients) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= desc.num_coefficients)
    return;
  coefficients[gid] = bwd_seg_eval_coefficient(desc, gid, challenges);
}

} // namespace airbender::prover::gkr::backward
