#include "seg_coeff_eval.cuh"

namespace airbender::gkr::backward {

// Fill one coefficient bank: one thread per bank slot, reading the round's
// challenge slab and writing E4 values the segmented executors index raw.
//
// The plan tables are device-resident, staged once per layer from a
// `SchedulerHostAllocator` blob; only the launch header rides the parameter
// space. `challenges` is round state the transcript squeezed on the device.
//
// `coefficients` is the `ab_gkr_bwd_seg_coeff_bank` symbol's device address.
//
// The reserved literals occupy bank slots 0 and 1 and are filled here like any
// other slot (constant plans, no factors), so ONE launch produces the whole
// reserved-inclusive payload and the host stages nothing.
EXTERN __launch_bounds__(128, 8) __global__
    void ab_gkr_bwd_seg_eval_coefficients_kernel(__grid_constant__ const bwd_seg_coeff_eval_desc desc, const e4 *challenges, e4 *coefficients) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= desc.num_coefficients)
    return;
  coefficients[gid] = bwd_seg_eval_coefficient(desc, gid, challenges);
}

} // namespace airbender::gkr::backward
