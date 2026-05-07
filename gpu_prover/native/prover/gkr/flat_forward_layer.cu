#include "flat_forward.cuh"

__device__ __constant__ e4 ab_gkr_lookup_gamma_consts[3];

namespace airbender::prover::gkr {

EXTERN __global__ void ab_gkr_lookup_gamma_consts_prelude(const e4 *gamma, e4 *staging) {
  const e4 value = gamma[0];
  staging[0] = value;
  staging[1] = e4::sqr(value);
  staging[2] = e4::dbl(value);
}

// Phase 0 baseline profiling hasn't been run yet, so start with a conservative
// launch bound of 4 blocks/SM at 128 threads. Phase 4 will tune this based on
// ncu measurements.
EXTERN __launch_bounds__(128, 4) __global__
    void ab_gkr_flat_forward_layer_e4_kernel(const __grid_constant__ flat_forward_static_desc<e4> desc, const unsigned count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;
  flat_forward_compute(desc, gid);
}

} // namespace airbender::prover::gkr
