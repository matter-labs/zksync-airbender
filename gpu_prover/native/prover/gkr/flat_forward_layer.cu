#include "flat_forward.cuh"

namespace airbender::prover::gkr {

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
