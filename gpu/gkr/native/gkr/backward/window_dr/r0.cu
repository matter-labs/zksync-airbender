#include "evaluate.cuh"

namespace airbender::gkr::backward {

EXTERN __global__ __launch_bounds__(BWD_WINDOW_BLOCK_THREADS, 2) void ab_gkr_dr_r0_window3_kernel(const __grid_constant__ gkr_dr_window3_desc desc) {
  dr_window_evaluate(desc, desc.batch.enabled_mask, blockIdx.x);
}

} // namespace airbender::gkr::backward
