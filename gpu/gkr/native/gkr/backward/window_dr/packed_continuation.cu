#include "continuation_split.cuh"

namespace airbender::gkr::backward {

EXTERN __global__ void __launch_bounds__(BWD_WINDOW_BLOCK_THREADS, 2) ab_gkr_dr_cont_window3_kernel(const __grid_constant__ gkr_dr_cont_window3_desc desc) {
  dr_cont_packed_unified(desc);
}

} // namespace airbender::gkr::backward
