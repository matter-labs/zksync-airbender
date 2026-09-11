#include "continuation_split.cuh"

namespace airbender::gkr::backward {

// Slot-major planes use the existing partials allocation and widened tail reduce.
EXTERN __global__ void __launch_bounds__(288, 2) ab_gkr_dr_cont_window3_packed_split_b2_kernel(const __grid_constant__ gkr_dr_cont_window3_desc desc) {
  dr_cont_packed_unified(desc);
}

} // namespace airbender::gkr::backward
