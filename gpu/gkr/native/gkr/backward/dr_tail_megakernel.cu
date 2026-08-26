#include "dr_tail_megakernel.cuh"

namespace airbender::gkr::backward {

EXTERN __global__ __launch_bounds__(GKR_DR_TAIL_BLOCK_THREADS,
                                    1) void ab_gkr_dr_tail_megakernel_e4_kernel(const __grid_constant__ gkr_dr_tail_megakernel_desc desc) {
  gkr_dr_tail_megakernel_inner(desc, gkr_dr_tail_noop_recorder{});
}

} // namespace airbender::gkr::backward
