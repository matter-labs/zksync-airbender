#include "dr_tail_megakernel.cuh"

namespace airbender::gkr::backward {

EXTERN __global__ __launch_bounds__(GKR_DR_TAIL_BLOCK_THREADS,
                                    1) void ab_gkr_dr_tail_megakernel_e4_kernel(const __grid_constant__ gkr_dr_tail_megakernel_desc desc, e4 *global_state) {
  dr_tail_cooperative_inner<GKR_DR_TAIL_BLOCK_THREADS>(desc, global_state);
}

} // namespace airbender::gkr::backward
