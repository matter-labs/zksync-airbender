#include "dr_tail_megakernel.cuh"

namespace airbender::gkr::proth120::backward {

EXTERN __global__ __launch_bounds__(PR_DR_TAIL_BLOCK_THREADS, 1) void ab_pr_gkr_dr_tail_megakernel(const __grid_constant__ pr_dr_tail_megakernel_desc desc,
                                                                                                   pr *global_state) {
  pr_dr_tail_inner(desc, global_state);
}

} // namespace airbender::gkr::proth120::backward
