#include "evaluate_pr.cuh"

namespace airbender::gkr::proth120::backward {

EXTERN __global__ __launch_bounds__(pr_dr_bwd::BWD_WINDOW_BLOCK_THREADS,
                                    2) void ab_pr_gkr_bwd_dr_window_r0_kernel(const __grid_constant__ pr_dr_window_desc desc) {
  pr_dr_window_evaluate<false>(desc, desc.batch.enabled_mask, blockIdx.x);
}

} // namespace airbender::gkr::proth120::backward
