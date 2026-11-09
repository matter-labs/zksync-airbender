#include "main_tail.cuh"

EXTERN __global__ __launch_bounds__(airbender::gkr::proth120::backward::BWD_PR_MAIN_TAIL_BLOCK_THREADS, 1) void ab_pr_gkr_main_tail_kernel(
    const __grid_constant__ airbender::gkr::proth120::backward::bwd_pr_main_tail_desc desc,
    const __grid_constant__ airbender::gkr::proth120::backward::bwd_pr_main_tail_program_blob program_blob) {
  using namespace airbender::gkr::proth120::backward;
  if (!bwd_pr_main_tail_valid(desc, program_blob.bytes))
    return;
  bwd_pr_main_tail_execute(desc, program_blob.bytes);
}
