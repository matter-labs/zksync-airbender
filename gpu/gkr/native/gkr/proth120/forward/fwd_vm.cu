#include "eval_vm_exec_pr.cuh"
namespace airbender::gkr::proth120::forward {
#if __CUDA_ARCH__ == 800
constexpr u32 PR_FWD_VM_MIN_BLOCKS = 6;
#else
constexpr u32 PR_FWD_VM_MIN_BLOCKS = 11;
#endif
EXTERN __launch_bounds__(128, PR_FWD_VM_MIN_BLOCKS) __global__ void ab_pr_gkr_fwd_vm_kernel(const __grid_constant__ fwd_vm_desc_pr desc) {
  fwd_vm_pr<PR_FWD_VM_BUCKETS>(desc);
}
} // namespace airbender::gkr::proth120::forward
