// Optional diagnostic bank. The default production archive excludes this file.
#include "window_control.cuh"

namespace airbender::gkr::backward {

AB_GKR_BWD_WINDOW_DEFINE_KERNEL(ab_gkr_r0_diag_470_b3, 0x470, 3);
AB_GKR_BWD_WINDOW_DEFINE_KERNEL(ab_gkr_r0_diag_470_b4, 0x470, 4);
AB_GKR_BWD_WINDOW_DEFINE_KERNEL(ab_gkr_r0_diag_471_b3, 0x471, 3);
AB_GKR_BWD_WINDOW_DEFINE_KERNEL(ab_gkr_r0_diag_5f7_b3, 0x5f7, 3);
AB_GKR_BWD_WINDOW_DEFINE_KERNEL(ab_gkr_r0_diag_5f7_b4, 0x5f7, 4);
AB_GKR_BWD_WINDOW_DEFINE_KERNEL(ab_gkr_r0_diag_3f7_b3, 0x3f7, 3);
AB_GKR_BWD_WINDOW_DEFINE_KERNEL(ab_gkr_r0_diag_3f7_b4, 0x3f7, 4);
AB_GKR_BWD_WINDOW_DEFINE_KERNEL(ab_gkr_r0_diag_7ff_b3, 0x7ff, 3);
AB_GKR_BWD_WINDOW_DEFINE_KERNEL(ab_gkr_r0_diag_7ff_b4, 0x7ff, 4);
AB_GKR_BWD_WINDOW_DEFINE_KERNEL(ab_gkr_r0_diag_fff_b3, 0xfff, 3);

// Compare every raw field limb. The injected difference is a negative control
// for the comparison path and has its own result counter.
EXTERN __global__ void ab_gkr_r0_diag_compare(const u32 *expected, const u32 *actual, const u32 limbs, u32 *mismatches, const u32 inject) {
  const u32 i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i < limbs && expected[i] != (actual[i] ^ ((inject && i == 0) ? 1u : 0u)))
    atomicAdd(mismatches, 1u);
}

} // namespace airbender::gkr::backward
