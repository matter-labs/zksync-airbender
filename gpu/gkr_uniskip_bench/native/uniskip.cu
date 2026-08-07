#include "uniskip_abi.cuh"

namespace airbender::gkr_uniskip_bench {

// Scaffold kernel: keeps the archive non-empty and exercises the Rust<->CUDA build
// bridge until the init/LDE kernels land.
EXTERN __global__ void ab_gkr_uniskip_touch_kernel(u32 *out, const u32 count) {
  const u32 i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i < count)
    out[i] = i * UNISKIP_TAPS + UNISKIP_CELLS;
}

} // namespace airbender::gkr_uniskip_bench
