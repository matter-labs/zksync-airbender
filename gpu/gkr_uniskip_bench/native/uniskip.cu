#include "uniskip_abi.cuh"

// Storage for the `__constant__` symbols declared by uniskip_abi.cuh.
__device__ __constant__ e4 ab_gkr_uniskip_coeff_bank[airbender::gkr_uniskip_bench::UNISKIP_COEFF_BANK];
__device__ __constant__ e4 ab_gkr_uniskip_eq_high[2 * airbender::gkr_uniskip_bench::UNISKIP_EQ_HIGH];
__device__ __constant__ bf ab_gkr_uniskip_lde_matrix[airbender::gkr_uniskip_bench::UNISKIP_TAPS * airbender::gkr_uniskip_bench::UNISKIP_TAPS];
__device__ __constant__ e4 ab_gkr_uniskip_fold_weights[airbender::gkr_uniskip_bench::UNISKIP_TAPS];

namespace airbender::gkr_uniskip_bench {

// Type-check the source accessor for both field classes until the kernels of the
// LDE/eval passes instantiate it.
template __device__ bf uniskip_source_value<bf>(const uniskip_vm_desc &, u16, u32, u32);
template __device__ e4 uniskip_source_value<e4>(const uniskip_vm_desc &, u16, u32, u32);

// Scaffold kernel: keeps the archive non-empty and exercises the Rust<->CUDA build
// bridge until the init/LDE kernels land.
EXTERN __global__ void ab_gkr_uniskip_touch_kernel(u32 *out, const u32 count) {
  const u32 i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i < count)
    out[i] = i * UNISKIP_TAPS + UNISKIP_CELLS;
}

} // namespace airbender::gkr_uniskip_bench
