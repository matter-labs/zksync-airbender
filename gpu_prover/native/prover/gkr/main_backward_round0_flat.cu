#include "flat_backward.cuh"

__device__ __constant__ e4 ab_gkr_flat_round0_coefficients[airbender::prover::gkr::FLAT_ROUND0_CONST_MAX];

namespace airbender::prover::gkr {

// Phase C compact path: descriptor's source array holds packed `u16`s
// resolved through `tables.bases` / `tables.log2_stride` instead of raw
// `*const u8` pointers.
EXTERN __launch_bounds__(128, 8) __global__
    void ab_gkr_main_round0_flat_compact_e4_kernel(const __grid_constant__ flat_round0_static_desc_compact static_desc, const e4 *coefficients,
                                                   const e4 *eq_values, e4 *contributions, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;
  flat_round0_compute_compact(static_desc, coefficients, eq_values, contributions, acc_size, gid);
}

EXTERN __launch_bounds__(128, 8) __global__
    void ab_gkr_main_round0_flat_constant_compact_e4_kernel(const __grid_constant__ flat_round0_static_desc_compact static_desc, const e4 *eq_values,
                                                            e4 *contributions, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;
  flat_round0_compute_constant_compact(static_desc, eq_values, contributions, acc_size, gid);
}

} // namespace airbender::prover::gkr
