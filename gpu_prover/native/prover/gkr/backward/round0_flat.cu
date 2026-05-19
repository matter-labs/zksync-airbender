#include "flat.cuh"

namespace airbender::prover::gkr::backward {

// Compact path: descriptor's source array holds packed `u16`s resolved
// through `tables.bases` / `tables.log2_stride` instead of raw
// `*const u8` pointers.
EXTERN __launch_bounds__(128, 8) __global__
    void ab_gkr_main_round0_flat_compact_e4_kernel(const __grid_constant__ flat_round0_static_desc_compact static_desc, const e4 *coefficients,
                                                   const e4 *eq_high_groups, const e4 *eq_low_buffer, const __grid_constant__ gkr_eq_layout_compact eq_layout,
                                                   e4 *contributions, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;
  flat_round0_compute_compact(static_desc, coefficients, eq_high_groups, eq_low_buffer, eq_layout, contributions, acc_size, gid);
}

EXTERN __launch_bounds__(128, 8) __global__
    void ab_gkr_main_round0_flat_constant_compact_e4_kernel(const __grid_constant__ flat_round0_static_desc_compact static_desc, const e4 *eq_high_groups,
                                                            const e4 *eq_low_buffer, const __grid_constant__ gkr_eq_layout_compact eq_layout, e4 *contributions,
                                                            const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;
  flat_round0_compute_constant_compact(static_desc, eq_high_groups, eq_low_buffer, eq_layout, contributions, acc_size, gid);
}

} // namespace airbender::prover::gkr::backward
