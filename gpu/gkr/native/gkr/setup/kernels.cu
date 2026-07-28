#include "../support/lookup_helpers.cuh"

__device__ __constant__ e4 ab_gkr_lookup_alpha_powers[airbender::gkr::GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS];

namespace airbender::gkr::setup {

EXTERN __global__ void ab_gkr_forward_setup_generic_lookup_e4_kernel(const __grid_constant__ gkr_forward_setup_generic_lookup_batch<e4> batch,
                                                                     const unsigned row_count) {
  gkr_forward_setup_generic_lookup(batch, row_count);
}

} // namespace airbender::gkr::setup
