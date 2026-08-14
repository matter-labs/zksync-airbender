#include "../support/lookup_helpers.cuh"

namespace airbender::gkr::forward {

EXTERN __global__ __launch_bounds__(GKR_DIM_REDUCING_FORWARD_TOWER_BLOCK, 4) void ab_gkr_dim_reducing_forward_tower_e4_kernel(
    const __grid_constant__ gkr_dim_reducing_forward_tower_batch<e4> batch) {
  gkr_dim_reducing_forward_tower(batch);
}

} // namespace airbender::gkr::forward
