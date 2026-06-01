#include "../support/lookup_helpers.cuh"

namespace airbender::prover::gkr::forward {

EXTERN __global__ __launch_bounds__(GKR_DIM_REDUCING_FORWARD_TOWER_BLOCK, 4) void ab_gkr_dim_reducing_forward_tower_pairwise_e4_kernel(
    const __grid_constant__ gkr_dim_reducing_forward_tower_pairwise_batch<e4> batch) {
  gkr_dim_reducing_forward_tower_pairwise(batch);
}

EXTERN __global__ __launch_bounds__(GKR_DIM_REDUCING_FORWARD_TOWER_BLOCK, 4) void ab_gkr_dim_reducing_forward_tower_lookup_e4_kernel(
    const __grid_constant__ gkr_dim_reducing_forward_tower_lookup_batch<e4> batch) {
  gkr_dim_reducing_forward_tower_lookup(batch);
}

} // namespace airbender::prover::gkr::forward
