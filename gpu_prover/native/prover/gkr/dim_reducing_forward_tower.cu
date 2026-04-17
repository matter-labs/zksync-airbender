#include "common.cuh"

namespace airbender::prover::gkr {

#define GKR_DIM_REDUCING_FORWARD_TOWER_KERNELS(arg_t)                                                                                                          \
  EXTERN __global__ __launch_bounds__(GKR_DIM_REDUCING_FORWARD_TOWER_BLOCK, 4) void ab_gkr_dim_reducing_forward_tower_pairwise_##arg_t##_kernel(               \
      const __grid_constant__ gkr_dim_reducing_forward_tower_pairwise_batch<arg_t> batch) {                                                                    \
    gkr_dim_reducing_forward_tower_pairwise(batch);                                                                                                            \
  }                                                                                                                                                            \
  EXTERN __global__ __launch_bounds__(GKR_DIM_REDUCING_FORWARD_TOWER_BLOCK, 4) void ab_gkr_dim_reducing_forward_tower_lookup_##arg_t##_kernel(                 \
      const __grid_constant__ gkr_dim_reducing_forward_tower_lookup_batch<arg_t> batch) {                                                                      \
    gkr_dim_reducing_forward_tower_lookup(batch);                                                                                                              \
  }

GKR_DIM_REDUCING_FORWARD_TOWER_KERNELS(e4);

} // namespace airbender::prover::gkr
