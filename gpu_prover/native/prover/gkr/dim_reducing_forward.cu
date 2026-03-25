#include "common.cuh"

namespace airbender::prover::gkr {

#define GKR_DIM_REDUCING_FORWARD_KERNELS(arg_t)                                                                                                                \
  EXTERN __global__ void ab_gkr_dim_reducing_forward_##arg_t##_kernel(const __grid_constant__ gkr_dim_reducing_forward_batch<arg_t> batch,                     \
                                                                      const unsigned row_count) {                                                              \
    gkr_dim_reducing_forward(batch, row_count);                                                                                                                \
  }

GKR_DIM_REDUCING_FORWARD_KERNELS(e2);
GKR_DIM_REDUCING_FORWARD_KERNELS(e4);
GKR_DIM_REDUCING_FORWARD_KERNELS(e6);

} // namespace airbender::prover::gkr
