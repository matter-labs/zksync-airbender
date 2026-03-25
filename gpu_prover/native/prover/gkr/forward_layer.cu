#include "common.cuh"

namespace airbender::prover::gkr {

#define GKR_FORWARD_LAYER_KERNELS(arg_t)                                                                                                                       \
  EXTERN __global__ void ab_gkr_forward_layer_##arg_t##_kernel(const __grid_constant__ gkr_forward_layer_batch<arg_t> batch, const unsigned count) {           \
    gkr_forward_layer(batch, count);                                                                                                                           \
  }

GKR_FORWARD_LAYER_KERNELS(e2);
GKR_FORWARD_LAYER_KERNELS(e4);
GKR_FORWARD_LAYER_KERNELS(e6);

} // namespace airbender::prover::gkr
