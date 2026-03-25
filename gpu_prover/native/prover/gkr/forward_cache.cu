#include "common.cuh"

namespace airbender::prover::gkr {

#define GKR_FORWARD_CACHE_KERNELS(arg_t)                                                                                                                       \
  EXTERN __global__ void ab_gkr_forward_cache_##arg_t##_kernel(const __grid_constant__ gkr_forward_cache_batch<arg_t> batch, const unsigned trace_len) {       \
    gkr_forward_cache(batch, trace_len);                                                                                                                       \
  }

GKR_FORWARD_CACHE_KERNELS(e2);
GKR_FORWARD_CACHE_KERNELS(e4);
GKR_FORWARD_CACHE_KERNELS(e6);

} // namespace airbender::prover::gkr
