#include "common.cuh"

namespace airbender::prover::gkr {

#define GKR_FORWARD_SETUP_KERNELS(arg_t)                                                                                                                       \
  EXTERN __global__ void ab_gkr_forward_setup_generic_lookup_##arg_t##_kernel(const __grid_constant__ gkr_forward_setup_generic_lookup_batch<arg_t> batch,     \
                                                                              const unsigned row_count) {                                                      \
    gkr_forward_setup_generic_lookup(batch, row_count);                                                                                                        \
  }

GKR_FORWARD_SETUP_KERNELS(e4);

} // namespace airbender::prover::gkr
