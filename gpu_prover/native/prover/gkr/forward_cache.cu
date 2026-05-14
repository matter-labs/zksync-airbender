#include "lookup_helpers.cuh"

namespace airbender::prover::gkr {

#define GKR_FORWARD_CACHE_KERNELS(arg_t)                                                                                                                       \
  EXTERN __global__ void ab_gkr_forward_cache_##arg_t##_kernel(const __grid_constant__ gkr_forward_cache_batch<arg_t> batch, const unsigned trace_len) {       \
    gkr_forward_cache(batch, trace_len);                                                                                                                       \
  }

GKR_FORWARD_CACHE_KERNELS(e4);

#define GKR_VIRTUAL_BASE_ACCUM_KERNELS(arg_t)                                                                                                                  \
  EXTERN __global__ void ab_gkr_virtual_base_accum_##arg_t##_kernel(const gkr_base_source_kind source_kind, const arg_t scalar, arg_t *dst,                    \
                                                                    const unsigned count) {                                                                    \
    const unsigned gid = static_cast<unsigned>(blockIdx.x) * blockDim.x + threadIdx.x;                                                                         \
    if (gid >= count)                                                                                                                                          \
      return;                                                                                                                                                  \
    arg_t value = load<arg_t, ld_modifier::cs>(dst, gid);                                                                                                      \
    value = arg_t::fma(scalar, gkr_virtual_base_value(source_kind, gid), value);                                                                               \
    store<arg_t, st_modifier::cs>(dst, value, gid);                                                                                                            \
  }

GKR_VIRTUAL_BASE_ACCUM_KERNELS(e4);

} // namespace airbender::prover::gkr
