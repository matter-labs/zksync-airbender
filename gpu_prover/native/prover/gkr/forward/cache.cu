#include "../support/lookup_helpers.cuh"

namespace airbender::prover::gkr::forward {

EXTERN __global__ void ab_gkr_forward_cache_e4_kernel(const __grid_constant__ gkr_forward_cache_batch<e4> batch, const unsigned trace_len) {
  gkr_forward_cache(batch, trace_len);
}

EXTERN __global__ void ab_gkr_virtual_base_accum_e4_kernel(const gkr_base_source_kind source_kind, const e4 scalar, e4 *dst, const unsigned count) {
  const unsigned gid = static_cast<unsigned>(blockIdx.x) * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;
  e4 value = load<e4, ld_modifier::cs>(dst, gid);
  value = e4::fma(scalar, gkr_virtual_base_value(source_kind, gid), value);
  store<e4, st_modifier::cs>(dst, value, gid);
}

} // namespace airbender::prover::gkr::forward
