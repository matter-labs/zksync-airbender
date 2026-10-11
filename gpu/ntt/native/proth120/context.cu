#include "context.cuh"

namespace airbender::ntt {

[[maybe_unused]] __device__ void pr_context_header_instantiations(const proth120_twiddle_descriptor d, const u32 e, pr *out) {
  out[0] = pr_root_power(d, e);
  out[1] = pr_root_power_inv(d, e);
  out[2] = get_forward_pr_twiddle(d, e);
  out[3] = TWO_INV();
}

} // namespace airbender::ntt
