#include "context.cuh"

namespace airbender::ntt {

[[maybe_unused]] __device__ void pr_context_header_instantiations(const proth120_twiddle_descriptor d, const u32 e, pr *out) {
  out[0] = pr_root_power(d, e);
  out[1] = pr_root_power_inv(d, e);
  out[2] = get_forward_pr_twiddle(d, e);
  out[3] = TWO_INV();
  pr leaf_0[1u << 0];
#pragma unroll
  for (u32 i = 0; i < (1u << 0); i++)
    leaf_0[i] = out[i];
  ab_pr_convert_leaf<0>(d, leaf_0, out[1]);
#pragma unroll
  for (u32 i = 0; i < (1u << 0); i++)
    out[i] = leaf_0[i];
  pr leaf_1[1u << 1];
#pragma unroll
  for (u32 i = 0; i < (1u << 1); i++)
    leaf_1[i] = out[i];
  ab_pr_convert_leaf<1>(d, leaf_1, out[1]);
#pragma unroll
  for (u32 i = 0; i < (1u << 1); i++)
    out[i] = leaf_1[i];
  pr leaf_2[1u << 2];
#pragma unroll
  for (u32 i = 0; i < (1u << 2); i++)
    leaf_2[i] = out[i];
  ab_pr_convert_leaf<2>(d, leaf_2, out[1]);
#pragma unroll
  for (u32 i = 0; i < (1u << 2); i++)
    out[i] = leaf_2[i];
  pr leaf_3[1u << 3];
#pragma unroll
  for (u32 i = 0; i < (1u << 3); i++)
    leaf_3[i] = out[i];
  ab_pr_convert_leaf<3>(d, leaf_3, out[1]);
#pragma unroll
  for (u32 i = 0; i < (1u << 3); i++)
    out[i] = leaf_3[i];
  pr leaf_4[1u << 4];
#pragma unroll
  for (u32 i = 0; i < (1u << 4); i++)
    leaf_4[i] = out[i];
  ab_pr_convert_leaf<4>(d, leaf_4, out[1]);
#pragma unroll
  for (u32 i = 0; i < (1u << 4); i++)
    out[i] = leaf_4[i];
}

} // namespace airbender::ntt
