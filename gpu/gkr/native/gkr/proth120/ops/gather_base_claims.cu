#include "primitives/proth120.cuh"
namespace airbender::gkr::proth120::ops {
using pr = ::airbender::primitives::field::proth120;
struct dense_claim_indices {
  u32 indices[106];
};
static_assert(sizeof(dense_claim_indices) == 424);
struct gather_arguments {
  const pr *claims;
  dense_claim_indices indices;
  pr *out;
  u32 count;
};
static_assert(sizeof(gather_arguments) == 448);
static_assert(sizeof(gather_arguments) <= 32764);
static_assert(offsetof(gather_arguments, count) == 440);
EXTERN __global__ void ab_pr_gkr_gather_base_claims_kernel(const pr *claims, const __grid_constant__ dense_claim_indices indices, pr *out, u32 count) {
  const u32 index = blockIdx.x * blockDim.x + threadIdx.x;
  if (index < count)
    out[index] = claims[indices.indices[index]];
}
} // namespace airbender::gkr::proth120::ops
