#include "primitives/proth120.cuh"
namespace airbender::gkr::proth120::ops {
using pr = ::airbender::primitives::field::proth120;
struct gather_arguments {
  const pr *claims;
  const u32 *indices;
  pr *out;
  u32 count;
};
static_assert(sizeof(gather_arguments) == 32);
static_assert(offsetof(gather_arguments, count) == 24);
EXTERN __global__ void ab_pr_gkr_gather_base_claims_kernel(const pr *claims, const u32 *indices, pr *out, u32 count) {
  const u32 index = blockIdx.x * blockDim.x + threadIdx.x;
  if (index < count)
    out[index] = claims[indices[index]];
}
} // namespace airbender::gkr::proth120::ops
