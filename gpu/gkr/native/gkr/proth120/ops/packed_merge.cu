#include "primitives/proth120.cuh"
namespace airbender::gkr::proth120::ops {
using namespace ::airbender::primitives;
using pr = field::proth120;
struct merge_arguments {
  const pr *claims;
  u32 count;
  const pr *extra;
  u32 pack_log2;
  pr *merged;
};
static_assert(sizeof(merge_arguments) == 40);
static_assert(offsetof(merge_arguments, extra) == 16);
static_assert(offsetof(merge_arguments, merged) == 32);
EXTERN __global__ void ab_pr_gkr_merge_claims_kernel(const pr *claims, u32 count, const pr *extra, u32 pack_log2, pr *merged) {
  const u32 group = (blockIdx.x * blockDim.x + threadIdx.x) / 32;
  const u32 lane = threadIdx.x % 32;
  if (pack_log2 != 4 || group >= count / 16 + (count % 16 != 0))
    return;
  const u32 index = group * 16 + lane;
  pr value = lane < 16 && index < count ? claims[index] : pr::ZERO();
#pragma unroll
  for (u32 round = 0; round < 4; ++round) {
    const pr other = memory::shfl_xor<pr>(0xffffffffu, value, 1 << round);
    if (lane < 16 && (lane & ((1u << (round + 1)) - 1)) == 0)
      value = pr::add(value, pr::mul(pr::sub(other, value), extra[round]));
  }
  if (lane == 0)
    merged[group] = value;
}
} // namespace airbender::gkr::proth120::ops
