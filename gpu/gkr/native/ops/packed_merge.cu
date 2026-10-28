#include "../gkr/support/descriptors.cuh"

namespace airbender::gkr::ops {

// Consecutive claims are the high-coordinate slots of one packed polynomial.
// Each warp owns a group; unused lanes and incomplete tail slots stay zero.
EXTERN __global__ void ab_gkr_merge_claims_e4_kernel(const e4 *claims, u32 count, const e4 *coordinates, u32 pack_log2, e4 *merged) {
  if (pack_log2 < 1 || pack_log2 > 4)
    __trap();
  const u32 width = 1u << pack_log2;
  const u32 group = (blockIdx.x * blockDim.x + threadIdx.x) / 32;
  const u32 lane = threadIdx.x % 32;
  if (group >= count / width + (count % width != 0))
    return;
  const u32 index = group * width + lane;
  e4 value = lane < width && index < count ? claims[index] : e4::ZERO();
  for (u32 round = 0; round < pack_log2; ++round) {
    bf limbs[4];
#pragma unroll
    for (u32 limb = 0; limb < 4; ++limb)
      limbs[limb] = bf(shfl_xor<u32>(0xffffffffu, value.base_coefficient_from_flat_idx(limb).limb, 1 << round));
    const e4 other(limbs);
    if (lane < width && (lane & ((1u << (round + 1)) - 1)) == 0)
      value = e4::add(value, e4::mul(e4::sub(other, value), coordinates[round]));
  }
  if (lane == 0)
    merged[group] = value;
}

} // namespace airbender::gkr::ops
