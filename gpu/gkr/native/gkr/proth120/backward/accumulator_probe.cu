#include "accumulator_pr.cuh"

namespace airbender::gkr::proth120::backward {

EXTERN __global__ void ab_pr_gkr_sum32_probe_kernel(const pr *values, const u32 *segment_offsets, const u32 segment_count, pr *sums) {
  const u32 segment = blockIdx.x * blockDim.x + threadIdx.x;
  if (segment >= segment_count)
    return;
  PrSum32 chunk = PrSum32::zero();
  pr total = pr::ZERO();
  for (u32 i = segment_offsets[segment]; i < segment_offsets[segment + 1]; i++) {
    if (chunk.full())
      total = pr::add(total, chunk.flush());
    chunk.add(values[i]);
  }
  sums[segment] = pr::add(total, chunk.flush());
}

} // namespace airbender::gkr::proth120::backward
