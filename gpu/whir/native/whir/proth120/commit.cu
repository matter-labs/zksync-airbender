#include "common.cuh"
#include "keccak256.cuh"
#include "primitives/memory.cuh"
#include "primitives/proth120.cuh"
#include "proth120/context.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;
using ::airbender::hash::keccak256::digest;

namespace airbender::whir {

EXTERN __launch_bounds__(256) __global__
    void ab_pr_whir_place_roots_kernel(const digest *retained, const u64 retained_stride, const u32 log_lde, digest *roots) {
  const u64 coset = static_cast<u64>(blockIdx.x) * blockDim.x + threadIdx.x;
  if (coset >> log_lde)
    return;
  roots[bitreverse_low_bits(static_cast<u32>(coset), log_lde)] = retained[coset * retained_stride + retained_stride - 1];
}

} // namespace airbender::whir
