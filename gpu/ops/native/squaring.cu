#include "common.cuh"
#include "primitives/field.cuh"

using namespace ::airbender::primitives::field;

namespace airbender::ops {

// Materializes [base^(2^0), base^(2^1), ..., base^(2^(count-1))] for E4.
// E.g. result[0] = base, result[1] = base^2, result[2] = base^4, etc.
// `count` is small (== log_n, typically <= 25), so we use a single-thread
// sequential loop — launch with grid=1, block=1.
EXTERN __global__ void ab_squaring_sequence_e4_kernel(const e4 *base, e4 *result, const unsigned count) {
  if (threadIdx.x != 0 || blockIdx.x != 0)
    return;
  if (count == 0)
    return;
  e4 value = *base;
  for (unsigned i = 0; i < count; ++i) {
    result[i] = value;
    value = e4::sqr(value);
  }
}

} // namespace airbender::ops
