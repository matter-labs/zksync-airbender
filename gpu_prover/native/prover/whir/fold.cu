#include "../../common.cuh"
#include "../../primitives/field.cuh"
#include "../../primitives/memory.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;

namespace airbender::prover::whir {

EXTERN __global__ void ab_whir_fold_monomial_e4_kernel(const e4 *src, const e4 *challenge, e4 *dst, const unsigned half_len) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= half_len)
    return;

  const e4 c0 = load<e4, ld_modifier::cs>(src, 2 * gid);
  const e4 c1 = load<e4, ld_modifier::cs>(src, 2 * gid + 1);
  const e4 folded = e4::add(c0, e4::mul(c1, *challenge));
  store<e4, st_modifier::cs>(dst, folded, gid);
}

EXTERN __global__ void ab_whir_fold_split_half_e4_kernel(e4 *values, const e4 *challenge, const unsigned half_len) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= half_len)
    return;

  const e4 a = load<e4, ld_modifier::cs>(values, gid);
  const e4 b = load<e4, ld_modifier::cs>(values, half_len + gid);
  const e4 diff = e4::sub(b, a);
  const e4 folded = e4::add(a, e4::mul(*challenge, diff));
  store<e4, st_modifier::cs>(values, folded, gid);
}

} // namespace airbender::prover::whir
