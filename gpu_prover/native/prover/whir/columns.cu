#include "../../common.cuh"
#include "../../primitives/field.cuh"
#include "../../primitives/memory.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;

namespace airbender::prover::whir {

EXTERN __global__ void ab_serialize_whir_e4_columns_kernel(const e4 *src, bf *dst, const unsigned count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;

  const e4 value = load<e4, ld_modifier::cs>(src, gid);
  store<bf, st_modifier::cs>(dst, value.base_coefficient_from_flat_idx(0), gid);
  store<bf, st_modifier::cs>(dst, value.base_coefficient_from_flat_idx(1), count + gid);
  store<bf, st_modifier::cs>(dst, value.base_coefficient_from_flat_idx(2), 2 * count + gid);
  store<bf, st_modifier::cs>(dst, value.base_coefficient_from_flat_idx(3), 3 * count + gid);
}

EXTERN __global__ void ab_deserialize_whir_e4_columns_kernel(const bf *src, e4 *dst, const unsigned count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;

  const bf coeffs[4] = {
      load<bf, ld_modifier::cs>(src, gid),
      load<bf, ld_modifier::cs>(src, count + gid),
      load<bf, ld_modifier::cs>(src, 2 * count + gid),
      load<bf, ld_modifier::cs>(src, 3 * count + gid),
  };
  store<e4, st_modifier::cs>(dst, e4(coeffs), gid);
}

constexpr unsigned TRACE_CHUNKS = 3;

struct BaseColumnsBatchingMetadata {
  const bf *values[TRACE_CHUNKS];
  const e4 *weights[TRACE_CHUNKS];
  const unsigned cols[TRACE_CHUNKS];
  const unsigned strides[TRACE_CHUNKS];
  e4 *result;
  const unsigned rows;
};

EXTERN __global__ void ab_accumulate_whir_base_columns_e4_kernel(const BaseColumnsBatchingMetadata metadata) {
  const unsigned rows = metadata.rows;
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= rows)
    return;

  e4 acc{e4::ZERO()};
  for (unsigned i = 0; i < TRACE_CHUNKS; i++) {
    const bf *values = metadata.values[i];
    const e4 *weights = metadata.weights[i];
    const unsigned cols = metadata.cols[i];
    const unsigned stride = metadata.strides[i];
    for (unsigned col = 0; col < cols; ++col) {
      const bf value = load<bf, ld_modifier::cs>(values, col * stride + gid);
      const e4 weight = load<e4, ld_modifier::cs>(weights, col);
      acc = e4::fma(weight, value, acc);
    }
  }

  store<e4, st_modifier::cs>(metadata.result, acc, gid);
}

} // namespace airbender::prover::whir
