#include "common.cuh"
#include "primitives/field.cuh"
#include "primitives/memory.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;

namespace airbender::whir {

constexpr unsigned TRACE_CHUNKS = 3;

struct BaseColumnsBatchingMetadata {
  const bf *values[TRACE_CHUNKS];
  const e4 *weights[TRACE_CHUNKS];
  const unsigned cols[TRACE_CHUNKS];
  const unsigned strides[TRACE_CHUNKS];
  e4 *result;
  const unsigned rows;
};

// Write the E4 result for folds and column-major BF limbs for the NTT in one pass.
EXTERN __global__ void ab_accumulate_whir_base_columns_with_serialized_bf_e4_kernel(const BaseColumnsBatchingMetadata metadata, bf *serialized_bf) {
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
  store<bf, st_modifier::cs>(serialized_bf, acc.base_coefficient_from_flat_idx(0), gid);
  store<bf, st_modifier::cs>(serialized_bf, acc.base_coefficient_from_flat_idx(1), rows + gid);
  store<bf, st_modifier::cs>(serialized_bf, acc.base_coefficient_from_flat_idx(2), 2 * rows + gid);
  store<bf, st_modifier::cs>(serialized_bf, acc.base_coefficient_from_flat_idx(3), 3 * rows + gid);
}

} // namespace airbender::whir
