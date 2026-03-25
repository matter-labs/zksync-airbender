#include "../../common.cuh"
#include "../../primitives/field.cuh"
#include "../../primitives/memory.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;

namespace airbender::prover::whir {

DEVICE_FORCEINLINE unsigned bitreverse_low_bits(const unsigned value, const unsigned num_bits) { return __brev(value) >> (32 - num_bits); }

EXTERN __global__ void ab_pack_rows_for_whir_leaves_bf_kernel(const matrix_getter<bf, ld_modifier::cs> src, const matrix_setter<bf, st_modifier::cs> dst,
                                                              const unsigned log_values_per_leaf, const unsigned dst_rows_per_slot, const unsigned row_stride,
                                                              const unsigned row_offset, const unsigned src_cols) {
  const unsigned row = blockIdx.x * blockDim.x + threadIdx.x;
  if (row >= dst_rows_per_slot)
    return;
  const unsigned col = blockIdx.y * blockDim.y + threadIdx.y;
  const unsigned dst_cols = src_cols << log_values_per_leaf;
  if (col >= dst_cols)
    return;
  const unsigned value_slot = col / src_cols;
  const unsigned coeff_col = col % src_cols;
  const unsigned src_row = row + bitreverse_low_bits(value_slot, log_values_per_leaf) * dst_rows_per_slot;
  const unsigned dst_row = row * row_stride + row_offset;
  dst.set(dst_row, col, src.get(src_row, coeff_col));
}

} // namespace airbender::prover::whir
