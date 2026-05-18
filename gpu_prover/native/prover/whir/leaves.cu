#include "../../common.cuh"
#include "../../primitives/field.cuh"
#include "../../primitives/memory.cuh"
#include "../../primitives/vectorized.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;
using namespace ::airbender::primitives::vectorized;

namespace airbender::prover::whir {

DEVICE_FORCEINLINE unsigned bitreverse_low_bits(const unsigned value, const unsigned num_bits) { return __brev(value) >> (32 - num_bits); }

EXTERN __global__ void ab_pack_rows_for_whir_leaves_bf_kernel(vectorized_e4_matrix_getter<ld_modifier::cs> src,
                                                              vectorized_e4_matrix_setter<st_modifier::cs> dst,
                                                              const unsigned log_trace_len,
                                                              const unsigned log_blocks_per_coset,
                                                              const unsigned log_values_per_leaf,
                                                              const unsigned dst_rows_per_coset) {
  const unsigned coset = blockIdx.x >> log_blocks_per_coset;
  const unsigned block_in_coset_mask = (1 << log_blocks_per_coset) - 1;
  const unsigned block_in_coset = blockIdx.x & block_in_coset_mask;

  src.add_row(coset << log_trace_len);
  dst.add_row(coset << (log_trace_len - log_values_per_leaf));

  const unsigned dst_row = block_in_coset * blockDim.x + threadIdx.x;
  if (dst_row >= dst_rows_per_coset)
    return;

  dst.add_row(dst_row);

  // extern __shared__ e4 smem[];
  // e4 *smem_warp = smem + 64 * threadIdx.y;

  unsigned dst_slot_in_leaf = 2 * threadIdx.y;
  unsigned src_row = dst_row + bitreverse_low_bits(dst_slot_in_leaf, log_values_per_leaf) * dst_rows_per_coset;
  for (; dst_slot_in_leaf < 2 * threadIdx.y + 2; dst_slot_in_leaf++, src_row += dst_rows_per_coset << (log_values_per_leaf - 1)) {
    const e4 val = src.get_at_row(src_row);
    dst.set_at_col(dst_slot_in_leaf, val);
  }
}

} // namespace airbender::prover::whir
