#include "../../common.cuh"
#include "../../primitives/field.cuh"
#include "../../primitives/memory.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;

namespace airbender::prover::whir {

DEVICE_FORCEINLINE unsigned bitreverse_low_bits(const unsigned value, const unsigned num_bits) { return __brev(value) >> (32 - num_bits); }

// Multi-coset pack: one launch handles `num_cosets_in_tile` independent cosets.
// `src` is the multi-coset NTT output -- coset-major outer (`coset_in_tile *
// src_cols_per_coset` advances to coset `coset_in_tile`'s column slab) and
// column-major inner. `dst` is the full packed_trace slab of total rows
// `dst_rows_per_slot << log_lde_factor`; coset `coset_global = coset_index_base
// + coset_in_tile` writes its `dst_rows_per_slot` rows at offset
// `bitreverse(coset_global, log_lde_factor) * dst_rows_per_slot`.
//
// `gridDim.x` packs (row_block, coset_in_tile) because `num_cosets_in_tile`
// scales to production schedules (~`2^19`), far exceeding the `gridDim.y/z`
// 65535 cap. `log_blocks_per_row_tile = log2(ceil(dst_rows_per_slot /
// blockDim.x))` is computed host-side; coset_in_tile occupies the high bits
// of `blockIdx.x`.
EXTERN __global__ void ab_pack_rows_for_whir_leaves_multi_coset_bf_kernel(const matrix_getter<bf, ld_modifier::cs> src,
                                                                          const matrix_setter<bf, st_modifier::cs> dst, const unsigned log_values_per_leaf,
                                                                          const unsigned dst_rows_per_slot, const unsigned log_blocks_per_row_tile,
                                                                          const unsigned log_lde_factor, const unsigned coset_index_base,
                                                                          const unsigned src_cols_per_coset) {
  const unsigned row_block = blockIdx.x & ((1u << log_blocks_per_row_tile) - 1u);
  const unsigned coset_in_tile = blockIdx.x >> log_blocks_per_row_tile;
  const unsigned row = row_block * blockDim.x + threadIdx.x;
  if (row >= dst_rows_per_slot)
    return;
  const unsigned col = blockIdx.y * blockDim.y + threadIdx.y;
  const unsigned dst_cols = src_cols_per_coset << log_values_per_leaf;
  if (col >= dst_cols)
    return;
  const unsigned coset_global = coset_index_base + coset_in_tile;
  const unsigned bitrev_coset = bitreverse_low_bits(coset_global, log_lde_factor);
  const unsigned value_slot = col / src_cols_per_coset;
  const unsigned coeff_col = col % src_cols_per_coset;
  const unsigned src_col_global = coset_in_tile * src_cols_per_coset + coeff_col;
  const unsigned src_row = row + bitreverse_low_bits(value_slot, log_values_per_leaf) * dst_rows_per_slot;
  const unsigned dst_row = row + bitrev_coset * dst_rows_per_slot;
  dst.set(dst_row, col, src.get(src_row, src_col_global));
}

} // namespace airbender::prover::whir
