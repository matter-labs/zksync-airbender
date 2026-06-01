#include "common.cuh"
#include "hash.cuh"
#include "primitives/field.cuh"
#include "primitives/memory.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;
using ::airbender::ops::blake2s::bitreverse_low_bits;
using ::airbender::ops::blake2s::BLOCK_SIZE;
using ::airbender::ops::blake2s::compress;
using ::airbender::ops::blake2s::digest;
using ::airbender::ops::blake2s::initialize;
using ::airbender::ops::blake2s::STATE_SIZE;

namespace airbender::prover::whir {

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

// Fused leaves-from-NTT kernel: reads the natural multi-coset NTT output and
// emits leaf digests at the same flat-tree positions pack+blake produce today,
// eliminating the pack-then-blake DRAM round-trip.
//
// `ntt_output` logical shape: rows = `trace_len`, cols = `lde_factor *
// src_cols_per_coset`; coset-major outer (col / src_cols_per_coset =
// coset_in_tile), column-major within coset. Address:
// `ntt_output[src_row + src_col * trace_len]`.
//
// `results` is the flat tree backing for the WHIR oracle (TraceHolder
// `log_lde_factor = 0`); digest at flat-tree leaf `idx` lives at
// `results[idx * STATE_SIZE]`.
//
// Output position derivation: pack writes the natural-coset `coset_in_tile`'s
// rows at `bitrev(coset_global, log_lde_factor) * per_coset_count` of the
// packed cosets backing; the existing blake-leaves kernel then hashes flat
// row `dst_row` and stores at `dst_row * STATE_SIZE`. This kernel inlines the
// source-side index math into `read()` and computes `dst_leaf_idx` directly.
EXTERN __global__ void ab_blake2s_leaves_from_ntt_multi_coset_kernel(const bf *ntt_output, u32 *results, const unsigned log_values_per_leaf,
                                                                     const unsigned src_cols_per_coset, const unsigned log_lde_factor,
                                                                     const unsigned coset_index_base, const unsigned per_coset_count,
                                                                     const unsigned log_per_coset_count, const unsigned trace_len, const unsigned count) {
  const unsigned gid_global = threadIdx.x + blockIdx.x * blockDim.x;
  if (gid_global >= count)
    return;

  const unsigned coset_in_tile = gid_global >> log_per_coset_count;
  const unsigned leaf_in_coset = gid_global & (per_coset_count - 1u);
  const unsigned coset_global = coset_index_base + coset_in_tile;
  const unsigned bitrev_coset = bitreverse_low_bits(coset_global, log_lde_factor);

  const unsigned dst_leaf_idx = leaf_in_coset + bitrev_coset * per_coset_count;
  digest *results_d = reinterpret_cast<digest *>(results) + dst_leaf_idx;

  const unsigned cols_count = src_cols_per_coset << log_values_per_leaf;
  const unsigned values_per_leaf = 1u << log_values_per_leaf;
  const unsigned col_mask = src_cols_per_coset - 1u;
  const unsigned log_src_cols_per_coset = __ffs(src_cols_per_coset) - 1u;

  auto read = [=](const unsigned offset) -> u32 {
    const unsigned col_in_leaf = offset & col_mask;               // FAST (low log_src_cols_per_coset bits)
    const unsigned value_slot = offset >> log_src_cols_per_coset; // SLOW (high log_values_per_leaf bits)
    if (value_slot >= values_per_leaf)
      return 0;
    const unsigned src_row = leaf_in_coset + bitreverse_low_bits(value_slot, log_values_per_leaf) * per_coset_count;
    const unsigned src_col_global = coset_in_tile * src_cols_per_coset + col_in_leaf;
    return bf::into_raw_u32(load_cs(ntt_output + src_row + static_cast<size_t>(src_col_global) * trace_len));
  };

  digest state;
  u32 block[BLOCK_SIZE];
  initialize(state.words);
  u32 t = 0;
  const unsigned values_count = cols_count;
  unsigned offset = 0;
  while (offset < values_count) {
    const unsigned remaining = values_count - offset;
    const bool is_final_block = remaining <= BLOCK_SIZE;
#pragma unroll
    for (unsigned i = 0; i < BLOCK_SIZE; i++, offset++)
      block[i] = read(offset);
    if (is_final_block)
      compress<true>(state.words, t, block, remaining);
    else
      compress<false>(state.words, t, block, BLOCK_SIZE);
  }
  store_cs(results_d, state);
}

} // namespace airbender::prover::whir
