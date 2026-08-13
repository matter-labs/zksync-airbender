#include <common.cuh>
#include <hash.cuh>
#include <primitives/field.cuh>
#include <primitives/memory.cuh>
#include <primitives/vectorized.cuh>
#include <whir_leaf_transform.cuh>

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;
using namespace ::airbender::primitives::vectorized;
using ::airbender::hash::bitreverse_low_bits;

namespace airbender::whir {

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

struct query_leaf_destination {
  static constexpr bool ALIASES_VALUES_SMEM = false;

  bf *dst;
  unsigned query_slot;
  unsigned log_values_per_leaf;
  bool enabled;

  DEVICE_FORCEINLINE void set_at_slot(const unsigned transform_slot, const e4 value) {
    if (!enabled)
      return;
    // Match the committed leaf reader's bit-reversed value-slot order.
    const unsigned output_slot = bitreverse_low_bits(transform_slot, log_values_per_leaf);
    bf *output = dst + ((size_t)query_slot << (log_values_per_leaf + 2)) + (output_slot << 2);
#pragma unroll
    for (unsigned coeff = 0; coeff < 4; coeff++)
      output[coeff] = value.base_coefficient_from_flat_idx(coeff);
  }
};

struct shared_query_leaf_destination {
  static constexpr bool ALIASES_VALUES_SMEM = true;

  e4 *values;
  unsigned log_values_per_leaf;

  DEVICE_FORCEINLINE void set_at_slot(const unsigned transform_slot, const e4 value) {
    const unsigned output_slot = bitreverse_low_bits(transform_slot, log_values_per_leaf);
    values[output_slot * blockDim.x + threadIdx.x] = value;
  }
};

EXTERN __launch_bounds__(512, 2) __global__
    void ab_gather_coefficient_leaves_for_queries_from_ntt_kernel(vectorized_e4_matrix_getter<ld_modifier::cs> ntt_output, bf *slab_dst,
                                                                  const ::airbender::ntt::whir_leaf_transform_params transform_params,
                                                                  const unsigned log_trace_len, const unsigned log_lde_factor,
                                                                  const unsigned log_values_per_leaf, const unsigned *query_indexes,
                                                                  const unsigned indexes_count) {
  const unsigned query_slot = blockIdx.x * blockDim.x + threadIdx.x;
  // The transform contains block-wide barriers. Inactive x lanes therefore
  // transform a valid leaf and suppress their stores instead of returning.
  const bool enabled = query_slot < indexes_count;
  const unsigned safe_query_slot = enabled ? query_slot : indexes_count - 1;
  const unsigned q = query_indexes[safe_query_slot];
  const unsigned log_packed_leaf_count = log_trace_len - log_values_per_leaf;
  const unsigned packed_leaf_count = 1u << log_packed_leaf_count;
  const unsigned input_row = q & (packed_leaf_count - 1u);
  const unsigned bitrev_coset = q >> log_packed_leaf_count;
  const unsigned natural_coset = bitreverse_low_bits(bitrev_coset, log_lde_factor);

  ntt_output.add_col(natural_coset);
  ntt_output.add_row(input_row);

  extern __shared__ __align__(16) uint8_t smem[];
  e4 *values_smem = reinterpret_cast<e4 *>(smem);
  bf *x_invs_smem = reinterpret_cast<bf *>(values_smem + 2 * blockDim.x * blockDim.y);
  query_leaf_destination destination{slab_dst, query_slot, log_values_per_leaf, enabled};
  const ::airbender::ntt::params_inverse_power_source inverse_power_source{transform_params};
  ::airbender::ntt::transform_whir_leaf_from_ntt(ntt_output, destination, log_trace_len, log_lde_factor, log_values_per_leaf, natural_coset, input_row,
                                                 values_smem, x_invs_smem, transform_params.two_inv_power, inverse_power_source);
}

// Partial-cache query path: transform the 32-leaf subtree containing each
// query, retain only those coefficient leaves in shared memory, hash the five
// omitted Merkle layers warp-cooperatively, then walk the cached upper tree.
EXTERN __launch_bounds__(512, 2) __global__ void ab_gather_coefficient_leaves_and_merkle_paths_partial_for_queries_from_ntt_kernel(
    vectorized_e4_matrix_getter<ld_modifier::cs> ntt_output, const u32 *partial_tree, bf *leaf_dst, u32 *path_dst,
    const ::airbender::ntt::whir_leaf_transform_params transform_params, const unsigned log_trace_len, const unsigned log_lde_factor,
    const unsigned log_values_per_leaf, const unsigned log_total_leaves_count, const unsigned layers_count, const unsigned *query_indexes,
    const unsigned indexes_count) {
  const unsigned query_slot = blockIdx.x;
  if (query_slot >= indexes_count)
    return;

  const unsigned q = query_indexes[query_slot];
  const unsigned lane_idx = threadIdx.x;
  const unsigned subtree_leaf = (q & ~::airbender::hash::WARP_MASK) | lane_idx;
  const unsigned log_packed_leaf_count = log_trace_len - log_values_per_leaf;
  const unsigned packed_leaf_count = 1u << log_packed_leaf_count;
  const unsigned input_row = subtree_leaf & (packed_leaf_count - 1u);
  const unsigned bitrev_coset = subtree_leaf >> log_packed_leaf_count;
  const unsigned natural_coset = bitreverse_low_bits(bitrev_coset, log_lde_factor);

  ntt_output.add_col(natural_coset);
  ntt_output.add_row(input_row);

  extern __shared__ __align__(16) uint8_t smem[];
  e4 *coefficient_leaves = reinterpret_cast<e4 *>(smem);
  bf *x_invs_smem = reinterpret_cast<bf *>(coefficient_leaves + (blockDim.x << log_values_per_leaf));
  shared_query_leaf_destination destination{coefficient_leaves, log_values_per_leaf};
  const ::airbender::ntt::params_inverse_power_source inverse_power_source{transform_params};
  ::airbender::ntt::transform_whir_leaf_from_ntt(ntt_output, destination, log_trace_len, log_lde_factor, log_values_per_leaf, natural_coset, input_row,
                                                 coefficient_leaves, x_invs_smem, transform_params.two_inv_power, inverse_power_source);
  __syncthreads();

  if (threadIdx.y != 0)
    return;

  const bool is_output_lane = subtree_leaf == q;
  if (is_output_lane) {
    bf *output = leaf_dst + ((size_t)query_slot << (log_values_per_leaf + 2));
    for (unsigned value_slot = 0; value_slot < (1u << log_values_per_leaf); value_slot++) {
      const e4 value = coefficient_leaves[value_slot * blockDim.x + lane_idx];
#pragma unroll
      for (unsigned coeff = 0; coeff < 4; coeff++)
        output[(value_slot << 2) + coeff] = value.base_coefficient_from_flat_idx(coeff);
    }
  }

  auto read_e4 = [=](const unsigned value_slot) -> e4 { return coefficient_leaves[value_slot * blockDim.x + lane_idx]; };
  u32 state[::airbender::hash::STATE_SIZE];
  ::airbender::hash::initialize(state);
  u32 t = 0;
  ::airbender::hash::absorb_e4_stream(state, t, 1u << log_values_per_leaf, read_e4);
  u32 *merkle_paths = path_dst + query_slot * layers_count * ::airbender::hash::STATE_SIZE;
  ::airbender::hash::collect_merkle_path_warp(state, merkle_paths, ::airbender::hash::STATE_SIZE, lane_idx, is_output_lane, q, log_total_leaves_count,
                                              layers_count, partial_tree);
}

constexpr unsigned bitreverse_low_bits_constant(unsigned value, const unsigned bits) {
  unsigned result = 0;
  for (unsigned i = 0; i < bits; i++) {
    result = (result << 1) | (value & 1);
    value >>= 1;
  }
  return result;
}

template <unsigned BLOCK_INDEX, unsigned VALUE_IN_BLOCK = 0>
DEVICE_FORCEINLINE void write_whir_leaf_two_limb_hash_block(const bf (&values)[2][32], u32 (&hash_block_smem)[16][32]) {
  constexpr unsigned output_slot = 4 * BLOCK_INDEX + VALUE_IN_BLOCK;
  constexpr unsigned transform_slot = bitreverse_low_bits_constant(output_slot, 5);
  const unsigned word = 4 * VALUE_IN_BLOCK + 2 * threadIdx.y;
  hash_block_smem[word][threadIdx.x] = bf::into_raw_u32(values[0][transform_slot]);
  hash_block_smem[word + 1][threadIdx.x] = bf::into_raw_u32(values[1][transform_slot]);
  if constexpr (VALUE_IN_BLOCK + 1 < 4)
    write_whir_leaf_two_limb_hash_block<BLOCK_INDEX, VALUE_IN_BLOCK + 1>(values, hash_block_smem);
}

template <unsigned WORD = 0> DEVICE_FORCEINLINE void load_whir_leaf_hash_block(const u32 (&hash_block_smem)[16][32], u32 (&block)[16]) {
  block[WORD] = hash_block_smem[WORD][threadIdx.x];
  if constexpr (WORD + 1 < 16)
    load_whir_leaf_hash_block<WORD + 1>(hash_block_smem, block);
}

DEVICE_FORCEINLINE void write_whir_leaf_two_limb_hash_block(const unsigned block_idx, const bf (&values)[2][32], u32 (&hash_block_smem)[16][32]) {
  switch (block_idx) {
  case 0:
    write_whir_leaf_two_limb_hash_block<0>(values, hash_block_smem);
    break;
  case 1:
    write_whir_leaf_two_limb_hash_block<1>(values, hash_block_smem);
    break;
  case 2:
    write_whir_leaf_two_limb_hash_block<2>(values, hash_block_smem);
    break;
  case 3:
    write_whir_leaf_two_limb_hash_block<3>(values, hash_block_smem);
    break;
  case 4:
    write_whir_leaf_two_limb_hash_block<4>(values, hash_block_smem);
    break;
  case 5:
    write_whir_leaf_two_limb_hash_block<5>(values, hash_block_smem);
    break;
  case 6:
    write_whir_leaf_two_limb_hash_block<6>(values, hash_block_smem);
    break;
  case 7:
    write_whir_leaf_two_limb_hash_block<7>(values, hash_block_smem);
    break;
  }
}

DEVICE_FORCEINLINE void transform_and_hash_whir_leaf_register_v32_two_limb(vectorized_e4_matrix_getter<ld_modifier::cs> ntt_output,
                                                                           const ::airbender::ntt::whir_leaf_transform_params transform_params,
                                                                           const unsigned log_trace_len, const unsigned log_lde_factor,
                                                                           const unsigned natural_coset, const unsigned leaf_in_coset,
                                                                           u32 (&hash_block_smem)[16][32], ::airbender::hash::digest &state) {
  auto src0 = ntt_output.internal;
  src0.add_col(2 * threadIdx.y);
  auto src1 = src0;
  src1.add_col(1);
  bf values[2][32];
  const ::airbender::ntt::params_inverse_power_source inverse_power_source{transform_params};
  ::airbender::ntt::transform_whir_leaf_two_limbs_from_ntt_registers<5>(src0, src1, log_trace_len, log_lde_factor, natural_coset, leaf_in_coset, values,
                                                                        transform_params.two_inv_power, inverse_power_source);

  if (threadIdx.y == 0)
    ::airbender::hash::initialize(state.words);
  u32 t = 0;
#pragma unroll 1
  for (unsigned block_idx = 0; block_idx < 8; block_idx++) {
    write_whir_leaf_two_limb_hash_block(block_idx, values, hash_block_smem);
    __syncthreads();
    if (threadIdx.y == 0) {
      u32 block[16];
      load_whir_leaf_hash_block(hash_block_smem, block);
      if (block_idx + 1 == 8)
        ::airbender::hash::compress<true>(state.words, t, block, 16);
      else
        ::airbender::hash::compress<false>(state.words, t, block, 16);
    }
    __syncthreads();
  }
}

EXTERN __launch_bounds__(64) __global__ void ab_transform_and_hash_whir_leaves_from_ntt_multi_coset_to_staging_register_v32_kernel(
    vectorized_e4_matrix_getter<ld_modifier::cs> ntt_output, u32 *staging, const ::airbender::ntt::whir_leaf_transform_params transform_params,
    const unsigned log_trace_len, const unsigned log_lde_factor, const unsigned coset_index_base, const unsigned leaves_count) {
  __shared__ u32 hash_block_smem[16][32];
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  const bool enabled = gid < leaves_count;
  const unsigned safe_gid = enabled ? gid : leaves_count - 1;
  const unsigned log_packed_leaf_count = log_trace_len - 5;
  const unsigned packed_leaf_count = 1u << log_packed_leaf_count;
  const unsigned coset_in_tile = safe_gid >> log_packed_leaf_count;
  const unsigned leaf_in_coset = safe_gid & (packed_leaf_count - 1u);
  const unsigned natural_coset = coset_index_base + coset_in_tile;
  ntt_output.add_col(coset_in_tile);
  ntt_output.add_row(leaf_in_coset);
  ::airbender::hash::digest state;
  transform_and_hash_whir_leaf_register_v32_two_limb(ntt_output, transform_params, log_trace_len, log_lde_factor, natural_coset, leaf_in_coset, hash_block_smem,
                                                     state);
  if (enabled && threadIdx.y == 0)
    store_cs(reinterpret_cast<::airbender::hash::digest *>(staging) + gid, state);
}

// Source columns are tile-local; twiddles and tree placement use global cosets.
EXTERN __launch_bounds__(512, 2) __global__
    void ab_transform_and_hash_whir_leaves_from_ntt_multi_coset_kernel(vectorized_e4_matrix_getter<ld_modifier::cs> ntt_output, u32 *results,
                                                                       const ::airbender::ntt::whir_leaf_transform_params transform_params,
                                                                       const unsigned log_trace_len, const unsigned log_lde_factor,
                                                                       const unsigned log_values_per_leaf, const unsigned coset_index_base,
                                                                       const unsigned leaves_count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  // The transform contains block-wide barriers, so a partial final block uses
  // a valid source leaf for inactive x lanes and suppresses their hashes.
  const bool enabled = gid < leaves_count;
  const unsigned safe_gid = enabled ? gid : leaves_count - 1;
  const unsigned log_packed_leaf_count = log_trace_len - log_values_per_leaf;
  const unsigned packed_leaf_count = 1u << log_packed_leaf_count;
  const unsigned coset_in_tile = safe_gid >> log_packed_leaf_count;
  const unsigned leaf_in_coset = safe_gid & (packed_leaf_count - 1u);
  const unsigned natural_coset = coset_index_base + coset_in_tile;

  ntt_output.add_col(coset_in_tile);
  ntt_output.add_row(leaf_in_coset);

  extern __shared__ __align__(16) uint8_t smem[];
  e4 *coefficient_leaves = reinterpret_cast<e4 *>(smem);
  bf *x_invs_smem = reinterpret_cast<bf *>(coefficient_leaves + (blockDim.x << log_values_per_leaf));
  shared_query_leaf_destination destination{coefficient_leaves, log_values_per_leaf};
  const ::airbender::ntt::params_inverse_power_source inverse_power_source{transform_params};
  ::airbender::ntt::transform_whir_leaf_from_ntt(ntt_output, destination, log_trace_len, log_lde_factor, log_values_per_leaf, natural_coset, leaf_in_coset,
                                                 coefficient_leaves, x_invs_smem, transform_params.two_inv_power, inverse_power_source);
  __syncthreads();

  if (threadIdx.y != 0 || !enabled)
    return;

  auto read_e4 = [=](const unsigned value_slot) -> e4 { return coefficient_leaves[value_slot * blockDim.x + threadIdx.x]; };
  ::airbender::hash::digest state;
  ::airbender::hash::initialize(state.words);
  u32 t = 0;
  ::airbender::hash::absorb_e4_stream(state.words, t, 1u << log_values_per_leaf, read_e4);
  const unsigned bitrev_coset = bitreverse_low_bits(natural_coset, log_lde_factor);
  const unsigned output_leaf = bitrev_coset * packed_leaf_count + leaf_in_coset;
  store_cs(reinterpret_cast<::airbender::hash::digest *>(results) + output_leaf, state);
}

EXTERN __launch_bounds__(512, 2) __global__
    void ab_transform_and_hash_whir_leaves_from_ntt_multi_coset_to_staging_kernel(vectorized_e4_matrix_getter<ld_modifier::cs> ntt_output, u32 *staging,
                                                                                  const ::airbender::ntt::whir_leaf_transform_params transform_params,
                                                                                  const unsigned log_trace_len, const unsigned log_lde_factor,
                                                                                  const unsigned log_values_per_leaf, const unsigned coset_index_base) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  const unsigned log_packed_leaf_count = log_trace_len - log_values_per_leaf;
  const unsigned packed_leaf_count = 1u << log_packed_leaf_count;
  const unsigned coset_in_tile = gid >> log_packed_leaf_count;
  const unsigned leaf_in_coset = gid & (packed_leaf_count - 1u);
  const unsigned natural_coset = coset_index_base + coset_in_tile;
  ntt_output.add_col(coset_in_tile);
  ntt_output.add_row(leaf_in_coset);

  extern __shared__ __align__(16) uint8_t smem[];
  e4 *coefficient_leaves = reinterpret_cast<e4 *>(smem);
  bf *x_invs_smem = reinterpret_cast<bf *>(coefficient_leaves + (blockDim.x << log_values_per_leaf));
  shared_query_leaf_destination destination{coefficient_leaves, log_values_per_leaf};
  const ::airbender::ntt::params_inverse_power_source inverse_power_source{transform_params};
  ::airbender::ntt::transform_whir_leaf_from_ntt(ntt_output, destination, log_trace_len, log_lde_factor, log_values_per_leaf, natural_coset, leaf_in_coset,
                                                 coefficient_leaves, x_invs_smem, transform_params.two_inv_power, inverse_power_source);
  __syncthreads();
  if (threadIdx.y != 0)
    return;

  auto read_e4 = [=](const unsigned value_slot) -> e4 { return coefficient_leaves[value_slot * blockDim.x + threadIdx.x]; };
  ::airbender::hash::digest state;
  ::airbender::hash::initialize(state.words);
  u32 t = 0;
  ::airbender::hash::absorb_e4_stream(state.words, t, 1u << log_values_per_leaf, read_e4);
  store_cs(reinterpret_cast<::airbender::hash::digest *>(staging) + gid, state);
}

EXTERN __launch_bounds__(512, 2) __global__
    void ab_transform_and_hash_whir_leaves_from_ntt_flat_range_to_staging_kernel(vectorized_e4_matrix_getter<ld_modifier::cs> ntt_output, u32 *staging,
                                                                                 const ::airbender::ntt::whir_leaf_transform_params transform_params,
                                                                                 const unsigned log_trace_len, const unsigned log_lde_factor,
                                                                                 const unsigned log_values_per_leaf, const unsigned flat_leaf_base) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  const unsigned flat_leaf = flat_leaf_base + gid;
  const unsigned log_packed_leaf_count = log_trace_len - log_values_per_leaf;
  const unsigned packed_leaf_count = 1u << log_packed_leaf_count;
  const unsigned bitrev_coset = flat_leaf >> log_packed_leaf_count;
  const unsigned leaf_in_coset = flat_leaf & (packed_leaf_count - 1u);
  const unsigned natural_coset = bitreverse_low_bits(bitrev_coset, log_lde_factor);
  ntt_output.add_col(natural_coset);
  ntt_output.add_row(leaf_in_coset);

  extern __shared__ __align__(16) uint8_t smem[];
  e4 *coefficient_leaves = reinterpret_cast<e4 *>(smem);
  bf *x_invs_smem = reinterpret_cast<bf *>(coefficient_leaves + (blockDim.x << log_values_per_leaf));
  shared_query_leaf_destination destination{coefficient_leaves, log_values_per_leaf};
  const ::airbender::ntt::params_inverse_power_source inverse_power_source{transform_params};
  ::airbender::ntt::transform_whir_leaf_from_ntt(ntt_output, destination, log_trace_len, log_lde_factor, log_values_per_leaf, natural_coset, leaf_in_coset,
                                                 coefficient_leaves, x_invs_smem, transform_params.two_inv_power, inverse_power_source);
  __syncthreads();
  if (threadIdx.y != 0)
    return;

  auto read_e4 = [=](const unsigned value_slot) -> e4 { return coefficient_leaves[value_slot * blockDim.x + threadIdx.x]; };
  ::airbender::hash::digest state;
  ::airbender::hash::initialize(state.words);
  u32 t = 0;
  ::airbender::hash::absorb_e4_stream(state.words, t, 1u << log_values_per_leaf, read_e4);
  store_cs(reinterpret_cast<::airbender::hash::digest *>(staging) + gid, state);
}

EXTERN __launch_bounds__(256) __global__ void ab_reduce_staged_whir_subtrees_flat_kernel(const u32 *staged, u32 *boundary_roots, const unsigned roots_count) {
  constexpr unsigned ROOTS_PER_BLOCK = 16;
  constexpr unsigned LEAVES_PER_BLOCK = ROOTS_PER_BLOCK << ::airbender::hash::LOG_WARP_SIZE;
  const unsigned root_base = blockIdx.x * ROOTS_PER_BLOCK;
  const unsigned valid_roots = min(ROOTS_PER_BLOCK, roots_count - root_base);
  const unsigned valid_leaves = valid_roots << ::airbender::hash::LOG_WARP_SIZE;
  const unsigned leaf_base = blockIdx.x * LEAVES_PER_BLOCK;
  const auto staged_d = reinterpret_cast<const ::airbender::hash::digest *>(staged);
  auto boundary_roots_d = reinterpret_cast<::airbender::hash::digest *>(boundary_roots);
  extern __shared__ __align__(32) uint8_t reducer_smem[];
  auto values = reinterpret_cast<::airbender::hash::digest *>(reducer_smem);
  if (threadIdx.x < valid_leaves)
    values[threadIdx.x] = load_cs(staged_d + leaf_base + threadIdx.x);
  if (threadIdx.x + blockDim.x < valid_leaves)
    values[threadIdx.x + blockDim.x] = load_cs(staged_d + leaf_base + threadIdx.x + blockDim.x);
  __syncthreads();
  ::airbender::hash::reduce_merkle_subtrees_block(values, valid_leaves >> 1);
  if (threadIdx.x < valid_roots)
    store_cs(boundary_roots_d + root_base + threadIdx.x, values[threadIdx.x]);
}

EXTERN __launch_bounds__(256) __global__
    void ab_reduce_staged_whir_subtrees_natural_tiles_kernel(const u32 *staged, u32 *boundary_roots, const unsigned log_packed_leaf_count,
                                                             const unsigned log_lde_factor, const unsigned first_tile_coset_base,
                                                             const unsigned staged_tile_leaves, const unsigned tiles_count, const unsigned tile_coset_stride,
                                                             const unsigned roots_count) {
  constexpr unsigned ROOTS_PER_BLOCK = 16;
  constexpr unsigned LEAVES_PER_BLOCK = ROOTS_PER_BLOCK << ::airbender::hash::LOG_WARP_SIZE;
  const unsigned root_base = blockIdx.x * ROOTS_PER_BLOCK;
  const unsigned valid_roots = min(ROOTS_PER_BLOCK, roots_count - root_base);
  const unsigned valid_leaves = valid_roots << ::airbender::hash::LOG_WARP_SIZE;
  const unsigned leaf_base = blockIdx.x * LEAVES_PER_BLOCK;
  const auto staged_d = reinterpret_cast<const ::airbender::hash::digest *>(staged);
  auto boundary_roots_d = reinterpret_cast<::airbender::hash::digest *>(boundary_roots);
  extern __shared__ __align__(32) uint8_t reducer_smem[];
  auto values = reinterpret_cast<::airbender::hash::digest *>(reducer_smem);
  if (threadIdx.x < valid_leaves)
    values[threadIdx.x] = load_cs(staged_d + leaf_base + threadIdx.x);
  if (threadIdx.x + blockDim.x < valid_leaves)
    values[threadIdx.x + blockDim.x] = load_cs(staged_d + leaf_base + threadIdx.x + blockDim.x);
  __syncthreads();
  ::airbender::hash::reduce_merkle_subtrees_block(values, valid_leaves >> 1);
  if (threadIdx.x < valid_roots) {
    const unsigned staged_root = root_base + threadIdx.x;
    const unsigned staged_leaf = staged_root << ::airbender::hash::LOG_WARP_SIZE;
    const unsigned tile = staged_leaf / staged_tile_leaves;
    const unsigned leaf_in_tile = staged_leaf - tile * staged_tile_leaves;
    const unsigned coset_in_tile = leaf_in_tile >> log_packed_leaf_count;
    const unsigned leaf_in_coset = leaf_in_tile & ((1u << log_packed_leaf_count) - 1u);
    const unsigned natural_coset = first_tile_coset_base + tile * tile_coset_stride + coset_in_tile;
    const unsigned bitrev_coset = bitreverse_low_bits(natural_coset, log_lde_factor);
    const unsigned roots_per_coset = 1u << (log_packed_leaf_count - ::airbender::hash::LOG_WARP_SIZE);
    const unsigned output_root = bitrev_coset * roots_per_coset + (leaf_in_coset >> ::airbender::hash::LOG_WARP_SIZE);
    store_cs(boundary_roots_d + output_root, values[threadIdx.x]);
  }
}

} // namespace airbender::whir
