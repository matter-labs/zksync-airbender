#include "hash.cuh"

namespace airbender::hash {

// One transcript squeeze round: seed_io <- Blake2s(seed_io), in place.
DEVICE_FORCEINLINE void advance_seed(u32 seed_io[STATE_SIZE]) {
  u32 state[STATE_SIZE];
  initialize(state);
  u32 block[BLOCK_SIZE] = {};
#pragma unroll
  for (unsigned i = 0; i < STATE_SIZE; i++)
    block[i] = seed_io[i];
  u32 t = 0;
  compress<true>(state, t, block, STATE_SIZE);
#pragma unroll
  for (unsigned i = 0; i < STATE_SIZE; i++)
    seed_io[i] = state[i];
}

// Reduce 4 raw squeeze u32 words into one E4 challenge, matching the host
// `draw_random_field_els*` reduction (`from_raw_repr_with_reduction` per limb).
DEVICE_FORCEINLINE e4 reduce_4_words_to_e4(const u32 *src) {
  const bf c0 = bf::from_raw_repr_with_reduction(src[0]);
  const bf c1 = bf::from_raw_repr_with_reduction(src[1]);
  const bf c2 = bf::from_raw_repr_with_reduction(src[2]);
  const bf c3 = bf::from_raw_repr_with_reduction(src[3]);
  return e4(e2(c0, c1), e2(c2, c3));
}

EXTERN __global__ void ab_blake2s_leaves_kernel(const bf *values, u32 *results, const unsigned log_rows_count, const unsigned cols_count,
                                                const unsigned count) {
  const unsigned gid = threadIdx.x + blockIdx.x * blockDim.x;
  if (gid >= count)
    return;
  const unsigned row_mask = (1u << log_rows_count) - 1;
  const unsigned domain_size = count << log_rows_count;
  auto read = [=](const unsigned offset) {
    const unsigned row_slot = offset & row_mask;
    const unsigned col = offset >> log_rows_count;
    const unsigned row = gid + bitreverse_low_bits(row_slot, log_rows_count) * count;
    return col < cols_count ? bf::into_raw_u32(load_cs(values + row + col * domain_size)) : 0;
  };
  digest state;
  initialize(state.words);
  u32 t = 0;
  absorb_stream(state.words, t, cols_count << log_rows_count, read);
  // Single 256-bit aligned store: STG.E.ENL2.256 on sm_100+ / 2× STG.E.128 on older arch.
  store_cs(reinterpret_cast<digest *>(results) + gid, state);
}

// LSB (physical-block) siblings of the leaf hashers in this file: the input is the
// BITREVERSED-order codeword, in which logical leaf `rev(gid)` is the contiguous
// run starting at `gid << log_rows_count`. Absorb enumeration, value counts, coset
// selection and digest destinations are unchanged, so the digests are byte-identical
// to the natural-order donors' — only enumerated in bitreversed leaf order.
DEVICE_FORCEINLINE digest hash_leaf_physical(const bf *values, const unsigned log_rows_count, const unsigned cols_count, const unsigned count,
                                             const unsigned gid) {
  const unsigned row_mask = (1u << log_rows_count) - 1;
  const unsigned domain_size = count << log_rows_count;
  auto read = [=](const unsigned offset) {
    const unsigned row_slot = offset & row_mask;
    const unsigned col = offset >> log_rows_count;
    const unsigned row = (gid << log_rows_count) + row_slot;
    return col < cols_count ? bf::into_raw_u32(load_cs(values + row + col * domain_size)) : 0;
  };
  digest state;
  initialize(state.words);
  u32 t = 0;
  absorb_stream(state.words, t, cols_count << log_rows_count, read);
  return state;
}

EXTERN __global__ void ab_blake2s_leaves_physical_kernel(const bf *values, u32 *results, const unsigned log_rows_count, const unsigned cols_count,
                                                         const unsigned count) {
  const unsigned gid = threadIdx.x + blockIdx.x * blockDim.x;
  if (gid >= count)
    return;
  const digest state = hash_leaf_physical(values, log_rows_count, cols_count, count, gid);
  store_cs(reinterpret_cast<digest *>(results) + gid, state);
}

DEVICE_FORCEINLINE digest hash_leaf_multi_coset(const bf *values, const unsigned log_rows_count, const unsigned cols_count, const unsigned log_per_coset_count,
                                                const unsigned per_coset_values_stride_bf, const unsigned gid_global) {
  const unsigned per_coset_count = 1u << log_per_coset_count;
  const unsigned coset = gid_global >> log_per_coset_count;
  const unsigned gid = gid_global & (per_coset_count - 1u);
  values += static_cast<size_t>(coset) * per_coset_values_stride_bf;
  const unsigned row_mask = (1u << log_rows_count) - 1;
  const unsigned domain_size = per_coset_count << log_rows_count;
  auto read = [=](const unsigned offset) {
    const unsigned row_slot = offset & row_mask;
    const unsigned col = offset >> log_rows_count;
    const unsigned row = gid + bitreverse_low_bits(row_slot, log_rows_count) * per_coset_count;
    return col < cols_count ? bf::into_raw_u32(load_cs(values + row + col * domain_size)) : 0;
  };
  digest state;
  initialize(state.words);
  u32 t = 0;
  absorb_stream(state.words, t, cols_count << log_rows_count, read);
  return state;
}

EXTERN __global__ void ab_blake2s_leaves_multi_coset_kernel(const bf *values, u32 *results, const unsigned log_rows_count, const unsigned cols_count,
                                                            const unsigned log_per_coset_count, const unsigned per_coset_values_stride_bf,
                                                            const unsigned per_coset_results_stride_digests, const unsigned count) {
  const unsigned gid_global = threadIdx.x + blockIdx.x * blockDim.x;
  if (gid_global >= count)
    return;
  const unsigned coset = gid_global >> log_per_coset_count;
  const unsigned gid = gid_global & ((1u << log_per_coset_count) - 1u);
  digest *results_d = reinterpret_cast<digest *>(results) + static_cast<size_t>(coset) * per_coset_results_stride_digests + gid;
  const digest state = hash_leaf_multi_coset(values, log_rows_count, cols_count, log_per_coset_count, per_coset_values_stride_bf, gid_global);
  store_cs(results_d, state);
}

DEVICE_FORCEINLINE digest hash_leaf_multi_coset_physical(const bf *values, const unsigned log_rows_count, const unsigned cols_count,
                                                         const unsigned log_per_coset_count, const unsigned per_coset_values_stride_bf,
                                                         const unsigned gid_global) {
  const unsigned per_coset_count = 1u << log_per_coset_count;
  const unsigned coset = gid_global >> log_per_coset_count;
  const unsigned gid_local = gid_global & (per_coset_count - 1u);
  values += static_cast<size_t>(coset) * per_coset_values_stride_bf;
  const unsigned row_mask = (1u << log_rows_count) - 1;
  const unsigned domain_size = per_coset_count << log_rows_count;
  auto read = [=](const unsigned offset) {
    const unsigned row_slot = offset & row_mask;
    const unsigned col = offset >> log_rows_count;
    const unsigned row = (gid_local << log_rows_count) + row_slot;
    return col < cols_count ? bf::into_raw_u32(load_cs(values + row + col * domain_size)) : 0;
  };
  digest state;
  initialize(state.words);
  u32 t = 0;
  absorb_stream(state.words, t, cols_count << log_rows_count, read);
  return state;
}

EXTERN __global__ void ab_blake2s_leaves_multi_coset_physical_kernel(const bf *values, u32 *results, const unsigned log_rows_count, const unsigned cols_count,
                                                                     const unsigned log_per_coset_count, const unsigned per_coset_values_stride_bf,
                                                                     const unsigned per_coset_results_stride_digests, const unsigned count) {
  const unsigned gid_global = threadIdx.x + blockIdx.x * blockDim.x;
  if (gid_global >= count)
    return;
  const unsigned coset = gid_global >> log_per_coset_count;
  const unsigned gid = gid_global & ((1u << log_per_coset_count) - 1u);
  digest *results_d = reinterpret_cast<digest *>(results) + static_cast<size_t>(coset) * per_coset_results_stride_digests + gid;
  const digest state = hash_leaf_multi_coset_physical(values, log_rows_count, cols_count, log_per_coset_count, per_coset_values_stride_bf, gid_global);
  store_cs(results_d, state);
}

EXTERN __launch_bounds__(256) __global__
    void ab_blake2s_partial_tree_multi_coset_kernel(const bf *values, u32 *tree_backing, const unsigned log_rows_count, const unsigned cols_count,
                                                    const unsigned log_per_coset_count, const unsigned per_coset_values_stride_bf,
                                                    const unsigned per_coset_tree_stride_digests, const unsigned count) {
  constexpr unsigned ROOTS_PER_BLOCK = 16;
  constexpr unsigned LEAVES_PER_BLOCK = ROOTS_PER_BLOCK << LOG_WARP_SIZE;
  const unsigned leaf_base = blockIdx.x * LEAVES_PER_BLOCK;
  const unsigned valid_leaves = min(LEAVES_PER_BLOCK, count - leaf_base);
  extern __shared__ __align__(32) uint8_t reducer_smem[];
  auto shared_values = reinterpret_cast<digest *>(reducer_smem);

  const unsigned leaf = leaf_base + threadIdx.x;
  if (threadIdx.x < valid_leaves)
    shared_values[threadIdx.x] = hash_leaf_multi_coset(values, log_rows_count, cols_count, log_per_coset_count, per_coset_values_stride_bf, leaf);
  if (threadIdx.x + blockDim.x < valid_leaves)
    shared_values[threadIdx.x + blockDim.x] =
        hash_leaf_multi_coset(values, log_rows_count, cols_count, log_per_coset_count, per_coset_values_stride_bf, leaf + blockDim.x);
  __syncthreads();

  reduce_merkle_subtrees_block(shared_values, valid_leaves >> 1);
  const unsigned valid_roots = valid_leaves >> LOG_WARP_SIZE;
  if (threadIdx.x < valid_roots) {
    const unsigned global_root = blockIdx.x * ROOTS_PER_BLOCK + threadIdx.x;
    const unsigned log_roots_per_coset = log_per_coset_count - LOG_WARP_SIZE;
    const unsigned coset = global_root >> log_roots_per_coset;
    const unsigned root_in_coset = global_root & ((1u << log_roots_per_coset) - 1u);
    auto roots = reinterpret_cast<digest *>(tree_backing) + static_cast<size_t>(coset) * per_coset_tree_stride_digests;
    store_cs(roots + root_in_coset, shared_values[threadIdx.x]);
  }
}

DEVICE_FORCEINLINE digest hash_node(const digest &left, const digest &right) {
  digest children[2] = {left, right};
  digest state;
  initialize(state.words);
  u32 t = 0;
  compress<true>(state.words, t, reinterpret_cast<const u32 *>(children), BLOCK_SIZE);
  return state;
}

template <unsigned LEVEL> DEVICE_FORCEINLINE bool insert_merkle_node(digest (&pending)[LOG_WARP_SIZE], digest &node, const unsigned leaf) {
  if ((leaf & (1u << LEVEL)) == 0) {
    pending[LEVEL] = node;
    return true;
  }
  node = hash_node(pending[LEVEL], node);
  return false;
}

// Fused LSB partial-tree builder. One thread produces one boundary root from
// 32 logical leaves without materializing their digests. Threads enumerate
// roots in PHYSICAL order; for a warp-uniform logical offset `t`, consecutive
// lanes therefore read consecutive physical leaf blocks at
//
//   bitreverse(t, 5) * roots_per_coset + physical_root.
//
// Only the final 32-byte root store is permuted back to logical order, so the
// existing upper tree and query-path layout stay byte-identical to the natural
// builder while the bulk values reads never permute the lane axis.
EXTERN __launch_bounds__(128) __global__
    void ab_blake2s_partial_tree_multi_coset_physical_kernel(const bf *values, u32 *tree_backing, const unsigned log_rows_count, const unsigned cols_count,
                                                             const unsigned log_per_coset_count, const unsigned per_coset_values_stride_bf,
                                                             const unsigned per_coset_tree_stride_digests, const unsigned count) {
  constexpr unsigned LEAVES_PER_ROOT = 1u << LOG_WARP_SIZE;
  const unsigned roots_count = count >> LOG_WARP_SIZE;
  const unsigned root_global = threadIdx.x + blockIdx.x * blockDim.x;
  if (root_global >= roots_count)
    return;

  const unsigned log_roots_per_coset = log_per_coset_count - LOG_WARP_SIZE;
  const unsigned roots_per_coset = 1u << log_roots_per_coset;
  const unsigned coset = root_global >> log_roots_per_coset;
  const unsigned physical_root = root_global & (roots_per_coset - 1u);

  digest pending[LOG_WARP_SIZE];
  digest node;
#pragma unroll 1
  for (unsigned t = 0; t < LEAVES_PER_ROOT; t++) {
    const unsigned physical_leaf = (bitreverse_low_bits(t, LOG_WARP_SIZE) << log_roots_per_coset) | physical_root;
    const unsigned leaf_global = (coset << log_per_coset_count) | physical_leaf;
    node = hash_leaf_multi_coset_physical(values, log_rows_count, cols_count, log_per_coset_count, per_coset_values_stride_bf, leaf_global);
    if (insert_merkle_node<0>(pending, node, t))
      continue;
    if (insert_merkle_node<1>(pending, node, t))
      continue;
    if (insert_merkle_node<2>(pending, node, t))
      continue;
    if (insert_merkle_node<3>(pending, node, t))
      continue;
    insert_merkle_node<4>(pending, node, t);
  }

  const unsigned logical_root = bitreverse_low_bits(physical_root, log_roots_per_coset);
  auto roots = reinterpret_cast<digest *>(tree_backing) + static_cast<size_t>(coset) * per_coset_tree_stride_digests;
  store_cs(roots + logical_root, node);
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
// `results` is the flat tree backing for the WHIR oracle (a single packed
// coset, `log_lde_factor = 0`); digest at flat-tree leaf `idx` lives at
// `results[idx * STATE_SIZE]`.
//
// Output position derivation: pack writes the natural-coset `coset_in_tile`'s
// rows at `bitrev(coset_global, log_lde_factor) * per_coset_count` of the
// packed cosets backing; the existing blake-leaves kernel then hashes flat
// row `dst_row` and stores at `dst_row * STATE_SIZE`. This kernel inlines the
// source-side index math into `read()` and computes `dst_leaf_idx` directly.
DEVICE_FORCEINLINE digest hash_leaf_from_ntt(const bf *ntt_output, const unsigned log_values_per_leaf, const unsigned src_cols_per_coset,
                                             const unsigned src_coset, const unsigned leaf_in_coset, const unsigned per_coset_count, const unsigned trace_len) {
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
    const unsigned src_col_global = src_coset * src_cols_per_coset + col_in_leaf;
    return bf::into_raw_u32(load_cs(ntt_output + src_row + static_cast<size_t>(src_col_global) * trace_len));
  };

  digest state;
  initialize(state.words);
  u32 t = 0;
  absorb_stream(state.words, t, cols_count, read);
  return state;
}

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
  const digest state = hash_leaf_from_ntt(ntt_output, log_values_per_leaf, src_cols_per_coset, coset_in_tile, leaf_in_coset, per_coset_count, trace_len);
  store_cs(results_d, state);
}

EXTERN __global__ void ab_blake2s_leaves_from_ntt_multi_coset_to_staging_kernel(const bf *ntt_output, u32 *staging, const unsigned log_values_per_leaf,
                                                                                const unsigned src_cols_per_coset, const unsigned per_coset_count,
                                                                                const unsigned log_per_coset_count, const unsigned trace_len,
                                                                                const unsigned count) {
  const unsigned gid = threadIdx.x + blockIdx.x * blockDim.x;
  if (gid >= count)
    return;
  const unsigned coset_in_tile = gid >> log_per_coset_count;
  const unsigned leaf_in_coset = gid & (per_coset_count - 1u);
  const digest state = hash_leaf_from_ntt(ntt_output, log_values_per_leaf, src_cols_per_coset, coset_in_tile, leaf_in_coset, per_coset_count, trace_len);
  store_cs(reinterpret_cast<digest *>(staging) + gid, state);
}

EXTERN __global__ void ab_blake2s_leaves_from_ntt_flat_range_to_staging_kernel(const bf *ntt_output, u32 *staging, const unsigned log_values_per_leaf,
                                                                               const unsigned src_cols_per_coset, const unsigned log_lde_factor,
                                                                               const unsigned flat_leaf_base, const unsigned per_coset_count,
                                                                               const unsigned log_per_coset_count, const unsigned trace_len,
                                                                               const unsigned count) {
  const unsigned gid = threadIdx.x + blockIdx.x * blockDim.x;
  if (gid >= count)
    return;
  const unsigned flat_leaf = flat_leaf_base + gid;
  const unsigned bitrev_coset = flat_leaf >> log_per_coset_count;
  const unsigned leaf_in_coset = flat_leaf & (per_coset_count - 1u);
  const unsigned natural_coset = bitreverse_low_bits(bitrev_coset, log_lde_factor);
  const digest state = hash_leaf_from_ntt(ntt_output, log_values_per_leaf, src_cols_per_coset, natural_coset, leaf_in_coset, per_coset_count, trace_len);
  store_cs(reinterpret_cast<digest *>(staging) + gid, state);
}

DEVICE_FORCEINLINE digest hash_leaf_from_ntt_physical(const bf *ntt_output, const unsigned log_values_per_leaf, const unsigned src_cols_per_coset,
                                                      const unsigned src_coset, const unsigned leaf_in_coset, const unsigned per_coset_count,
                                                      const unsigned trace_len) {
  const unsigned cols_count = src_cols_per_coset << log_values_per_leaf;
  const unsigned values_per_leaf = 1u << log_values_per_leaf;
  const unsigned col_mask = src_cols_per_coset - 1u;
  const unsigned log_src_cols_per_coset = __ffs(src_cols_per_coset) - 1u;

  auto read = [=](const unsigned offset) -> u32 {
    const unsigned col_in_leaf = offset & col_mask;               // FAST (low log_src_cols_per_coset bits)
    const unsigned value_slot = offset >> log_src_cols_per_coset; // SLOW (high log_values_per_leaf bits)
    if (value_slot >= values_per_leaf)
      return 0;
    const unsigned src_row = (leaf_in_coset << log_values_per_leaf) + value_slot;
    const unsigned src_col_global = src_coset * src_cols_per_coset + col_in_leaf;
    return bf::into_raw_u32(load_cs(ntt_output + src_row + static_cast<size_t>(src_col_global) * trace_len));
  };

  digest state;
  initialize(state.words);
  u32 t = 0;
  absorb_stream(state.words, t, cols_count, read);
  return state;
}

EXTERN __global__ void ab_blake2s_leaves_from_ntt_multi_coset_physical_kernel(const bf *ntt_output, u32 *results, const unsigned log_values_per_leaf,
                                                                              const unsigned src_cols_per_coset, const unsigned log_lde_factor,
                                                                              const unsigned coset_index_base, const unsigned per_coset_count,
                                                                              const unsigned log_per_coset_count, const unsigned trace_len,
                                                                              const unsigned count) {
  const unsigned gid_global = threadIdx.x + blockIdx.x * blockDim.x;
  if (gid_global >= count)
    return;

  const unsigned coset_in_tile = gid_global >> log_per_coset_count;
  const unsigned leaf_in_coset = gid_global & (per_coset_count - 1u);
  const unsigned coset_global = coset_index_base + coset_in_tile;
  const unsigned bitrev_coset = bitreverse_low_bits(coset_global, log_lde_factor);
  const unsigned dst_leaf_idx = leaf_in_coset + bitrev_coset * per_coset_count;
  digest *results_d = reinterpret_cast<digest *>(results) + dst_leaf_idx;
  const digest state =
      hash_leaf_from_ntt_physical(ntt_output, log_values_per_leaf, src_cols_per_coset, coset_in_tile, leaf_in_coset, per_coset_count, trace_len);
  store_cs(results_d, state);
}

EXTERN __global__ void ab_blake2s_leaves_from_ntt_multi_coset_to_staging_physical_kernel(const bf *ntt_output, u32 *staging, const unsigned log_values_per_leaf,
                                                                                         const unsigned src_cols_per_coset, const unsigned per_coset_count,
                                                                                         const unsigned log_per_coset_count, const unsigned trace_len,
                                                                                         const unsigned count) {
  const unsigned gid = threadIdx.x + blockIdx.x * blockDim.x;
  if (gid >= count)
    return;
  const unsigned coset_in_tile = gid >> log_per_coset_count;
  const unsigned leaf_in_coset = gid & (per_coset_count - 1u);
  const digest state =
      hash_leaf_from_ntt_physical(ntt_output, log_values_per_leaf, src_cols_per_coset, coset_in_tile, leaf_in_coset, per_coset_count, trace_len);
  store_cs(reinterpret_cast<digest *>(staging) + gid, state);
}

EXTERN __global__ void ab_blake2s_leaves_from_ntt_flat_range_to_staging_physical_kernel(const bf *ntt_output, u32 *staging, const unsigned log_values_per_leaf,
                                                                                        const unsigned src_cols_per_coset, const unsigned log_lde_factor,
                                                                                        const unsigned flat_leaf_base, const unsigned per_coset_count,
                                                                                        const unsigned log_per_coset_count, const unsigned trace_len,
                                                                                        const unsigned count) {
  const unsigned gid = threadIdx.x + blockIdx.x * blockDim.x;
  if (gid >= count)
    return;
  const unsigned flat_leaf = flat_leaf_base + gid;
  const unsigned bitrev_coset = flat_leaf >> log_per_coset_count;
  const unsigned leaf_in_coset = flat_leaf & (per_coset_count - 1u);
  const unsigned natural_coset = bitreverse_low_bits(bitrev_coset, log_lde_factor);
  const digest state =
      hash_leaf_from_ntt_physical(ntt_output, log_values_per_leaf, src_cols_per_coset, natural_coset, leaf_in_coset, per_coset_count, trace_len);
  store_cs(reinterpret_cast<digest *>(staging) + gid, state);
}

// Fused node tower: one launch folds `layers` Merkle layers instead of one
// launch per layer. Every intermediate layer is still written at its flat
// prefix-sum offset, because gather.cu resolves a layer by closed form
// (`(1<<(L+1)) - (1<<(L+1-layer))`) with no per-layer pointer table — no layer
// may be skipped or displaced. `src`/`dst` are independent bases so this serves
// both the flat single-tree build and the multi-coset build.
EXTERN __global__ void ab_blake2s_nodes_tower_multi_coset_kernel(const u32 *src, u32 *dst, const unsigned layers, const unsigned log_blocks_per_coset,
                                                                 const unsigned stride_digests, const unsigned src_count_per_coset) {
  extern __shared__ digest values[];
  const unsigned threads = blockDim.x;
  const unsigned coset = blockIdx.x >> log_blocks_per_coset;
  const unsigned block_in_coset = blockIdx.x & ((1u << log_blocks_per_coset) - 1u);

  const digest *src_d = reinterpret_cast<const digest *>(src) + static_cast<size_t>(coset) * stride_digests + static_cast<size_t>(block_in_coset) * 2 * threads;
  digest *dst_d = reinterpret_cast<digest *>(dst) + static_cast<size_t>(coset) * stride_digests;

  unsigned layer_count = src_count_per_coset >> 1;
  unsigned layer_off = 0;

  // Layer 0 reads from gmem; only its output is staged in smem, which halves
  // the footprint and doubles the block-per-SM limit.
  {
    digest children[2];
    children[0] = load_cs(src_d + 2 * threadIdx.x);
    children[1] = load_cs(src_d + 2 * threadIdx.x + 1);
    digest state;
    initialize(state.words);
    u32 t = 0;
    compress<true>(state.words, t, reinterpret_cast<const u32 *>(children), BLOCK_SIZE);
    values[threadIdx.x] = state;
    store_cs(dst_d + layer_off + static_cast<size_t>(block_in_coset) * threads + threadIdx.x, state);
  }
  __syncthreads();
  layer_off += layer_count;
  layer_count >>= 1;

  for (unsigned layer = 1; layer < layers; layer++) {
    const unsigned n_active = threads >> layer;
    const bool enabled = threadIdx.x < n_active;
    digest children[2];
    if (enabled) {
      children[0] = values[2 * threadIdx.x];
      children[1] = values[2 * threadIdx.x + 1];
    }
    __syncthreads(); // children read before any thread overwrites the lower half
    if (enabled) {
      digest state;
      initialize(state.words);
      u32 t = 0;
      compress<true>(state.words, t, reinterpret_cast<const u32 *>(children), BLOCK_SIZE);
      values[threadIdx.x] = state;
      store_cs(dst_d + layer_off + static_cast<size_t>(block_in_coset) * n_active + threadIdx.x, state);
    }
    __syncthreads();
    layer_off += layer_count;
    layer_count >>= 1;
  }
}

EXTERN __global__ void ab_blake2s_pow_kernel(const u64 *seed, const u32 bits_count, const u64 max_nonce, volatile u64 *result) {
  const u32 digest_mask = 0xffffffff << 32 - bits_count;
  const auto result_ptr = reinterpret_cast<unsigned long long *>(const_cast<u64 *>(result));
  __align__(8) u32 m_u32[BLOCK_SIZE] = {};
  auto m_u64 = reinterpret_cast<u64 *>(m_u32);
#pragma unroll
  for (unsigned i = 0; i < 4; i++)
    m_u64[i] = seed[i];
  const unsigned stride = blockDim.x * gridDim.x;
  for (u64 nonce = threadIdx.x + blockIdx.x * blockDim.x; nonce < max_nonce; nonce += stride) {
    m_u64[STATE_SIZE / 2] = nonce;
    u32 state[STATE_SIZE];
    initialize(state);
    u32 t = 0;
    compress<true>(state, t, m_u32, STATE_SIZE + 2);
    if (!(state[0] & digest_mask)) {
#ifdef AB_DETERMINISTIC_POW
      atomicMin(result_ptr, static_cast<unsigned long long>(nonce));
#else
      atomicCAS(result_ptr, UINT64_MAX, nonce);
#endif
      __threadfence();
    }
    if (*result
#ifdef AB_DETERMINISTIC_POW
        <= nonce
#else
        != UINT64_MAX
#endif
    )
      return;
  }
}

// ---------------------------------------------------------------------------
// Device-side Fiat-Shamir transcript operations (single-thread kernels).
// These mirror the host Blake2sTranscript::commit_with_seed / draw_randomness
// so that challenge derivation can happen entirely on the device without D2H
// round-trips.
// ---------------------------------------------------------------------------

// Mirror of `GpuChunkedInputDesc` in gpu/hash/src/blake2s/transcript.rs. Holds the
// per-launch chunk source pointer table inline as kernel-arg data so the
// chunked-commit kernel reads `num_chunks` contiguous u32 buffers without an
// auxiliary device allocation.
constexpr unsigned GKR_CHUNKED_COMMIT_MAX_CHUNKS = 8;

struct gpu_chunked_input_desc {
  u32 num_chunks;
  u32 _pad;
  unsigned long long src_ptrs[GKR_CHUNKED_COMMIT_MAX_CHUNKS];
  u32 chunk_lens[GKR_CHUNKED_COMMIT_MAX_CHUNKS];
};

static_assert(sizeof(gpu_chunked_input_desc) == 8 + 12 * GKR_CHUNKED_COMMIT_MAX_CHUNKS,
              "must mirror GpuChunkedInputDesc in gpu/hash/src/blake2s/transcript.rs");

// commit_initial_chunked: seed_out = Blake2s(chunk_0 || chunk_1 || ... || chunk_{N-1}).
// Blake2s streams 64-byte (= 16 u32) blocks, so chunk boundaries that fall
// mid-block are handled transparently and the digest matches a single-buffer
// commit over the same logical concatenation.
EXTERN __global__ void ab_transcript_commit_initial_chunked_kernel(__grid_constant__ const gpu_chunked_input_desc desc, u32 *seed_out) {
  u32 state[STATE_SIZE];
  initialize(state);
  u32 t = 0;
  u32 block[BLOCK_SIZE];
#pragma unroll
  for (unsigned i = 0; i < BLOCK_SIZE; i++)
    block[i] = 0;

  unsigned block_offset = 0;
  unsigned remaining_total = 0;
  for (unsigned c = 0; c < desc.num_chunks; c++)
    remaining_total += desc.chunk_lens[c];

  for (unsigned c = 0; c < desc.num_chunks; c++) {
    const u32 *src = reinterpret_cast<const u32 *>(desc.src_ptrs[c]);
    unsigned chunk_remaining = desc.chunk_lens[c];
    while (chunk_remaining > 0) {
      const unsigned space = BLOCK_SIZE - block_offset;
      const unsigned n = chunk_remaining < space ? chunk_remaining : space;
      for (unsigned i = 0; i < n; i++)
        block[block_offset + i] = src[i];
      block_offset += n;
      src += n;
      chunk_remaining -= n;
      remaining_total -= n;

      if (block_offset == BLOCK_SIZE && remaining_total > 0) {
        compress<false>(state, t, block, BLOCK_SIZE);
#pragma unroll
        for (unsigned i = 0; i < BLOCK_SIZE; i++)
          block[i] = 0;
        block_offset = 0;
      }
    }
  }

  // Zero-pad and finalize.
  for (unsigned i = block_offset; i < BLOCK_SIZE; i++)
    block[i] = 0;
  compress<true>(state, t, block, block_offset);

#pragma unroll
  for (unsigned i = 0; i < STATE_SIZE; i++)
    seed_out[i] = state[i];
}

// commit_with_seed: new_seed = Blake2s(old_seed || input).
// seed_io: STATE_SIZE u32 words, read then overwritten with the new seed.
// input:   input_len u32 words to absorb after the seed.
EXTERN __global__ void ab_transcript_commit_kernel(u32 *seed_io, const u32 *input, const unsigned input_len) {
  u32 state[STATE_SIZE];
  initialize(state);
  u32 t = 0;
  u32 block[BLOCK_SIZE];

  // Start the block with the seed.
#pragma unroll
  for (unsigned i = 0; i < STATE_SIZE; i++)
    block[i] = seed_io[i];
#pragma unroll
  for (unsigned i = STATE_SIZE; i < BLOCK_SIZE; i++)
    block[i] = 0;

  unsigned block_offset = STATE_SIZE;
  unsigned remaining = input_len;
  const u32 *src = input;

  while (remaining > 0) {
    const unsigned space = BLOCK_SIZE - block_offset;
    const unsigned n = remaining < space ? remaining : space;
    for (unsigned i = 0; i < n; i++)
      block[block_offset + i] = src[i];
    block_offset += n;
    src += n;
    remaining -= n;

    if (block_offset == BLOCK_SIZE && remaining > 0) {
      compress<false>(state, t, block, BLOCK_SIZE);
#pragma unroll
      for (unsigned i = 0; i < BLOCK_SIZE; i++)
        block[i] = 0;
      block_offset = 0;
    }
  }

  // Zero-pad and finalize.
  for (unsigned i = block_offset; i < BLOCK_SIZE; i++)
    block[i] = 0;
  compress<true>(state, t, block, block_offset);

#pragma unroll
  for (unsigned i = 0; i < STATE_SIZE; i++)
    seed_io[i] = state[i];
}

// draw_randomness: expand seed into output_len u32 words.
// The first STATE_SIZE words are the seed itself (no hashing).
// Each subsequent STATE_SIZE-word chunk hashes the seed to advance it.
// seed_io:    STATE_SIZE u32 words; updated in-place when output_len > STATE_SIZE.
// output:     output_len u32 words (must be a multiple of STATE_SIZE).
// output_len: total words to produce.
EXTERN __global__ void ab_transcript_squeeze_kernel(u32 *seed_io, u32 *output, const unsigned output_len) {
  // Round 0: emit the current seed verbatim.
#pragma unroll
  for (unsigned i = 0; i < STATE_SIZE; i++)
    output[i] = seed_io[i];

  const unsigned num_rounds = output_len / STATE_SIZE;
  for (unsigned round = 1; round < num_rounds; round++) {
    advance_seed(seed_io);
#pragma unroll
    for (unsigned i = 0; i < STATE_SIZE; i++)
      output[round * STATE_SIZE + i] = seed_io[i];
  }
}

// Device-side `Transcript::commit_initial` seed → `draw_random_field_els::<BF, E4>(seed, count)`.
// Writes `count` E4 challenges in Montgomery form, matching host
// `BabyBearField::from_raw_repr_with_reduction` applied to each 4-u32 squeeze chunk, and
// updates `seed_io` with the advanced seed.
//
// `count` must be positive. Each challenge consumes 4 consecutive raw squeeze u32 words; the
// kernel advances the seed once per STATE_SIZE (= 8) raw words produced (i.e. every 2 E4s),
// matching the CPU's `draw_randomness` chunking with `next_multiple_of(STATE_SIZE)` padding.
EXTERN __global__ void ab_transcript_squeeze_e4_kernel(u32 *seed_io, e4 *output_e4, const unsigned count) {
  if (count == 0)
    return;
  // Produce enough raw u32 words for `count` E4 challenges, padded to a multiple of STATE_SIZE.
  const unsigned raw_len = ((count * 4u + STATE_SIZE - 1u) / STATE_SIZE) * STATE_SIZE;
  const unsigned num_rounds = raw_len / STATE_SIZE;

  u32 raw_chunk[STATE_SIZE];
  // Round 0: verbatim seed.
#pragma unroll
  for (unsigned i = 0; i < STATE_SIZE; i++)
    raw_chunk[i] = seed_io[i];

  unsigned emitted = 0;
  for (unsigned round = 0; round < num_rounds; round++) {
    if (round > 0) {
      // Advance seed by Blake2s(seed) and refill raw_chunk.
      advance_seed(seed_io);
#pragma unroll
      for (unsigned i = 0; i < STATE_SIZE; i++)
        raw_chunk[i] = seed_io[i];
    }
    // Consume raw_chunk 4 u32s at a time → 1 E4 challenge.
    for (unsigned slot = 0; slot < STATE_SIZE / 4 && emitted < count; slot++)
      output_e4[emitted++] = reduce_4_words_to_e4(&raw_chunk[slot * 4]);
  }
}

// Reduce a flat run of raw squeeze u32 words into `count` E4 challenges, matching
// the host `draw_random_field_els*` reduction (`bf::from_raw_repr_with_reduction`
// per limb, packed `e4(e2(w0,w1), e2(w2,w3))`). `raw` points at the first word to
// consume — PoW-gated draws pass `&raw[1]` to honor the skip-first-word convention
// of `draw_random_field_els_with_pow` — and must hold at least `count * 4` words.
// Unlike `ab_transcript_squeeze_e4_kernel` this does NOT touch the seed: the caller
// squeezes the padded raw words (advancing the seed) with `ab_transcript_squeeze_kernel`
// first, then reduces here.
EXTERN __global__ void ab_reduce_raw_words_to_e4_kernel(const u32 *raw, e4 *output_e4, const unsigned count) {
  const unsigned gid = threadIdx.x + blockIdx.x * blockDim.x;
  if (gid >= count)
    return;
  output_e4[gid] = reduce_4_words_to_e4(&raw[gid * 4]);
}

} // namespace airbender::hash
