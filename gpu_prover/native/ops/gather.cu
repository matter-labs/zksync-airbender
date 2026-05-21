#include "hash.cuh"

namespace airbender::ops::blake2s {

EXTERN __global__ void ab_gather_rows_kernel(const unsigned *indexes, const unsigned indexes_count, const bool bit_reverse_indexes,
                                             const unsigned log_rows_count, const matrix_getter<bf, ld_modifier::cs> values,
                                             const matrix_setter<bf, st_modifier::cs> results) {
  const unsigned idx = threadIdx.y + blockIdx.x * blockDim.y;
  if (idx >= indexes_count)
    return;
  const unsigned i = indexes[idx];
  const unsigned index = bit_reverse_indexes ? __brev(i) >> (32 - log_rows_count) : i;
  const unsigned src_row = index * blockDim.x + threadIdx.x;
  const unsigned dst_row = idx * blockDim.x + threadIdx.x;
  const unsigned col = blockIdx.y;
  const bf result = values.get(src_row, col);
  results.set(dst_row, col, result);
}

EXTERN __global__ void ab_gather_leaf_rows_kernel(const unsigned *indexes, const unsigned indexes_count, const bool bit_reverse_indexes,
                                                  const unsigned log_leaves_count, const unsigned log_rows_per_leaf,
                                                  const matrix_getter<bf, ld_modifier::cs> values, const matrix_setter<bf, st_modifier::cs> results) {
  const unsigned idx = threadIdx.y + blockIdx.x * blockDim.y;
  if (idx >= indexes_count)
    return;
  const unsigned i = indexes[idx];
  const unsigned leaf_index = bit_reverse_indexes ? __brev(i) >> (32 - log_leaves_count) : i;
  const unsigned leaves_count = 1u << log_leaves_count;
  const unsigned src_row = leaf_index + bitreverse_low_bits(threadIdx.x, log_rows_per_leaf) * leaves_count;
  const unsigned dst_row = (idx << log_rows_per_leaf) + threadIdx.x;
  const unsigned col = blockIdx.y;
  const bf result = values.get(src_row, col);
  results.set(dst_row, col, result);
}

EXTERN __global__ void ab_gather_merkle_paths_kernel(const unsigned *indexes, const unsigned indexes_count, const u32 *values, const unsigned log_leaves_count,
                                                     u32 *results) {
  const unsigned idx = threadIdx.y + blockIdx.x * blockDim.y;
  if (idx >= indexes_count)
    return;
  const unsigned leaf_index = indexes[idx];
  const unsigned layer_index = blockIdx.y;
  const unsigned layer_offset = ((1u << log_leaves_count + 1) - (1u << log_leaves_count + 1 - layer_index)) * STATE_SIZE;
  const unsigned hash_offset = (leaf_index >> layer_index ^ 1) * STATE_SIZE;
  const unsigned element_offset = threadIdx.x;
  const unsigned src_index = layer_offset + hash_offset + element_offset;
  const unsigned dst_index = layer_index * indexes_count * STATE_SIZE + idx * STATE_SIZE + element_offset;
  results[dst_index] = values[src_index];
}

EXTERN __global__ void ab_gather_rows_and_merkle_paths_kernel(const unsigned *indexes, const unsigned indexes_count, const bool bit_reverse_indexes,
                                                              const bf *values, const unsigned log_rows_per_leaf, const unsigned cols_count,
                                                              const unsigned log_total_leaves_count, const matrix_setter<bf, st_modifier::cs> leaf_values,
                                                              const u32 *tree_bottom, const unsigned layers_count, u32 *merkle_paths) {
  // This fused kernel is for partial-tree queries: it hashes the queried leaves, writes the first
  // LOG_WARP_SIZE sibling layers from warp-local reductions, then resumes path collection from
  // the cached upper tree pointed to by tree_bottom.
  const unsigned lane_idx = threadIdx.x;
  const unsigned idx = blockIdx.x;
  if (idx >= indexes_count)
    return;
  const unsigned query_index = indexes[idx];
  const unsigned index_lane = (query_index & ~WARP_MASK) | lane_idx;
  const bool is_output_lane = query_index == index_lane;
  const unsigned leaf_index = bit_reverse_indexes ? __brev(index_lane) >> (32 - log_total_leaves_count) : index_lane;
  const unsigned log_rows_count = log_total_leaves_count + log_rows_per_leaf;
  const unsigned leaves_count = 1u << log_total_leaves_count;
  merkle_paths += idx * STATE_SIZE;
  auto read = [=](const unsigned offset) {
    const unsigned row_slot = offset & ((1u << log_rows_per_leaf) - 1);
    const unsigned col = offset >> log_rows_per_leaf;
    const unsigned row = leaf_index + bitreverse_low_bits(row_slot, log_rows_per_leaf) * leaves_count;
    const auto address = values + row + (col << log_rows_count);
    return col < cols_count ? bf::into_raw_u32(load_cs(address)) : 0;
  };
  u32 state[STATE_SIZE];
  u32 block[BLOCK_SIZE];
  initialize(state);
  u32 t = 0;
  const unsigned values_count = cols_count << log_rows_per_leaf;
  unsigned offset = 0;
  while (offset < values_count) {
    const unsigned remaining = values_count - offset;
    const bool is_final_block = remaining <= BLOCK_SIZE;
#pragma unroll
    for (unsigned i = 0; i < BLOCK_SIZE; i++, offset++) {
      const u32 value = read(offset);
      block[i] = value;
      if (is_output_lane && offset < values_count) {
        const unsigned row = offset & ((1u << log_rows_per_leaf) - 1);
        const unsigned col = offset >> log_rows_per_leaf;
        leaf_values.set((idx << log_rows_per_leaf) + row, col, bf::from_reduced_raw_repr(value));
      }
    }
    if (is_final_block)
      compress<true>(state, t, block, remaining);
    else
      compress<false>(state, t, block, BLOCK_SIZE);
  }
#pragma unroll
  for (unsigned layer = 0; layer < LOG_WARP_SIZE; layer++) {
    u32 other_state[STATE_SIZE];
    const bool take_other_first = (lane_idx >> layer) & 1;
#pragma unroll
    for (unsigned i = 0; i < STATE_SIZE; i++) {
      other_state[i] = __shfl_xor_sync(FULL_MASK, state[i], 1 << layer);
      if (is_output_lane)
        merkle_paths[i] = other_state[i];
      if (take_other_first) {
        block[i] = other_state[i];
        block[i + STATE_SIZE] = state[i];
      } else {
        block[i] = state[i];
        block[i + STATE_SIZE] = other_state[i];
      }
    }
    initialize(state);
    t = 0;
    compress<true>(state, t, block, BLOCK_SIZE);
    merkle_paths += indexes_count * STATE_SIZE;
  }
  if (lane_idx >= STATE_SIZE)
    return;
  unsigned digest_index = query_index >> LOG_WARP_SIZE;
  unsigned log_digests_count = log_total_leaves_count - LOG_WARP_SIZE;
  const u32 *tree_layer = tree_bottom + lane_idx;
  u32 *merkle_paths_dst = merkle_paths + lane_idx;
  for (unsigned layer = LOG_WARP_SIZE; layer < layers_count; layer++) {
    const unsigned other_index = digest_index ^ 1;
    *merkle_paths_dst = *(tree_layer + other_index * STATE_SIZE);
    digest_index >>= 1;
    tree_layer += (1u << log_digests_count) * STATE_SIZE;
    log_digests_count--;
    merkle_paths_dst += indexes_count * STATE_SIZE;
  }
}

EXTERN __global__ void ab_gather_merkle_paths_from_rows_kernel(const unsigned *indexes, const unsigned indexes_count, const bool bit_reverse_indexes,
                                                               const bf *values, const unsigned log_rows_per_leaf, const unsigned cols_count,
                                                               const unsigned log_total_leaves_count, const u32 *tree_bottom, const unsigned layers_count,
                                                               u32 *merkle_paths) {
  const unsigned lane_idx = threadIdx.x;
  const unsigned idx = blockIdx.x;
  if (idx >= indexes_count)
    return;
  const unsigned query_index = indexes[idx];
  const unsigned index_lane = (query_index & ~WARP_MASK) | lane_idx;
  const bool is_output_lane = query_index == index_lane;
  const unsigned leaf_index = bit_reverse_indexes ? __brev(index_lane) >> (32 - log_total_leaves_count) : index_lane;
  const unsigned log_rows_count = log_total_leaves_count + log_rows_per_leaf;
  const unsigned leaves_count = 1u << log_total_leaves_count;
  merkle_paths += idx * STATE_SIZE;
  auto read = [=](const unsigned offset) {
    const unsigned row_slot = offset & ((1u << log_rows_per_leaf) - 1);
    const unsigned col = offset >> log_rows_per_leaf;
    const unsigned row = leaf_index + bitreverse_low_bits(row_slot, log_rows_per_leaf) * leaves_count;
    const auto address = values + row + (col << log_rows_count);
    return col < cols_count ? bf::into_raw_u32(load_cs(address)) : 0;
  };
  u32 state[STATE_SIZE];
  u32 block[BLOCK_SIZE];
  initialize(state);
  u32 t = 0;
  const unsigned values_count = cols_count << log_rows_per_leaf;
  unsigned offset = 0;
  while (offset < values_count) {
    const unsigned remaining = values_count - offset;
    const bool is_final_block = remaining <= BLOCK_SIZE;
#pragma unroll
    for (unsigned i = 0; i < BLOCK_SIZE; i++, offset++)
      block[i] = read(offset);
    if (is_final_block)
      compress<true>(state, t, block, remaining);
    else
      compress<false>(state, t, block, BLOCK_SIZE);
  }
#pragma unroll
  for (unsigned layer = 0; layer < LOG_WARP_SIZE; layer++) {
    u32 other_state[STATE_SIZE];
    const bool take_other_first = (lane_idx >> layer) & 1;
#pragma unroll
    for (unsigned i = 0; i < STATE_SIZE; i++) {
      other_state[i] = __shfl_xor_sync(FULL_MASK, state[i], 1 << layer);
      if (is_output_lane)
        merkle_paths[i] = other_state[i];
      if (take_other_first) {
        block[i] = other_state[i];
        block[i + STATE_SIZE] = state[i];
      } else {
        block[i] = state[i];
        block[i + STATE_SIZE] = other_state[i];
      }
    }
    initialize(state);
    t = 0;
    compress<true>(state, t, block, BLOCK_SIZE);
    merkle_paths += indexes_count * STATE_SIZE;
  }
  if (lane_idx >= STATE_SIZE)
    return;
  unsigned digest_index = query_index >> LOG_WARP_SIZE;
  unsigned log_digests_count = log_total_leaves_count - LOG_WARP_SIZE;
  const u32 *tree_layer = tree_bottom + lane_idx;
  u32 *merkle_paths_dst = merkle_paths + lane_idx;
  for (unsigned layer = LOG_WARP_SIZE; layer < layers_count; layer++) {
    const unsigned other_index = digest_index ^ 1;
    *merkle_paths_dst = *(tree_layer + other_index * STATE_SIZE);
    digest_index >>= 1;
    tree_layer += (1u << log_digests_count) * STATE_SIZE;
    log_digests_count--;
    merkle_paths_dst += indexes_count * STATE_SIZE;
  }
}

// Gather Merkle-tree cap regions from N source buffers into one contiguous destination, in the
// order given by `src_ptrs`. Each block handles one coset; threads stripe the per-coset copy.
// `src_ptrs[i]` is a u64 carrying the device pointer to coset i's cap region
// (cap_words_per_coset u32s). The kernel reinterprets it as `const u32 *` on device.
// dst[i*cap_words_per_coset .. (i+1)*cap_words_per_coset] receives that coset's data.
EXTERN __global__ void ab_gather_tree_caps_kernel(const unsigned long long *src_ptrs, u32 *dst, const unsigned cap_words_per_coset,
                                                  const unsigned coset_count) {
  const unsigned coset_idx = blockIdx.x;
  if (coset_idx >= coset_count)
    return;
  const u32 *src = reinterpret_cast<const u32 *>(src_ptrs[coset_idx]);
  u32 *coset_dst = dst + coset_idx * cap_words_per_coset;
  for (unsigned i = threadIdx.x; i < cap_words_per_coset; i += blockDim.x) {
    coset_dst[i] = src[i];
  }
}

// Mirror of `GpuGatherTreeCapsDesc` in gpu_prover/src/ops/blake2s.rs.
// Consolidated-tree form: a single base pointer + per-coset stride lets the
// kernel gather all per-coset cap regions from one contiguous tree backing.
// The kernel folds the natural→bit-reversed coset reindex inline so the
// unified-cap destination layout matches the legacy stage1 ordering.
constexpr unsigned GKR_GATHER_TREE_CAPS_MAX_COSETS = 32;

struct gpu_gather_tree_caps_desc {
  u32 coset_count;
  u32 cap_words_per_coset;
  u32 stride_per_coset_in_u32_words;
  u32 log_lde_factor;
  unsigned long long base_ptr;
};

static_assert(sizeof(gpu_gather_tree_caps_desc) <= 32u * 1024u, "gpu_gather_tree_caps_desc must fit under the 32 KB inline kernel-arg ceiling");

// Inline-descriptor variant of `ab_gather_tree_caps_kernel`. Each block
// gathers one coset's cap region from a single contiguous backing:
//   src[natural_idx] = base + natural_idx * stride
//   dst[stage1_pos] = bitreverse(natural_idx, log_lde_factor) * cap_words
// The bit-reversal preserves the legacy stage1 coset ordering used by the
// per-coset readers (e.g. read_per_coset_caps_synchronously).
EXTERN __global__ void ab_gather_tree_caps_inline_kernel(__grid_constant__ const gpu_gather_tree_caps_desc desc, u32 *dst) {
  const unsigned natural_idx = blockIdx.x;
  if (natural_idx >= desc.coset_count)
    return;
  unsigned stage1_pos = 0;
  for (unsigned b = 0; b < desc.log_lde_factor; ++b) {
    stage1_pos |= ((natural_idx >> b) & 1u) << (desc.log_lde_factor - 1u - b);
  }
  const u32 *src = reinterpret_cast<const u32 *>(desc.base_ptr) + natural_idx * desc.stride_per_coset_in_u32_words;
  u32 *coset_dst = dst + stage1_pos * desc.cap_words_per_coset;
  for (unsigned i = threadIdx.x; i < desc.cap_words_per_coset; i += blockDim.x) {
    coset_dst[i] = src[i];
  }
}

// Mirror of `GpuGatherEAddressesDesc` in gpu_prover/src/ops/blake2s.rs.
// Holds the per-launch source-pointer table inline as kernel-arg data —
// replaces the prior per-launch H2D of the pointer table.
constexpr unsigned GKR_GATHER_MAX_ADDRESSES = 1280;

struct gpu_gather_e_addresses_desc {
  u32 num_addresses;
  u32 elements_per_addr;
  unsigned long long src_ptrs[GKR_GATHER_MAX_ADDRESSES];
};

static_assert(sizeof(gpu_gather_e_addresses_desc) <= 32u * 1024u, "gpu_gather_e_addresses_desc must fit under the 32 KB inline kernel-arg ceiling");

// Gather E4 evaluations from N source buffers (one per address) into one
// contiguous destination, in the order given by desc.src_ptrs. Each block
// handles one address; threads stripe the per-address copy. desc.src_ptrs[i]
// is a u64 carrying the device pointer to address i's `elements_per_addr`
// E4 values. dst[i*elements_per_addr .. (i+1)*elements_per_addr] receives
// that address's data. Internally copies `elements_per_addr * 4` u32 words
// per address (each E4 is 16 bytes / 4 u32 words). Replaces the per-address
// `memory_copy_async` loop in the backward schedulers with a single launch.
EXTERN __global__ void ab_gather_e_addresses_kernel(__grid_constant__ const gpu_gather_e_addresses_desc desc, u32 *dst) {
  const unsigned addr_idx = blockIdx.x;
  if (addr_idx >= desc.num_addresses)
    return;
  const u32 *src = reinterpret_cast<const u32 *>(desc.src_ptrs[addr_idx]);
  const unsigned words_per_addr = desc.elements_per_addr * 4u;
  u32 *addr_dst = dst + addr_idx * words_per_addr;
  for (unsigned i = threadIdx.x; i < words_per_addr; i += blockDim.x) {
    addr_dst[i] = src[i];
  }
}

// Phase 3 (WHIR-on-device): per-query, compute the merkle tree-index from a raw
// query index. The verifier's BaseFieldQuery.index expects the tree-space index
//   tree = bitreverse(coset, log_lde) * coset_tree_size + internal
// where coset = q & (lde-1) and internal = q >> log_lde_factor. One thread per
// query.
EXTERN __global__ void ab_query_index_to_tree_index_kernel(const u32 *d_query_indexes, u32 *d_out, const u32 indexes_count, const u32 log_lde_factor,
                                                           const u32 coset_tree_size_log2) {
  const unsigned i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i >= indexes_count)
    return;
  const u32 q = d_query_indexes[i];
  const u32 lde_mask = log_lde_factor == 0u ? 0u : ((1u << log_lde_factor) - 1u);
  const u32 coset = q & lde_mask;
  const u32 internal = q >> log_lde_factor;
  const u32 coset_dest = log_lde_factor == 0u ? 0u : (__brev(coset) >> (32u - log_lde_factor));
  const u32 tree_idx = (coset_dest << coset_tree_size_log2) | internal;
  d_out[i] = tree_idx;
}

// Phase 3 (WHIR-on-device, GKR consolidation): single-launch base-field leaf
// gather across all LDE cosets and up to three oracles. The kernel reads the
// consolidated cosets backing
// for each active oracle: coset `c` lives at
//   base + c * (desc.columns_count << log_domain_size)
// elements (column-major within each coset, stride = 1 << log_domain_size).
// Thread mapping mirrors the legacy kernel: threadIdx.x = v ∈ [0, rows_per_leaf),
// (threadIdx.y, blockIdx.x) tile the queries, blockIdx.y = column, and
// blockIdx.z = oracle index (0..num_oracles). The per-oracle grid.y bound is
// the max columns_count across active oracles, so each oracle guards
// `col >= desc.columns_count`. Oracles with columns_count == 0 are skipped.
struct gpu_oracle_gather_desc {
  unsigned long long cosets_ptr; // const bf*, consolidated cosets backing for one oracle
  u32 columns_count;             // 0 if this slot is unused or oracle has no columns
  u32 _pad;
  unsigned long long slab_dst_ptr; // bf*, slab destination for this oracle
};

static_assert(sizeof(gpu_oracle_gather_desc) <= 32u * 1024u, "gpu_oracle_gather_desc must fit under the 32 KB inline kernel-arg ceiling");

EXTERN __global__ void ab_gather_leaves_for_queries_kernel(const u32 num_oracles, __grid_constant__ const gpu_oracle_gather_desc desc0,
                                                           __grid_constant__ const gpu_oracle_gather_desc desc1,
                                                           __grid_constant__ const gpu_oracle_gather_desc desc2, const u32 log_lde_factor,
                                                           const u32 log_domain_size, const u32 log_rows_per_leaf, const u32 *query_indexes,
                                                           const u32 indexes_count) {
  const unsigned oracle_idx = blockIdx.z;
  if (oracle_idx >= num_oracles)
    return;
  const gpu_oracle_gather_desc desc = oracle_idx == 0u ? desc0 : (oracle_idx == 1u ? desc1 : desc2);
  if (desc.columns_count == 0u)
    return;
  const unsigned idx = threadIdx.y + blockIdx.x * blockDim.y;
  if (idx >= indexes_count)
    return;
  const unsigned col = blockIdx.y;
  if (col >= desc.columns_count)
    return;
  const unsigned q = query_indexes[idx];
  const unsigned lde_mask = log_lde_factor == 0u ? 0u : ((1u << log_lde_factor) - 1u);
  const unsigned coset = q & lde_mask;
  const unsigned internal_index = q >> log_lde_factor;
  const unsigned v = threadIdx.x;
  const unsigned log_rows_count = log_domain_size;
  const unsigned log_leaves_count = log_rows_count - log_rows_per_leaf;
  const unsigned leaves_count = 1u << log_leaves_count;
  const unsigned values_per_leaf = 1u << log_rows_per_leaf;
  const unsigned src_row = internal_index + bitreverse_low_bits(v, log_rows_per_leaf) * leaves_count;
  const unsigned domain_size = 1u << log_domain_size;
  const unsigned stride_per_coset = desc.columns_count << log_domain_size;
  const bf *base = reinterpret_cast<const bf *>(desc.cosets_ptr) + coset * stride_per_coset;
  const bf result = load_cs(base + col * domain_size + src_row);
  bf *slab_dst = reinterpret_cast<bf *>(desc.slab_dst_ptr);
  slab_dst[idx * (values_per_leaf * desc.columns_count) + v * desc.columns_count + col] = result;
}

// Phase 3 (WHIR-on-device, Step 3 consolidation): consolidated single-oracle
// Full-tree merkle-path gather. Each thread reads one digest word from the
// consolidated tree backing, resolving the per-coset segment via
// `coset = q & lde_mask`. The consolidated backing stores cosets in NATURAL
// order (coset c occupies
// `[c * stride_per_coset_in_digests, (c+1) * stride_per_coset_in_digests)`),
// matching `CosetsHolder::Full`/`TreesHolder::Full` indexing in
// `prover/trace/holder/mod.rs`. `stride_per_coset_in_digests` is the per-coset
// tree size in `Digest` items (= `2 * leaves_count` for Full mode); the kernel
// multiplies by `STATE_SIZE` internally to index into the `u32` view of the
// backing. `log_leaves_count` is per-coset, not whole tree.
//   slab[q * layers_count * STATE_SIZE + layer * STATE_SIZE + word]
EXTERN __global__ void ab_gather_merkle_paths_full_for_queries_kernel(const u32 *query_indexes, const u32 indexes_count, const u32 log_lde_factor,
                                                                      const u32 stride_per_coset_in_digests, const u32 *consolidated_tree,
                                                                      const u32 log_leaves_count, const u32 layers_count, u32 *slab_dst) {
  const u32 idx = threadIdx.y + blockIdx.x * blockDim.y;
  if (idx >= indexes_count)
    return;
  const u32 q = query_indexes[idx];
  const u32 lde_mask = log_lde_factor == 0u ? 0u : ((1u << log_lde_factor) - 1u);
  const u32 coset = q & lde_mask;
  const u32 leaf_index = q >> log_lde_factor;
  const u32 layer_index = blockIdx.y;
  const u32 layer_offset = ((1u << log_leaves_count + 1) - (1u << log_leaves_count + 1 - layer_index)) * STATE_SIZE;
  const u32 hash_offset = (leaf_index >> layer_index ^ 1) * STATE_SIZE;
  const u32 element_offset = threadIdx.x;
  const u32 coset_offset = coset * stride_per_coset_in_digests * STATE_SIZE;
  const u32 src_index = coset_offset + layer_offset + hash_offset + element_offset;
  const u32 dst_index = idx * layers_count * STATE_SIZE + layer_index * STATE_SIZE + element_offset;
  slab_dst[dst_index] = consolidated_tree[src_index];
}

// Phase 3 (WHIR-on-device, GKR consolidation): consolidated multi-oracle
// Partial-tree merkle-path gather. Hashes the bottom `LOG_WARP_SIZE` layers on
// the fly from the consolidated per-oracle BF cosets backing via warp-shuffle
// compression; reads the upper layers from the consolidated per-oracle
// partial-tree backing.
//
// Per-oracle consolidated cosets backing: coset `c` lives at
//   base_bf + c * (desc.columns_count << log_domain_size)
// elements (column-major within each coset, stride = 1 << log_domain_size).
// Per-oracle consolidated partial-tree backing: coset `c` lives at
//   base_digests + c * stride_per_coset_in_digests digests
// (multiplied by STATE_SIZE for the u32 view). `stride_per_coset_in_digests`
// matches `1 << (log_total_leaves_count + 1 - LOG_WARP_SIZE)` (= per-coset
// partial-tree length in digests for `TreesHolder::Partial`).
//
// Thread mapping: gridDim.x = indexes_count, blockDim.x = WARP_SIZE. The oracle
// dimension uses gridDim.y. Oracles with columns_count == 0 are skipped.
struct gpu_oracle_partial_path_desc {
  unsigned long long cosets_ptr;       // const bf*, consolidated cosets backing for one oracle
  unsigned long long partial_tree_ptr; // const u32*, consolidated partial-tree (digest words) for one oracle
  u32 columns_count;                   // 0 == inactive slot, kernel skips
  u32 _pad;
  unsigned long long slab_dst_ptr; // u32*, slab destination for this oracle
};

static_assert(sizeof(gpu_oracle_partial_path_desc) <= 32u * 1024u, "gpu_oracle_partial_path_desc must fit under the 32 KB inline kernel-arg ceiling");

EXTERN __global__ void ab_gather_merkle_paths_partial_for_queries_kernel(const u32 num_oracles, __grid_constant__ const gpu_oracle_partial_path_desc desc0,
                                                                         __grid_constant__ const gpu_oracle_partial_path_desc desc1,
                                                                         __grid_constant__ const gpu_oracle_partial_path_desc desc2, const u32 log_lde_factor,
                                                                         const u32 log_rows_per_leaf, const u32 log_total_leaves_count,
                                                                         const u32 stride_per_coset_in_digests, const u32 layers_count,
                                                                         const u32 *query_indexes, const u32 indexes_count) {
  const u32 oracle_idx = blockIdx.y;
  if (oracle_idx >= num_oracles)
    return;
  const gpu_oracle_partial_path_desc desc = oracle_idx == 0u ? desc0 : (oracle_idx == 1u ? desc1 : desc2);
  if (desc.columns_count == 0u)
    return;

  const unsigned lane_idx = threadIdx.x;
  const unsigned idx = blockIdx.x;
  if (idx >= indexes_count)
    return;

  const unsigned q = query_indexes[idx];
  const unsigned lde_mask = log_lde_factor == 0u ? 0u : ((1u << log_lde_factor) - 1u);
  const unsigned coset = q & lde_mask;
  const unsigned query_index = q >> log_lde_factor;

  // Per-coset bases (per-oracle).
  const unsigned log_domain_size = log_total_leaves_count + log_rows_per_leaf;
  const bf *values = reinterpret_cast<const bf *>(desc.cosets_ptr) + (size_t)coset * ((size_t)desc.columns_count << log_domain_size);
  const u32 *tree_bottom = reinterpret_cast<const u32 *>(desc.partial_tree_ptr) + (size_t)coset * (size_t)stride_per_coset_in_digests * STATE_SIZE;
  u32 *slab_dst = reinterpret_cast<u32 *>(desc.slab_dst_ptr);
  const unsigned cols_count = desc.columns_count;

  // Warp-shuffle hashing of bottom layers + walk of the cached partial-tree
  // bottom for upper layers. `values` / `tree_bottom` / `slab_dst` are resolved
  // per (oracle, coset) above.
  const unsigned index_lane = (query_index & ~WARP_MASK) | lane_idx;
  const bool is_output_lane = query_index == index_lane;
  const unsigned leaf_index = index_lane;
  const unsigned log_rows_count = log_total_leaves_count + log_rows_per_leaf;
  const unsigned leaves_count = 1u << log_total_leaves_count;
  u32 *merkle_paths = slab_dst + idx * layers_count * STATE_SIZE;
  auto read = [=](const unsigned offset) {
    const unsigned row_slot = offset & ((1u << log_rows_per_leaf) - 1);
    const unsigned col = offset >> log_rows_per_leaf;
    const unsigned row = leaf_index + bitreverse_low_bits(row_slot, log_rows_per_leaf) * leaves_count;
    const auto address = values + row + (col << log_rows_count);
    return col < cols_count ? bf::into_raw_u32(load_cs(address)) : 0;
  };
  u32 state[STATE_SIZE];
  u32 block[BLOCK_SIZE];
  initialize(state);
  u32 t = 0;
  const unsigned values_count = cols_count << log_rows_per_leaf;
  unsigned offset = 0;
  while (offset < values_count) {
    const unsigned remaining = values_count - offset;
    const bool is_final_block = remaining <= BLOCK_SIZE;
#pragma unroll
    for (unsigned i = 0; i < BLOCK_SIZE; i++, offset++)
      block[i] = read(offset);
    if (is_final_block)
      compress<true>(state, t, block, remaining);
    else
      compress<false>(state, t, block, BLOCK_SIZE);
  }
#pragma unroll
  for (unsigned layer = 0; layer < LOG_WARP_SIZE; layer++) {
    u32 other_state[STATE_SIZE];
    const bool take_other_first = (lane_idx >> layer) & 1;
#pragma unroll
    for (unsigned i = 0; i < STATE_SIZE; i++) {
      other_state[i] = __shfl_xor_sync(FULL_MASK, state[i], 1 << layer);
      if (is_output_lane)
        merkle_paths[i] = other_state[i];
      if (take_other_first) {
        block[i] = other_state[i];
        block[i + STATE_SIZE] = state[i];
      } else {
        block[i] = state[i];
        block[i + STATE_SIZE] = other_state[i];
      }
    }
    initialize(state);
    t = 0;
    compress<true>(state, t, block, BLOCK_SIZE);
    merkle_paths += STATE_SIZE;
  }
  if (lane_idx >= STATE_SIZE)
    return;
  unsigned digest_index = query_index >> LOG_WARP_SIZE;
  unsigned log_digests_count = log_total_leaves_count - LOG_WARP_SIZE;
  const u32 *tree_layer = tree_bottom + lane_idx;
  u32 *merkle_paths_dst = merkle_paths + lane_idx;
  for (unsigned layer = LOG_WARP_SIZE; layer < layers_count; layer++) {
    const unsigned other_index = digest_index ^ 1;
    *merkle_paths_dst = *(tree_layer + other_index * STATE_SIZE);
    digest_index >>= 1;
    tree_layer += (1u << log_digests_count) * STATE_SIZE;
    log_digests_count--;
    merkle_paths_dst += STATE_SIZE;
  }
}

} // namespace airbender::ops::blake2s
