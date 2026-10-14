#include "keccak256.cuh"

namespace airbender::hash::keccak256 {

EXTERN __global__ void ab_keccak256_gather_leaves_kernel(const proth120 *values, const u32 resident_coset, const u32 log_lde, const u32 log_domain,
                                                         const u32 log_v, const u64 columns, const u32 *queries, const u64 count, proth120 *out) {
  const u32 log_leaves = log_domain - log_v;
  const u64 leaf_values = columns << log_v;
  const u64 total = count * leaf_values;
  const u32 coset_mask = (1u << log_lde) - 1;
  const u64 query_limit = u64{1} << (log_leaves + log_lde);
  for (u64 gid = static_cast<u64>(blockIdx.x) * blockDim.x + threadIdx.x; gid < total; gid += static_cast<u64>(gridDim.x) * blockDim.x) {
    const u64 index = gid / leaf_values;
    const u32 query = queries[index];
    if (query >= query_limit)
      __trap();
    if ((query & coset_mask) != resident_coset)
      continue;
    const u64 within = gid % leaf_values;
    const u64 column = within % columns;
    const u32 slot = bitreverse_low_bits(static_cast<u32>(within / columns), log_v);
    const u32 leaf = query >> log_lde;
    out[gid] = values[(column << log_domain) + leaf + (static_cast<u64>(slot) << log_leaves)];
  }
}

EXTERN __global__ void ab_keccak256_gather_partial_paths_kernel(const proth120 *values, const u32 resident_coset, const u32 log_lde, const u32 log_domain,
                                                                const u32 log_v, const u64 columns, const u32 cap_log, const u32 skip_bottom,
                                                                const digest *retained, const u32 *queries, const u64 count, digest *paths) {
  const u64 index = blockIdx.x;
  if (index >= count)
    return;
  const u32 log_leaves = log_domain - log_v;
  const u32 query = queries[index];
  if (query >= (u64{1} << (log_leaves + log_lde)))
    __trap();
  if ((query & ((1u << log_lde) - 1)) != resident_coset)
    return;
  const u32 lane = threadIdx.x;
  const u32 leaf = query >> log_lde;
  const u32 group_mask = (1u << skip_bottom) - 1;
  const u32 output_lane = leaf & group_mask;
  const u32 depth = log_leaves + log_lde - cap_log;
  if (skip_bottom <= 5) {
    digest state{};
    if (lane <= group_mask)
      state = hash_leaf(values, log_domain, log_v, static_cast<u32>(columns), (leaf & ~group_mask) + lane);
    for (u32 layer = 0; layer < skip_bottom; layer++) {
      digest sibling;
#pragma unroll
      for (u32 word = 0; word < 8; word++)
        sibling.words[word] = __shfl_xor_sync(0xffffffffu, state.words[word], 1u << layer);
      if (lane == output_lane)
        paths[index * depth + layer] = sibling;
      digest left, right;
#pragma unroll
      for (u32 word = 0; word < 8; word++) {
        left.words[word] = (lane >> layer) & 1 ? sibling.words[word] : state.words[word];
        right.words[word] = (lane >> layer) & 1 ? state.words[word] : sibling.words[word];
      }
      state = hash_node(left, right);
    }
  } else {
    extern __shared__ digest nodes[];
    for (u32 slot = lane; slot <= group_mask; slot += blockDim.x)
      nodes[slot] = hash_leaf(values, log_domain, log_v, static_cast<u32>(columns), (leaf & ~group_mask) + slot);
    __syncthreads();
    for (u32 layer = 0; layer < skip_bottom; layer++) {
      const u32 sibling = (output_lane >> layer) ^ 1;
      if (lane == sibling % blockDim.x)
        paths[index * depth + layer] = nodes[sibling];
      const u32 parent_count = (1u << skip_bottom) >> (layer + 1);
      digest parents[2];
      for (u32 parent = lane; parent < parent_count; parent += blockDim.x)
        parents[parent / blockDim.x] = hash_node(nodes[2 * parent], nodes[2 * parent + 1]);
      __syncthreads();
      for (u32 parent = lane; parent < parent_count; parent += blockDim.x)
        nodes[parent] = parents[parent / blockDim.x];
      __syncthreads();
    }
  }
  if (lane >= 8)
    return;
  const u64 leaves = u64{1} << log_leaves;
  for (u32 layer = skip_bottom; layer < log_leaves; layer++) {
    const u64 offset = 2 * (leaves >> skip_bottom) - 2 * (leaves >> layer);
    paths[index * depth + layer].words[lane] = retained[offset + ((leaf >> layer) ^ 1)].words[lane];
  }
}

EXTERN __global__ void ab_keccak256_append_top_paths_kernel(const digest *roots, const digest *top_nodes, const u32 log_lde, const u32 cap_log,
                                                            const u32 log_coset_leaves, const u32 *queries, const u64 count, digest *paths, u32 *tree_indexes) {
  const u64 index = static_cast<u64>(blockIdx.x) * blockDim.x + threadIdx.x;
  if (index >= count)
    return;
  const u32 query = queries[index];
  if (query >= (u64{1} << (log_coset_leaves + log_lde)))
    __trap();
  const u32 cosets = 1u << log_lde;
  const u32 physical = bitreverse_low_bits(query & (cosets - 1), log_lde);
  const u32 leaf = query >> log_lde;
  const u32 depth = log_coset_leaves + log_lde - cap_log;
  tree_indexes[index] = (physical << log_coset_leaves) + leaf;
  for (u32 layer = 0; layer < log_lde - cap_log; layer++) {
    const u64 sibling = (physical >> layer) ^ 1;
    const digest value = layer == 0 ? roots[sibling] : top_nodes[cosets - (cosets >> (layer - 1)) + sibling];
    paths[index * depth + log_coset_leaves + layer] = value;
  }
}

} // namespace airbender::hash::keccak256
