#include "keccak256.cuh"

namespace airbender::hash::keccak256 {

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

// Path layers 3..log_leaves-1 of the queries in coset *coset (an openings slot, gated by *gate), block = query: layers below
// skip_bottom from the depth-3 nodes of the query's subtree (nodes[j >> 3] of the slot's coset), the rest from the coset's
// retained tree retained_all[*coset * retained_stride + ...].
EXTERN __launch_bounds__(128) __global__
    void ab_keccak256_open_paths_kernel(const digest *nodes, const digest *retained_all, const u64 retained_stride, const u32 *coset, const u32 *gate,
                                        const u32 *queries, const u32 log_lde, const u32 log_leaves, const u32 skip_bottom, const u32 depth, digest *paths) {
  __shared__ digest subtree[128];
  if (gate && !*gate)
    return;
  const u32 query = queries[blockIdx.x];
  if (query >= (u64{1} << (log_leaves + log_lde)))
    __trap();
  if ((query & ((1u << log_lde) - 1)) != *coset)
    return;
  const u32 tid = threadIdx.x;
  const u32 leaf = query >> log_lde;
  digest *path = paths + static_cast<u64>(blockIdx.x) * depth;
  const u32 width = 1u << (skip_bottom - 3);
  for (u32 i = tid; i < width; i += blockDim.x)
    subtree[i] = nodes[((leaf >> skip_bottom) << (skip_bottom - 3)) + i];
  __syncthreads();
  for (u32 layer = 3; layer < skip_bottom; layer++) {
    const u32 count = 1u << (skip_bottom - layer);
    if (tid == 0)
      path[layer] = subtree[((leaf >> layer) & (count - 1)) ^ 1];
    digest parent;
    if (tid < count / 2)
      parent = hash_node(subtree[2 * tid], subtree[2 * tid + 1]);
    __syncthreads();
    if (tid < count / 2)
      subtree[tid] = parent;
    __syncthreads();
  }
  const digest *retained = retained_all + static_cast<u64>(*coset) * retained_stride;
  const u64 leaves = u64{1} << log_leaves;
  for (u32 layer = skip_bottom + tid; layer < log_leaves; layer += blockDim.x)
    path[layer] = retained[2 * (leaves >> skip_bottom) - 2 * (leaves >> layer) + ((leaf >> layer) ^ 1)];
}

// Distinct physical cosets of the queries in first-occurrence order: touched[s] (s < count), count, and active[s] = s < count
// (inactive slots get touched 0). One warp, thread = query.
EXTERN __launch_bounds__(1024) __global__
    void ab_keccak256_coset_query_plan_kernel(const u32 *queries, const u32 count, const u32 log_lde, u32 *touched, u32 *active, u32 *touched_count) {
  __shared__ u32 first[1u << 12];
  __shared__ u32 warp_counts[32];
  const u32 tid = threadIdx.x;
  const u32 lane = tid & 31;
  const u32 warp = tid >> 5;
  for (u32 coset = tid; coset < (1u << log_lde); coset += blockDim.x)
    first[coset] = ~0u;
  __syncthreads();
  const u32 coset = tid < count ? queries[tid] & ((1u << log_lde) - 1) : 0;
  if (tid < count)
    atomicMin(&first[coset], tid);
  __syncthreads();
  const bool leading = tid < count && first[coset] == tid;
  const u32 ballot = __ballot_sync(0xffffffffu, leading);
  if (lane == 0)
    warp_counts[warp] = __popc(ballot);
  __syncthreads();
  u32 before = 0;
  u32 total = 0;
  for (u32 w = 0; w < blockDim.x / 32; w++) {
    before += w < warp ? warp_counts[w] : 0;
    total += warp_counts[w];
  }
  const u32 slot = before + __popc(ballot & ((1u << lane) - 1));
  if (leading)
    touched[slot] = coset;
  if (tid < count) {
    active[tid] = tid < total;
    if (tid >= total)
      touched[tid] = 0;
  }
  if (tid == 0)
    *touched_count = total;
}

} // namespace airbender::hash::keccak256
