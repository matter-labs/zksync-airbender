#include "keccak256.cuh"

namespace airbender::hash::keccak256 {

EXTERN __global__ void ab_keccak256_partial_roots_kernel(const proth120 *values, const u32 log_domain, const u32 log_v, const u32 columns,
                                                         const u32 skip_bottom, const u32 cosets_in_tile, const u64 values_stride, const u64 retained_stride,
                                                         digest *retained) {
  __shared__ digest nodes[256];
  const u32 log_leaves = log_domain - log_v;
  const u64 leaf_mask = (u64{1} << log_leaves) - 1;
  const u64 count = static_cast<u64>(cosets_in_tile) << log_leaves;
  const u64 first = static_cast<u64>(blockIdx.x) * blockDim.x;
  const u64 gid = first + threadIdx.x;
  if (gid < count)
    nodes[threadIdx.x] = hash_leaf(values + (gid >> log_leaves) * values_stride, log_domain, log_v, columns, static_cast<u32>(gid & leaf_mask));
  for (u32 layer = 1; layer <= skip_bottom; layer++) {
    __syncthreads();
    const bool active = threadIdx.x < (blockDim.x >> layer) && first + (static_cast<u64>(threadIdx.x) << layer) < count;
    digest parent;
    if (active)
      parent = hash_node(nodes[2 * threadIdx.x], nodes[2 * threadIdx.x + 1]);
    __syncthreads();
    if (active)
      nodes[threadIdx.x] = parent;
  }
  const u64 subtree = first + (static_cast<u64>(threadIdx.x) << skip_bottom);
  if (threadIdx.x < (blockDim.x >> skip_bottom) && subtree < count)
    retained[(subtree >> log_leaves) * retained_stride + ((subtree & leaf_mask) >> skip_bottom)] = nodes[threadIdx.x];
}

EXTERN __global__ void ab_keccak256_reduce_roots_kernel(const digest *src, const u64 count, const u32 reduction_layers, digest *dst) {
  const u64 gid = static_cast<u64>(blockIdx.x) * blockDim.x + threadIdx.x;
  const u64 input_count = count << reduction_layers;
  digest root{};
  if (gid < input_count)
    root = src[gid];
  for (u32 layer = 0; layer < reduction_layers; layer++) {
    digest sibling;
#pragma unroll
    for (u32 word = 0; word < 8; word++)
      sibling.words[word] = __shfl_xor_sync(0xffffffffu, root.words[word], 1u << layer);
    if (gid < input_count && (threadIdx.x & ((1u << (layer + 1)) - 1)) == 0)
      root = hash_node(root, sibling);
  }
  if (gid < input_count && (threadIdx.x & ((1u << reduction_layers) - 1)) == 0)
    dst[gid >> reduction_layers] = root;
}

EXTERN __global__ void ab_keccak256_nodes_kernel(const digest *src, const u64 count, const u32 cosets_in_tile, const u64 src_stride, const u64 dst_stride,
                                                 digest *dst) {
  const u64 gid = static_cast<u64>(blockIdx.x) * blockDim.x + threadIdx.x;
  if (gid >= cosets_in_tile * count)
    return;
  const u64 coset = gid / count;
  const u64 index = gid % count;
  const digest *children = src + coset * src_stride + 2 * index;
  dst[coset * dst_stride + index] = hash_node(children[0], children[1]);
}

EXTERN __global__ void ab_keccak256_gather_cap_kernel(const digest *src, const u64 count, digest *dst) {
  const u64 gid = static_cast<u64>(blockIdx.x) * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;
  dst[gid] = src[gid];
}

} // namespace airbender::hash::keccak256
