#include <common.cuh>
#include <hash.cuh>
#include <primitives/memory.cuh>

using namespace ::airbender::primitives::memory;
using ::airbender::hash::bitreverse_low_bits;

namespace airbender::whir {

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
