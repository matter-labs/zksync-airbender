#include "common.cuh"
#include "keccak256.cuh"
#include "primitives/proth120.cuh"
#include "proth120/context.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;
using ::airbender::hash::keccak256::digest;
using ::airbender::ntt::pr_root_power;
using ::airbender::ntt::proth120_twiddle_descriptor;

namespace airbender::whir {

DEVICE_FORCEINLINE u64 pr_whir_sibling_offset(const u32 log_leaves, const u32 skip_bottom, const u32 level, const u32 j) {
  return (2ull << (log_leaves - skip_bottom)) - (2ull << (log_leaves - level)) + ((j >> level) ^ 1u);
}

EXTERN __launch_bounds__(256) __global__
    void ab_pr_whir_subtree_points_kernel(const u32 *queries, const u32 count, const u32 query_domain_log2, const u32 log_lde, const u32 skip_bottom,
                                          const proth120_twiddle_descriptor d, const u32 log_domain, pr *points) {
  const u64 gid = static_cast<u64>(blockIdx.x) * blockDim.x + threadIdx.x;
  const u32 query = static_cast<u32>(gid >> skip_bottom);
  if (query >= count)
    return;
  const u32 q = queries[query];
  if (static_cast<u64>(q) >> query_domain_log2) {
    __trap();
    return;
  }
  const u32 k_mask = (1u << skip_bottom) - 1u;
  const u32 c = q & ((1u << log_lde) - 1u);
  const u32 j = q >> log_lde;
  const u32 q_m = c + (((j & ~k_mask) + (static_cast<u32>(gid) & k_mask)) << log_lde);
  const u32 log_v = log_domain - query_domain_log2;
  const u64 exponent = ((static_cast<u64>(q_m) << log_v) << (d.log_max_domain - log_domain)) & ((u64{1} << d.log_max_domain) - 1);
  points[gid] = pr_root_power(d, exponent);
}

EXTERN __launch_bounds__(256) __global__ void ab_pr_whir_horner_leaves_kernel(const pr *monomials, const u32 log_n, const u32 log_v, const pr *points,
                                                                              pr *leaves, const u32 count, const u32 tower_log_k) {
  const u32 leaf = blockIdx.x;
  if (leaf >= count)
    return;
  __shared__ pr partials[256];
  const u32 tid = threadIdx.x;
  const u32 values = 1u << log_v;
  const u32 slot = tid & (values - 1u);
  const u32 parts = 256u >> log_v;
  const pr y = points[leaf];
  const pr y_parts = pr::pow(y, parts);
  pr result = pr::ZERO();
  for (u32 a = 1u << (log_n - 8); a > 0; a--)
    result = pr::fma(result, y_parts, load_cg(monomials + ((static_cast<u64>(a - 1u) << 8) + tid)));
  partials[tid] = result;
  __syncthreads();
  if (tid >= values)
    return;
  result = partials[((parts - 1u) << log_v) + slot];
  for (u32 part = parts - 1u; part > 0; part--)
    result = pr::fma(result, y, partials[((part - 1u) << log_v) + slot]);
  const u64 offset = tower_log_k == 0 ? (static_cast<u64>(leaf) << log_v) + slot
                                      : (static_cast<u64>(leaf >> tower_log_k) << (tower_log_k + log_v)) + (leaf & ((1u << tower_log_k) - 1u)) +
                                            (static_cast<u64>(bitreverse_low_bits(slot, log_v)) << tower_log_k);
  leaves[offset] = result;
}

EXTERN __launch_bounds__(128) __global__
    void ab_pr_whir_extract_paths_kernel(const pr *leaves, const digest *towers, const digest *retained, const u64 retained_stride, const u32 log_lde,
                                         const u32 log_leaves, const u32 skip_bottom, const u32 log_v, const u32 *queries, pr *out_leaves, digest *out_paths,
                                         const u32 path_stride, const u32 count) {
  const u32 query = blockIdx.x * 4u + (threadIdx.x >> 5);
  if (query >= count)
    return;
  const u32 q = queries[query];
  if (static_cast<u64>(q) >> (log_lde + log_leaves)) {
    __trap();
    return;
  }
  const u32 lane = threadIdx.x & 31u;
  const u32 c = q & ((1u << log_lde) - 1u);
  const u32 j = q >> log_lde;
  const u32 k = 1u << skip_bottom;
  if (lane < (1u << log_v))
    out_leaves[(static_cast<u64>(query) << log_v) + lane] =
        leaves[(static_cast<u64>(query) << (skip_bottom + log_v)) + (j & (k - 1u)) + (static_cast<u64>(bitreverse_low_bits(lane, log_v)) << skip_bottom)];
  if (lane < log_leaves) {
    const digest sibling = lane < skip_bottom ? towers[static_cast<u64>(query) * (2u * k - 1u) + pr_whir_sibling_offset(skip_bottom, 0, lane, j & (k - 1u))]
                                              : retained[static_cast<u64>(c) * retained_stride + pr_whir_sibling_offset(log_leaves, skip_bottom, lane, j)];
    out_paths[static_cast<u64>(query) * path_stride + lane] = sibling;
  }
}

} // namespace airbender::whir
