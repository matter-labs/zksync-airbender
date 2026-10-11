#include "keccak256.cuh"

namespace airbender::hash::keccak256 {

EXTERN __global__ void ab_keccak256_hash_bytes_kernel(const u8 *input, u64 len, u8 *out) {
  if (blockIdx.x == 0 && threadIdx.x == 0) {
    u8 bytes[32];
    hash_bytes(input, len, bytes);
    const auto result = digest_from_bytes(bytes);
    digest_to_bytes(result, out);
  }
}

EXTERN __global__ void ab_keccak256_leaves_kernel(const proth120 *values, const u32 log_domain, const u32 log_v, const u32 columns, const u32 cosets_in_tile,
                                                  const u64 values_stride, const u64 out_stride, digest *out) {
  const u32 log_leaves = log_domain - log_v;
  const u64 gid = static_cast<u64>(blockIdx.x) * blockDim.x + threadIdx.x;
  if (gid >= static_cast<u64>(cosets_in_tile) << log_leaves)
    return;
  const u64 coset = gid >> log_leaves;
  const u32 leaf = static_cast<u32>(gid & ((u64{1} << log_leaves) - 1));
  out[coset * out_stride + leaf] = hash_leaf(values + coset * values_stride, log_domain, log_v, columns, leaf);
}

} // namespace airbender::hash::keccak256
