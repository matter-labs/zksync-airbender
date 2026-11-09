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

template <u32 COLUMNS, u32 LOG_V> DEVICE_FORCEINLINE void leaf_sponge_probe(const proth120 *values, const u32 log_domain, digest *out) {
  const u32 log_leaves = log_domain - LOG_V;
  const u32 leaf = blockIdx.x * blockDim.x + threadIdx.x;
  if (leaf >> log_leaves)
    return;
  leaf_sponge<(COLUMNS << LOG_V) * 2> sponge;
  static_for<(COLUMNS << LOG_V)>([&](auto element) {
    constexpr u32 E = decltype(element)::value;
    const u32 column = E >> LOG_V;
    const u32 slot = bitreverse_low_bits(E & ((1u << LOG_V) - 1), LOG_V);
    sponge.template absorb_element<E>(values[(static_cast<u64>(column) << log_domain) + leaf + (static_cast<u64>(slot) << log_leaves)]);
  });
  out[leaf] = sponge.finalize();
}

// Test support: `leaf_sponge` over the production (columns, values per leaf) shapes.
EXTERN __global__ void ab_keccak256_leaf_sponge_probe_kernel(const proth120 *values, const u32 log_domain, const u32 columns, const u32 log_v, digest *out) {
  if (columns == 1 && log_v == 1)
    leaf_sponge_probe<1, 1>(values, log_domain, out);
  else if (columns == 1 && log_v == 2)
    leaf_sponge_probe<1, 2>(values, log_domain, out);
  else if (columns == 1 && log_v == 3)
    leaf_sponge_probe<1, 3>(values, log_domain, out);
  else if (columns == 1 && log_v == 4)
    leaf_sponge_probe<1, 4>(values, log_domain, out);
  else if (columns == 2 && log_v == 1)
    leaf_sponge_probe<2, 1>(values, log_domain, out);
  else if (columns == 7 && log_v == 2)
    leaf_sponge_probe<7, 2>(values, log_domain, out);
  else if (columns == 13 && log_v == 1)
    leaf_sponge_probe<13, 1>(values, log_domain, out);
  else
    __trap();
}

} // namespace airbender::hash::keccak256
