#include "keccak256.cuh"

EXTERN __global__ void ab_keccak256_hash_bytes_kernel(const u8 *input, u64 len, u8 *out) {
  if (blockIdx.x == 0 && threadIdx.x == 0) {
    u8 bytes[32];
    airbender::hash::keccak256::hash_bytes(input, len, bytes);
    const auto result = airbender::hash::keccak256::digest_from_bytes(bytes);
    airbender::hash::keccak256::digest_to_bytes(result, out);
  }
}
