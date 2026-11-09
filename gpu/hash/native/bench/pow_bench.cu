#include "../hash.cuh"
#include "../keccak256.cuh"

EXTERN __global__ void ab_keccak256_pow_grid_stride_min_bench_kernel(const u8 *seed, const u32 bits, const u64 max_nonce, u64 *result) {
  airbender::hash::keccak256::pow_search_grid_stride<true>(seed, bits, max_nonce, result);
}

EXTERN __global__ void ab_keccak256_pow_grid_stride_first_bench_kernel(const u8 *seed, const u32 bits, const u64 max_nonce, u64 *result) {
  airbender::hash::keccak256::pow_search_grid_stride<false>(seed, bits, max_nonce, result);
}

EXTERN __global__ void ab_keccak256_pow_counter_min_bench_kernel(const u8 *seed, const u32 bits, const u64 max_nonce, const u32 chunk_steps, u64 *counter,
                                                                 u64 *result) {
  airbender::hash::keccak256::pow_search_counter(seed, bits, max_nonce, chunk_steps, counter, result);
}

EXTERN __global__ void ab_blake2s_pow_grid_stride_min_bench_kernel(const u64 *seed, const u32 bits_count, const u64 max_nonce, volatile u64 *result) {
  airbender::hash::pow_search_grid_stride<true>(seed, bits_count, max_nonce, result);
}

EXTERN __global__ void ab_blake2s_pow_grid_stride_first_bench_kernel(const u64 *seed, const u32 bits_count, const u64 max_nonce, volatile u64 *result) {
  airbender::hash::pow_search_grid_stride<false>(seed, bits_count, max_nonce, result);
}

EXTERN __global__ void ab_blake2s_pow_counter_min_bench_kernel(const u64 *seed, const u32 bits_count, const u64 max_nonce, const u32 chunk_steps, u64 *counter,
                                                               u64 *result) {
  airbender::hash::pow_search_counter(seed, bits_count, max_nonce, chunk_steps, counter, result);
}
