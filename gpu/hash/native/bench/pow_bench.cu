#include "../hash.cuh"
#include "../keccak256.cuh"
#include <cuda/atomic>

namespace airbender::hash::keccak256 {

DEVICE_FORCEINLINE void pow_search_grid_stride(const u8 *seed, const u32 bits, const u64 max_nonce, u64 *result) {
  u64 nonce = static_cast<u64>(blockIdx.x) * blockDim.x + threadIdx.x;
  const u64 stride = static_cast<u64>(gridDim.x) * blockDim.x;
  u8 current_seed[32];
  load_seed(seed, current_seed);
  auto *result_ptr = reinterpret_cast<unsigned long long *>(result);
  cuda::atomic_ref<unsigned long long, cuda::thread_scope_device> found(*result_ptr);
  while (nonce < max_nonce) {
    u8 value[32];
    pow_digest(current_seed, nonce, value);
    if (top_bits_are_zero(value, bits))
      atomicMin(result_ptr, static_cast<unsigned long long>(nonce));
    if (found.load(cuda::memory_order_relaxed) <= nonce)
      break;
    u64 next;
    if (!advance(nonce, stride, max_nonce, next))
      break;
    nonce = next;
  }
}

} // namespace airbender::hash::keccak256

namespace airbender::hash {

template <bool DETERMINISTIC> DEVICE_FORCEINLINE void pow_search_grid_stride(const u64 *seed, const u32 bits_count, const u64 max_nonce, volatile u64 *result) {
  const u32 digest_mask = 0xffffffff << 32 - bits_count;
  const auto result_ptr = reinterpret_cast<unsigned long long *>(const_cast<u64 *>(result));
  __align__(8) u32 m_u32[BLOCK_SIZE] = {};
  auto m_u64 = reinterpret_cast<u64 *>(m_u32);
#pragma unroll
  for (unsigned i = 0; i < 4; i++)
    m_u64[i] = seed[i];
  const unsigned stride = blockDim.x * gridDim.x;
  for (u64 nonce = threadIdx.x + blockIdx.x * blockDim.x; nonce < max_nonce; nonce += stride) {
    m_u64[STATE_SIZE / 2] = nonce;
    u32 state[STATE_SIZE];
    initialize(state);
    u32 t = 0;
    compress<true>(state, t, m_u32, STATE_SIZE + 2);
    if (!(state[0] & digest_mask)) {
      if constexpr (DETERMINISTIC)
        atomicMin(result_ptr, static_cast<unsigned long long>(nonce));
      else
        atomicCAS(result_ptr, UINT64_MAX, nonce);
      __threadfence();
    }
    if (DETERMINISTIC ? *result <= nonce : *result != UINT64_MAX)
      return;
  }
}

} // namespace airbender::hash

EXTERN __global__ void ab_keccak256_pow_grid_stride_bench_kernel(const u8 *seed, const u32 bits, const u64 max_nonce, u64 *result) {
  airbender::hash::keccak256::pow_search_grid_stride(seed, bits, max_nonce, result);
}

EXTERN __global__ void ab_keccak256_pow_counter_min_bench_kernel(const u8 *seed, const u32 bits, const u64 max_nonce, const u32 chunk_steps, u64 *counter,
                                                                 u64 *result) {
  airbender::hash::keccak256::pow_search<true>(seed, bits, max_nonce, chunk_steps, counter, result);
}

EXTERN __global__ void ab_keccak256_pow_counter_first_bench_kernel(const u8 *seed, const u32 bits, const u64 max_nonce, const u32 chunk_steps, u64 *counter,
                                                                   u64 *result) {
  airbender::hash::keccak256::pow_search<false>(seed, bits, max_nonce, chunk_steps, counter, result);
}

EXTERN __global__ void ab_blake2s_pow_grid_stride_min_bench_kernel(const u64 *seed, const u32 bits_count, const u64 max_nonce, volatile u64 *result) {
  airbender::hash::pow_search_grid_stride<true>(seed, bits_count, max_nonce, result);
}

EXTERN __global__ void ab_blake2s_pow_grid_stride_first_bench_kernel(const u64 *seed, const u32 bits_count, const u64 max_nonce, volatile u64 *result) {
  airbender::hash::pow_search_grid_stride<false>(seed, bits_count, max_nonce, result);
}

EXTERN __global__ void ab_blake2s_pow_counter_min_bench_kernel(const u64 *seed, const u32 bits_count, const u64 max_nonce, const u32 chunk_steps, u64 *counter,
                                                               u64 *result) {
  airbender::hash::pow_search<true>(seed, bits_count, max_nonce, chunk_steps, counter, result);
}

EXTERN __global__ void ab_blake2s_pow_counter_first_bench_kernel(const u64 *seed, const u32 bits_count, const u64 max_nonce, const u32 chunk_steps, u64 *counter,
                                                                 u64 *result) {
  airbender::hash::pow_search<false>(seed, bits_count, max_nonce, chunk_steps, counter, result);
}
