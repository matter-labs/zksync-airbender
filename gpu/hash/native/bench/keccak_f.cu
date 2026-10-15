#include "../keccak256.cuh"

namespace airbender::hash::keccak256 {

template <bool ROUND_LOOP> DEVICE_FORCEINLINE void bench_keccak_f_chain(const u32 chain, const u64 threads, u64 *out) {
  const u64 index = static_cast<u64>(blockIdx.x) * blockDim.x + threadIdx.x;
  if (index >= threads)
    return;
  u64 state[25];
#pragma unroll
  for (unsigned lane = 0; lane < 25; lane++)
    state[lane] = index * 0x9e3779b97f4a7c15ULL + lane;
#pragma unroll 1
  for (u32 i = 0; i < chain; i++)
    permute<ROUND_LOOP>(state);
  out[index] = state[0];
}

} // namespace airbender::hash::keccak256

EXTERN __global__ void ab_keccak_f_chain_unroll_kernel(const u32 chain, const u64 threads, u64 *out) {
  airbender::hash::keccak256::bench_keccak_f_chain<false>(chain, threads, out);
}

EXTERN __global__ void ab_keccak_f_chain_loop_kernel(const u32 chain, const u64 threads, u64 *out) {
  airbender::hash::keccak256::bench_keccak_f_chain<true>(chain, threads, out);
}
