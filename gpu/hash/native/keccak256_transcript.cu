#include "keccak256.cuh"
#include <cuda/atomic>

namespace airbender::hash::keccak256 {

DEVICE_FORCEINLINE void load_seed(const u8 *src, u8 seed[32]) {
#pragma unroll
  for (u32 byte = 0; byte < 32; byte++)
    seed[byte] = src[byte];
}

DEVICE_FORCEINLINE void store_seed(const u8 seed[32], u8 *dst) {
#pragma unroll
  for (u32 byte = 0; byte < 32; byte++)
    dst[byte] = seed[byte];
}

EXTERN __global__ void ab_keccak256_transcript_initial_u32_kernel(const u32 *input, const u64 count, u8 *seed_out) {
  if (blockIdx.x != 0 || threadIdx.x != 0)
    return;
  u8 seed[32];
  commit_initial_u32(input, count, seed);
  store_seed(seed, seed_out);
}

EXTERN __global__ void ab_keccak256_transcript_commit_u32_kernel(u8 *seed_io, const u32 *input, const u64 count) {
  if (blockIdx.x != 0 || threadIdx.x != 0)
    return;
  u8 seed[32];
  load_seed(seed_io, seed);
  commit_u32(seed, input, count);
  store_seed(seed, seed_io);
}

EXTERN __global__ void ab_keccak256_transcript_commit_fields_kernel(u8 *seed_io, const proth120 *input, const u64 count) {
  if (blockIdx.x != 0 || threadIdx.x != 0)
    return;
  u8 seed[32];
  load_seed(seed_io, seed);
  commit_fields(seed, input, count);
  store_seed(seed, seed_io);
}

EXTERN __global__ void ab_keccak256_transcript_draw_u32_kernel(u8 *seed_io, u32 *out, const u64 count) {
  if (blockIdx.x != 0 || threadIdx.x != 0)
    return;
  u8 seed[32];
  load_seed(seed_io, seed);
  draw_u32(seed, out, count);
  store_seed(seed, seed_io);
}

EXTERN __global__ void ab_keccak256_transcript_draw_fields_kernel(u8 *seed_io, proth120 *out, const u64 count) {
  if (blockIdx.x != 0 || threadIdx.x != 0)
    return;
  u8 seed[32];
  load_seed(seed_io, seed);
  for (u64 i = 0; i < count; i++)
    out[i] = draw_field(seed);
  store_seed(seed, seed_io);
}

constexpr u64 POW_STOP = u64{1} << 63;

EXTERN __global__ void ab_keccak256_pow_kernel(const u8 *seed, const u32 bits, const u64 max_nonce, const u32 chunk_steps, u64 *counter, u64 *result) {
  const u32 lane = threadIdx.x & 31;
  u8 current_seed[32];
  load_seed(seed, current_seed);
  auto *counter_ptr = reinterpret_cast<unsigned long long *>(counter);
  auto *result_ptr = reinterpret_cast<unsigned long long *>(result);
  const u64 chunk = static_cast<u64>(chunk_steps) * 32;
  while (true) {
    u64 index = 0;
    if (lane == 0)
      index = atomicAdd(counter_ptr, 1ull);
    index = __shfl_sync(0xffffffffu, index, 0);
    const u64 start = index * chunk;
    if (index >= POW_STOP || __umul64hi(index, chunk) != 0 || start >= max_nonce)
      return;
    const u64 remaining = max_nonce - start;
    bool hit = false;
    bool stopped = false;
#pragma unroll 1
    for (u32 step = 0; step < chunk_steps; step++) {
      const u64 offset = step * 32 + lane;
      if (offset < remaining) {
        const u64 nonce = start + offset;
        u8 value[32];
        pow_digest(current_seed, nonce, value);
        if (top_bits_are_zero(value, bits)) {
          atomicMin(result_ptr, static_cast<unsigned long long>(nonce));
          hit = true;
        }
      }
      if (!stopped && __any_sync(0xffffffffu, hit)) {
        if (lane == 0)
          atomicMax(counter_ptr, static_cast<unsigned long long>(POW_STOP));
        stopped = true;
#ifndef AB_DETERMINISTIC_POW
        return;
#endif
      }
    }
    if (stopped)
      return;
  }
}

EXTERN __global__ void ab_keccak256_pow_finalize_kernel(u8 *seed_io, const u32 bits, const u64 *nonce) {
  if (blockIdx.x != 0 || threadIdx.x != 0)
    return;
  u8 seed[32], value[32];
  load_seed(seed_io, seed);
  pow_digest(seed, *nonce, value);
  if (!top_bits_are_zero(value, bits)) {
    printf("keccak256_pow: nonce space exhausted\n");
    __trap();
    return;
  }
  store_seed(value, seed_io);
}

EXTERN __global__ void ab_keccak256_pow_helpers_probe_kernel(const u8 *digests, const u32 *bits, const u64 *candidates, const u64 *strides, const u64 count,
                                                             u32 *predicates, u64 *next, u32 *can_advance) {
  const u64 index = static_cast<u64>(blockIdx.x) * blockDim.x + threadIdx.x;
  if (index >= count)
    return;
  if (bits[index] > 256)
    __trap();
  u8 value[32];
  load_seed(digests + index * 32, value);
  predicates[index] = top_bits_are_zero(value, bits[index]);
  u64 next_nonce;
  can_advance[index] = advance(candidates[index], strides[index], UINT64_MAX, next_nonce);
  next[index] = next_nonce;
}

} // namespace airbender::hash::keccak256
