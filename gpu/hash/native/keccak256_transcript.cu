#include "keccak256.cuh"

namespace airbender::hash::keccak256 {

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

EXTERN __global__ void ab_keccak256_pow_kernel(const u8 *seed, const u32 bits, const u64 max_nonce, const u32 chunk_steps, u64 *counter, u64 *result) {
  pow_search_counter(seed, bits, max_nonce, chunk_steps, counter, result);
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
