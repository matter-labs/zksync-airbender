#include "keccak256.cuh"

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

} // namespace airbender::hash::keccak256
