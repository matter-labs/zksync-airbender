#include "../keccak256.cuh"

namespace airbender::hash::keccak256 {

template <unsigned BYTES, bool ROUND_LOOP> DEVICE_FORCEINLINE digest bench_hash(u64 index) {
  sponge_impl<ROUND_LOOP> hash;
  hash.absorb_stream(BYTES, [=](u64 byte) { return static_cast<u8>(index * 31 + byte); });
  u8 bytes[32];
  hash.finalize(bytes);
  return digest_from_bytes(bytes);
}

template <bool ROUND_LOOP> DEVICE_FORCEINLINE void bench_hash(u32 bytes, u64 count, digest *out) {
  const u64 index = static_cast<u64>(blockIdx.x) * blockDim.x + threadIdx.x;
  if (index >= count)
    return;
  switch (bytes) {
  case 40:
    out[index] = bench_hash<40, ROUND_LOOP>(index);
    break;
  case 64:
    out[index] = bench_hash<64, ROUND_LOOP>(index);
    break;
  case 256:
    out[index] = bench_hash<256, ROUND_LOOP>(index);
    break;
  case 448:
    out[index] = bench_hash<448, ROUND_LOOP>(index);
    break;
  }
}

} // namespace airbender::hash::keccak256

EXTERN __global__ void ab_keccak256_bench_unroll_kernel(u32 bytes, u64 count, airbender::hash::keccak256::digest *out) {
  airbender::hash::keccak256::bench_hash<false>(bytes, count, out);
}

EXTERN __global__ void ab_keccak256_bench_loop_kernel(u32 bytes, u64 count, airbender::hash::keccak256::digest *out) {
  airbender::hash::keccak256::bench_hash<true>(bytes, count, out);
}
