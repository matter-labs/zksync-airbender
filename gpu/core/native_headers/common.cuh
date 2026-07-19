#pragma once

#include <cstdint>
#include <cstdio>
#include <cuda_runtime.h>

#ifdef __CUDA_ARCH__
#define likely(x) __builtin_expect(!!(x), 1)
#define unlikely(x) __builtin_expect(!!(x), 0)
#else
#define likely(x) (x)
#define unlikely(x) (x)
#endif

#define DEVICE_FORCEINLINE __device__ __forceinline__

#define HOST_DEVICE_FORCEINLINE __host__ __device__ __forceinline__

#define EXTERN extern "C" [[maybe_unused]]

// Arch-detected max-threads-per-SM. Pair with
// __launch_bounds__(BLK, MAX_THREADS_PER_SM / BLK) for full-occupancy and an
// arch-portable per-thread reg cap.
#if defined(__CUDA_ARCH__) && (__CUDA_ARCH__ == 860 || __CUDA_ARCH__ == 870 || __CUDA_ARCH__ == 890 || __CUDA_ARCH__ == 1200)
#define MAX_THREADS_PER_SM 1536
#else
#define MAX_THREADS_PER_SM 2048
#endif

using u8 = uint8_t;
using u16 = uint16_t;
using u32 = uint32_t;
using u64 = uint64_t;
using i32 = int32_t;
using i64 = int64_t;

// Bit-reverse of the low `num_bits` bits of `value` (the high `32 - num_bits`
// bits are dropped). Single source of truth for the NTT/hash/WHIR bit-reversal
// helpers. Guarded: `num_bits == 0` returns 0, avoiding the undefined `>> 32`
// on a 32-bit value; for `num_bits >= 1` it is bit-identical to the historic
// `__brev(value) >> (32 - num_bits)` per-crate copies.
DEVICE_FORCEINLINE unsigned bitreverse_low_bits(const unsigned value, const unsigned num_bits) {
  return num_bits == 0 ? 0 : (__brev(value) >> (32 - num_bits));
}
