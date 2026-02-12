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

#define u8 uint8_t
#define u16 uint16_t
#define u32 uint32_t
#define u64 uint64_t
#define i32 int32_t
#define i64 int64_t