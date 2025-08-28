#pragma once

#include "../field.cuh"
#include "../memory.cuh"
#include <cub/cub.cuh>

using namespace ::cub;
using namespace ::airbender::field;
using namespace ::airbender::memory;

namespace airbender::ops_cub {

typedef uint32_t u32;
typedef uint64_t u64;
typedef base_field bf;
typedef ext2_field e2;
typedef ext4_field e4;

#define BINARY_OP(op, init_fn)                                                                                                                                 \
  template <typename T> struct op {                                                                                                                            \
    DEVICE_FORCEINLINE T operator()(const T &a, const T &b) const { return T::op(a, b); }                                                                      \
    static HOST_DEVICE_FORCEINLINE T init() { return T::init_fn(); }                                                                                           \
  }

BINARY_OP(add, zero);
BINARY_OP(mul, one);

template <> struct add<u32> {
  DEVICE_FORCEINLINE u32 operator()(const u32 &a, const u32 &b) const { return a + b; }
  static HOST_DEVICE_FORCEINLINE u32 init() { return 0; }
};

template <> struct mul<u32> {
  DEVICE_FORCEINLINE u32 operator()(const u32 &a, const u32 &b) const { return a * b; }
  static HOST_DEVICE_FORCEINLINE u32 init() { return 1; }
};
} // namespace airbender::ops_cub