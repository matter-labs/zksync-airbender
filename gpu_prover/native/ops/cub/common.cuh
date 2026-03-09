#pragma once

#include "../../primitives/memory.cuh"
#include "../../primitives/field.cuh"
#include <cub/cub.cuh>

using namespace ::cub;
using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;

namespace airbender::ops::cub {

#define BINARY_OP(op, init_fn)                                                                                                                                 \
  template <typename T> struct op {                                                                                                                            \
    DEVICE_FORCEINLINE T operator()(const T &a, const T &b) const { return T::op(a, b); }                                                                      \
    static HOST_DEVICE_FORCEINLINE T init() { return T::init_fn(); }                                                                                           \
  }

BINARY_OP(add, ZERO);
BINARY_OP(mul, ONE);

template <> struct add<u32> {
  DEVICE_FORCEINLINE u32 operator()(const u32 &a, const u32 &b) const { return a + b; }
  static HOST_DEVICE_FORCEINLINE u32 init() { return 0; }
};

template <> struct mul<u32> {
  DEVICE_FORCEINLINE u32 operator()(const u32 &a, const u32 &b) const { return a * b; }
  static HOST_DEVICE_FORCEINLINE u32 init() { return 1; }
};

} // namespace airbender::ops::cub
