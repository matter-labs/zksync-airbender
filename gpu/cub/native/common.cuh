#pragma once

#include "primitives/field.cuh"
#include "primitives/memory.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;

namespace airbender::cub {

// Field-addition reduction operator for CUB DeviceReduce/DeviceSegmentedReduce,
// instantiated over the field types (bf, e4) in device_reduce_*.cu.
template <typename T> struct add {
  DEVICE_FORCEINLINE T operator()(const T &a, const T &b) const { return T::add(a, b); }
  static HOST_DEVICE_FORCEINLINE T init() { return T::ZERO(); }
};

} // namespace airbender::cub
