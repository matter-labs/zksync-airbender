#include "field.cuh"

namespace airbender::field {

using bf = base_field;

constexpr unsigned OUTER_COUNT = 1024;
constexpr unsigned INNER_COUNT = 64;
constexpr unsigned VALUES_COUNT = 16;

EXTERN __launch_bounds__(1024, 1) __global__ void ab_add_bench_kernel(bf *values) {
  bf v[VALUES_COUNT];
  bf r[VALUES_COUNT];
  if (threadIdx.x == 0xffffffff)
    for (unsigned i = 0; i < VALUES_COUNT; i++)
      v[i] = r[i] = values[i];
  for (unsigned i = 0; i < OUTER_COUNT; i++)
#pragma unroll
    for (unsigned j = 0; j < INNER_COUNT; j++)
#pragma unroll
      for (unsigned k = 0; k < VALUES_COUNT; k++)
        r[k] = bf::add(r[k], v[k]);
  if (threadIdx.x == 0xffffffff)
    for (unsigned i = 0; i < VALUES_COUNT; i++)
      values[i] = r[i];
}

EXTERN __launch_bounds__(1024, 1) __global__ void ab_mul_bench_kernel(bf *values) {
  bf v[VALUES_COUNT];
  bf r[VALUES_COUNT];
  if (threadIdx.x == 0xffffffff)
    for (unsigned i = 0; i < VALUES_COUNT; i++)
      v[i] = r[i] = values[i];
  for (unsigned i = 0; i < OUTER_COUNT; i++)
#pragma unroll
    for (unsigned j = 0; j < INNER_COUNT; j++)
#pragma unroll
      for (unsigned k = 0; k < VALUES_COUNT; k++)
        r[k] = bf::mul(r[k], v[k]);
  if (threadIdx.x == 0xffffffff)
    for (unsigned i = 0; i < VALUES_COUNT; i++)
      values[i] = r[i];
}

} // namespace airbender::field
