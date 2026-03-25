#include "../primitives/field.cuh"

namespace airbender::primitives::field {

template <typename T> using binary_op = T (*)(T, T);

template <typename T, unsigned OUTER_COUNT, unsigned INNER_COUNT, unsigned VALUES_COUNT>
DEVICE_FORCEINLINE void bench(bf *bf_values, const unsigned count, const binary_op<T> op) {
  auto values = reinterpret_cast<T *>(bf_values);
  T v[VALUES_COUNT] = {};
  T r[VALUES_COUNT] = {};
  if (count != 0)
    for (int i = 0; i < VALUES_COUNT; i++)
      v[i] = r[i] = values[i];
#pragma unroll 1
  for (int i = 0; i < OUTER_COUNT; i++)
#pragma unroll
    for (int j = 0; j < INNER_COUNT; j++)
#pragma unroll
      for (int k = 0; k < VALUES_COUNT; k++)
        r[k] = op(r[k], v[k]);
#pragma unroll
  for (int i = 0; i < VALUES_COUNT; i++)
    if (*reinterpret_cast<u32 *>(&r[i]) == 0)
      return;
#pragma unroll
  for (int i = 0; i < VALUES_COUNT; i++)
    values[i] = r[i];
}

EXTERN __launch_bounds__(1024, 1) __global__ void ab_add_bf_bench_kernel(bf *values, const unsigned count) { bench<bf, 1024, 32, 32>(values, count, bf::add); }

EXTERN __launch_bounds__(1024, 1) __global__ void ab_mul_bf_bench_kernel(bf *values, const unsigned count) { bench<bf, 1024, 32, 32>(values, count, bf::mul); }

EXTERN __launch_bounds__(1024, 1) __global__ void ab_add_e2_bench_kernel(bf *values, const unsigned count) { bench<e2, 1024, 16, 16>(values, count, e2::add); }

EXTERN __launch_bounds__(1024, 1) __global__ void ab_mul_e2_bench_kernel(bf *values, const unsigned count) { bench<e2, 1024, 16, 16>(values, count, e2::mul); }

EXTERN __launch_bounds__(1024, 1) __global__ void ab_add_e4_bench_kernel(bf *values, const unsigned count) { bench<e4, 1024, 8, 8>(values, count, e4::add); }

EXTERN __launch_bounds__(1024, 1) __global__ void ab_mul_e4_bench_kernel(bf *values, const unsigned count) { bench<e4, 1024, 8, 8>(values, count, e4::mul); }

EXTERN __launch_bounds__(1024, 1) __global__ void ab_add_e6_bench_kernel(bf *values, const unsigned count) { bench<e6, 1024, 5, 5>(values, count, e6::add); }

EXTERN __launch_bounds__(1024, 1) __global__ void ab_mul_e6_bench_kernel(bf *values, const unsigned count) { bench<e6, 1024, 5, 5>(values, count, e6::mul); }

} // namespace airbender::primitives::field
