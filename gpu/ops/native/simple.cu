#include "primitives/field.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;

namespace airbender::ops::simple {

template <typename T> struct value_getter {
  using value_type = T;
  T value;

  DEVICE_FORCEINLINE T get(const unsigned, const unsigned) const { return value; }
};

using bf_value_getter = value_getter<bf>;
using bf_getter = wrapping_matrix_getter<bf_matrix_getter<ld_modifier::cs>>;
using bf_setter = wrapping_matrix_setter<bf_matrix_setter<st_modifier::cs>>;

using e4_value_getter = value_getter<e4>;
using e4_getter = wrapping_matrix_getter<e4_matrix_getter<ld_modifier::cs>>;
using e4_setter = wrapping_matrix_setter<e4_matrix_setter<st_modifier::cs>>;

using u32_value_getter = value_getter<u32>;
using u32_getter = wrapping_matrix_getter<matrix_getter<u32, ld_modifier::cs>>;
using u32_setter = wrapping_matrix_setter<matrix_setter<u32, st_modifier::cs>>;

using u64_value_getter = value_getter<u64>;
using u64_getter = wrapping_matrix_getter<matrix_getter<u64, ld_modifier::cs>>;
using u64_setter = wrapping_matrix_setter<matrix_setter<u64, st_modifier::cs>>;

template <class T, class U> using unary_fn = U (*)(T);

template <class T0, class T1, class U> using binary_fn = U (*)(T0, T1);

template <class T, class U> DEVICE_FORCEINLINE void unary_op(const unary_fn<typename T::value_type, typename U::value_type> func, const T arg, U result) {
  const unsigned row = threadIdx.x + blockIdx.x * blockDim.x;
  if (row >= result.rows)
    return;
  const unsigned col = blockIdx.y;
  const typename T::value_type arg_value = arg.get(row, col);
  const typename U::value_type result_value = func(arg_value);
  result.set(row, col, result_value);
}

template <class T0, class T1, class U>
DEVICE_FORCEINLINE void binary_op(const binary_fn<typename T0::value_type, typename T1::value_type, typename U::value_type> func, const T0 arg0, const T1 arg1,
                                  U result) {
  const unsigned row = threadIdx.x + blockIdx.x * blockDim.x;
  if (row >= result.rows)
    return;
  const unsigned col = blockIdx.y;
  const typename T0::value_type arg0_value = arg0.get(row, col);
  const typename T1::value_type arg1_value = arg1.get(row, col);
  const typename U::value_type result_value = func(arg0_value, arg1_value);
  result.set(row, col, result_value);
}

template <class T> DEVICE_FORCEINLINE T return_value(const T x) { return x; }

#define SET_BY_VAL_KERNEL(arg_t)                                                                                                                               \
  EXTERN __global__ void ab_set_by_val_##arg_t##_kernel(const arg_t##_value_getter arg, arg_t##_setter result) { unary_op(return_value, arg, result); }

SET_BY_VAL_KERNEL(u32)
SET_BY_VAL_KERNEL(u64)
SET_BY_VAL_KERNEL(bf)
SET_BY_VAL_KERNEL(e4)

#define SET_BY_REF_KERNEL(arg_t)                                                                                                                               \
  EXTERN __global__ void ab_set_by_ref_##arg_t##_kernel(const arg_t##_getter arg, arg_t##_setter result) { unary_op(return_value, arg, result); }

SET_BY_REF_KERNEL(u32)
SET_BY_REF_KERNEL(u64)
SET_BY_REF_KERNEL(bf)
SET_BY_REF_KERNEL(e4)

#define PARAMETRIZED_KERNEL(op, arg_t)                                                                                                                         \
  EXTERN __global__ void ab_##op##_##arg_t##_kernel(const arg_t##_getter arg, const u32_value_getter parameter, arg_t##_setter result) {                       \
    binary_op(arg_t::op, arg, parameter, result);                                                                                                              \
  }

PARAMETRIZED_KERNEL(pow, bf)
PARAMETRIZED_KERNEL(pow, e4)

#define BINARY_KERNEL(op, arg0_t, arg1_t, result_t)                                                                                                            \
  EXTERN __global__ void ab_##op##_##arg0_t##_##arg1_t##_kernel(const arg0_t##_getter arg0, const arg1_t##_getter arg1, result_t##_setter result) {            \
    binary_op(result_t::op, arg0, arg1, result);                                                                                                               \
  }

BINARY_KERNEL(add, bf, bf, bf)
BINARY_KERNEL(add, bf, e4, e4)
BINARY_KERNEL(add, e4, bf, e4)
BINARY_KERNEL(add, e4, e4, e4)
BINARY_KERNEL(mul, bf, bf, bf)
BINARY_KERNEL(mul, bf, e4, e4)
BINARY_KERNEL(mul, e4, bf, e4)
BINARY_KERNEL(mul, e4, e4, e4)
BINARY_KERNEL(sub, bf, bf, bf)
BINARY_KERNEL(sub, bf, e4, e4)
BINARY_KERNEL(sub, e4, bf, e4)
BINARY_KERNEL(sub, e4, e4, e4)

} // namespace airbender::ops::simple
