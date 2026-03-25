#include "../common.cuh"
#include "../primitives/field.cuh"
#include "../primitives/memory.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;

namespace airbender::ops {

template <typename F>
DEVICE_FORCEINLINE void get_powers(const F &base, const unsigned offset, const bool bit_reverse, vector_setter<F, st_modifier::cs> result,
                                   const unsigned count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;
  const unsigned power = (bit_reverse ? __brev(gid) : gid) + offset;
  const F value = F::pow(base, power);
  result.set(gid, value);
}

#define GET_POWERS_BY_VAL_KERNEL(arg_t)                                                                                                                        \
  EXTERN __global__ void ab_get_powers_by_val_##arg_t##_kernel(const arg_t base, const unsigned offset, const bool bit_reverse,                                \
                                                               vector_setter<arg_t, st_modifier::cs> result, const unsigned count) {                           \
    get_powers(base, offset, bit_reverse, result, count);                                                                                                      \
  }
#define GET_POWERS_BY_REF_KERNEL(arg_t)                                                                                                                        \
  EXTERN __global__ void ab_get_powers_by_ref_##arg_t##_kernel(const arg_t *base, const unsigned offset, const bool bit_reverse,                               \
                                                               vector_setter<arg_t, st_modifier::cs> result, const unsigned count) {                           \
    get_powers(*base, offset, bit_reverse, result, count);                                                                                                     \
  }

GET_POWERS_BY_VAL_KERNEL(bf);
GET_POWERS_BY_VAL_KERNEL(e2);
GET_POWERS_BY_VAL_KERNEL(e4);
GET_POWERS_BY_VAL_KERNEL(e6);
GET_POWERS_BY_REF_KERNEL(bf);
GET_POWERS_BY_REF_KERNEL(e2);
GET_POWERS_BY_REF_KERNEL(e4);
GET_POWERS_BY_REF_KERNEL(e6);

} // namespace airbender::ops
