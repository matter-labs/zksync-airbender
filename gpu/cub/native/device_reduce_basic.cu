#include "common.cuh"
#include <cub/device/device_reduce.cuh>

using namespace ::cub;

namespace airbender::cub::device_reduce {

#define REDUCE(op, arg_t)                                                                                                                                      \
  EXTERN cudaError_t ab_reduce_##op##_##arg_t(void *d_temp_storage, size_t &temp_storage_bytes, const arg_t *d_in, arg_t *d_out, const int num_items,          \
                                              const cudaStream_t stream) {                                                                                     \
    return DeviceReduce::Reduce(d_temp_storage, temp_storage_bytes, d_in, d_out, num_items, op<arg_t>(), op<arg_t>::init(), stream);                           \
  }

REDUCE(add, bf);
REDUCE(add, e4);
REDUCE(mul, bf);
REDUCE(mul, e4);

} // namespace airbender::cub::device_reduce
