#include "common.cuh"
#include <cub/device/device_radix_sort.cuh>

using namespace ::cub;

namespace airbender::ops::cub::device_radix_sort {

#define SORT_KEYS(dir, arg_t, method)                                                                                                                          \
  EXTERN cudaError_t ab_sort_keys_##dir##_##arg_t(void *d_temp_storage, size_t &temp_storage_bytes, const arg_t *d_keys_in, arg_t *d_keys_out,                 \
                                                  const unsigned num_items, const int begin_bit, const int end_bit, const cudaStream_t stream) {               \
    return DeviceRadixSort::method(d_temp_storage, temp_storage_bytes, d_keys_in, d_keys_out, num_items, begin_bit, end_bit, stream);                          \
  }

SORT_KEYS(a, u32, SortKeys);
SORT_KEYS(d, u32, SortKeysDescending);

} // namespace airbender::ops::cub::device_radix_sort
