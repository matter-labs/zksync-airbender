#include "common.cuh"

namespace airbender::ops_cub::device_radix_sort {

#define SORT_KEYS(dir, arg_t, method)                                                                                                                          \
  EXTERN cudaError_t ab_sort_keys_##dir##_##arg_t(void *d_temp_storage, size_t &temp_storage_bytes, const arg_t *d_keys_in, arg_t *d_keys_out,                 \
                                                  const unsigned num_items, const int begin_bit, const int end_bit, const cudaStream_t stream) {               \
    return DeviceRadixSort::method(d_temp_storage, temp_storage_bytes, d_keys_in, d_keys_out, num_items, begin_bit, end_bit, stream);                          \
  }

SORT_KEYS(a, u32, SortKeys);
SORT_KEYS(d, u32, SortKeysDescending);

#define SORT_PAIRS(dir, arg_k_t, arg_v_t, method)                                                                                                              \
  EXTERN cudaError_t ab_sort_pairs_##dir##_##arg_k_t##_##arg_v_t(                                                                                              \
      void *d_temp_storage, size_t &temp_storage_bytes, const arg_k_t *d_keys_in, arg_k_t *d_keys_out, const arg_v_t *d_values_in, arg_v_t *d_values_out,      \
      const unsigned num_items, const int begin_bit, const int end_bit, const cudaStream_t stream) {                                                           \
    return DeviceRadixSort::method(d_temp_storage, temp_storage_bytes, d_keys_in, d_keys_out, d_values_in, d_values_out, num_items, begin_bit, end_bit,        \
                                   stream);                                                                                                                    \
  }

SORT_PAIRS(a, u32, u32, SortPairs);
SORT_PAIRS(d, u32, u32, SortPairsDescending);

} // namespace airbender::ops_cub::device_radix_sort