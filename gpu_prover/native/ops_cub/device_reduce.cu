#include "common.cuh"

namespace airbender::ops_cub::device_reduce {

#define REDUCE(op, arg_t)                                                                                                                                      \
  EXTERN cudaError_t ab_reduce_##op##_##arg_t(void *d_temp_storage, size_t &temp_storage_bytes, const arg_t *d_in, arg_t *d_out, const int num_items,          \
                                              const cudaStream_t stream) {                                                                                     \
    return DeviceReduce::Reduce(d_temp_storage, temp_storage_bytes, d_in, d_out, num_items, op<arg_t>(), op<arg_t>::init(), stream);                           \
  }

REDUCE(add, bf);
REDUCE(add, e2);
REDUCE(add, e4);
REDUCE(mul, bf);
REDUCE(mul, e2);
REDUCE(mul, e4);

struct offset_iterator {
#if CUB_VERSION >= 200300
  using iterator_category = cuda::std::random_access_iterator_tag;
  using value_type = int;
  using difference_type = int;
  using pointer = int *;
  using reference = int &;
#endif
  const int offset;
  const int stride;
  DEVICE_FORCEINLINE int operator[](const int idx) const { return offset + idx * stride; }
};

#define SEGMENTED_REDUCE(op, arg_t)                                                                                                                            \
  EXTERN cudaError_t ab_segmented_reduce_##op##_##arg_t(void *d_temp_storage, size_t &temp_storage_bytes, const matrix_accessor<arg_t> d_in, arg_t *d_out,     \
                                                        const int num_segments, const int num_items, const cudaStream_t stream) {                              \
    const int stride = static_cast<int>(d_in.stride);                                                                                                          \
    const offset_iterator d_begin_offsets{0, stride};                                                                                                          \
    const offset_iterator d_end_offsets{num_items, stride};                                                                                                    \
    return DeviceSegmentedReduce::Reduce(d_temp_storage, temp_storage_bytes, d_in.ptr, d_out, num_segments, d_begin_offsets, d_end_offsets, op<arg_t>(),       \
                                         op<arg_t>::init(), stream);                                                                                           \
  }

SEGMENTED_REDUCE(add, bf);
SEGMENTED_REDUCE(add, e2);
SEGMENTED_REDUCE(add, e4);
SEGMENTED_REDUCE(mul, bf);
SEGMENTED_REDUCE(mul, e2);
SEGMENTED_REDUCE(mul, e4);

} // namespace airbender::ops_cub::device_reduce