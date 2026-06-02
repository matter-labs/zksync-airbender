#include "common.cuh"
#include <cub/device/device_reduce.cuh>
#include <cub/device/device_segmented_reduce.cuh>

using namespace ::cub;

namespace airbender::cub::device_reduce {

struct offset_iterator {
#if CUB_VERSION >= 200300
  using iterator_category = cuda::std::random_access_iterator_tag;
  using value_type = size_t;
  using difference_type = size_t;
  using pointer = size_t *;
  using reference = size_t &;
#endif
  size_t offset;
  const size_t stride;
  DEVICE_FORCEINLINE size_t operator[](const i64 idx) const { return offset + idx * stride; }
  DEVICE_FORCEINLINE offset_iterator &operator+=(const i64 idx) {
    this->offset += idx * stride;
    return *this;
  }
};

#define SEGMENTED_REDUCE(op, arg_t)                                                                                                                            \
  EXTERN cudaError_t ab_segmented_reduce_##op##_##arg_t(void *d_temp_storage, size_t &temp_storage_bytes, const matrix_accessor<arg_t> d_in, arg_t *d_out,     \
                                                        const int num_segments, const int num_items, const cudaStream_t stream) {                              \
    const offset_iterator d_begin_offsets{0, d_in.stride};                                                                                                     \
    const offset_iterator d_end_offsets{static_cast<size_t>(num_items), d_in.stride};                                                                          \
    return DeviceSegmentedReduce::Reduce(d_temp_storage, temp_storage_bytes, d_in.ptr, d_out, num_segments, d_begin_offsets, d_end_offsets, op<arg_t>(),       \
                                         op<arg_t>::init(), stream);                                                                                           \
  }

SEGMENTED_REDUCE(add, bf);
SEGMENTED_REDUCE(add, e4);
SEGMENTED_REDUCE(mul, bf);
SEGMENTED_REDUCE(mul, e4);

} // namespace airbender::cub::device_reduce
