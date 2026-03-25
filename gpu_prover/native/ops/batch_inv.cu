#include "../primitives/memory.cuh"
#include "batch_inv.cuh"

using namespace ::airbender::primitives::memory;

namespace airbender::ops {

template <typename T, typename GETTER, typename SETTER> DEVICE_FORCEINLINE void batch_inv_impl(GETTER src, SETTER dst, const unsigned count) {
  constexpr unsigned INV_BATCH = InvBatch<T>::INV_BATCH;

  // ints for indexing because some bounds checks count down and check if an index drops below 0
  const int gid = static_cast<int>(blockIdx.x * blockDim.x + threadIdx.x);

  // If count < grid size, the kernel is inefficient no matter what (because each thread processes just one element)
  // but we should still bail out if a thread has no assigned elems at all.
  if (gid >= count)
    return;

  const int grid_size = static_cast<int>(blockDim.x * gridDim.x);

  T inputs[INV_BATCH];
  T outputs[INV_BATCH];

  int runtime_batch_size = 0;
  int g = gid;
#pragma unroll
  for (int i = 0; i < INV_BATCH; i++, g += grid_size)
    if (g < count) {
      inputs[i] = src.get(g);
      runtime_batch_size++;
    }

  if (runtime_batch_size < INV_BATCH) {
    batch_inv_registers<T, INV_BATCH, false>(inputs, outputs, runtime_batch_size);
  } else {
    batch_inv_registers<T, INV_BATCH, true>(inputs, outputs, runtime_batch_size);
  }

  g -= grid_size;
#pragma unroll
  for (int i = INV_BATCH - 1; i >= 0; --i, g -= grid_size)
    if (i < runtime_batch_size)
      dst.set(g, outputs[i]);
}

EXTERN __launch_bounds__(128, 8) __global__
    void ab_batch_inv_bf_kernel(const bf_vector_getter<ld_modifier::cs> src, const bf_vector_setter<st_modifier::cs> dst, const unsigned count) {
  batch_inv_impl<bf>(src, dst, count);
}

EXTERN __launch_bounds__(128, 8) __global__
    void ab_batch_inv_e2_kernel(const e2_vector_getter<ld_modifier::cs> src, const e2_vector_setter<st_modifier::cs> dst, const unsigned count) {
  batch_inv_impl<e2>(src, dst, count);
}

EXTERN __launch_bounds__(128, 8) __global__
    void ab_batch_inv_e4_kernel(const e4_vector_getter<ld_modifier::cs> src, const e4_vector_setter<st_modifier::cs> dst, const unsigned count) {
  batch_inv_impl<e4>(src, dst, count);
}

} // namespace airbender::ops
