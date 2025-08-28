#pragma once

#include "field.cuh"

using namespace ::airbender::field;

namespace airbender::ops_complex {

using bf = base_field;
using e2 = ext2_field;
using e4 = ext4_field;

// I could also remove INV_BATCH as a separate arg and use T::INV_BATCH internally
// But with nvcc 12.3 and 12.4, the max inv batch I can use with triggering a compile-hang
// weirdly depends on the point of use. So for now, the InvBatch structs below are just hints,
// and callers may set INV_BATCH independently.
template <typename T, int INV_BATCH, bool batch_is_full>
DEVICE_FORCEINLINE void batch_inv_registers(const T *inputs, T *fwd_scan_and_outputs, int runtime_batch_size) {
  // If count < grid size, the kernel is inefficient no matter what (because each thread processes just one element)
  // but we should still bail out if a thread has no assigned elems at all.
  T running_prod = T::one();
#pragma unroll
  for (int i = 0; i < INV_BATCH; i++)
    if (batch_is_full || i < runtime_batch_size) {
      fwd_scan_and_outputs[i] = running_prod;
      running_prod = T::mul(running_prod, inputs[i]);
    }

  T inv = T::inv(running_prod);

#pragma unroll
  for (int i = INV_BATCH - 1; i >= 0; i--) {
    if (batch_is_full || i < runtime_batch_size) {
      const auto input = inputs[i];
      // Isolates and stores this input's inv
      fwd_scan_and_outputs[i] = T::mul(fwd_scan_and_outputs[i], inv);
      // Removes this input's inv contribution
      if (i > 0)
        inv = T::mul(inv, input);
    }
  }
}

template <typename T> struct InvBatch {};
template <> struct InvBatch<bf> {
  // INV_BATCH = 20 incurs 58 registers per thread with nvcc 12.4 targeting sm_89.
  static constexpr unsigned INV_BATCH = 20;
  // INV_BATCH = 21 would incur 62 regs/thread, but I think 20 is good enough
  // to amortize invs while staying comfortably beneath the 64-reg mark.
};
template <> struct InvBatch<e2> {
  // INV_BATCH = 5 incurs 48 registers per thread with nvcc 12.4 targeting sm_89.
  // When I increase it to 6 or more, the build appears to hang, which is weird
  // because it compiles quickly with 5.
  static constexpr unsigned INV_BATCH = 5;
};
template <> struct InvBatch<e4> {
  // INV_BATCH = 3 is the highest I can set without nvcc hanging.
  static constexpr unsigned INV_BATCH = 3;
};

} // namespace airbender::ops_complex