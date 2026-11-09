#pragma once
#include "eq_inline.cuh"
#include "kernel_helpers.cuh"

namespace airbender::gkr {

template <typename E> struct gkr_independent_eq_group_writer {
  E *destination;
  unsigned source_offset;

  DEVICE_FORCEINLINE void operator()(const unsigned index, const E &value) const { store<E, st_modifier::cs>(destination, value, index - source_offset); }
};

template <typename F>
DEVICE_FORCEINLINE void gkr_build_eq_high_low_from_point(const F *claim_point, const unsigned challenge_offset, const unsigned challenge_count, F *high_0,
                                                         F *high_1, F *low_buffer) {
  if (threadIdx.x == 0) {
    if (blockIdx.x == 0)
      high_0[0] = F::ONE();
    else if (blockIdx.x == 1)
      high_1[0] = F::ONE();
  }
  const unsigned groups_count = gkr_eq_group_count(challenge_count);
  if (blockIdx.x >= groups_count)
    return;
  F *destination = low_buffer;
  if (blockIdx.x + 1u != groups_count)
    destination = blockIdx.x == 0 ? high_0 : high_1;
  const gkr_independent_eq_group_writer<F> write_destination{destination, blockIdx.x * GKR_EQ_GROUP_TABLE_LEN};
  gkr_build_eq_group_table_from_point<F>(claim_point, challenge_offset, challenge_count, blockIdx.x, write_destination);
}

} // namespace airbender::gkr
