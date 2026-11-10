#include "../multiplicities.cuh"
#include "field.cuh"
namespace airbender::trace::witness::proth120::multiplicities {
EXTERN __global__ void ab_pr_count_multiplicities_kernel(u32 *const __restrict__ lookup_mapping, const unsigned lookup_mapping_size,
                                                         u32 *const __restrict__ counter_shards, const unsigned active_counts_len,
                                                         const unsigned counter_replicas) {
  ::airbender::trace::witness::multiplicities::count_multiplicities(lookup_mapping, lookup_mapping_size, counter_shards, active_counts_len, counter_replicas);
}
EXTERN __global__ void ab_pr_reduce_convert_multiplicities_kernel(const u32 *const counter_shards, pr *const multiplicities, const unsigned active_counts_len,
                                                                  const unsigned counter_replicas) {
  ::airbender::trace::witness::multiplicities::reduce_convert_multiplicities(counter_shards, multiplicities, active_counts_len, counter_replicas);
}
} // namespace airbender::trace::witness::proth120::multiplicities
