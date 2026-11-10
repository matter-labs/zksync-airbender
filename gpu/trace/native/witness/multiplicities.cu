#include "lookup_mapping.cuh"
#include "memory.cuh"
#include "multiplicities.cuh"
#include "primitives/memory.cuh"

using namespace ::airbender::primitives::memory;
using namespace ::airbender::trace::witness::memory;

namespace airbender::trace::witness::multiplicities {

static_assert(sizeof(bf) == sizeof(u32));
static_assert(alignof(bf) == alignof(u32));

EXTERN __global__ void ab_count_multiplicities_kernel(u32 *const __restrict__ lookup_mapping, const unsigned lookup_mapping_size,
                                                      bf *const __restrict__ counter_shards, const unsigned active_counts_len,
                                                      const unsigned counter_replicas) {
  ::airbender::trace::witness::multiplicities::count_multiplicities(lookup_mapping, lookup_mapping_size, counter_shards, active_counts_len, counter_replicas);
}
EXTERN __global__ void ab_reduce_convert_multiplicities_kernel(const bf *const counter_shards, bf *const multiplicities, const unsigned active_counts_len,
                                                               const unsigned counter_replicas) {
  ::airbender::trace::witness::multiplicities::reduce_convert_multiplicities(counter_shards, multiplicities, active_counts_len, counter_replicas);
}
EXTERN __launch_bounds__(128, 8) __global__
    void ab_generate_range_check_lookup_mapping_kernel(matrix_getter<bf, ld_modifier::cg> memory, matrix_getter<bf, ld_modifier::cg> witness,
                                                       matrix_getter<bf, ld_modifier::cg> scratch,
                                                       __grid_constant__ const LookupExpressionsBf range_check_16_lookup_expressions,
                                                       matrix_setter<unsigned, st_modifier::cs> range_check_16_lookup_mapping,
                                                       __grid_constant__ const LookupExpressionsBf range_check_timestamp_lookup_expressions,
                                                       matrix_setter<unsigned, st_modifier::cs> range_check_timestamp_lookup_mapping, const unsigned count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;

  witness.add_row(gid);
  memory.add_row(gid);
  scratch.add_row(gid);
  range_check_16_lookup_mapping.add_row(gid);
  range_check_timestamp_lookup_mapping.add_row(gid);
  process_lookup_expressions(memory, witness, scratch, range_check_16_lookup_expressions, range_check_16_lookup_mapping);
  process_lookup_expressions(memory, witness, scratch, range_check_timestamp_lookup_expressions, range_check_timestamp_lookup_mapping);
}

} // namespace airbender::trace::witness::multiplicities
