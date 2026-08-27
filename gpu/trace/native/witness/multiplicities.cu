#include "common.cuh"
#include "lookup_mapping.cuh"
#include "memory.cuh"
#include "primitives/memory.cuh"

using namespace ::airbender::primitives::memory;
using namespace ::airbender::trace::witness::memory;

namespace airbender::trace::witness::multiplicities {

static_assert(sizeof(bf) == sizeof(u32));
static_assert(alignof(bf) == alignof(u32));

EXTERN __global__ void ab_count_multiplicities_kernel(u32 *const __restrict__ lookup_mapping, const unsigned lookup_mapping_size,
                                                      bf *const __restrict__ counter_shards, const unsigned active_counts_len,
                                                      const unsigned counter_replicas) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  const unsigned active_mask = __activemask();
  const bool in_bounds = gid < lookup_mapping_size;
  const u32 index = in_bounds ? load<u32, ld_modifier::cs>(lookup_mapping + gid) : 0xffffffffu;
  const bool countable = in_bounds && index != 0xffffffffu;
  const bool invalid = countable && index >= active_counts_len;
  const unsigned invalid_mask = __ballot_sync(active_mask, invalid);
  const unsigned countable_mask = __ballot_sync(active_mask, countable);

  if (in_bounds && index == 0xffffffffu)
    store<u32, st_modifier::cs>(lookup_mapping + gid, 0);
  if (invalid_mask != 0)
    __trap();
  if (!countable)
    return;

  const unsigned peers = __match_any_sync(countable_mask, index);
  const unsigned lane = threadIdx.x & (warpSize - 1);
  const unsigned leader = __ffs(peers) - 1;
  if (lane == leader) {
    const unsigned replica = blockIdx.x & (counter_replicas - 1);
    (void)atomicAdd(&counter_shards[replica * active_counts_len + index].limb, __popc(peers));
  }
}

// counter_shards may alias multiplicities when the output tail stores the replicas.
EXTERN __global__ void ab_reduce_convert_multiplicities_kernel(const bf *const counter_shards, bf *const multiplicities, const unsigned active_counts_len,
                                                               const unsigned counter_replicas) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= active_counts_len)
    return;
  u32 count = 0;
  for (unsigned replica = 0; replica < counter_replicas; ++replica)
    count += counter_shards[replica * active_counts_len + gid].limb;
  multiplicities[gid] = bf::from_u32_unchecked(count);
}

EXTERN __launch_bounds__(128, 8) __global__
    void ab_generate_range_check_lookup_mapping_kernel(matrix_getter<bf, ld_modifier::cg> memory, matrix_getter<bf, ld_modifier::cg> witness,
                                                       matrix_getter<bf, ld_modifier::cg> scratch,
                                                       __grid_constant__ const LookupExpressions range_check_16_lookup_expressions,
                                                       matrix_setter<unsigned, st_modifier::cs> range_check_16_lookup_mapping,
                                                       __grid_constant__ const LookupExpressions range_check_timestamp_lookup_expressions,
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
