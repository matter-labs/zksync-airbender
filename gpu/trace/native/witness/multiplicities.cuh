#pragma once
#include "common.cuh"
#include "primitives/memory.cuh"
using namespace ::airbender::primitives::memory;
namespace airbender::trace::witness::multiplicities {
template <typename Shard> DEVICE_FORCEINLINE auto counter_word(Shard *ptr) {
  if constexpr (std::is_same_v<std::remove_const_t<Shard>, bf>)
    return &ptr->limb;
  else
    return ptr;
}
template <typename Shard>
DEVICE_FORCEINLINE void count_multiplicities(u32 *const __restrict__ lookup_mapping, const unsigned lookup_mapping_size,
                                             Shard *const __restrict__ counter_shards, const unsigned active_counts_len, const unsigned counter_replicas) {
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
    (void)atomicAdd(counter_word(counter_shards + (replica * active_counts_len + index)), __popc(peers));
  }
}
template <typename F, typename Shard>
DEVICE_FORCEINLINE void reduce_convert_multiplicities(const Shard *const counter_shards, F *const multiplicities, const unsigned active_counts_len,
                                                      const unsigned counter_replicas) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= active_counts_len)
    return;
  u32 count = 0;
  for (unsigned replica = 0; replica < counter_replicas; ++replica)
    count += *counter_word(counter_shards + (replica * active_counts_len + gid));
  multiplicities[gid] = witness_field<F>::from_u32(count);
}
} // namespace airbender::trace::witness::multiplicities
