#pragma once

#include "common.cuh"

namespace airbender::hash::pow_search_detail {

#ifdef AB_DETERMINISTIC_POW
constexpr bool COUNTER_SEARCH = true;
#else
constexpr bool COUNTER_SEARCH = false;
#endif

constexpr u64 STOP = u64{1} << 63;

// FULL_CHUNK skips per-nonce bounds checks for complete counter-search chunks.
// CHECKED_GRID retains the hashes' existing advance and publication policies.
template <bool COUNTER, bool FULL_CHUNK, bool CHECKED_GRID, typename Predicate, typename Published>
DEVICE_FORCEINLINE void search(const u64 max_nonce, const u32 chunk_steps, u64 *counter, u64 *result, Predicate predicate, Published published) {
  auto *result_ptr = reinterpret_cast<unsigned long long *>(result);
  if constexpr (COUNTER) {
    const u32 lane = threadIdx.x & 31;
    auto *counter_ptr = reinterpret_cast<unsigned long long *>(counter);
    bool hit = false;
    const auto try_nonce = [&](const u64 nonce) {
      if (predicate(nonce)) {
        atomicMin(result_ptr, static_cast<unsigned long long>(nonce));
        hit = true;
      }
    };
    const u64 chunk = static_cast<u64>(chunk_steps) * 32;
    while (true) {
      u64 index = 0;
      if (lane == 0)
        index = atomicAdd(counter_ptr, 1ull);
      index = __shfl_sync(0xffffffffu, index, 0);
      const u64 start = index * chunk;
      if (index >= STOP || __umul64hi(index, chunk) != 0 || start >= max_nonce)
        return;
      const u64 limit = max_nonce - start;
      if (FULL_CHUNK && limit >= chunk) {
#pragma unroll 1
        for (u32 step = 0; step < chunk_steps; step++)
          try_nonce(start + step * 32 + lane);
      } else {
#pragma unroll 1
        for (u32 step = 0; step < chunk_steps; step++) {
          const u64 offset = step * 32 + lane;
          if (offset < limit)
            try_nonce(start + offset);
        }
      }
      if (__any_sync(0xffffffffu, hit)) {
        if (lane == 0)
          atomicMax(counter_ptr, static_cast<unsigned long long>(STOP));
        return;
      }
    }
  } else {
    u64 nonce;
    u64 stride;
    if constexpr (CHECKED_GRID) {
      nonce = static_cast<u64>(blockIdx.x) * blockDim.x + threadIdx.x;
      stride = static_cast<u64>(gridDim.x) * blockDim.x;
    } else {
      nonce = threadIdx.x + blockIdx.x * blockDim.x;
      stride = blockDim.x * gridDim.x;
    }
    while (nonce < max_nonce) {
      if (predicate(nonce)) {
        atomicCAS(result_ptr, UINT64_MAX, static_cast<unsigned long long>(nonce));
        if constexpr (!CHECKED_GRID)
          __threadfence();
      }
      if (published() != UINT64_MAX)
        return;
      if constexpr (CHECKED_GRID) {
        if (stride > max_nonce || nonce >= max_nonce - stride)
          return;
      }
      nonce += stride;
    }
  }
}

} // namespace airbender::hash::pow_search_detail
