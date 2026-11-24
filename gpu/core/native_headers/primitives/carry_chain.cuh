#pragma once

#include "ptx.cuh"
#include <cstdint>

namespace airbender::primitives::field {

template <unsigned OPS_COUNT = UINT32_MAX, bool CARRY_IN = false, bool CARRY_OUT = false> struct carry_chain {
  unsigned index;

  constexpr __device__ __forceinline__ carry_chain() : index(0) {}

  __device__ __forceinline__ uint32_t add(const uint32_t x, const uint32_t y) {
    index++;
    if (index == 1 && OPS_COUNT == 1 && !CARRY_IN && !CARRY_OUT)
      return ptx::add(x, y);
    else if (index == 1 && !CARRY_IN)
      return ptx::add_cc(x, y);
    else if (index < OPS_COUNT || CARRY_OUT)
      return ptx::addc_cc(x, y);
    else
      return ptx::addc(x, y);
  }

  __device__ __forceinline__ uint32_t sub(const uint32_t x, const uint32_t y) {
    index++;
    if (index == 1 && OPS_COUNT == 1 && !CARRY_IN && !CARRY_OUT)
      return ptx::sub(x, y);
    else if (index == 1 && !CARRY_IN)
      return ptx::sub_cc(x, y);
    else if (index < OPS_COUNT || CARRY_OUT)
      return ptx::subc_cc(x, y);
    else
      return ptx::subc(x, y);
  }
};

} // namespace airbender::primitives::field
