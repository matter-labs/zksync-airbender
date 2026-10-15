#pragma once

#include <primitives/ptx.cuh>
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

  __device__ __forceinline__ uint32_t mad_lo(const uint32_t x, const uint32_t y, const uint32_t z) {
    index++;
    if (index == 1 && OPS_COUNT == 1 && !CARRY_IN && !CARRY_OUT)
      return ptx::mad_lo(x, y, z);
    else if (index == 1 && !CARRY_IN)
      return ptx::mad_lo_cc(x, y, z);
    else if (index < OPS_COUNT || CARRY_OUT)
      return ptx::madc_lo_cc(x, y, z);
    else
      return ptx::madc_lo(x, y, z);
  }

  __device__ __forceinline__ uint32_t mad_hi(const uint32_t x, const uint32_t y, const uint32_t z) {
    index++;
    if (index == 1 && OPS_COUNT == 1 && !CARRY_IN && !CARRY_OUT)
      return ptx::mad_hi(x, y, z);
    else if (index == 1 && !CARRY_IN)
      return ptx::mad_hi_cc(x, y, z);
    else if (index < OPS_COUNT || CARRY_OUT)
      return ptx::madc_hi_cc(x, y, z);
    else
      return ptx::madc_hi(x, y, z);
  }
};

} // namespace airbender::primitives::field
