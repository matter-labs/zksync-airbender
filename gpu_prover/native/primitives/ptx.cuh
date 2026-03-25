#pragma once

#include "../common.cuh"

namespace airbender::primitives::ptx {

/*****
 * u32
 *****/

DEVICE_FORCEINLINE u32 mul_lo(u32 a, u32 b) {
  u32 r;
  asm volatile("mul.lo.u32 %0, %1, %2;" : "=r"(r) : "r"(a), "r"(b));
  return r;
}

DEVICE_FORCEINLINE u32 mul_hi(u32 a, u32 b) {
  u32 r;
  asm volatile("mul.hi.u32 %0, %1, %2;" : "=r"(r) : "r"(a), "r"(b));
  return r;
}

DEVICE_FORCEINLINE u32 mad_lo(u32 a, u32 b, u32 c) {
  u32 r;
  asm volatile("mad.lo.u32 %0, %1, %2, %3;" : "=r"(r) : "r"(a), "r"(b), "r"(c));
  return r;
}

DEVICE_FORCEINLINE u32 mad_lo_cc(u32 a, u32 b, u32 c) {
  u32 r;
  asm volatile("mad.lo.cc.u32 %0, %1, %2, %3;" : "=r"(r) : "r"(a), "r"(b), "r"(c));
  return r;
}

DEVICE_FORCEINLINE u32 mad_hi_cc(const u32 x, const u32 y, const u32 z) {
  u32 result;
  asm volatile("mad.hi.cc.u32 %0, %1, %2, %3;" : "=r"(result) : "r"(x), "r"(y), "r"(z));
  return result;
}

DEVICE_FORCEINLINE u32 madc_hi(u32 a, u32 b, u32 c) {
  u32 r;
  asm volatile("madc.hi.u32 %0, %1, %2, %3;" : "=r"(r) : "r"(a), "r"(b), "r"(c));
  return r;
}

DEVICE_FORCEINLINE u32 madc_hi_cc(u32 a, u32 b, u32 c) {
  u32 r;
  asm volatile("madc.hi.cc.u32 %0, %1, %2, %3;" : "=r"(r) : "r"(a), "r"(b), "r"(c));
  return r;
}

DEVICE_FORCEINLINE u32 madc_lo_cc(const u32 x, const u32 y, const u32 z) {
  u32 result;
  asm volatile("madc.lo.cc.u32 %0, %1, %2, %3;" : "=r"(result) : "r"(x), "r"(y), "r"(z));
  return result;
}

DEVICE_FORCEINLINE u32 addc(u32 a, u32 b) {
  u32 r;
  asm volatile("addc.u32 %0, %1, %2;" : "=r"(r) : "r"(a), "r"(b));
  return r;
}

DEVICE_FORCEINLINE u32 add_cc(u32 a, u32 b) {
  u32 r;
  asm volatile("add.cc.u32 %0, %1, %2;" : "=r"(r) : "r"(a), "r"(b));
  return r;
}

DEVICE_FORCEINLINE u32 addc_cc(u32 a, u32 b) {
  u32 r;
  asm volatile("addc.cc.u32 %0, %1, %2;" : "=r"(r) : "r"(a), "r"(b));
  return r;
}

DEVICE_FORCEINLINE u64 mul_wide(u32 a, u32 b) {
  u64 r;
  asm volatile("mul.wide.u32 %0, %1, %2;" : "=l"(r) : "r"(a), "r"(b));
  return r;
}

/*****
 * u64
 *****/

DEVICE_FORCEINLINE u64 sub_cc(const u64 x, const u64 y) {
  u64 result;
  asm volatile("sub.cc.u64 %0, %1, %2;" : "=l"(result) : "l"(x), "l"(y));
  return result;
}

DEVICE_FORCEINLINE u64 subc(const u64 x, const u64 y) {
  u64 result;
  asm volatile("subc.u64 %0, %1, %2;" : "=l"(result) : "l"(x), "l"(y));
  return result;
}

DEVICE_FORCEINLINE u64 subc_cc(const u64 x, const u64 y) {
  u64 result;
  asm volatile("subc.cc.u64 %0, %1, %2;" : "=l"(result) : "l"(x), "l"(y));
  return result;
}

DEVICE_FORCEINLINE u64 mul_lo(u64 a, u64 b) {
  u64 r;
  asm volatile("mul.lo.u64 %0, %1, %2;" : "=l"(r) : "l"(a), "l"(b));
  return r;
}

DEVICE_FORCEINLINE u64 mul_hi(u64 a, u64 b) {
  u64 r;
  asm volatile("mul.hi.u64 %0, %1, %2;" : "=l"(r) : "l"(a), "l"(b));
  return r;
}

DEVICE_FORCEINLINE u64 mad_lo_cc(u64 a, u64 b, u64 c) {
  u64 r;
  asm volatile("mad.lo.cc.u64 %0, %1, %2, %3;" : "=l"(r) : "l"(a), "l"(b), "l"(c));
  return r;
}

DEVICE_FORCEINLINE u64 mad_hi_cc(const u64 x, const u64 y, const u64 z) {
  u64 result;
  asm volatile("mad.hi.cc.u64 %0, %1, %2, %3;" : "=l"(result) : "l"(x), "l"(y), "l"(z));
  return result;
}

DEVICE_FORCEINLINE u64 madc_hi(u64 a, u64 b, u64 c) {
  u64 r;
  asm volatile("madc.hi.u64 %0, %1, %2, %3;" : "=l"(r) : "l"(a), "l"(b), "l"(c));
  return r;
}

DEVICE_FORCEINLINE u64 madc_hi_cc(u64 a, u64 b, u64 c) {
  u64 r;
  asm volatile("madc.hi.cc.u64 %0, %1, %2, %3;" : "=l"(r) : "l"(a), "l"(b), "l"(c));
  return r;
}

DEVICE_FORCEINLINE u64 madc_lo_cc(const u64 x, const u64 y, const u64 z) {
  u64 result;
  asm volatile("madc.lo.cc.u64 %0, %1, %2, %3;" : "=l"(result) : "l"(x), "l"(y), "l"(z));
  return result;
}

DEVICE_FORCEINLINE u64 addc(u64 a, u64 b) {
  u64 r;
  asm volatile("addc.u64 %0, %1, %2;" : "=l"(r) : "l"(a), "l"(b));
  return r;
}

} // namespace airbender::primitives::ptx
