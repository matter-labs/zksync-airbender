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

// Fused multiply-accumulate: returns a * b + acc in u64.
// Uses mad_lo_cc + madc_hi carry chain (2 multiply-pipe ops).
DEVICE_FORCEINLINE u64 mad_wide(u32 a, u32 b, u64 acc) {
  u32 acc_lo = reinterpret_cast<const u32 *>(&acc)[0];
  u32 acc_hi = reinterpret_cast<const u32 *>(&acc)[1];
  acc_lo = mad_lo_cc(a, b, acc_lo);
  acc_hi = madc_hi(a, b, acc_hi);
  u64 result;
  reinterpret_cast<u32 *>(&result)[0] = acc_lo;
  reinterpret_cast<u32 *>(&result)[1] = acc_hi;
  return result;
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

/*****
 * Global memory loads/stores. v8 needs PTX 8.8 / sm_100+; falls back to two
 * v4.u32 ops on older arch.
 *****/

struct __align__(32) u32x8 {
  uint4 lo;
  uint4 hi;
};

#define AB_PTX_LD_V1(NAME, MOD)                                                                                                                                \
  DEVICE_FORCEINLINE u32 NAME(const u32 *p) {                                                                                                                  \
    u32 r;                                                                                                                                                     \
    asm volatile("ld.global." MOD ".u32 %0, [%1];" : "=r"(r) : "l"(p));                                                                                        \
    return r;                                                                                                                                                  \
  }

#define AB_PTX_LD_V2(NAME, MOD)                                                                                                                                \
  DEVICE_FORCEINLINE uint2 NAME(const uint2 *p) {                                                                                                              \
    uint2 r;                                                                                                                                                   \
    asm volatile("ld.global." MOD ".v2.u32 {%0, %1}, [%2];" : "=r"(r.x), "=r"(r.y) : "l"(p));                                                                  \
    return r;                                                                                                                                                  \
  }

#define AB_PTX_LD_V4(NAME, MOD)                                                                                                                                \
  DEVICE_FORCEINLINE uint4 NAME(const uint4 *p) {                                                                                                              \
    uint4 r;                                                                                                                                                   \
    asm volatile("ld.global." MOD ".v4.u32 {%0, %1, %2, %3}, [%4];" : "=r"(r.x), "=r"(r.y), "=r"(r.z), "=r"(r.w) : "l"(p));                                    \
    return r;                                                                                                                                                  \
  }

#if defined(__CUDA_ARCH__) && __CUDA_ARCH__ >= 1000
#define AB_PTX_LD_V8(NAME, MOD)                                                                                                                                \
  DEVICE_FORCEINLINE u32x8 NAME(const u32x8 *p) {                                                                                                              \
    u32x8 r;                                                                                                                                                   \
    u64 a, b, c, d;                                                                                                                                            \
    asm volatile("ld.global." MOD ".v4.b64 {%0, %1, %2, %3}, [%4];" : "=l"(a), "=l"(b), "=l"(c), "=l"(d) : "l"(p));                                            \
    reinterpret_cast<u64 *>(&r)[0] = a;                                                                                                                        \
    reinterpret_cast<u64 *>(&r)[1] = b;                                                                                                                        \
    reinterpret_cast<u64 *>(&r)[2] = c;                                                                                                                        \
    reinterpret_cast<u64 *>(&r)[3] = d;                                                                                                                        \
    return r;                                                                                                                                                  \
  }
#else
#define AB_PTX_LD_V8(NAME, MOD)                                                                                                                                \
  DEVICE_FORCEINLINE u32x8 NAME(const u32x8 *p) {                                                                                                              \
    u32x8 r;                                                                                                                                                   \
    const uint4 *p4 = reinterpret_cast<const uint4 *>(p);                                                                                                      \
    asm volatile("ld.global." MOD ".v4.u32 {%0, %1, %2, %3}, [%4];" : "=r"(r.lo.x), "=r"(r.lo.y), "=r"(r.lo.z), "=r"(r.lo.w) : "l"(p4));                       \
    asm volatile("ld.global." MOD ".v4.u32 {%0, %1, %2, %3}, [%4];" : "=r"(r.hi.x), "=r"(r.hi.y), "=r"(r.hi.z), "=r"(r.hi.w) : "l"(p4 + 1));                   \
    return r;                                                                                                                                                  \
  }
#endif

#define AB_PTX_LD_ALL(NAME, MOD) AB_PTX_LD_V1(NAME, MOD) AB_PTX_LD_V2(NAME, MOD) AB_PTX_LD_V4(NAME, MOD) AB_PTX_LD_V8(NAME, MOD)

AB_PTX_LD_ALL(ld_g, "nc")
AB_PTX_LD_ALL(ld_cg, "cg")
AB_PTX_LD_ALL(ld_ca, "ca")
AB_PTX_LD_ALL(ld_cs, "cs")
AB_PTX_LD_ALL(ld_lu, "lu")
AB_PTX_LD_ALL(ld_cv, "cv")

#undef AB_PTX_LD_ALL
#undef AB_PTX_LD_V8
#undef AB_PTX_LD_V4
#undef AB_PTX_LD_V2
#undef AB_PTX_LD_V1

#define AB_PTX_ST_V1(NAME, MOD)                                                                                                                                \
  DEVICE_FORCEINLINE void NAME(u32 *p, u32 v) { asm volatile("st.global." MOD ".u32 [%0], %1;" : : "l"(p), "r"(v)); }

#define AB_PTX_ST_V2(NAME, MOD)                                                                                                                                \
  DEVICE_FORCEINLINE void NAME(uint2 *p, uint2 v) { asm volatile("st.global." MOD ".v2.u32 [%0], {%1, %2};" : : "l"(p), "r"(v.x), "r"(v.y)); }

#define AB_PTX_ST_V4(NAME, MOD)                                                                                                                                \
  DEVICE_FORCEINLINE void NAME(uint4 *p, uint4 v) {                                                                                                            \
    asm volatile("st.global." MOD ".v4.u32 [%0], {%1, %2, %3, %4};" : : "l"(p), "r"(v.x), "r"(v.y), "r"(v.z), "r"(v.w));                                       \
  }

#if defined(__CUDA_ARCH__) && __CUDA_ARCH__ >= 1000
#define AB_PTX_ST_V8(NAME, MOD)                                                                                                                                \
  DEVICE_FORCEINLINE void NAME(u32x8 *p, u32x8 v) {                                                                                                            \
    const u64 *vp = reinterpret_cast<const u64 *>(&v);                                                                                                         \
    asm volatile("st.global." MOD ".v4.b64 [%0], {%1, %2, %3, %4};" : : "l"(p), "l"(vp[0]), "l"(vp[1]), "l"(vp[2]), "l"(vp[3]));                               \
  }
#else
#define AB_PTX_ST_V8(NAME, MOD)                                                                                                                                \
  DEVICE_FORCEINLINE void NAME(u32x8 *p, u32x8 v) {                                                                                                            \
    uint4 *p4 = reinterpret_cast<uint4 *>(p);                                                                                                                  \
    asm volatile("st.global." MOD ".v4.u32 [%0], {%1, %2, %3, %4};" : : "l"(p4), "r"(v.lo.x), "r"(v.lo.y), "r"(v.lo.z), "r"(v.lo.w));                          \
    asm volatile("st.global." MOD ".v4.u32 [%0], {%1, %2, %3, %4};" : : "l"(p4 + 1), "r"(v.hi.x), "r"(v.hi.y), "r"(v.hi.z), "r"(v.hi.w));                      \
  }
#endif

#define AB_PTX_ST_ALL(NAME, MOD) AB_PTX_ST_V1(NAME, MOD) AB_PTX_ST_V2(NAME, MOD) AB_PTX_ST_V4(NAME, MOD) AB_PTX_ST_V8(NAME, MOD)

AB_PTX_ST_ALL(st_wb, "wb")
AB_PTX_ST_ALL(st_cg, "cg")
AB_PTX_ST_ALL(st_cs, "cs")
AB_PTX_ST_ALL(st_wt, "wt")

#undef AB_PTX_ST_ALL
#undef AB_PTX_ST_V8
#undef AB_PTX_ST_V4
#undef AB_PTX_ST_V2
#undef AB_PTX_ST_V1

} // namespace airbender::primitives::ptx
