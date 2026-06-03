// Ported from ntt-experiments include/memory.cuh (rr/v8-logn13-two-pass-ntt).
// Slim matrix accessors with cache-modifier loads/stores.
// Pattern matches gpu_prover/native/primitives/memory.cuh for the cg modifier,
// stripped to the bf row/col API used by NTT kernels.

#pragma once
#include <primitives/field.cuh>
#include <primitives/ptx.cuh>
using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives;
namespace airbender {
namespace ntt {

// `cg`: bypass L1, allocate L2-only. Matches gpu_prover usage.
DEVICE_FORCEINLINE bf ld_cg(const bf *p) { return bf::from_reduced_raw_repr(ptx::ld_cg(reinterpret_cast<const u32 *>(p))); }
DEVICE_FORCEINLINE void st_cg(bf *p, bf v) { ptx::st_cg(reinterpret_cast<u32 *>(p), bf::into_raw_u32(v)); }

// Vec2 (uint64_t = 2 bf) variants for V1.
DEVICE_FORCEINLINE void ld_cg_v2(const bf *p, bf &a, bf &b) {
  u32 a_v, b_v;
  asm volatile("ld.global.cg.v2.u32 {%0, %1}, [%2];" : "=r"(a_v), "=r"(b_v) : "l"(p));
  a = bf::from_reduced_raw_repr(a_v);
  b = bf::from_reduced_raw_repr(b_v);
}
DEVICE_FORCEINLINE void st_cg_v2(bf *p, bf a, bf b) {
  asm volatile("st.global.cg.v2.u32 [%0], {%1, %2};" ::"l"(p), "r"(bf::into_raw_u32(a)), "r"(bf::into_raw_u32(b)));
}

// Vec4 variants for V1 at wider configs.
DEVICE_FORCEINLINE void ld_cg_v4(const bf *p, bf &a, bf &b, bf &c, bf &d) {
  u32 a_v, b_v, c_v, d_v;
  asm volatile("ld.global.cg.v4.u32 {%0, %1, %2, %3}, [%4];" : "=r"(a_v), "=r"(b_v), "=r"(c_v), "=r"(d_v) : "l"(p));
  a = bf::from_reduced_raw_repr(a_v);
  b = bf::from_reduced_raw_repr(b_v);
  c = bf::from_reduced_raw_repr(c_v);
  d = bf::from_reduced_raw_repr(d_v);
}
DEVICE_FORCEINLINE void st_cg_v4(bf *p, bf a, bf b, bf c, bf d) {
  asm volatile("st.global.cg.v4.u32 [%0], {%1, %2, %3, %4};" ::"l"(p), "r"(bf::into_raw_u32(a)), "r"(bf::into_raw_u32(b)), "r"(bf::into_raw_u32(c)),
               "r"(bf::into_raw_u32(d)));
}

// Vec8 cg load — single LDG.E.128 fused with another, or LDG.E.ENL2.256 on
// sm_100+. Matches the st.global.cg.v8.b32 store side.
DEVICE_FORCEINLINE void ld_cg_v8(const bf *p, bf &a0, bf &a1, bf &a2, bf &a3, bf &a4, bf &a5, bf &a6, bf &a7) {
  u32 v0, v1, v2, v3, v4, v5, v6, v7;
  asm volatile("ld.global.cg.v8.b32 {%0, %1, %2, %3, %4, %5, %6, %7}, [%8];"
               : "=r"(v0), "=r"(v1), "=r"(v2), "=r"(v3), "=r"(v4), "=r"(v5), "=r"(v6), "=r"(v7)
               : "l"(p));
  a0 = bf::from_reduced_raw_repr(v0);
  a1 = bf::from_reduced_raw_repr(v1);
  a2 = bf::from_reduced_raw_repr(v2);
  a3 = bf::from_reduced_raw_repr(v3);
  a4 = bf::from_reduced_raw_repr(v4);
  a5 = bf::from_reduced_raw_repr(v5);
  a6 = bf::from_reduced_raw_repr(v6);
  a7 = bf::from_reduced_raw_repr(v7);
}

// Cached-all load (constant-uniform): used for twiddle table reads.
DEVICE_FORCEINLINE bf ld_ca(const bf *p) { return bf::from_reduced_raw_repr(ptx::ld_ca(reinterpret_cast<const u32 *>(p))); }

// Vec4 cached-all load — 4 contiguous BFs in one LDG.E.CA.128 → fully
// coalesced when the warp's threads access stride-VPT addresses. Caller must
// 16 B-align p.
DEVICE_FORCEINLINE void ld_ca_v4(const bf *p, bf &a, bf &b, bf &c, bf &d) {
  u32 a_v, b_v, c_v, d_v;
  asm volatile("ld.global.ca.v4.u32 {%0, %1, %2, %3}, [%4];" : "=r"(a_v), "=r"(b_v), "=r"(c_v), "=r"(d_v) : "l"(p));
  a = bf::from_reduced_raw_repr(a_v);
  b = bf::from_reduced_raw_repr(b_v);
  c = bf::from_reduced_raw_repr(c_v);
  d = bf::from_reduced_raw_repr(d_v);
}

// `cs`: cache streaming (likely evict-first hint). Used for write-once output
// where L2 caching is wasted (output > L2 capacity).
DEVICE_FORCEINLINE void st_cs_v4(bf *p, bf a, bf b, bf c, bf d) {
  asm volatile("st.global.cs.v4.u32 [%0], {%1, %2, %3, %4};" ::"l"(p), "r"(bf::into_raw_u32(a)), "r"(bf::into_raw_u32(b)), "r"(bf::into_raw_u32(c)),
               "r"(bf::into_raw_u32(d)));
}

// `wb`: write-back, default global store behavior. Caches in L2 (and L1 if available).
DEVICE_FORCEINLINE void st_wb_v4(bf *p, bf a, bf b, bf c, bf d) {
  asm volatile("st.global.wb.v4.u32 [%0], {%1, %2, %3, %4};" ::"l"(p), "r"(bf::into_raw_u32(a)), "r"(bf::into_raw_u32(b)), "r"(bf::into_raw_u32(c)),
               "r"(bf::into_raw_u32(d)));
}

// `wt`: write-through. Forces every store to commit to L2 AND DRAM. Used by
// the benchmark harness to measure honest DRAM throughput — `cs` writes get
// caught in L2 / write-combining buffers and the kernel finishes before the
// data actually reaches DRAM, so cs-based timing reports L2 throughput. With
// wt, per-launch time is bounded by DRAM bandwidth.
DEVICE_FORCEINLINE void st_wt_v4(bf *p, bf a, bf b, bf c, bf d) {
  asm volatile("st.global.wt.v4.u32 [%0], {%1, %2, %3, %4};" ::"l"(p), "r"(bf::into_raw_u32(a)), "r"(bf::into_raw_u32(b)), "r"(bf::into_raw_u32(c)),
               "r"(bf::into_raw_u32(d)));
}
DEVICE_FORCEINLINE void st_wt_v2(bf *p, bf a, bf b) {
  asm volatile("st.global.wt.v2.u32 [%0], {%1, %2};" ::"l"(p), "r"(bf::into_raw_u32(a)), "r"(bf::into_raw_u32(b)));
}
DEVICE_FORCEINLINE void st_v8_aligned_wt(bf *p, bf a0, bf a1, bf a2, bf a3, bf a4, bf a5, bf a6, bf a7) {
  asm volatile("st.global.wt.v8.b32 [%0], {%1, %2, %3, %4, %5, %6, %7, %8};" ::"l"(p), "r"(bf::into_raw_u32(a0)), "r"(bf::into_raw_u32(a1)),
               "r"(bf::into_raw_u32(a2)), "r"(bf::into_raw_u32(a3)), "r"(bf::into_raw_u32(a4)), "r"(bf::into_raw_u32(a5)), "r"(bf::into_raw_u32(a6)),
               "r"(bf::into_raw_u32(a7)));
}

// 32-byte aligned packed-8 struct. When both source struct and destination
// pointer are 32B-aligned, the SASS compiler fuses two v4 stores into a single
// STG.E.ENL2.256 instruction (vec8 store). Target ≈97.5% DRAM SOL vs 96.7% for
// vec4 stores on Blackwell.
struct __align__(32) bf8_wide {
  uint4 lo;
  uint4 hi;
};

DEVICE_FORCEINLINE void st_v8_aligned(bf *p, bf a0, bf a1, bf a2, bf a3, bf a4, bf a5, bf a6, bf a7) {
  bf8_wide packed;
  packed.lo = make_uint4(bf::into_raw_u32(a0), bf::into_raw_u32(a1), bf::into_raw_u32(a2), bf::into_raw_u32(a3));
  packed.hi = make_uint4(bf::into_raw_u32(a4), bf::into_raw_u32(a5), bf::into_raw_u32(a6), bf::into_raw_u32(a7));
  *reinterpret_cast<bf8_wide *>(p) = packed;
}

// Same packed-8 store but with the `cs` (cache-streaming, evict-first) hint —
// matches production's `st.global.cs` modifier so writes drain past L2 quickly
// and don't pollute the cache with output the kernel will not read back.
// PTX 8.8 `st.global.cs.v8.b32` → SASS `STG.E.EF.ENL2.256` on sm_100+ (fused
// 256-bit). Targets sm_100+ only (this Makefile builds sm_100, so fine).
DEVICE_FORCEINLINE void st_v8_aligned_cs(bf *p, bf a0, bf a1, bf a2, bf a3, bf a4, bf a5, bf a6, bf a7) {
  asm volatile("st.global.cs.v8.b32 [%0], {%1, %2, %3, %4, %5, %6, %7, %8};" ::"l"(p), "r"(bf::into_raw_u32(a0)), "r"(bf::into_raw_u32(a1)),
               "r"(bf::into_raw_u32(a2)), "r"(bf::into_raw_u32(a3)), "r"(bf::into_raw_u32(a4)), "r"(bf::into_raw_u32(a5)), "r"(bf::into_raw_u32(a6)),
               "r"(bf::into_raw_u32(a7)));
}

// 16-byte aligned packed-4 struct → single STG.E.128 on all archs. Used by the
// VPT=4 kernel variant.
struct __align__(16) bf4_wide {
  uint4 v;
};

DEVICE_FORCEINLINE void st_v4_aligned(bf *p, bf a0, bf a1, bf a2, bf a3) {
  bf4_wide packed;
  packed.v = make_uint4(bf::into_raw_u32(a0), bf::into_raw_u32(a1), bf::into_raw_u32(a2), bf::into_raw_u32(a3));
  *reinterpret_cast<bf4_wide *>(p) = packed;
}

DEVICE_FORCEINLINE void st_v4_aligned_cs(bf *p, bf a0, bf a1, bf a2, bf a3) { st_cs_v4(p, a0, a1, a2, a3); }

// Vec2 smem load — 8 bytes (2 bf) per thread in one LDS instruction.
DEVICE_FORCEINLINE void ld_shared_v2(const bf *p, bf &a, bf &b) {
  u32 av, bv;
  asm volatile("ld.shared.v2.u32 {%0, %1}, [%2];" : "=r"(av), "=r"(bv) : "l"(p));
  a = bf::from_reduced_raw_repr(av);
  b = bf::from_reduced_raw_repr(bv);
}

// Vec4 smem load/store (used for per-thread monomial state).
DEVICE_FORCEINLINE void ld_shared_v4(const bf *p, bf &a, bf &b, bf &c, bf &d) {
  u32 av, bv, cv, dv;
  asm volatile("ld.shared.v4.u32 {%0, %1, %2, %3}, [%4];" : "=r"(av), "=r"(bv), "=r"(cv), "=r"(dv) : "l"(p));
  a = bf::from_reduced_raw_repr(av);
  b = bf::from_reduced_raw_repr(bv);
  c = bf::from_reduced_raw_repr(cv);
  d = bf::from_reduced_raw_repr(dv);
}
DEVICE_FORCEINLINE void st_shared_v4(bf *p, bf a, bf b, bf c, bf d) {
  asm volatile("st.shared.v4.u32 [%0], {%1, %2, %3, %4};" ::"l"(p), "r"(bf::into_raw_u32(a)), "r"(bf::into_raw_u32(b)), "r"(bf::into_raw_u32(c)),
               "r"(bf::into_raw_u32(d)));
}
// Vec2 smem store — 8 bytes (2 bf) per thread in one STS instruction.
DEVICE_FORCEINLINE void st_shared_v2(bf *p, bf a, bf b) {
  asm volatile("st.shared.v2.u32 [%0], {%1, %2};" ::"l"(p), "r"(bf::into_raw_u32(a)), "r"(bf::into_raw_u32(b)));
}

// Column-major matrix getter / setter, mirroring gpu_prover's matrix_accessor.
// stride = bytes-per-column / sizeof(bf) = row count.
struct bf_matrix_getter {
  const bf *ptr;
  size_t stride;
  HOST_DEVICE_FORCEINLINE bf_matrix_getter(const bf *p, size_t s) : ptr(p), stride(s) {}
  DEVICE_FORCEINLINE void add_col(unsigned c) { ptr += c * stride; }
  DEVICE_FORCEINLINE void add_row(unsigned r) { ptr += r; }
  DEVICE_FORCEINLINE bf get() const { return ld_cg(ptr); }
  DEVICE_FORCEINLINE bf get_at_row(unsigned r) const { return ld_cg(ptr + r); }
};

struct bf_matrix_setter {
  bf *ptr;
  size_t stride;
  HOST_DEVICE_FORCEINLINE bf_matrix_setter(bf *p, size_t s) : ptr(p), stride(s) {}
  DEVICE_FORCEINLINE void add_col(unsigned c) { ptr += c * stride; }
  DEVICE_FORCEINLINE void add_row(unsigned r) { ptr += r; }
  DEVICE_FORCEINLINE void set(bf v) const { st_cg(ptr, v); }
  DEVICE_FORCEINLINE void set_at_row(unsigned r, bf v) const { st_cg(ptr + r, v); }
};

DEVICE_FORCEINLINE unsigned bitrev_u32(unsigned x, unsigned log_n) { return __brev(x) >> (32 - log_n); }

// =========================================================================
// Vec_VPT gmem load/store helpers (relocated from warp_ntt.cuh so the NTT
// engine in include/ntt/ depends only on this low-level header).
// =========================================================================
template <unsigned LOG_VPT> DEVICE_FORCEINLINE void load_vec_vpt(const bf *p, bf regs[]) {
  if constexpr (LOG_VPT == 1) {
    ld_cg_v2(p, regs[0], regs[1]);
  } else if constexpr (LOG_VPT == 2) {
    ld_cg_v4(p, regs[0], regs[1], regs[2], regs[3]);
  } else if constexpr (LOG_VPT == 3) {
    ld_cg_v8(p, regs[0], regs[1], regs[2], regs[3], regs[4], regs[5], regs[6], regs[7]);
  } else {
#pragma unroll
    for (unsigned i = 0; i < (1u << LOG_VPT); ++i)
      regs[i] = ld_cg(p + i);
  }
}
// Store mode: CS = production (cache-streaming hint, fast for L2-resident
// consumers); WT = write-through, every byte commits to DRAM. WT is for the
// benchmark harness — it gives honest DRAM throughput because the kernel can't
// "finish" while the data is still in L2 write-combining buffers.
enum class StoreMode { CS, WT };

template <unsigned LOG_VPT, StoreMode SM> DEVICE_FORCEINLINE void store_vec_vpt(bf *p, bf regs[]) {
  if constexpr (SM == StoreMode::CS) {
    if constexpr (LOG_VPT == 1) {
      st_cg_v2(p, regs[0], regs[1]);
    } else if constexpr (LOG_VPT == 2) {
      st_cs_v4(p, regs[0], regs[1], regs[2], regs[3]);
    } else if constexpr (LOG_VPT == 3) {
      st_v8_aligned_cs(p, regs[0], regs[1], regs[2], regs[3], regs[4], regs[5], regs[6], regs[7]);
    } else {
#pragma unroll
      for (unsigned i = 0; i < (1u << LOG_VPT); ++i)
        st_cg(p + i, regs[i]);
    }
  } else { // StoreMode::WT
    if constexpr (LOG_VPT == 1) {
      st_wt_v2(p, regs[0], regs[1]);
    } else if constexpr (LOG_VPT == 2) {
      st_wt_v4(p, regs[0], regs[1], regs[2], regs[3]);
    } else if constexpr (LOG_VPT == 3) {
      st_v8_aligned_wt(p, regs[0], regs[1], regs[2], regs[3], regs[4], regs[5], regs[6], regs[7]);
    } else {
#pragma unroll
      for (unsigned i = 0; i < (1u << LOG_VPT); ++i) {
        ptx::st_wt(reinterpret_cast<u32 *>(p + i), bf::into_raw_u32(regs[i]));
      }
    }
  }
}

// =========================================================================
// Combined-table (delta `d`) gmem AOS -> smem 2-row staging (relocated from
// warp_ntt_2pass.cuh; geometry inlined so this header has no geom dependency).
//   ROWS = VPT / 4   (1 for v4, 2 for v8);   ROW_BFS = (N/VPT) * 4 bf per row.
// Each thread does 1 vec_VPT LDG from gmem, then ROWS v4 STS into the per-row
// smem regions. Total smem footprint = N bf.
// =========================================================================
template <unsigned LOG_N, unsigned LOG_VPT> DEVICE_FORCEINLINE void stage_combined(bf *__restrict__ smem_dst, const bf *__restrict__ gmem_src, unsigned tid) {
  constexpr unsigned VPT = 1u << LOG_VPT;
  constexpr unsigned ROWS = VPT / 4u;
  constexpr unsigned ROW_BFS = ((1u << LOG_N) / VPT) * 4u;
  bf v[VPT];
  load_vec_vpt<LOG_VPT>(gmem_src + tid * VPT, v);
#pragma unroll
  for (unsigned row = 0; row < ROWS; ++row) {
    st_shared_v4(smem_dst + row * ROW_BFS + tid * 4u, v[row * 4u + 0], v[row * 4u + 1], v[row * 4u + 2], v[row * 4u + 3]);
  }
}

// Load this thread's VPT combined factors. STAGED=true → ROWS v4 LDS from the
// 2-row smem layout; STAGED=false → 1 vec_VPT LDG from gmem AOS.
template <unsigned LOG_N, unsigned LOG_VPT, bool STAGED> DEVICE_FORCEINLINE void load_combined(bf out[], const bf *__restrict__ src, unsigned tid) {
  constexpr unsigned VPT = 1u << LOG_VPT;
  constexpr unsigned ROWS = VPT / 4u;
  constexpr unsigned ROW_BFS = ((1u << LOG_N) / VPT) * 4u;
  if constexpr (STAGED) {
#pragma unroll
    for (unsigned row = 0; row < ROWS; ++row) {
      ld_shared_v4(src + row * ROW_BFS + tid * 4u, out[row * 4u + 0], out[row * 4u + 1], out[row * 4u + 2], out[row * 4u + 3]);
    }
  } else {
    load_vec_vpt<LOG_VPT>(src + tid * VPT, out);
  }
}

} // namespace ntt
} // namespace airbender
