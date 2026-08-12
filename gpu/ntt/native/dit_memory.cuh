// bf-typed memory helpers. Every access routes through gpu_core's memory.cuh
// load_*/store_* wrappers, which select the PTX vector width from the POD's
// size and alignment and own the sm_100+ 256-bit arch guard, so no raw asm
// lives here.

#pragma once
#include <primitives/field.cuh>
#include <primitives/memory.cuh>
#include <primitives/ptx.cuh>
using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives;
namespace airbender {
namespace ntt {

namespace mem = ::airbender::primitives::memory;

// Packed bf vectors. Size and alignment select the access width via
// memory::load_unit<T>: 8 B -> uint2, 16 B -> uint4, 32 B -> u32x8. Not named
// bf2/bf4/bf8 -- e2/e4 are the extension-field prefixes in field.cuh.
struct __align__(8) bf2_wide {
  bf v[2];
};
struct __align__(16) bf4_wide {
  bf v[4];
};
struct __align__(32) bf8_wide {
  bf v[8];
};

// The alignments are load-bearing: at align(16), bf8_wide still satisfies
// ld/st's alignof check but load_unit selects uint4 and silently issues two
// 128-bit accesses in place of one 256-bit access.
static_assert(sizeof(bf2_wide) == 8 && alignof(bf2_wide) == 8, "bf2_wide ABI");
static_assert(sizeof(bf4_wide) == 16 && alignof(bf4_wide) == 16, "bf4_wide ABI");
static_assert(sizeof(bf8_wide) == 32 && alignof(bf8_wide) == 32, "bf8_wide ABI");

// `cg`: bypass L1, allocate L2-only.
DEVICE_FORCEINLINE bf ld_cg(const bf *p) { return bf::from_reduced_raw_repr(ptx::ld_cg(reinterpret_cast<const u32 *>(p))); }
DEVICE_FORCEINLINE void st_cg(bf *p, bf v) { ptx::st_cg(reinterpret_cast<u32 *>(p), bf::into_raw_u32(v)); }

DEVICE_FORCEINLINE void ld_cg_v2(const bf *p, bf &a, bf &b) {
  const bf2_wide r = mem::load_cg(reinterpret_cast<const bf2_wide *>(p));
  a = r.v[0];
  b = r.v[1];
}
DEVICE_FORCEINLINE void st_cg_v2(bf *p, bf a, bf b) {
  const bf2_wide w{{a, b}};
  mem::store_cg(reinterpret_cast<bf2_wide *>(p), w);
}

DEVICE_FORCEINLINE void ld_cg_v4(const bf *p, bf &a, bf &b, bf &c, bf &d) {
  const bf4_wide r = mem::load_cg(reinterpret_cast<const bf4_wide *>(p));
  a = r.v[0];
  b = r.v[1];
  c = r.v[2];
  d = r.v[3];
}
DEVICE_FORCEINLINE void st_cg_v4(bf *p, bf a, bf b, bf c, bf d) {
  const bf4_wide w{{a, b, c, d}};
  mem::store_cg(reinterpret_cast<bf4_wide *>(p), w);
}

DEVICE_FORCEINLINE void ld_cg_v8(const bf *p, bf &a0, bf &a1, bf &a2, bf &a3, bf &a4, bf &a5, bf &a6, bf &a7) {
  const bf8_wide r = mem::load_cg(reinterpret_cast<const bf8_wide *>(p));
  a0 = r.v[0];
  a1 = r.v[1];
  a2 = r.v[2];
  a3 = r.v[3];
  a4 = r.v[4];
  a5 = r.v[5];
  a6 = r.v[6];
  a7 = r.v[7];
}

// `ca`: cached-all, for the uniform twiddle-table reads.
DEVICE_FORCEINLINE bf ld_ca(const bf *p) { return bf::from_reduced_raw_repr(ptx::ld_ca(reinterpret_cast<const u32 *>(p))); }

// Caller must 16 B-align p.
DEVICE_FORCEINLINE void ld_ca_v4(const bf *p, bf &a, bf &b, bf &c, bf &d) {
  const bf4_wide r = mem::load_ca(reinterpret_cast<const bf4_wide *>(p));
  a = r.v[0];
  b = r.v[1];
  c = r.v[2];
  d = r.v[3];
}

// `cs`: cache-streaming (evict-first). For write-once output exceeding L2.
DEVICE_FORCEINLINE void st_cs_v4(bf *p, bf a, bf b, bf c, bf d) {
  const bf4_wide w{{a, b, c, d}};
  mem::store_cs(reinterpret_cast<bf4_wide *>(p), w);
}

// `wb`: write-back, the default store behavior.
DEVICE_FORCEINLINE void st_wb_v4(bf *p, bf a, bf b, bf c, bf d) {
  const bf4_wide w{{a, b, c, d}};
  mem::store_wb(reinterpret_cast<bf4_wide *>(p), w);
}

// `wt`: write-through, commits to DRAM. For the bench harness only: `cs` writes
// can still sit in L2, so cs-based timing reports L2 rather than DRAM throughput.
DEVICE_FORCEINLINE void st_wt_v4(bf *p, bf a, bf b, bf c, bf d) {
  const bf4_wide w{{a, b, c, d}};
  mem::store_wt(reinterpret_cast<bf4_wide *>(p), w);
}
DEVICE_FORCEINLINE void st_wt_v2(bf *p, bf a, bf b) {
  const bf2_wide w{{a, b}};
  mem::store_wt(reinterpret_cast<bf2_wide *>(p), w);
}
DEVICE_FORCEINLINE void st_v8_aligned_wt(bf *p, bf a0, bf a1, bf a2, bf a3, bf a4, bf a5, bf a6, bf a7) {
  const bf8_wide w{{a0, a1, a2, a3, a4, a5, a6, a7}};
  mem::store_wt(reinterpret_cast<bf8_wide *>(p), w);
}

// Packed stores at the default `wb` cache op, and their `cs` counterparts.
DEVICE_FORCEINLINE void st_v8_aligned(bf *p, bf a0, bf a1, bf a2, bf a3, bf a4, bf a5, bf a6, bf a7) {
  const bf8_wide w{{a0, a1, a2, a3, a4, a5, a6, a7}};
  mem::store_wb(reinterpret_cast<bf8_wide *>(p), w);
}

DEVICE_FORCEINLINE void st_v8_aligned_cs(bf *p, bf a0, bf a1, bf a2, bf a3, bf a4, bf a5, bf a6, bf a7) {
  const bf8_wide w{{a0, a1, a2, a3, a4, a5, a6, a7}};
  mem::store_cs(reinterpret_cast<bf8_wide *>(p), w);
}

DEVICE_FORCEINLINE void st_v4_aligned(bf *p, bf a0, bf a1, bf a2, bf a3) {
  const bf4_wide w{{a0, a1, a2, a3}};
  mem::store_wb(reinterpret_cast<bf4_wide *>(p), w);
}

DEVICE_FORCEINLINE void st_v4_aligned_cs(bf *p, bf a0, bf a1, bf a2, bf a3) { st_cs_v4(p, a0, a1, a2, a3); }

// Shared space: memory.cuh's ld_single/st_single are global-only, so these stay
// local. Well defined because every `extern __shared__` site declares
// __align__(16).
DEVICE_FORCEINLINE void ld_shared_v2(const bf *p, bf &a, bf &b) {
  const bf2_wide r = *reinterpret_cast<const bf2_wide *>(p);
  a = r.v[0];
  b = r.v[1];
}

DEVICE_FORCEINLINE void ld_shared_v4(const bf *p, bf &a, bf &b, bf &c, bf &d) {
  const bf4_wide r = *reinterpret_cast<const bf4_wide *>(p);
  a = r.v[0];
  b = r.v[1];
  c = r.v[2];
  d = r.v[3];
}
DEVICE_FORCEINLINE void st_shared_v4(bf *p, bf a, bf b, bf c, bf d) { *reinterpret_cast<bf4_wide *>(p) = bf4_wide{{a, b, c, d}}; }
DEVICE_FORCEINLINE void st_shared_v2(bf *p, bf a, bf b) { *reinterpret_cast<bf2_wide *>(p) = bf2_wide{{a, b}}; }

DEVICE_FORCEINLINE unsigned bitrev_u32(unsigned x, unsigned log_n) { return ::bitreverse_low_bits(x, log_n); }

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
// Combined-table (delta `d`) gmem AOS -> smem 2-row staging (geometry inlined
// so this header has no geom dependency).
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
