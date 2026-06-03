// Ported from ntt-experiments include/ntt/twiddles.cuh (rr/v8-logn13-two-pass-ntt).
// Unified twiddle layout: the N-1 per-thread triangle. ONE read path for both
// kernel families; only the baked VALUES and the caller's (tw_row, tw_base)
// differ (clean: keyed on lane, no redundancy; coupled pass-1: keyed on tid,
// n2-block folded in). Verified in scripts/dit_pass1_couple.py (build_cmp /
// build_clean_triangle). Local stages tid/lane-direct (V4/V2/V1 by count U_s);
// cross stages one-per-group (V1 broadcast). Total per phase = 2^M - 1.
#pragma once
#include "dit_memory.cuh" // ld_shared_v2/v4, ld_cg_v4, st_shared_v4
#include <primitives/field.cuh>
using namespace ::airbender::primitives::field;
namespace airbender {
namespace ntt {

// --- read primitives (ported from warp_ntt_2pass.cuh) ----------------------
// Stage-block offset within the per-thread triangle. BOTH the local THREADS and
// the cross block scale with LOG_TBL (the table-sizing log), NOT LOG_M:
//   CLEAN triangle (single-pass / pass-2): LOG_TBL = LOG_M  -> THREADS = LANES,
//     cross block = 2^(LOG_M-1-s)  (one phase's groups; n2 absent).
//   COUPLED pass-1 triangle:               LOG_TBL = LOG_N  -> THREADS = full
//     block, cross block = 2^(LOG_N-1-s) (all n2 blocks' global groups).
// LOG_M is unused here (it parametrizes only the in-phase gf shift in the
// engine); the original pt_stage_offset likewise ignored its LOG_M arg.
template <unsigned LOG_M, unsigned LOG_VPT, unsigned LOG_TBL> DEVICE_FORCEINLINE constexpr unsigned pt_stage_offset(unsigned s) {
  const unsigned THREADS = 1u << (LOG_TBL - LOG_VPT);
  unsigned off = 0;
  for (unsigned k = 0; k < s; ++k) {
    if (k < LOG_VPT)
      off += THREADS * (1u << (LOG_VPT - 1u - k)); // local block
    else
      off += 1u << (LOG_TBL - 1u - k); // cross block
  }
  return off;
}

// U unique local-stage twiddles in one LDS: V4 (U=4) / V2 (U=2) / scalar (U=1).
template <unsigned U> DEVICE_FORCEINLINE void load_local_stage_tw(bf out[], const bf *base, unsigned row) {
  if constexpr (U == 4u)
    ld_shared_v4(base + row * 4u, out[0], out[1], out[2], out[3]);
  else if constexpr (U == 2u)
    ld_shared_v2(base + row * 2u, out[0], out[1]);
  else
    out[0] = base[row];
}

// --- host builders ---------------------------------------------------------
// CLEAN size-M triangle count (used for smem sizing/staging).
template <unsigned LOG_M, unsigned LOG_VPT> constexpr unsigned clean_triangle_count() {
  constexpr unsigned LANES = 1u << (LOG_M - LOG_VPT);
  return (LANES << LOG_VPT) - 1u; // 2^M - 1
}

// COUPLED pass-1 triangle count (used for smem sizing/staging).
template <unsigned LOG_N, unsigned LOG_VPT, unsigned LOG_N1> constexpr unsigned coupled_triangle_count() {
  constexpr unsigned VPT = 1u << LOG_VPT;
  constexpr unsigned THREADS = 1u << (LOG_N - LOG_VPT);
  constexpr unsigned LANES_P1 = 1u << (LOG_N1 - LOG_VPT);
  constexpr unsigned N2 = 1u << (LOG_N - LOG_N1);
  return THREADS * (VPT - 1u) + N2 * (LANES_P1 - 1u);
}

// V4 global->smem staging of a triangle. `count` may not be a multiple of 4:
// the CLEAN triangle is 2^M-1 (== 3 mod 4) so 3 tail elements remain after the
// V4 loop; the COUPLED triangle count is a multiple of 4 (tail=0). The V4 loop
// covers [0, count & ~3); the (count & 3) tail uses scalar stores.
DEVICE_FORCEINLINE void stage_triangle_v4(bf *dst, const bf *src, unsigned count, unsigned tid, unsigned block_threads) {
  const unsigned tail = count & 3u; // 3 for clean (2^M-1), 0 for coupled
  const unsigned v4 = count >> 2u;  // number of 4-element groups
  for (unsigned i = tid; i < v4; i += block_threads) {
    bf a, b, c, d;
    ld_cg_v4(src + 4u * i, a, b, c, d);
    st_shared_v4(dst + 4u * i, a, b, c, d);
  }
  // Stage the (always 3) tail elements: thread tid handles tail element tid.
  const unsigned tail_base = v4 * 4u;
  if (tid < tail) {
    dst[tail_base + tid] = ld_cg(src + tail_base + tid);
  }
}

} // namespace ntt
} // namespace airbender
