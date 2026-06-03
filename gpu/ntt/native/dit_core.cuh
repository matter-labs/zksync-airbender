// Ported from ntt-experiments include/ntt/dit_core.cuh (rr/v8-logn13-two-pass-ntt).
// Unified within-warp radix-2 DIT engine. Ported from dit_phase
// (warp_ntt_2pass_dit.cuh), math-identical, with two simplifications:
//   * SINGLE_ROUND restore only (DitRestore enum + STAGED branch + RESTORE
//     param dropped).
//   * ONE twiddle read path (the N-1 per-thread triangle). The caller chooses
//     "clean" vs "coupled" purely via (LOG_TBL, tw_base, tw_row):
//       clean   (single-pass full NTT, two-pass pass-2): LOG_TBL=LOG_M,
//               tw_row=lane,  tw_base=lane*VPT      -> n2 absent, M-1 values.
//       coupled (two-pass pass-1):                  LOG_TBL=LOG_N,
//               tw_row=tid,   tw_base=p1_n2*N1      -> n2-block folded in.
// Operates IN-PLACE on w[VPT]; leaves natural per-thread layout (slot (lane,r)
// holds logical position lane*VPT + r). Handles sub-warp groups for LANES<32
// (single-pass NTTS-per-warp packing) and the full warp for LANES==32.
// Closed forms + restore verified in scripts/dit_pass1_couple.py (all configs).
#pragma once
#include <primitives/field.cuh>
#include "dit_twiddles.cuh"   // pt_stage_offset, load_local_stage_tw
using namespace ::airbender::primitives::field;
namespace airbender { namespace ntt {

// Local stages s in [0, LOG_VPT): in-register, in-place, per-thread triangle.
template<unsigned S, unsigned LOG_M, unsigned LOG_VPT, unsigned LOG_TBL>
DEVICE_FORCEINLINE void apply_local_stages_pt(bf w[], const bf* tw, unsigned tw_row) {
  constexpr unsigned VPT = 1u << LOG_VPT;
  if constexpr (S < LOG_VPT) {
    constexpr unsigned U    = VPT >> (S + 1u);
    constexpr unsigned half = 1u << S;
    bf tw_stage[U];
    airbender::ntt::load_local_stage_tw<U>(tw_stage, tw + pt_stage_offset<LOG_M, LOG_VPT, LOG_TBL>(S), tw_row);
    #pragma unroll
    for (unsigned p = 0; p < (VPT >> 1); ++p) {
      const unsigned low  = ((p >> S) << (S + 1u)) | (p & (half - 1u));
      const unsigned high = low + half;
      const unsigned q    = low >> (S + 1u);
      const bf l_val = w[low];
      const bf r_val = w[high];
      w[low]  = bf::add(l_val, r_val);
      w[high] = bf::mul(bf::sub(l_val, r_val), tw_stage[q]);
    }
    apply_local_stages_pt<S + 1u, LOG_M, LOG_VPT, LOG_TBL>(w, tw, tw_row);
  }
}

// One within-warp DIT phase of size 2^LOG_M. LANES = 2^(LOG_M-LOG_VPT) <= 32.
template<unsigned LOG_M, unsigned LANES, unsigned LOG_TBL, unsigned LOG_VPT,
         bool SKIP_LAST_TW>
DEVICE_FORCEINLINE void dit_phase(const bf* tw, unsigned tw_base, unsigned tw_row,
                                  unsigned lane, bf w[]) {
  constexpr unsigned VPT  = 1u << LOG_VPT;
  constexpr unsigned HALF = VPT >> 1u;
  static_assert(LANES == (1u << (LOG_M - LOG_VPT)), "dit_phase lane count");
  static_assert(LANES <= 32u, "phase must fit one warp");

  apply_local_stages_pt<0u, LOG_M, LOG_VPT, LOG_TBL>(w, tw, tw_row);

  if constexpr (LOG_M > LOG_VPT) {
    const unsigned warp_lane    = threadIdx.x & 31u;
    const unsigned subwarp_base = warp_lane & ~(LANES - 1u);
    const unsigned subwarp_mask = (LANES >= 32u)
        ? 0xFFFFFFFFu
        : (((1u << (LANES & 31u)) - 1u) << subwarp_base);

    // Non-restoring cross stages s in [LOG_VPT, LOG_M).
    #pragma unroll
    for (unsigned s = LOG_VPT; s < LOG_M; ++s) {
      const unsigned lane_mask  = 1u << (s - LOG_VPT);
      const bool     is_low     = (lane & lane_mask) == 0u;
      const bool     last_stage = (s + 1u) == LOG_M;
      const bool     skip_tw    = last_stage && SKIP_LAST_TW;
      const unsigned bg         = lane >> (s + 1u - LOG_VPT);
      bf tw_val;
      if (!skip_tw) {
        const unsigned gf = ((tw_base >> LOG_M) << (LOG_M - 1u - s)) | bg;
        tw_val = tw[pt_stage_offset<LOG_M, LOG_VPT, LOG_TBL>(s) + gf];
      }
      bf nw[VPT];
      #pragma unroll
      for (unsigned j = 0; j < HALF; ++j) {
        const bf reg_lo = w[j];
        const bf reg_hi = w[HALF + j];
        const bf send   = is_low ? reg_hi : reg_lo;
        const unsigned raw = __shfl_xor_sync(
            subwarp_mask, bf::into_raw_u32(send), lane_mask, LANES);
        const bf recv = bf::from_reduced_raw_repr(raw);
        const bf a    = is_low ? reg_lo : reg_hi;
        const bf sum  = bf::add(a, recv);
        const bf d    = is_low ? bf::sub(a, recv) : bf::sub(recv, a);
        nw[j]        = sum;
        nw[HALF + j] = skip_tw ? d : bf::mul(d, tw_val);
      }
      #pragma unroll
      for (unsigned r = 0; r < VPT; ++r) w[r] = nw[r];
    }

    // SINGLE_ROUND restore to natural per-thread layout.
    constexpr unsigned C = LOG_M - LOG_VPT;   // >= 1 here
    const unsigned t   = lane >> (C - 1u);
    const unsigned slb = 2u * (lane & ((1u << (C - 1u)) - 1u));
    bf nw[VPT];
    #pragma unroll
    for (unsigned regHi_d = 0; regHi_d < 2u; ++regHi_d) {
      const unsigned sl = slb + regHi_d;
      #pragma unroll
      for (unsigned regLow = 0; regLow < HALF; ++regLow) {
        const unsigned lo = __shfl_sync(subwarp_mask, bf::into_raw_u32(w[regLow]),        sl, LANES);
        const unsigned hi = __shfl_sync(subwarp_mask, bf::into_raw_u32(w[HALF + regLow]), sl, LANES);
        nw[regHi_d * HALF + regLow] = bf::from_reduced_raw_repr(t ? hi : lo);
      }
    }
    #pragma unroll
    for (unsigned r = 0; r < VPT; ++r) w[r] = nw[r];
  }
}

}}  // namespace airbender::ntt
