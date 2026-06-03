// Ported from ntt-experiments include/ntt/geometry.cuh (rr/v8-logn13-two-pass-ntt).
// Compile-time geometry for the unified kernels.
#pragma once
#include <primitives/field.cuh>
using namespace ::airbender::primitives::field;
namespace airbender {
namespace ntt {

// Single-pass: one within-warp DIT phase. LANES = N/VPT in [1,32]. When
// LANES < 32 the warp packs NTTS_PER_WARP independent NTTs (same twiddles).
template <unsigned LOG_N_, unsigned LOG_VPT_> struct NttSingleGeom {
  static constexpr unsigned LOG_N = LOG_N_;
  static constexpr unsigned LOG_VPT = LOG_VPT_;
  static constexpr unsigned VPT = 1u << LOG_VPT;
  static constexpr unsigned N = 1u << LOG_N;
  static constexpr unsigned LANES = 1u << (LOG_N - LOG_VPT);
  static constexpr unsigned NTTS_PER_WARP = 32u / (LANES < 32u ? LANES : 32u);
  static_assert(LOG_VPT == 2u || LOG_VPT == 3u, "LOG_VPT in {2,3}");
  static_assert(LOG_N >= LOG_VPT, "LOG_N >= LOG_VPT");
  static_assert(LOG_N <= LOG_VPT + 5u, "single-pass fits one warp");
};

// Two-pass: conflict-free split (larger half -> pass 1), mirrors
// WarpNtt2PassDitGeom exactly.
template <unsigned LOG_N_, unsigned LOG_VPT_> struct NttTwoPassGeom {
  static constexpr unsigned LOG_N = LOG_N_;
  static constexpr unsigned LOG_VPT = LOG_VPT_;
  static constexpr unsigned VPT = 1u << LOG_VPT;
  static constexpr unsigned N = 1u << LOG_N;
  static constexpr unsigned LOG_N2 = (LOG_N / 2u < LOG_VPT + 3u) ? (LOG_N / 2u) : (LOG_VPT + 3u);
  static constexpr unsigned LOG_N1 = LOG_N - LOG_N2;
  static constexpr unsigned N1 = 1u << LOG_N1;
  static constexpr unsigned N2 = 1u << LOG_N2;
  static constexpr unsigned THREADS = N / VPT;
  static constexpr unsigned LANES_P1 = 1u << (LOG_N1 - LOG_VPT);
  static constexpr unsigned LANES_P2 = 1u << (LOG_N2 - LOG_VPT);
  static_assert(LOG_VPT == 2u || LOG_VPT == 3u, "LOG_VPT in {2,3}");
  static_assert(LOG_N1 >= LOG_VPT && LOG_N2 >= LOG_VPT, "each phase >= VPT");
  static_assert(LOG_N1 <= LOG_VPT + 5u && LOG_N2 <= LOG_VPT + 5u, "each phase fits one warp");
};

} // namespace ntt
} // namespace airbender
