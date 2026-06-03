// Ported from ntt-experiments include/ntt/swizzle.cuh (rr/v8-logn13-two-pass-ntt).
// V4SG slab-address swizzle for the unified two-pass transpose. Ported verbatim
// from warp_ntt_2pass.cuh (v4sg_dit_mask/v4sg_dit_addr) — the conflict-free
// masks for the full-DIT split (LOG_N2 = min(floor(LOG_N/2), LOG_VPT+3), larger
// half -> pass 1). Verified in scripts/ntt_transpose_bank.py. swz(L) flips only
// bits >= 2 (V4 alignment): the (L>>5)&1 term fixes the v8 V4-store 2-way, the
// (L>>k)&7 term spreads the phase-2 V1 read across banks. v4 store is already
// conflict-free (block = 4*tid) so only the spread term is used there.
#pragma once
#include <primitives/field.cuh>
using namespace ::airbender::primitives::field;
namespace airbender { namespace ntt {

template<unsigned LOG_N, unsigned LOG_VPT>
DEVICE_FORCEINLINE unsigned v4sg_dit_mask(unsigned L) {
  if constexpr (LOG_VPT == 3u) {            // v8
    if constexpr (LOG_N == 9u)  return ((L >> 5) & 1u) ^ ((L >> 6)  & 7u);
    if constexpr (LOG_N == 10u) return ((L >> 5) & 1u) ^ ((L >> 7)  & 7u);
    if constexpr (LOG_N == 11u) return ((L >> 5) & 1u) ^ ((L >> 8)  & 7u);
    if constexpr (LOG_N == 12u) return ((L >> 5) & 1u) ^ ((L >> 9)  & 7u);
    if constexpr (LOG_N == 13u) return ((L >> 5) & 1u) ^ ((L >> 10) & 7u);
  } else if constexpr (LOG_VPT == 2u) {     // v4
    if constexpr (LOG_N == 8u)  return (L >> 5) & 7u;
    if constexpr (LOG_N == 9u)  return (L >> 6) & 7u;
    if constexpr (LOG_N == 10u) return (L >> 7) & 7u;
    if constexpr (LOG_N == 11u) return (L >> 8) & 7u;
    if constexpr (LOG_N == 12u) return (L >> 9) & 7u;
  }
  return 0u;
}

template<unsigned LOG_N, unsigned LOG_VPT>
DEVICE_FORCEINLINE unsigned v4sg_dit_addr(unsigned L) {
  return L ^ (v4sg_dit_mask<LOG_N, LOG_VPT>(L) << 2);
}

}}  // namespace airbender::ntt
