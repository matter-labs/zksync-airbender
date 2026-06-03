// Ported from ntt-experiments include/ntt/coset.cuh (rr/v8-logn13-two-pass-ntt).
// Shared coset glue. Initial per-slot twist mono[r] *= w^(bitrev(slot)*cfp);
// single-pass holds the per-step delta in registers (multi-coset walk).
// Coset omega now sourced from red's get_forward_twiddle_power (context.cuh),
// backed by red's Rust-initialized ab_ntt_forward_powers __constant__ table.
#pragma once
#include "context.cuh"    // get_forward_twiddle_power (red's Rust-initialized twiddle table)
#include "dit_memory.cuh" // bitrev_u32
#include <primitives/field.cuh>
using namespace ::airbender::primitives::field;
namespace airbender {
namespace ntt {

// Twist this thread's VPT slots in place. `slot0` = first logical slot index.
template <unsigned LOG_N, unsigned VPT> DEVICE_FORCEINLINE void coset_twist(bf mono[], unsigned slot0, u32 cfp) {
#pragma unroll
  for (unsigned r = 0; r < VPT; ++r) {
    const u32 br = bitrev_u32(slot0 + r, LOG_N);
    mono[r] = bf::mul(mono[r], get_forward_twiddle_power(br * cfp));
  }
}

// Per-step register delta for the single-pass multi-coset walk:
// d[r] = w^(bitrev(slot0+r) * coset_step). Apply with mono[r] *= d[r].
template <unsigned LOG_N, unsigned VPT> DEVICE_FORCEINLINE void coset_delta(bf d[], unsigned slot0, u32 coset_step) {
#pragma unroll
  for (unsigned r = 0; r < VPT; ++r) {
    const u32 br = bitrev_u32(slot0 + r, LOG_N);
    d[r] = get_forward_twiddle_power(br * coset_step);
  }
}

} // namespace ntt
} // namespace airbender
