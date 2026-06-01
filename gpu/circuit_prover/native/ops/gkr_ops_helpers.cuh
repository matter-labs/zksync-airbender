#pragma once

// Shared device-side helpers used by the backward sumcheck round-update
// kernel (`ab_backward_sumcheck_round_update_kernel` in `gkr_ops.cu`, used
// as the small-`acc_size` fallback by the backward main-layer scheduler)
// and by the fused-tail `mega_finalize` template at
// `gpu/circuit_prover/native/prover/gkr/backward/mega_finalize.cuh`. Keeping the
// algebra in one header guarantees the two consumers produce byte-identical
// per-round outputs.

#include "hash.cuh"

namespace airbender::ops::blake2s {

DEVICE_FORCEINLINE e4 e4_from_raw_u32x4(const u32 *words) {
  return e4(e2(bf::from_raw_repr_with_reduction(words[0]), bf::from_raw_repr_with_reduction(words[1])),
            e2(bf::from_raw_repr_with_reduction(words[2]), bf::from_raw_repr_with_reduction(words[3])));
}

// Port of prover::gkr::sumcheck::output_univariate_monomial_form_max_quadratic.
DEVICE_FORCEINLINE void compute_univariate_coeffs_max_quadratic(const e4 prev_challenge, const e4 prev_claim, const e4 e, const e4 c, e4 out[4]) {
  const e4 ONE = e4::ONE();
  const e4 b = e4::sub(ONE, prev_challenge);
  const e4 a = e4::sub(e4::dbl(prev_challenge), ONE);
  // a + b = prev_challenge.
  const e4 a_plus_b_inv = e4::inv(prev_challenge);

  const e4 be = e4::mul(b, e);
  e4 d = e4::sub(prev_claim, be);
  d = e4::mul(d, a_plus_b_inv);
  d = e4::sub(d, c);
  d = e4::sub(d, e);

  out[0] = be;
  out[1] = e4::add(e4::mul(a, e), e4::mul(b, d));
  out[2] = e4::add(e4::mul(a, d), e4::mul(b, c));
  out[3] = e4::mul(a, c);
}

// Horner evaluation of a degree-3 polynomial with 4 coefficients.
DEVICE_FORCEINLINE e4 eval_degree3_poly(const e4 coeffs[4], const e4 point) {
  e4 r = coeffs[3];
  r = e4::add(e4::mul(r, point), coeffs[2]);
  r = e4::add(e4::mul(r, point), coeffs[1]);
  r = e4::add(e4::mul(r, point), coeffs[0]);
  return r;
}

// eq(x, y) = x*y + (1-x)*(1-y).
DEVICE_FORCEINLINE e4 eq_poly(const e4 x, const e4 y) {
  const e4 ONE = e4::ONE();
  const e4 t = e4::mul(e4::sub(ONE, x), e4::sub(ONE, y));
  return e4::add(e4::mul(x, y), t);
}

// Blake2s transcript commit of (seed || flatten(coeffs)) and folding-challenge
// extraction. Matches the host `commit_field_els + draw_random_field_els`
// pair: seed (8 words) || flatten(4 E4 coeffs = 16 words) = 24 words processed
// as one non-final 16-word block followed by one final 8-word block, then the
// challenge is the first 4 u32 words of the updated state interpreted as a
// reduced E4. `seed_io` is overwritten with the post-commit state.
//
// Layout: `coeffs` must be 4 contiguous E4 elements with the layout shared by
// host `as_u32_raw_repr_reduced` flatten order — i.e. 4 u32 limbs per E4.
DEVICE_FORCEINLINE e4 commit_quadratic_and_draw_challenge(u32 *seed_io, const e4 coeffs[4]) {
  u32 state[STATE_SIZE];
  initialize(state);
  u32 t = 0;
  u32 block[BLOCK_SIZE];

#pragma unroll
  for (unsigned i = 0; i < STATE_SIZE; i++)
    block[i] = seed_io[i];
  const u32 *coeff_words = reinterpret_cast<const u32 *>(&coeffs[0]);
#pragma unroll
  for (unsigned i = 0; i < STATE_SIZE; i++)
    block[STATE_SIZE + i] = coeff_words[i];
  compress<false>(state, t, block, BLOCK_SIZE);

#pragma unroll
  for (unsigned i = 0; i < STATE_SIZE; i++)
    block[i] = coeff_words[STATE_SIZE + i];
#pragma unroll
  for (unsigned i = STATE_SIZE; i < BLOCK_SIZE; i++)
    block[i] = 0;
  compress<true>(state, t, block, STATE_SIZE);

#pragma unroll
  for (unsigned i = 0; i < STATE_SIZE; i++)
    seed_io[i] = state[i];

  // draw_random_field_els<E4>(seed, 1) yields 8 padding words but consumes
  // only 4 — the seed itself is not further hashed for a single draw.
  return e4_from_raw_u32x4(state);
}

// Per-round backward sumcheck state update. Given reduction outputs
// `(e_partial, c_partial)`, the previous-round claim point coordinate, and
// the running `(seed, claim, eq_prefactor)` state, this:
//   1. normalizes the claim by `1/eq_prefactor`,
//   2. derives the round's 4 univariate coefficients,
//   3. commits them to the Blake2s transcript and extracts the next challenge,
//   4. folds the claim through the univariate poly at the challenge,
//   5. refreshes `eq_prefactor = eq(challenge, prev_coord)`,
//   6. writes coeffs and challenge to the supplied output buffers.
//
// All pointers are device-resident. Intended to be called single-threaded
// (e.g. by lane 0 of a finalize block, or by the singleton thread of the
// standalone round-update kernel).
DEVICE_FORCEINLINE void run_round_update_single_thread(const e4 e_partial, const e4 c_partial, const e4 prev_coord, u32 *seed_io, e4 *claim_io,
                                                       e4 *eq_prefactor_io, e4 *coeffs_out, e4 *challenge_out) {
  const e4 claim = *claim_io;
  const e4 eq_prefactor = *eq_prefactor_io;
  const e4 normalized_claim = e4::mul(claim, e4::inv(eq_prefactor));

  e4 coeffs[4];
  compute_univariate_coeffs_max_quadratic(prev_coord, normalized_claim, e_partial, c_partial, coeffs);
#pragma unroll
  for (unsigned i = 0; i < 4; i++)
    coeffs_out[i] = coeffs[i];

  const e4 challenge = commit_quadratic_and_draw_challenge(seed_io, coeffs);
  *challenge_out = challenge;
  *claim_io = eval_degree3_poly(coeffs, challenge);
  *eq_prefactor_io = eq_poly(challenge, prev_coord);
}

} // namespace airbender::ops::blake2s
