#pragma once

// Backward sumcheck round-update helpers.

#include "hash.cuh"

namespace airbender::gkr::ops {

using namespace ::airbender::hash;

DEVICE_FORCEINLINE e4 e4_from_raw_u32x4(const u32 *words) {
  return e4(e2(bf::from_raw_repr_with_reduction(words[0]), bf::from_raw_repr_with_reduction(words[1])),
            e2(bf::from_raw_repr_with_reduction(words[2]), bf::from_raw_repr_with_reduction(words[3])));
}

// Port of prover::gkr::sumcheck::output_univariate_monomial_form_max_quadratic.
DEVICE_FORCEINLINE void compute_univariate_coeffs_max_quadratic(const e4 prev_challenge, const e4 prev_claim, const e4 e, const e4 c,
                                                                const e4 inv_prev_challenge, e4 out[4]) {
  const e4 ONE = e4::ONE();
  const e4 b = e4::sub(ONE, prev_challenge);
  const e4 a = e4::sub(e4::dbl(prev_challenge), ONE);
  const e4 be = e4::mul(b, e);
  e4 d = e4::sub(prev_claim, be);
  d = e4::mul(d, inv_prev_challenge);
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

// Called by one thread with device-resident state. The inverses may be
// computed cooperatively by the caller; the returned value is the new challenge.
DEVICE_FORCEINLINE e4 run_round_update_with_inverses(const e4 e_partial, const e4 c_partial, const e4 prev_coord, const e4 inv_eq, const e4 inv_prev_coord,
                                                     u32 *seed_io, e4 *claim_io, e4 *eq_prefactor_io, e4 *coeffs_out) {
  const e4 normalized_claim = e4::mul(*claim_io, inv_eq);
  e4 coeffs[4];
  compute_univariate_coeffs_max_quadratic(prev_coord, normalized_claim, e_partial, c_partial, inv_prev_coord, coeffs);
#pragma unroll
  for (unsigned i = 0; i < 4; i++)
    coeffs_out[i] = coeffs[i];
  const e4 challenge = commit_quadratic_and_draw_challenge(seed_io, coeffs);
  *claim_io = eval_degree3_poly(coeffs, challenge);
  *eq_prefactor_io = eq_poly(challenge, prev_coord);
  return challenge;
}

DEVICE_FORCEINLINE void run_round_update_single_thread(const e4 e_partial, const e4 c_partial, const e4 prev_coord, u32 *seed_io, e4 *claim_io,
                                                       e4 *eq_prefactor_io, e4 *coeffs_out, e4 *challenge_out) {
  const e4 inv_eq = e4::inv(*eq_prefactor_io);
  const e4 inv_prev_coord = e4::inv(prev_coord);
  *challenge_out = run_round_update_with_inverses(e_partial, c_partial, prev_coord, inv_eq, inv_prev_coord, seed_io, claim_io, eq_prefactor_io, coeffs_out);
}

// Body of `ab_whir_fold_round_update_kernel`: one thread consumes the three
// reductions and the running seed, writes the round's coefficients, the
// advanced seed and the fold challenge. Also called from `gpu_whir`'s fused
// symbolic step kernel.
DEVICE_FORCEINLINE void whir_fold_round_update_inline(const e4 *reduction_output, u32 *seed_io, e4 *coeffs_out, e4 *challenge_out) {
  // Derive constants: quart = 1/4, two_inv = 1/2 (Montgomery form).
  const bf two = bf::from_u32_unchecked(2);
  const bf four = bf::from_u32_unchecked(4);
  const bf two_inv_bf = bf::inv(two);
  const bf quart_bf = bf::inv(four);
  const e4 random_point = e4::from_scalar(two_inv_bf);
  const e4 ONE = e4::ONE();
  const e4 ZERO = e4::ZERO();

  // Load evals and scale the half-point evaluation by 1/4 (the host does
  // `values[2].mul_assign_by_base(&quart)`).
  const e4 eval_at_0 = reduction_output[0];
  const e4 eval_at_1 = reduction_output[1];
  const e4 eval_at_random = e4::mul(reduction_output[2], quart_bf);

  // Lagrange interpolant at x in {0, 1, random_point = 1/2}.
  //   coeffs_for_0      = [rp, -(1+rp), 1]
  //   coeffs_for_1      = [ 0,     -rp, 1]
  //   coeffs_for_random = [ 0,      -1, 1]
  e4 coeffs_for_0[3];
  coeffs_for_0[0] = random_point;
  coeffs_for_0[1] = e4::neg(e4::add(ONE, random_point));
  coeffs_for_0[2] = ONE;

  e4 coeffs_for_1[3];
  coeffs_for_1[0] = ZERO;
  coeffs_for_1[1] = e4::neg(random_point);
  coeffs_for_1[2] = ONE;

  e4 coeffs_for_random[3];
  coeffs_for_random[0] = ZERO;
  coeffs_for_random[1] = e4::neg(ONE);
  coeffs_for_random[2] = ONE;

  // Denominators:
  //   dens[0] = (0 - 1) * (0 - rp) = rp
  //   dens[1] = (1 - rp)
  //   dens[2] = rp * (rp - 1)
  e4 dens[3];
  dens[0] = random_point;
  dens[1] = e4::sub(ONE, random_point);
  dens[2] = e4::mul(random_point, e4::sub(random_point, ONE));

  // Three inversions (launched <<<1,1>>> — no parallelism to gain from a
  // batched Montgomery trick here, and explicit inv keeps the bookkeeping
  // obvious).
  dens[0] = e4::inv(dens[0]);
  dens[1] = e4::inv(dens[1]);
  dens[2] = e4::inv(dens[2]);

  // Accumulate interpolant coefficients.
  const e4 evals[3] = {eval_at_0, eval_at_1, eval_at_random};
  const e4 *coeff_tables[3] = {coeffs_for_0, coeffs_for_1, coeffs_for_random};
  e4 result[3] = {ZERO, ZERO, ZERO};
#pragma unroll
  for (unsigned j = 0; j < 3; j++) {
    const e4 eval_den = e4::mul(evals[j], dens[j]);
#pragma unroll
    for (unsigned i = 0; i < 3; i++) {
      result[i] = e4::add(result[i], e4::mul(eval_den, coeff_tables[j][i]));
    }
  }

#pragma unroll
  for (unsigned i = 0; i < 3; i++)
    coeffs_out[i] = result[i];

  // Blake2s commit: seed (8 words) || flatten(3 × E4 = 12 words) = 20 words.
  // One non-final 16-word block, then one final 4-word block.
  u32 state[STATE_SIZE];
  initialize(state);
  u32 t = 0;
  u32 block[BLOCK_SIZE];

#pragma unroll
  for (unsigned i = 0; i < STATE_SIZE; i++)
    block[i] = seed_io[i];
  const u32 *coeff_words = reinterpret_cast<const u32 *>(&result[0]);
#pragma unroll
  for (unsigned i = 0; i < STATE_SIZE; i++)
    block[STATE_SIZE + i] = coeff_words[i];
  compress<false>(state, t, block, BLOCK_SIZE);

#pragma unroll
  for (unsigned i = 0; i < 4; i++)
    block[i] = coeff_words[STATE_SIZE + i];
#pragma unroll
  for (unsigned i = 4; i < BLOCK_SIZE; i++)
    block[i] = 0;
  compress<true>(state, t, block, 4);

#pragma unroll
  for (unsigned i = 0; i < STATE_SIZE; i++)
    seed_io[i] = state[i];

  // Extract the fold challenge from the first 4 words of the new seed.
  *challenge_out = e4_from_raw_u32x4(state);
}

} // namespace airbender::gkr::ops
