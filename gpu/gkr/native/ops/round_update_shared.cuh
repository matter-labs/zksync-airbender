#pragma once
#include "primitives/field.cuh"

namespace airbender::gkr::ops::shared {

template <typename F>
DEVICE_FORCEINLINE void compute_univariate_coeffs_max_quadratic(const F prev_challenge, const F prev_claim, const F e, const F c, const F inv_prev_challenge,
                                                                F out[4]) {
  const F ONE = F::ONE();
  const F b = F::sub(ONE, prev_challenge);
  const F a = F::sub(F::dbl(prev_challenge), ONE);
  const F be = F::mul(b, e);
  F d = F::sub(prev_claim, be);
  d = F::mul(d, inv_prev_challenge);
  d = F::sub(d, c);
  d = F::sub(d, e);

  out[0] = be;
  out[1] = F::add(F::mul(a, e), F::mul(b, d));
  out[2] = F::add(F::mul(a, d), F::mul(b, c));
  out[3] = F::mul(a, c);
}

template <typename F> DEVICE_FORCEINLINE F eval_degree3_poly(const F coeffs[4], const F point) {
  F r = coeffs[3];
  r = F::add(F::mul(r, point), coeffs[2]);
  r = F::add(F::mul(r, point), coeffs[1]);
  r = F::add(F::mul(r, point), coeffs[0]);
  return r;
}

template <typename F> DEVICE_FORCEINLINE F eq_poly(const F x, const F y) {
  const F ONE = F::ONE();
  const F t = F::mul(F::sub(ONE, x), F::sub(ONE, y));
  return F::add(F::mul(x, y), t);
}

template <typename F, typename Seed, typename Commit>
DEVICE_FORCEINLINE F run_round_update_with_inverses(const F e_partial, const F c_partial, const F prev_coord, const F inv_eq, const F inv_prev_coord,
                                                    Seed *seed_io, F *claim_io, F *eq_prefactor_io, F *coeffs_out, Commit commit) {
  const F normalized_claim = F::mul(*claim_io, inv_eq);
  F coeffs[4];
  compute_univariate_coeffs_max_quadratic(prev_coord, normalized_claim, e_partial, c_partial, inv_prev_coord, coeffs);
#pragma unroll
  for (unsigned i = 0; i < 4; i++)
    coeffs_out[i] = coeffs[i];
  const F challenge = commit(seed_io, coeffs);
  *claim_io = eval_degree3_poly(coeffs, challenge);
  *eq_prefactor_io = eq_poly(challenge, prev_coord);
  return challenge;
}

template <typename F, typename Seed, typename Commit>
DEVICE_FORCEINLINE void run_round_update_single_thread(const F e_partial, const F c_partial, const F prev_coord, Seed *seed_io, F *claim_io, F *eq_prefactor_io,
                                                       F *coeffs_out, F *challenge_out, Commit commit) {
  const F inv_eq = F::inv(*eq_prefactor_io);
  const F inv_prev_coord = F::inv(prev_coord);
  *challenge_out =
      run_round_update_with_inverses(e_partial, c_partial, prev_coord, inv_eq, inv_prev_coord, seed_io, claim_io, eq_prefactor_io, coeffs_out, commit);
}

} // namespace airbender::gkr::ops::shared
