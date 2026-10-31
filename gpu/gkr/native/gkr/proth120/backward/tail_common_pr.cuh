#pragma once
#include "../../support/descriptors.cuh"
#include "accumulator_pr.cuh"
#include "keccak256.cuh"
#include "primitives/proth120.cuh"

namespace airbender::gkr::proth120::backward {

using pr = ::airbender::primitives::field::proth120;

DEVICE_FORCEINLINE void compute_univariate_coeffs_max_quadratic_pr(const pr prev_challenge, const pr prev_claim, const pr e, const pr c,
                                                                   const pr inv_prev_challenge, pr out[4]) {
  const pr b = pr::sub(pr_one(), prev_challenge);
  const pr a = pr::sub(pr::dbl(prev_challenge), pr_one());
  const pr be = pr::mul(b, e);
  pr d = pr::sub(prev_claim, be);
  d = pr::mul(d, inv_prev_challenge);
  d = pr::sub(d, c);
  d = pr::sub(d, e);
  out[0] = be;
  out[1] = pr::add(pr::mul(a, e), pr::mul(b, d));
  out[2] = pr::add(pr::mul(a, d), pr::mul(b, c));
  out[3] = pr::mul(a, c);
}

DEVICE_FORCEINLINE pr eval_degree3_poly_pr(const pr coeffs[4], const pr point) {
  pr r = coeffs[3];
  r = pr::add(pr::mul(r, point), coeffs[2]);
  r = pr::add(pr::mul(r, point), coeffs[1]);
  r = pr::add(pr::mul(r, point), coeffs[0]);
  return r;
}

DEVICE_FORCEINLINE pr eq_poly_pr(const pr x, const pr y) {
  const pr t = pr::mul(pr::sub(pr_one(), x), pr::sub(pr_one(), y));
  return pr::add(pr::mul(x, y), t);
}

DEVICE_FORCEINLINE pr run_round_update_pr(u8 *seed, const pr coeffs[4]) {
  ::airbender::hash::keccak256::commit_fields(seed, coeffs, 4);
  return ::airbender::hash::keccak256::draw_field(seed);
}

DEVICE_FORCEINLINE pr run_round_update_with_inverses_pr(const pr e_partial, const pr c_partial, const pr prev_coord, const pr inv_eq, const pr inv_prev_coord,
                                                        u8 *seed, pr *claim_io, pr *eq_prefactor_io, pr *coeffs_out) {
  const pr normalized_claim = pr::mul(*claim_io, inv_eq);
  pr coeffs[4];
  compute_univariate_coeffs_max_quadratic_pr(prev_coord, normalized_claim, e_partial, c_partial, inv_prev_coord, coeffs);
#pragma unroll
  for (u32 i = 0; i < 4; i++)
    coeffs_out[i] = coeffs[i];
  const pr challenge = run_round_update_pr(seed, coeffs);
  *claim_io = eval_degree3_poly_pr(coeffs, challenge);
  *eq_prefactor_io = eq_poly_pr(challenge, prev_coord);
  return challenge;
}

DEVICE_FORCEINLINE void run_round_update_single_thread_pr(const pr e_partial, const pr c_partial, const pr prev_coord, u8 *seed, pr *claim_io,
                                                          pr *eq_prefactor_io, pr *coeffs_out, pr *challenge_out) {
  const pr inv_eq = pr::inv(*eq_prefactor_io);
  const pr inv_prev_coord = pr::inv(prev_coord);
  *challenge_out = run_round_update_with_inverses_pr(e_partial, c_partial, prev_coord, inv_eq, inv_prev_coord, seed, claim_io, eq_prefactor_io, coeffs_out);
}

template <u32 BLOCK_THREADS> DEVICE_FORCEINLINE void fold_active_eq_slot_pr(pr *__restrict__ active_eq_slot_base, const u32 active_eq_size_before_fold) {
  static_assert(BLOCK_THREADS >= ::airbender::gkr::GKR_EQ_GROUP_TABLE_LEN / 2);
  const u32 tid = threadIdx.x;
  const u32 new_g_len = active_eq_size_before_fold >= 1 ? 1u << (active_eq_size_before_fold - 1) : 0u;
  const bool folds = tid < new_g_len;
  pr folded = pr_zero();
  if (folds)
    folded = pr::add(active_eq_slot_base[2 * tid], active_eq_slot_base[2 * tid + 1]);
  __syncthreads();
  if (folds)
    active_eq_slot_base[tid] = folded;
}

} // namespace airbender::gkr::proth120::backward
