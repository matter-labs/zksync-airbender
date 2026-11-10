#pragma once
#include "../../../ops/round_update_shared.cuh"
#include "../../backward/tail_common.cuh"
#include "../../support/descriptors.cuh"
#include "accumulator_pr.cuh"
#include "keccak256.cuh"
#include "primitives/proth120.cuh"

namespace airbender::gkr::proth120::backward {

using pr = ::airbender::primitives::field::proth120;

DEVICE_FORCEINLINE void compute_univariate_coeffs_max_quadratic_pr(const pr prev_challenge, const pr prev_claim, const pr e, const pr c,
                                                                   const pr inv_prev_challenge, pr out[4]) {
  ::airbender::gkr::ops::shared::compute_univariate_coeffs_max_quadratic(prev_challenge, prev_claim, e, c, inv_prev_challenge, out);
}

DEVICE_FORCEINLINE pr eval_degree3_poly_pr(const pr coeffs[4], const pr point) { return ::airbender::gkr::ops::shared::eval_degree3_poly(coeffs, point); }

DEVICE_FORCEINLINE pr eq_poly_pr(const pr x, const pr y) { return ::airbender::gkr::ops::shared::eq_poly(x, y); }

DEVICE_FORCEINLINE pr run_round_update_pr(u8 *seed, const pr coeffs[4]) {
  ::airbender::hash::keccak256::commit_fields(seed, coeffs, 4);
  return ::airbender::hash::keccak256::draw_field(seed);
}
struct quadratic_round_commit {
  DEVICE_FORCEINLINE pr operator()(u8 *seed, const pr *coeffs) const { return run_round_update_pr(seed, coeffs); }
};

DEVICE_FORCEINLINE pr run_round_update_with_inverses_pr(const pr e_partial, const pr c_partial, const pr prev_coord, const pr inv_eq, const pr inv_prev_coord,
                                                        u8 *seed, pr *claim_io, pr *eq_prefactor_io, pr *coeffs_out) {
  return ::airbender::gkr::ops::shared::run_round_update_with_inverses(e_partial, c_partial, prev_coord, inv_eq, inv_prev_coord, seed, claim_io,
                                                                       eq_prefactor_io, coeffs_out, quadratic_round_commit{});
}

DEVICE_FORCEINLINE void run_round_update_single_thread_pr(const pr e_partial, const pr c_partial, const pr prev_coord, u8 *seed, pr *claim_io,
                                                          pr *eq_prefactor_io, pr *coeffs_out, pr *challenge_out) {
  ::airbender::gkr::ops::shared::run_round_update_single_thread(e_partial, c_partial, prev_coord, seed, claim_io, eq_prefactor_io, coeffs_out, challenge_out,
                                                                quadratic_round_commit{});
}

} // namespace airbender::gkr::proth120::backward
