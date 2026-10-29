#pragma once
#include "keccak256.cuh"
#include "primitives/proth120.cuh"

namespace airbender::whir {

using ::airbender::primitives::field::pr;

DEVICE_FORCEINLINE void pr_whir_round_update_inline(pr *reductions, u8 *seed_io, pr *coeffs_out, pr *challenge_out) {
  const pr a = reductions[0];
  const pr b = reductions[1];
  const pr d = reductions[2];
  coeffs_out[0] = a;
  coeffs_out[1] = pr::sub(pr::sub(d, pr::add(pr::dbl(a), a)), b);
  coeffs_out[2] = pr::sub(pr::dbl(pr::add(a, b)), d);
  airbender::hash::keccak256::commit_fields(seed_io, coeffs_out, 3);
  *challenge_out = airbender::hash::keccak256::draw_field(seed_io);
}

} // namespace airbender::whir
