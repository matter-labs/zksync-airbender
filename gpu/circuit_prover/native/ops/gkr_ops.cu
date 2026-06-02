#include "gkr_ops_helpers.cuh"

namespace airbender::ops::gkr_ops {

using namespace ::airbender::hash;

// ---------------------------------------------------------------------------
// Backward sumcheck per-round state update (device-side).
//
// Standalone entry point used by the small-`acc_size` fallback in the
// backward main-layer scheduler. Wraps the shared
// `run_round_update_single_thread` helper (see `gkr_ops_helpers.cuh`); the
// fused-tail kernels in `prover/gkr/backward/` reuse the same helper inside
// their mega-finalize blocks so the two paths produce byte-identical
// per-round outputs.
// ---------------------------------------------------------------------------
EXTERN __global__ void ab_backward_sumcheck_round_update_kernel(const e4 *reduction_output, const e4 *prev_claim_coord, u32 *seed_io, e4 *claim_io,
                                                                e4 *eq_prefactor_io, e4 *coeffs_out, e4 *challenge_out) {
  const e4 e_partial = reduction_output[0];
  const e4 c_partial = reduction_output[1];
  const e4 prev_coord = *prev_claim_coord;
  run_round_update_single_thread(e_partial, c_partial, prev_coord, seed_io, claim_io, eq_prefactor_io, coeffs_out, challenge_out);
}

// ---------------------------------------------------------------------------
// WHIR fold per-round state update (device-side).
//
// Replaces the host callback that runs after each special 3-point evaluation.
// Consumes the three reduction outputs (f(0), f(1), raw ⟨eval_l+eval_h,
// eq_l+eq_h⟩) and the running transcript seed, then:
//   1. computes f(1/2) = reduction_output[2] * (1/4),
//   2. Lagrange-interpolates the degree-2 sumcheck univariate at (0, 1, 1/2),
//   3. commits those 3 E4 coefficients to the transcript (Blake2s),
//   4. extracts the fold challenge from the first 4 u32 words of the updated
//      seed (matching host `BabyBearField::from_raw_repr_with_reduction`).
//
// All I/O buffers are on device. The kernel is launched <<<1,1>>>. Memory
// layout of e4 is 4 consecutive u32 limbs (Montgomery-form base field), which
// matches the host flatten order used by commit_field_els.
// ---------------------------------------------------------------------------
EXTERN __global__ void ab_whir_fold_round_update_kernel(const e4 *reduction_output, u32 *seed_io, e4 *coeffs_out, e4 *challenge_out) {
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

// ---------------------------------------------------------------------------
// Backward per-address "new_claims" evaluators (device-side).
//
// Replace the host loop that runs inside the end-of-layer final-readback
// callback. For the dimension-reducing case, each address i has 4 E4 values
// packed at `last_evals[4*i..4*i+4]` and the next claim is
// eq_ext(values, r_before_last, r_last)
//   = v0 * (1-r_bl) * (1-r_l)
//   + v1 * (1-r_bl) *    r_l
//   + v2 *    r_bl  * (1-r_l)
//   + v3 *    r_bl  *    r_l
//   = (1-r_bl) * lerp(v0, v1, r_l) + r_bl * lerp(v2, v3, r_l)
//   = lerp(lerp(v0, v1, r_l), lerp(v2, v3, r_l), r_bl)
// For the main-layer case, each address i has 2 E4 values at
// `last_evals[2*i..2*i+2]` and the next claim is lerp(v0, v1, last_r).
//
// Both kernels use `lerp(a, b, r) = a + r * (b - a)` which matches the host
// helpers `evaluate_with_two_variable_eq_ext` and `interpolate_linear`
// bit-for-bit.
//
// Buffer contracts:
// - `last_evals_packed`: `num_addresses * values_per_address` e4 values, packed
//   `[addr0_v0, addr0_v1, ..., addr_{N-1}_v_{P-1}]`.
// - `challenges`: 2 e4 `[r_before_last, r_last]` (two-var) or 1 e4 `[last_r]`
//   (linear).
// - `new_claims_out`: `num_addresses` e4 outputs.
// ---------------------------------------------------------------------------
DEVICE_FORCEINLINE e4 e4_lerp(const e4 a, const e4 b, const e4 r) {
  // a + r * (b - a)
  return e4::add(a, e4::mul(r, e4::sub(b, a)));
}

EXTERN __global__ void ab_backward_new_claims_two_var_kernel(const e4 *last_evals_packed, const e4 *challenges, e4 *new_claims_out,
                                                             const unsigned num_addresses) {
  const unsigned idx = blockIdx.x * blockDim.x + threadIdx.x;
  if (idx >= num_addresses)
    return;
  const e4 r_before_last = challenges[0];
  const e4 r_last = challenges[1];
  const unsigned base = idx * 4u;
  const e4 v0 = last_evals_packed[base + 0];
  const e4 v1 = last_evals_packed[base + 1];
  const e4 v2 = last_evals_packed[base + 2];
  const e4 v3 = last_evals_packed[base + 3];
  const e4 low = e4_lerp(v0, v1, r_last);
  const e4 high = e4_lerp(v2, v3, r_last);
  new_claims_out[idx] = e4_lerp(low, high, r_before_last);
}

EXTERN __global__ void ab_backward_new_claims_linear_kernel(const e4 *last_evals_packed, const e4 *challenges, e4 *new_claims_out,
                                                            const unsigned num_addresses) {
  const unsigned idx = blockIdx.x * blockDim.x + threadIdx.x;
  if (idx >= num_addresses)
    return;
  const e4 r = challenges[0];
  const unsigned base = idx * 2u;
  const e4 v0 = last_evals_packed[base + 0];
  const e4 v1 = last_evals_packed[base + 1];
  new_claims_out[idx] = e4_lerp(v0, v1, r);
}

// Mirror of `GpuCombinedClaimDesc` in gpu/circuit_prover/src/ops/blake2s.rs. Holds
// the per-layer `(exp, claim_idx)` descriptor pairs for `build_combined_claim`
// inline as kernel-arg data — replaces the prior device-buffer + per-layer H2D.
constexpr unsigned GKR_COMBINED_CLAIM_MAX_PAIRS = 1024;

struct gpu_combined_claim_desc {
  u32 num_terms;
  u32 _pad;
  u32 entries[2 * GKR_COMBINED_CLAIM_MAX_PAIRS];
};

static_assert(sizeof(gpu_combined_claim_desc) <= 32u * 1024u, "gpu_combined_claim_desc must fit under the 32 KB inline kernel-arg ceiling");

EXTERN __global__ void ab_build_combined_claim_kernel(const e4 *claims, const e4 *batching, __grid_constant__ const gpu_combined_claim_desc desc, e4 *claim_out,
                                                      e4 *eq_prefactor_out) {
  if (threadIdx.x != 0 || blockIdx.x != 0)
    return;
  const e4 b = *batching;
  e4 result = e4::ZERO();
  for (unsigned i = 0; i < desc.num_terms; i++) {
    const unsigned exp = desc.entries[2u * i];
    const unsigned idx = desc.entries[2u * i + 1u];
    e4 pow = e4::ONE();
    for (unsigned j = 0; j < exp; j++)
      pow = e4::mul(pow, b);
    result = e4::add(result, e4::mul(pow, claims[idx]));
  }
  *claim_out = result;
  *eq_prefactor_out = e4::ONE();
}

// ---------------------------------------------------------------------------
// Assemble query indexes from a stream of random u32 words (device-side).
//
// Mirrors the host `BitSource` + `assemble_query_index(log_domain_size, ...)`
// chain used in WHIR PoW query derivation. The bit stream is LE-packed across
// u32 words; the first 32 bits are skipped (they were consumed as the PoW
// header in `draw_query_bits_after_verified_pow`). Each query reads
// `log_domain_size` contiguous bits.
//
// Buffer contracts:
// - `raw_bits`: padded u32 buffer (matches the squeeze output size, at least
//   `ceil((32 + num_queries * log_domain_size) / 32)` words).
// - `indexes_out`: `num_queries` u32 indexes, one per thread.
// ---------------------------------------------------------------------------
EXTERN __global__ void ab_assemble_query_indexes_kernel(const u32 *raw_bits, u32 *indexes_out, const unsigned num_queries, const unsigned log_domain_size) {
  const unsigned idx = blockIdx.x * blockDim.x + threadIdx.x;
  if (idx >= num_queries)
    return;
  // Skip the first 32 bits (PoW header word); each subsequent query consumes
  // log_domain_size bits.
  const unsigned start_bit = 32u + idx * log_domain_size;
  u32 result = 0;
  for (unsigned i = 0; i < log_domain_size; i++) {
    const unsigned bit_pos = start_bit + i;
    const unsigned word_idx = bit_pos >> 5;
    const unsigned bit_idx = bit_pos & 31u;
    const u32 bit = (raw_bits[word_idx] >> bit_idx) & 1u;
    result |= bit << i;
  }
  indexes_out[idx] = result;
}

} // namespace airbender::ops::gkr_ops
