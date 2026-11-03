#include "../gkr/support/kernel_helpers.cuh"
#include "gkr_ops_helpers.cuh"

namespace airbender::gkr::ops {

using namespace ::airbender::hash;

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
  whir_fold_round_update_inline(reduction_output, seed_io, coeffs_out, challenge_out);
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

// Dim-reducing final-round LSB-line reduction. The last sumcheck round now
// emits a univariate monomial and draws `r_before_last` in-loop; the [e4;4] bilinear
// `last_evals` (over (last-output-coord) x (LSB-coord), packed
// [v0=(0,0), v1=(0,1), v2=(1,0), v3=(1,1)]) is reduced over the last-output coord at
// `r_before_last` into the [e4;2] LSB line that is sent in the proof and committed to
// the transcript. Per address: out[0]=lerp(v0,v2,rbl), out[1]=lerp(v1,v3,rbl). Matches
// the host `interpolate_linear(evals[0],evals[2],rbl)` / `(evals[1],evals[3],rbl)`.
// - `last_evals_packed`: `num_addresses * 4` e4.
// - `challenges`: `[r_before_last, ..]` (only slot 0 read).
// - `lsb_lines_out`: `num_addresses * 2` e4.
EXTERN __global__ void ab_backward_dim_reducing_lsb_lines_kernel(const e4 *last_evals_packed, const e4 *challenges, e4 *lsb_lines_out,
                                                                 const unsigned num_addresses) {
  const unsigned idx = blockIdx.x * blockDim.x + threadIdx.x;
  if (idx >= num_addresses)
    return;
  const e4 r_before_last = challenges[0];
  const unsigned base = idx * 4u;
  const e4 v0 = last_evals_packed[base + 0];
  const e4 v1 = last_evals_packed[base + 1];
  const e4 v2 = last_evals_packed[base + 2];
  const e4 v3 = last_evals_packed[base + 3];
  lsb_lines_out[idx * 2u + 0u] = e4_lerp(v0, v2, r_before_last);
  lsb_lines_out[idx * 2u + 1u] = e4_lerp(v1, v3, r_before_last);
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

EXTERN __global__ __launch_bounds__(256) void ab_build_combined_claim_kernel(const e4 *claims, const e4 *batching,
                                                                             __grid_constant__ const gpu_combined_claim_desc desc, e4 *claim_out,
                                                                             e4 *eq_prefactor_out) {
  if (blockDim.x != 256 || gridDim.x != 1)
    return;
  const e4 b = *batching;
  e4 result = e4::ZERO();
  for (unsigned i = threadIdx.x; i < desc.num_terms; i += 256) {
    const unsigned exp = desc.entries[2u * i];
    const unsigned idx = desc.entries[2u * i + 1u];
    result = e4::add(result, e4::mul(e4::pow(b, exp), claims[idx]));
  }
  result = gkr_trace_holder_partials_warp_reduce_sum(result);
  __shared__ e4 warp_sums[8];
  const unsigned lane = threadIdx.x & 31;
  const unsigned warp = threadIdx.x >> 5;
  if (lane == 0)
    warp_sums[warp] = result;
  __syncthreads();
  if (warp == 0) {
    result = lane < 8 ? warp_sums[lane] : e4::ZERO();
    result = gkr_trace_holder_partials_warp_reduce_sum(result);
    if (lane == 0) {
      *claim_out = result;
      *eq_prefactor_out = e4::ONE();
    }
  }
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

} // namespace airbender::gkr::ops
