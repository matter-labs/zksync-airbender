#include "common.cuh"

namespace airbender::prover::gkr {

#define GKR_FORWARD_SETUP_KERNELS(arg_t)                                                                                                                       \
  EXTERN __global__ void ab_gkr_forward_setup_generic_lookup_##arg_t##_kernel(const __grid_constant__ gkr_forward_setup_generic_lookup_batch<arg_t> batch,     \
                                                                              const unsigned row_count) {                                                      \
    gkr_forward_setup_generic_lookup(batch, row_count);                                                                                                        \
  }

GKR_FORWARD_SETUP_KERNELS(e4);

// Evaluates a virtual range-check setup polynomial at the GKR base-layer claim
// point. Mirrors `evaluate_virtual_range_check_setup_poly<F, E, BITS>` in
// `prover/src/gkr/virtual_polys/range_check.rs`.
//
// The succinct form is:
//   result = (sum_{k=0..BITS-1} 2^k * x_{N-1-k}) * prod_{k=BITS..N-1} (1 - x_{N-1-k})
// where `eval_point[i]` is x_{i+1} indexed from the leading variable, so the
// reverse iteration starts at the trailing variable x_N.
static DEVICE_FORCEINLINE e4 evaluate_virtual_range_check_setup_poly(const e4 *eval_point, const u32 trace_len_log2, const u32 bits) {
  e4 result = e4(e2::ZERO(), e2::ZERO());
  bf prefactor = bf::ONE();
  for (u32 k = 0; k < bits; k++) {
    const e4 el = eval_point[trace_len_log2 - 1 - k];
    result = e4::add(result, e4::mul(el, prefactor));
    prefactor = bf::dbl(prefactor);
  }
  for (u32 k = bits; k < trace_len_log2; k++) {
    const e4 el = eval_point[trace_len_log2 - 1 - k];
    const e4 one_minus_el = e4::sub(bf::ONE(), el);
    result = e4::mul(result, one_minus_el);
  }
  return result;
}

// Evaluates the inits-and-teardowns base-address virtual setup polynomials
// at the GKR base-layer claim point. Mirrors
// `evaluate_virtual_inits_and_teardowns_base_address_setup_polys<F, E, WORD_BITS>`
// in `prover/src/gkr/virtual_polys/init_and_teardown_base.rs`.
//
// `low_out` cycles 2^WORD_BITS-multiples that wrap at 2^16.
// `high_out` increments once per wrap.
static DEVICE_FORCEINLINE void evaluate_virtual_inits_and_teardowns_base_address_setup_polys(const e4 *eval_point, const u32 trace_len_log2,
                                                                                             const u32 word_bits, e4 *low_out, e4 *high_out) {
  const u32 take_count = 16u - word_bits;
  e4 low_eval = e4(e2::ZERO(), e2::ZERO());
  bf prefactor = bf::from_u32_unchecked(1u << word_bits);
  for (u32 k = 0; k < take_count; k++) {
    const e4 el = eval_point[trace_len_log2 - 1 - k];
    low_eval = e4::add(low_eval, e4::mul(el, prefactor));
    prefactor = bf::dbl(prefactor);
  }
  *low_out = low_eval;

  e4 high_eval = e4(e2::ZERO(), e2::ZERO());
  prefactor = bf::ONE();
  for (u32 k = take_count; k < trace_len_log2; k++) {
    const e4 el = eval_point[trace_len_log2 - 1 - k];
    high_eval = e4::add(high_eval, e4::mul(el, prefactor));
    prefactor = bf::dbl(prefactor);
  }
  *high_out = high_eval;
}

// Computes the four virtual setup polynomial evaluations consumed by the host
// `populate_virtual_setup_claims` aggregation. Single block, single thread —
// the work per output is O(trace_len_log2) field ops, total ≪ 1 µs.
//
// Output slots (`*output`, length 4):
//   [0] = RangeCheck16Bits          (BITS = 16)
//   [1] = RangeCheckTimestamp       (BITS = TIMESTAMP_COLUMNS_NUM_BITS = 19)
//   [2] = InitsAndTeardownsLow      (WORD_BITS = 2)
//   [3] = InitsAndTeardownsHigh     (WORD_BITS = 2)
EXTERN __global__ void ab_gkr_eval_virtual_setup_claims_e4_kernel(const e4 *claim_point, const u32 trace_len_log2, e4 *output) {
  if (threadIdx.x != 0 || blockIdx.x != 0) {
    return;
  }
  output[0] = evaluate_virtual_range_check_setup_poly(claim_point, trace_len_log2, 16u);
  output[1] = evaluate_virtual_range_check_setup_poly(claim_point, trace_len_log2, 19u);
  e4 low_eval, high_eval;
  evaluate_virtual_inits_and_teardowns_base_address_setup_polys(claim_point, trace_len_log2, 2u, &low_eval, &high_eval);
  output[2] = low_eval;
  output[3] = high_eval;
}

} // namespace airbender::prover::gkr
