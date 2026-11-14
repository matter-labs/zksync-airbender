#pragma once
#include "../gkr/support/kernel_helpers.cuh"

namespace airbender::gkr::ops::shared {

template <typename F> DEVICE_FORCEINLINE F lerp(const F a, const F b, const F r) { return F::add(a, F::mul(r, F::sub(b, a))); }

template <typename F>
DEVICE_FORCEINLINE void new_claims_two_var(const F *last_evals_packed, const F *challenges, F *new_claims_out, const unsigned num_addresses) {
  const unsigned idx = blockIdx.x * blockDim.x + threadIdx.x;
  if (idx >= num_addresses)
    return;
  const F r_before_last = challenges[0];
  const F r_last = challenges[1];
  const unsigned base = idx * 4u;
  const F v0 = last_evals_packed[base + 0];
  const F v1 = last_evals_packed[base + 1];
  const F v2 = last_evals_packed[base + 2];
  const F v3 = last_evals_packed[base + 3];
  const F low = lerp(v0, v1, r_last);
  const F high = lerp(v2, v3, r_last);
  new_claims_out[idx] = lerp(low, high, r_before_last);
}

template <typename F>
DEVICE_FORCEINLINE void new_claims_linear(const F *last_evals_packed, const F *challenges, F *new_claims_out, const unsigned num_addresses) {
  const unsigned idx = blockIdx.x * blockDim.x + threadIdx.x;
  if (idx >= num_addresses)
    return;
  const F r = challenges[0];
  const unsigned base = idx * 2u;
  const F v0 = last_evals_packed[base + 0];
  const F v1 = last_evals_packed[base + 1];
  new_claims_out[idx] = lerp(v0, v1, r);
}

template <typename F>
DEVICE_FORCEINLINE void dim_reducing_lsb_lines(const F *last_evals_packed, const F *challenges, F *lsb_lines_out, const unsigned num_addresses) {
  const unsigned idx = blockIdx.x * blockDim.x + threadIdx.x;
  if (idx >= num_addresses)
    return;
  const F r_before_last = challenges[0];
  const unsigned base = idx * 4u;
  const F v0 = last_evals_packed[base + 0];
  const F v1 = last_evals_packed[base + 1];
  const F v2 = last_evals_packed[base + 2];
  const F v3 = last_evals_packed[base + 3];
  lsb_lines_out[idx * 2u + 0u] = lerp(v0, v2, r_before_last);
  lsb_lines_out[idx * 2u + 1u] = lerp(v1, v3, r_before_last);
}

template <typename F, typename Desc>
DEVICE_FORCEINLINE void build_combined_claim(const F *claims, const F *batching, const Desc &desc, F *claim_out, F *eq_prefactor_out, F *warp_sums) {
  if (blockDim.x != 256 || gridDim.x != 1)
    return;
  const F b = *batching;
  F result = F::ZERO();
  for (unsigned i = threadIdx.x; i < desc.num_terms; i += 256) {
    const unsigned exp = desc.entries[2u * i];
    const unsigned idx = desc.entries[2u * i + 1u];
    result = F::add(result, F::mul(F::pow(b, exp), claims[idx]));
  }
  result = gkr_trace_holder_partials_warp_reduce_sum(result);
  const unsigned lane = threadIdx.x & 31;
  const unsigned warp = threadIdx.x >> 5;
  if (lane == 0)
    warp_sums[warp] = result;
  __syncthreads();
  if (warp == 0) {
    result = lane < 8 ? warp_sums[lane] : F::ZERO();
    result = gkr_trace_holder_partials_warp_reduce_sum(result);
    if (lane == 0) {
      *claim_out = result;
      *eq_prefactor_out = F::ONE();
    }
  }
}

} // namespace airbender::gkr::ops::shared
