#include "../../gkr/support/kernel_helpers.cuh"
#include "primitives/proth120.cuh"

namespace airbender::gkr::proth120::ops {

using pr = ::airbender::primitives::field::proth120;

static_assert(sizeof(void *) == 8 && sizeof(unsigned) == 4 && sizeof(pr) == 16);
static_assert(3 * sizeof(void *) + sizeof(unsigned) <= 32764);

DEVICE_FORCEINLINE pr pr_lerp(const pr a, const pr b, const pr r) { return pr::add(a, pr::mul(r, pr::sub(b, a))); }

EXTERN __global__ void ab_pr_gkr_ops_new_claims_two_var_kernel(const pr *last_evals_packed, const pr *challenges, pr *new_claims_out,
                                                               const unsigned num_addresses) {
  const unsigned idx = blockIdx.x * blockDim.x + threadIdx.x;
  if (idx >= num_addresses)
    return;
  const pr r_before_last = challenges[0];
  const pr r_last = challenges[1];
  const unsigned base = idx * 4u;
  const pr low = pr_lerp(last_evals_packed[base + 0], last_evals_packed[base + 1], r_last);
  const pr high = pr_lerp(last_evals_packed[base + 2], last_evals_packed[base + 3], r_last);
  new_claims_out[idx] = pr_lerp(low, high, r_before_last);
}

EXTERN __global__ void ab_pr_gkr_ops_new_claims_linear_kernel(const pr *last_evals_packed, const pr *challenges, pr *new_claims_out,
                                                              const unsigned num_addresses) {
  const unsigned idx = blockIdx.x * blockDim.x + threadIdx.x;
  if (idx >= num_addresses)
    return;
  const unsigned base = idx * 2u;
  new_claims_out[idx] = pr_lerp(last_evals_packed[base + 0], last_evals_packed[base + 1], challenges[0]);
}

EXTERN __global__ void ab_pr_gkr_ops_dim_reducing_lsb_lines_kernel(const pr *last_evals_packed, const pr *challenges, pr *lsb_lines_out,
                                                                   const unsigned num_addresses) {
  const unsigned idx = blockIdx.x * blockDim.x + threadIdx.x;
  if (idx >= num_addresses)
    return;
  const pr r_before_last = challenges[0];
  const unsigned base = idx * 4u;
  lsb_lines_out[idx * 2u + 0u] = pr_lerp(last_evals_packed[base + 0], last_evals_packed[base + 2], r_before_last);
  lsb_lines_out[idx * 2u + 1u] = pr_lerp(last_evals_packed[base + 1], last_evals_packed[base + 3], r_before_last);
}

constexpr unsigned PR_COMBINED_CLAIM_MAX_PAIRS = 1024;

struct pr_combined_claim_desc {
  u32 num_terms;
  u32 _pad;
  u32 entries[2 * PR_COMBINED_CLAIM_MAX_PAIRS];
};

static_assert(sizeof(pr_combined_claim_desc) == 8 + 8 * PR_COMBINED_CLAIM_MAX_PAIRS);
static_assert(2 * sizeof(void *) + sizeof(pr_combined_claim_desc) + 2 * sizeof(void *) <= 32764);

EXTERN __global__ __launch_bounds__(256) void ab_pr_gkr_ops_build_combined_claim_kernel(const pr *claims, const pr *batching,
                                                                                        __grid_constant__ const pr_combined_claim_desc desc, pr *claim_out,
                                                                                        pr *eq_prefactor_out) {
  if (blockDim.x != 256 || gridDim.x != 1)
    return;
  const pr b = *batching;
  pr result = pr::ZERO();
  for (unsigned i = threadIdx.x; i < desc.num_terms; i += 256)
    result = pr::add(result, pr::mul(pr::pow(b, desc.entries[2u * i]), claims[desc.entries[2u * i + 1u]]));
  result = ::airbender::gkr::gkr_trace_holder_partials_warp_reduce_sum(result);
  __shared__ pr warp_sums[8];
  const unsigned lane = threadIdx.x & 31;
  const unsigned warp = threadIdx.x >> 5;
  if (lane == 0)
    warp_sums[warp] = result;
  __syncthreads();
  if (warp == 0) {
    result = lane < 8 ? warp_sums[lane] : pr::ZERO();
    result = ::airbender::gkr::gkr_trace_holder_partials_warp_reduce_sum(result);
    if (lane == 0) {
      *claim_out = result;
      *eq_prefactor_out = pr::ONE();
    }
  }
}

} // namespace airbender::gkr::proth120::ops
