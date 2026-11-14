#include "../../gkr/support/kernel_helpers.cuh"
#include "../gkr_ops_shared.cuh"
#include "primitives/proth120.cuh"

namespace airbender::gkr::proth120::ops {

using pr = ::airbender::primitives::field::proth120;

static_assert(sizeof(void *) == 8 && sizeof(unsigned) == 4 && sizeof(pr) == 16);
static_assert(3 * sizeof(void *) + sizeof(unsigned) <= 32764);

EXTERN __global__ void ab_pr_gkr_ops_new_claims_two_var_kernel(const pr *last_evals_packed, const pr *challenges, pr *new_claims_out,
                                                               const unsigned num_addresses) {
  ::airbender::gkr::ops::shared::new_claims_two_var(last_evals_packed, challenges, new_claims_out, num_addresses);
}
EXTERN __global__ void ab_pr_gkr_ops_new_claims_linear_kernel(const pr *last_evals_packed, const pr *challenges, pr *new_claims_out,
                                                              const unsigned num_addresses) {
  ::airbender::gkr::ops::shared::new_claims_linear(last_evals_packed, challenges, new_claims_out, num_addresses);
}
EXTERN __global__ void ab_pr_gkr_ops_dim_reducing_lsb_lines_kernel(const pr *last_evals_packed, const pr *challenges, pr *lsb_lines_out,
                                                                   const unsigned num_addresses) {
  ::airbender::gkr::ops::shared::dim_reducing_lsb_lines(last_evals_packed, challenges, lsb_lines_out, num_addresses);
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
  __shared__ pr warp_sums[8];
  ::airbender::gkr::ops::shared::build_combined_claim(claims, batching, desc, claim_out, eq_prefactor_out, warp_sums);
}
} // namespace airbender::gkr::proth120::ops
