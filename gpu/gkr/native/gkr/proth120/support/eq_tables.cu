#include "../../support/eq_high_low.cuh"
#include "../../support/eq_inline.cuh"
#include "../../support/kernel_helpers.cuh"
#include "primitives/proth120.cuh"
namespace airbender::gkr::proth120::support {
using pr = ::airbender::primitives::field::proth120;
static_assert(sizeof(void *) == 8 && sizeof(u32) == 4 && sizeof(pr) == 16 && alignof(pr) == 16);
static_assert(3 * sizeof(void *) + 2 * sizeof(u32) <= 32764);
static_assert(4 * sizeof(void *) + 2 * sizeof(u32) <= 32764);
EXTERN __global__ void ab_pr_gkr_build_eq_group_tables_kernel(const pr *claim_point, const unsigned challenge_offset, const unsigned challenge_count,
                                                              pr *eq_group_tables) {
  gkr_build_eq_group_tables_from_point(claim_point, challenge_offset, challenge_count, eq_group_tables);
}

EXTERN __global__ void ab_pr_gkr_build_eq_high_low_from_point_kernel(const pr *claim_point, const unsigned challenge_offset, const unsigned challenge_count,
                                                                     pr *high_0, pr *high_1, pr *low_buffer) {
  gkr_build_eq_high_low_from_point(claim_point, challenge_offset, challenge_count, high_0, high_1, low_buffer);
}
EXTERN __global__ void ab_pr_gkr_build_eq_values_from_group_tables_kernel(const pr *eq_group_tables, const unsigned challenge_count, pr *eq_values,
                                                                          const unsigned acc_size) {
  gkr_build_eq_values_from_group_tables(eq_group_tables, challenge_count, eq_values, acc_size);
}

} // namespace airbender::gkr::proth120::support
