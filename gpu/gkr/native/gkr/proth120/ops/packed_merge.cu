#include "ops/gkr_ops_shared.cuh"
#include "primitives/proth120/field.cuh"
namespace airbender::gkr::proth120::ops {
using namespace ::airbender::primitives;
using pr = field::proth120;
struct merge_arguments {
  const pr *claims;
  u32 count;
  const pr *extra;
  u32 pack_log2;
  pr *merged;
};
static_assert(sizeof(merge_arguments) == 40);
static_assert(offsetof(merge_arguments, extra) == 16);
static_assert(offsetof(merge_arguments, merged) == 32);
EXTERN __global__ void ab_pr_gkr_merge_claims_kernel(const pr *claims, u32 count, const pr *extra, u32 pack_log2, pr *merged) {
  if (pack_log2 < 1 || pack_log2 > 4)
    __trap();
  ::airbender::gkr::ops::shared::merge_claims(claims, count, extra, pack_log2, merged);
}
} // namespace airbender::gkr::proth120::ops
