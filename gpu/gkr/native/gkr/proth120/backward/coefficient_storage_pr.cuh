#pragma once
#include "primitives/proth120.cuh"
namespace airbender::gkr::proth120::backward {
using pr = ::airbender::primitives::field::proth120;
// R0 and continuation have disjoint ranges. Layers reuse them on exec_stream:
// each fill is enqueued after the preceding layer's last constant-bank reader.
constexpr u32 PR_COEFF_BANK_STRIDE = 278 + 17;
constexpr u32 PR_COEFF_BANK_CAPACITY = 2 * PR_COEFF_BANK_STRIDE;
static_assert(PR_COEFF_BANK_CAPACITY * sizeof(pr) == 9440);
} // namespace airbender::gkr::proth120::backward
EXTERN __device__ __constant__ ::airbender::primitives::field::proth120 ab_pr_gkr_bwd_coeff_bank[::airbender::gkr::proth120::backward::PR_COEFF_BANK_CAPACITY];
namespace airbender::gkr::proth120::backward {
DEVICE_FORCEINLINE pr coefficient_from_bank(const u32 offset, const u32 index) { return ::ab_pr_gkr_bwd_coeff_bank[offset + index]; }
} // namespace airbender::gkr::proth120::backward
