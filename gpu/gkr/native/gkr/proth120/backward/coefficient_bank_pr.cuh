#pragma once

#include "../../support/kernel_helpers.cuh"
#include "primitives/proth120.cuh"

namespace airbender::gkr::proth120::backward {

using pr = ::airbender::primitives::field::proth120;

constexpr u32 PR_COEFF_PLAN_DIRECT = 0;
constexpr u32 PR_COEFF_PLAN_SCALED = 1;
constexpr u32 PR_COEFF_CHALLENGES = 9;
constexpr u8 PR_COEFF_CHALLENGE_ABSENT = 0xff;
constexpr u32 PR_COEFF_FILL_BLOCK_THREADS = 128;
constexpr u32 PR_COEFF_FILL_WARPS = PR_COEFF_FILL_BLOCK_THREADS / 32;

struct bwd_coeff_recipe_pr {
  u32 monomial_offset;
  u32 monomial_count;
  u32 kind;
  u32 scalar_index;
};

struct bwd_coeff_monomial_pr {
  u16 batch_power;
  u8 challenge_idx_0;
  u8 challenge_idx_1;
  u8 power_0;
  u8 power_1;
  u8 _pad[2];
};

struct alignas(8) bwd_coeff_fill_desc_pr {
  const bwd_coeff_recipe_pr *recipes;
  const bwd_coeff_monomial_pr *monomials;
  const pr *monomial_coeffs;
  const pr *scalars;
  const pr *challenges;
  const pr *claim_batching;
  pr *coefficients;
  u32 recipe_first;
  u32 recipe_count;
};

static_assert(sizeof(bwd_coeff_recipe_pr) == 16 && alignof(bwd_coeff_recipe_pr) == 4);
static_assert(__builtin_offsetof(bwd_coeff_recipe_pr, monomial_count) == 4);
static_assert(__builtin_offsetof(bwd_coeff_recipe_pr, kind) == 8);
static_assert(__builtin_offsetof(bwd_coeff_recipe_pr, scalar_index) == 12);
static_assert(sizeof(bwd_coeff_monomial_pr) == 8 && alignof(bwd_coeff_monomial_pr) == 2);
static_assert(__builtin_offsetof(bwd_coeff_monomial_pr, challenge_idx_0) == 2);
static_assert(__builtin_offsetof(bwd_coeff_monomial_pr, challenge_idx_1) == 3);
static_assert(__builtin_offsetof(bwd_coeff_monomial_pr, power_0) == 4);
static_assert(__builtin_offsetof(bwd_coeff_monomial_pr, power_1) == 5);
static_assert(sizeof(bwd_coeff_fill_desc_pr) == 64 && alignof(bwd_coeff_fill_desc_pr) == 8);
static_assert(__builtin_offsetof(bwd_coeff_fill_desc_pr, monomials) == 8);
static_assert(__builtin_offsetof(bwd_coeff_fill_desc_pr, monomial_coeffs) == 16);
static_assert(__builtin_offsetof(bwd_coeff_fill_desc_pr, scalars) == 24);
static_assert(__builtin_offsetof(bwd_coeff_fill_desc_pr, challenges) == 32);
static_assert(__builtin_offsetof(bwd_coeff_fill_desc_pr, claim_batching) == 40);
static_assert(__builtin_offsetof(bwd_coeff_fill_desc_pr, coefficients) == 48);
static_assert(__builtin_offsetof(bwd_coeff_fill_desc_pr, recipe_first) == 56);
static_assert(__builtin_offsetof(bwd_coeff_fill_desc_pr, recipe_count) == 60);
static_assert(sizeof(bwd_coeff_fill_desc_pr) <= 32764);

} // namespace airbender::gkr::proth120::backward
