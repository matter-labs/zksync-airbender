#pragma once

#include "../../support/kernel_helpers.cuh"
#include "coefficient_storage_pr.cuh"
#include "primitives/proth120.cuh"

namespace airbender::gkr::proth120::backward {

using pr = ::airbender::primitives::field::proth120;

constexpr u32 PR_COEFF_CHALLENGES = 9;
constexpr u8 PR_COEFF_CHALLENGE_ABSENT = 0xff;
constexpr u32 PR_COEFF_FILL_BLOCK_THREADS = 128;
constexpr u32 PR_COEFF_FILL_WARPS = PR_COEFF_FILL_BLOCK_THREADS / 32;

struct bwd_coeff_recipe_pr {
  u32 monomial_offset;
  u32 monomial_count;
};

struct bwd_coeff_monomial_pr {
  u16 batch_power;
  u8 challenge_idx_0;
  u8 challenge_idx_1;
  u8 power_0;
  u8 power_1;
  u8 _pad[2];
};

constexpr u32 PR_COEFF_CHUNK_RECIPES = 278;
constexpr u32 PR_COEFF_CHUNK_MONOMIALS = 577;
constexpr u32 PR_COEFF_CHUNK_IMMEDIATES = 17;
static_assert(PR_COEFF_BANK_STRIDE == PR_COEFF_CHUNK_RECIPES + PR_COEFF_CHUNK_IMMEDIATES);

struct alignas(16) bwd_coeff_chunk_desc_pr {
  u32 bank_first;
  u32 bank_count;
  u32 monomial_count;
  u32 immediate_count;
  bwd_coeff_recipe_pr recipes[PR_COEFF_CHUNK_RECIPES];
  bwd_coeff_monomial_pr monomials[PR_COEFF_CHUNK_MONOMIALS];
  pr monomial_coeffs[PR_COEFF_CHUNK_MONOMIALS];
  pr immediates[PR_COEFF_CHUNK_IMMEDIATES];
};

static_assert(sizeof(bwd_coeff_recipe_pr) == 8 && alignof(bwd_coeff_recipe_pr) == 4);
static_assert(__builtin_offsetof(bwd_coeff_recipe_pr, monomial_offset) == 0);
static_assert(__builtin_offsetof(bwd_coeff_recipe_pr, monomial_count) == 4);
static_assert(sizeof(bwd_coeff_monomial_pr) == 8 && alignof(bwd_coeff_monomial_pr) == 2);
static_assert(__builtin_offsetof(bwd_coeff_monomial_pr, challenge_idx_0) == 2);
static_assert(__builtin_offsetof(bwd_coeff_monomial_pr, challenge_idx_1) == 3);
static_assert(__builtin_offsetof(bwd_coeff_monomial_pr, power_0) == 4);
static_assert(__builtin_offsetof(bwd_coeff_monomial_pr, power_1) == 5);
static_assert(sizeof(bwd_coeff_chunk_desc_pr) == 16368 && alignof(bwd_coeff_chunk_desc_pr) == 16);
static_assert(__builtin_offsetof(bwd_coeff_chunk_desc_pr, recipes) == 16);
static_assert(__builtin_offsetof(bwd_coeff_chunk_desc_pr, monomials) == 2240);
static_assert(__builtin_offsetof(bwd_coeff_chunk_desc_pr, monomial_coeffs) == 6864);
static_assert(__builtin_offsetof(bwd_coeff_chunk_desc_pr, immediates) == 16096);
static_assert(sizeof(bwd_coeff_chunk_desc_pr) + 3 * sizeof(pr *) == 16392);
static_assert(sizeof(bwd_coeff_chunk_desc_pr) + 3 * sizeof(pr *) <= 32764);

} // namespace airbender::gkr::proth120::backward
