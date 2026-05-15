#pragma once

#include "../support/descriptors.cuh"

namespace airbender::prover::gkr {

// Device-side recipe format for GPU coefficient evaluation.
// Compiled from CoefficientRecipe at prepare time, uploaded once per circuit/layer.

struct gpu_recipe_header {
  u16 batch_power;
  u8 group_count_0;
  u8 group_count_1;
  u16 terms_offset;
  u16 immediate_idx;
};

struct gpu_prefactor_term {
  bf coeff;
  u8 source; // 0=lookup_mul, 1=lookup_add
  u8 power;
  u16 _pad;
};

struct immediate_factor_recipe_header {
  u16 monomial_offset;
  u8 monomial_count;
  u8 _pad;
};

struct immediate_factor_monomial {
  bf coeff;
  u8 challenge_idx_0;
  u8 challenge_idx_1;
  u8 power_0;
  u8 power_1;
};

constexpr unsigned FLAT_RECIPE_MAX_HEADERS = 2816;
constexpr unsigned FLAT_RECIPE_MAX_TERMS = 640;
constexpr unsigned FLAT_IMMEDIATE_MAX_RECIPES = 128;
constexpr unsigned FLAT_IMMEDIATE_MAX_MONOMIALS = 384;
constexpr u8 IMMEDIATE_FACTOR_ABSENT = 0xff;

struct gpu_flat_recipe_eval_desc {
  gpu_recipe_header headers[FLAT_RECIPE_MAX_HEADERS];
  gpu_prefactor_term terms[FLAT_RECIPE_MAX_TERMS];
  immediate_factor_recipe_header immediate_recipes[FLAT_IMMEDIATE_MAX_RECIPES];
  immediate_factor_monomial immediate_monomials[FLAT_IMMEDIATE_MAX_MONOMIALS];
};

static_assert(sizeof(gpu_recipe_header) == 8, "gpu_recipe_header must be 8 bytes");
static_assert(sizeof(gpu_prefactor_term) == 8, "gpu_prefactor_term must be 8 bytes");
static_assert(sizeof(immediate_factor_recipe_header) == 4, "immediate_factor_recipe_header must be 4 bytes");
static_assert(sizeof(immediate_factor_monomial) == 8, "immediate_factor_monomial must be 8 bytes");
static_assert(sizeof(gpu_flat_recipe_eval_desc) <= 32u * 1024u, "gpu_flat_recipe_eval_desc must fit under the 32 KB inline kernel-arg ceiling");

DEVICE_FORCEINLINE e4 eval_immediate_factor(const immediate_factor_recipe_header &recipe, const immediate_factor_monomial *all_monomials,
                                            const e4 *ext_challenges) {
  e4 acc = e4::ZERO();
  for (unsigned i = 0; i < recipe.monomial_count; i++) {
    const immediate_factor_monomial &mon = all_monomials[recipe.monomial_offset + i];
    e4 term = e4::from_scalar(mon.coeff);
    if (mon.challenge_idx_0 != IMMEDIATE_FACTOR_ABSENT) {
      term = e4::mul(term, e4::pow(ext_challenges[mon.challenge_idx_0], mon.power_0));
    }
    if (mon.challenge_idx_1 != IMMEDIATE_FACTOR_ABSENT) {
      term = e4::mul(term, e4::pow(ext_challenges[mon.challenge_idx_1], mon.power_1));
    }
    acc = e4::add(acc, term);
  }
  return acc;
}

DEVICE_FORCEINLINE e4 eval_single_recipe(const gpu_recipe_header &recipe, const gpu_flat_recipe_eval_desc &desc, const e4 &batch_base, const e4 &lookup_mul,
                                         const e4 &lookup_add, const e4 *ext_challenges) {
  e4 c = e4::pow(batch_base, recipe.batch_power);
  const e4 immediate = eval_immediate_factor(desc.immediate_recipes[recipe.immediate_idx], desc.immediate_monomials, ext_challenges);
  c = e4::mul(c, immediate);

  unsigned offset = recipe.terms_offset;
  const unsigned group_counts[2] = {recipe.group_count_0, recipe.group_count_1};
  for (unsigned g = 0; g < 2; g++) {
    const unsigned count = group_counts[g];
    if (count == 0)
      continue;
    e4 group_sum = e4::ZERO();
    for (unsigned t = 0; t < count; t++) {
      const gpu_prefactor_term &term = desc.terms[offset + t];
      e4 challenge;
      switch (term.source) {
      case 0:
        challenge = lookup_mul;
        break;
      case 1:
        challenge = lookup_add;
        break;
      default:
        challenge = e4::ZERO();
        break;
      }
      const e4 val = e4::pow(challenge, term.power);
      group_sum = e4::fma(val, term.coeff, group_sum);
    }
    offset += count;
    c = e4::mul(c, group_sum);
  }

  return c;
}

} // namespace airbender::prover::gkr
