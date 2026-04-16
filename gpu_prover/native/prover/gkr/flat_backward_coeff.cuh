#pragma once

#include "common.cuh"

namespace airbender::prover::gkr {

// Device-side recipe format for GPU coefficient evaluation.
// Compiled from CoefficientRecipe at prepare time, uploaded once per circuit/layer.

struct gpu_recipe_header {
  u32 batch_power;
  e4 immediate_factor; // pre-negated if recipe.negate
  u16 num_groups;      // 0, 1, or 2
  u16 group_counts[2]; // terms per prefactor group
  u32 terms_offset;    // start index into flat terms array
};

struct gpu_prefactor_term {
  bf coeff;
  u32 source; // 0=lookup_mul, 1=lookup_add, 2=constraint_batch
  u32 power;
};

DEVICE_FORCEINLINE e4 eval_single_recipe(const gpu_recipe_header &recipe, const gpu_prefactor_term *all_terms, const e4 &batch_base, const e4 &lookup_mul,
                                         const e4 &lookup_add, const e4 &constraint_batch) {
  e4 c = e4::pow(batch_base, recipe.batch_power);
  c = e4::mul(c, recipe.immediate_factor);

  unsigned offset = recipe.terms_offset;
  for (unsigned g = 0; g < recipe.num_groups; g++) {
    e4 group_sum = e4::ZERO();
    const unsigned count = recipe.group_counts[g];
    for (unsigned t = 0; t < count; t++) {
      const gpu_prefactor_term &term = all_terms[offset + t];
      e4 challenge;
      switch (term.source) {
      case 0:
        challenge = lookup_mul;
        break;
      case 1:
        challenge = lookup_add;
        break;
      default:
        challenge = constraint_batch;
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
