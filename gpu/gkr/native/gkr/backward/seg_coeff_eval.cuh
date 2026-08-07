#pragma once

// Device evaluator for compiled coefficient recipes. Its Rust ABI mirror is
// `src/backward/vm/seg_coeff_eval.rs`.
#include "segmented_vm.cuh"

namespace airbender::gkr {

// One bank slot's recipe: a span of monomials in the layer's monomial table.
//
struct bwd_seg_coeff_recipe {
  u16 monomial_offset;
  u16 monomial_count;
};

// `coeff * beta^batch_power * challenge[idx_0]^power_0 * challenge[idx_1]^power_1`,
// where `beta` is the claim-batching challenge and `idx_*` index the challenge
// slab. `BWD_SEG_CHALLENGE_ABSENT` in an index means the factor is not present.
//
// The batching challenge NEVER rides an index: the translation always routes it to
// `batch_power`, so the two spellings cannot disagree.
struct bwd_seg_coeff_monomial {
  bf coeff;
  u16 batch_power;
  u8 challenge_idx_0;
  u8 challenge_idx_1;
  u8 power_0;
  u8 power_1;
  u8 _pad[2];
};

// The challenge slab's layout, mirrored in `seg_coeff_eval.rs`. Slots 0..=6 are
// six permutation linearization challenges followed by the additive part.
constexpr u8 BWD_SEG_CHALLENGE_PERM_LINEARIZATION_BASE = 0;
constexpr u8 BWD_SEG_CHALLENGE_PERM_ADDITIVE = 6;
constexpr u8 BWD_SEG_CHALLENGE_LOOKUP_MULTIPLICATIVE = 7;
constexpr u8 BWD_SEG_CHALLENGE_LOOKUP_ADDITIVE = 8;
constexpr u8 BWD_SEG_CHALLENGE_CLAIM_BATCHING = 9;
constexpr unsigned BWD_SEG_CHALLENGE_SLOTS = 10;
constexpr u8 BWD_SEG_CHALLENGE_ABSENT = 0xff;

// Maximum that fits beside the recipe array in the by-value kernel argument.
constexpr unsigned BWD_SEG_COEFF_MAX_MONOMIALS = 2304;

// The whole evaluator input, BY VALUE.
//
struct bwd_seg_coeff_eval_desc {
  bwd_seg_coeff_recipe recipes[BWD_SEG_CONST_BANK];
  bwd_seg_coeff_monomial monomials[BWD_SEG_COEFF_MAX_MONOMIALS];
  // Bank slots to fill, reserved literals included. Entries at and past it are
  // zero-filled and never read.
  u32 num_coefficients;
};

static_assert(sizeof(bwd_seg_coeff_recipe) == 4, "bwd_seg_coeff_recipe must be 4 bytes");
static_assert(sizeof(bwd_seg_coeff_monomial) == 12, "bwd_seg_coeff_monomial must be 12 bytes");
static_assert(__builtin_offsetof(bwd_seg_coeff_monomial, batch_power) == 4, "monomial batch_power ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_coeff_monomial, challenge_idx_0) == 6, "monomial challenge_idx_0 ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_coeff_monomial, power_0) == 8, "monomial power_0 ABI offset drift");
static_assert(sizeof(bwd_seg_coeff_eval_desc) == 32260, "bwd_seg_coeff_eval_desc ABI size drift");
static_assert(__builtin_offsetof(bwd_seg_coeff_eval_desc, monomials) == 4608, "desc monomials ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_coeff_eval_desc, num_coefficients) == 32256, "desc num_coefficients ABI offset drift");
// The descriptor plus the two device pointers the kernel also takes. This is the
// gate on the capacities above: the whole parameter list has to fit.
static_assert(sizeof(bwd_seg_coeff_eval_desc) + 2 * sizeof(void *) <= 32764,
              "the coefficient evaluator's parameter list must fit the by-value kernel-argument cap");

// An offset into the monomial array must be addressable by the recipe's `u16`, which
// is what makes the narrow header exact rather than a gamble on the census.
static_assert(BWD_SEG_COEFF_MAX_MONOMIALS <= 0xffffu, "the monomial cap must stay inside the recipe header's u16 offset");

// Evaluate one bank slot.
//
// `pow` is square-and-multiply over Montgomery products, each reduced to the
// canonical representative, so the value is bit-identical to the host oracle's
// repeated multiplication of the individual challenge factors
// (`NormalizedCoefficientRecipe::evaluate`) even though neither the factor order
// nor the exponentiation shape matches. `seg_coeff_eval_matches_the_host_oracle`
// is what proves that rather than assumes it.
DEVICE_FORCEINLINE e4 bwd_seg_eval_coefficient(const bwd_seg_coeff_eval_desc &desc, const unsigned slot, const e4 *challenges) {
  const bwd_seg_coeff_recipe &recipe = desc.recipes[slot];
  const e4 batch_base = challenges[BWD_SEG_CHALLENGE_CLAIM_BATCHING];
  e4 acc = e4::ZERO();
  for (unsigned i = 0; i < recipe.monomial_count; i++) {
    const bwd_seg_coeff_monomial &mon = desc.monomials[recipe.monomial_offset + i];
    e4 term = e4::from_scalar(mon.coeff);
    if (mon.batch_power != 0)
      term = e4::mul(term, e4::pow(batch_base, mon.batch_power));
    if (mon.challenge_idx_0 != BWD_SEG_CHALLENGE_ABSENT)
      term = e4::mul(term, e4::pow(challenges[mon.challenge_idx_0], mon.power_0));
    if (mon.challenge_idx_1 != BWD_SEG_CHALLENGE_ABSENT)
      term = e4::mul(term, e4::pow(challenges[mon.challenge_idx_1], mon.power_1));
    acc = e4::add(acc, term);
  }
  return acc;
}

} // namespace airbender::gkr
