#pragma once

// Device evaluator for compiled coefficient plans. Its Rust ABI mirror is
// `src/backward/vm/seg_coeff_eval.rs`.
#include "segmented_vm.cuh"

namespace airbender::gkr {

// Plan kinds. `Direct` is the plain recipe value; `Scaled` multiplies it by a
// base-field scalar; `LinearBasis` multiplies it by the E4 basis element its
// limb selects.
constexpr u8 BWD_SEG_COEFF_PLAN_DIRECT = 0;
constexpr u8 BWD_SEG_COEFF_PLAN_SCALED = 1;
constexpr u8 BWD_SEG_COEFF_PLAN_LINEAR_BASIS = 2;
constexpr u8 BWD_SEG_COEFF_PLAN_KINDS = 3;

// One bank slot's plan: a span of monomials in the layer's monomial table, plus
// the post-multiply its kind selects.
struct bwd_seg_coeff_recipe {
  bf scalar;
  u16 monomial_offset;
  u16 monomial_count;
  u8 kind;
  u8 limb;
  u8 _pad[2];
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

// The plan capacities: the output bank (`BWD_SEG_OUTPUT_BANK`) is a
// __constant__ symbol; these bound the compiled plan a layer may carry.
constexpr unsigned BWD_SEG_EVAL_RECIPES = 1792;
constexpr unsigned BWD_SEG_EVAL_MONOMIALS = 2304;
constexpr unsigned BWD_SEG_WINDOW_PLANS = 1728;
// Reserved literal slots the windowed arm's plan ids are biased by.
constexpr unsigned BWD_SEG_WINDOW_BANK_BIAS = 2;

// One by-value fill chunk: a contiguous bank range's recipes and exactly the
// monomials those recipes reference, rebased so `monomial_offset` indexes
// `monomials`. The whole plan rides the launch parameter space in bounded
// chunks — no host staging and no device table buffer exist. Sized for the
// 32,764-byte kernel-parameter space of the CUDA >= 12.1 ABI the sm_120
// build uses.
constexpr unsigned BWD_SEG_COEFF_CHUNK_RECIPES = 1024;
constexpr unsigned BWD_SEG_COEFF_CHUNK_MONOMIALS = 1536;

struct bwd_seg_coeff_chunk_desc {
  // First bank slot this chunk fills.
  u32 bank_first;
  // Bank slots this chunk fills == live entries in `recipes`.
  u32 bank_count;
  // Live entries in `monomials`.
  u32 monomial_count;
  u32 _pad;
  bwd_seg_coeff_recipe recipes[BWD_SEG_COEFF_CHUNK_RECIPES];
  bwd_seg_coeff_monomial monomials[BWD_SEG_COEFF_CHUNK_MONOMIALS];
};

static_assert(sizeof(bwd_seg_coeff_recipe) == 12, "bwd_seg_coeff_recipe must be 12 bytes");
static_assert(__builtin_offsetof(bwd_seg_coeff_recipe, monomial_offset) == 4, "recipe monomial_offset ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_coeff_recipe, kind) == 8, "recipe kind ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_coeff_recipe, limb) == 9, "recipe limb ABI offset drift");
static_assert(sizeof(bwd_seg_coeff_monomial) == 12, "bwd_seg_coeff_monomial must be 12 bytes");
static_assert(__builtin_offsetof(bwd_seg_coeff_monomial, batch_power) == 4, "monomial batch_power ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_coeff_monomial, challenge_idx_0) == 6, "monomial challenge_idx_0 ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_coeff_monomial, power_0) == 8, "monomial power_0 ABI offset drift");

// Every filled bank slot needs a plan entry, and every plan id must be nameable
// by the thirteen coefficient bits of the lean header.
static_assert(BWD_SEG_EVAL_RECIPES >= BWD_SEG_OUTPUT_BANK, "the plan table must cover every output bank slot");
static_assert(BWD_SEG_WINDOW_PLANS + BWD_SEG_WINDOW_BANK_BIAS <= BWD_SEG_OUTPUT_BANK, "window plans exceed the output bank");
// An offset into a chunk's monomial array must be addressable by the plan
// header's `u16`.
static_assert(BWD_SEG_COEFF_CHUNK_MONOMIALS <= 0xffffu, "the chunk monomial cap must stay inside the plan header's u16 offset");

static_assert(__builtin_offsetof(bwd_seg_coeff_chunk_desc, recipes) == 16, "chunk recipes ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_coeff_chunk_desc, monomials) == 16 + BWD_SEG_COEFF_CHUNK_RECIPES * sizeof(bwd_seg_coeff_recipe),
              "chunk monomials ABI offset drift");
static_assert(sizeof(bwd_seg_coeff_chunk_desc) ==
                  16 + BWD_SEG_COEFF_CHUNK_RECIPES * sizeof(bwd_seg_coeff_recipe) + BWD_SEG_COEFF_CHUNK_MONOMIALS * sizeof(bwd_seg_coeff_monomial),
              "bwd_seg_coeff_chunk_desc ABI size drift");
// The whole chunk plus the two device pointers must fit the 32,764-byte
// kernel-parameter space (CUDA >= 12.1 ABI; the build targets sm_120).
static_assert(sizeof(bwd_seg_coeff_chunk_desc) + 2 * sizeof(void *) <= 32764, "the coefficient chunk must stay inside the by-value kernel-argument space");

// Evaluate one bank slot of one chunk.
//
// `pow` is square-and-multiply over Montgomery products, each reduced to the
// canonical representative, so the value is bit-identical to the host oracle's
// repeated multiplication of the individual challenge factors
// (`NormalizedCoefficientRecipe::evaluate`) even though neither the factor order
// nor the exponentiation shape matches.
DEVICE_FORCEINLINE e4 bwd_seg_eval_coefficient(const bwd_seg_coeff_chunk_desc &desc, const unsigned slot, const e4 *challenges) {
  const bwd_seg_coeff_recipe recipe = desc.recipes[slot];
  const bwd_seg_coeff_monomial *monomials = desc.monomials + recipe.monomial_offset;
  const e4 batch_base = challenges[BWD_SEG_CHALLENGE_CLAIM_BATCHING];
  e4 acc = e4::ZERO();
  for (unsigned i = 0; i < recipe.monomial_count; i++) {
    const bwd_seg_coeff_monomial mon = monomials[i];
    e4 term = e4::from_scalar(mon.coeff);
    if (mon.batch_power != 0)
      term = e4::mul(term, e4::pow(batch_base, mon.batch_power));
    if (mon.challenge_idx_0 != BWD_SEG_CHALLENGE_ABSENT)
      term = e4::mul(term, e4::pow(challenges[mon.challenge_idx_0], mon.power_0));
    if (mon.challenge_idx_1 != BWD_SEG_CHALLENGE_ABSENT)
      term = e4::mul(term, e4::pow(challenges[mon.challenge_idx_1], mon.power_1));
    acc = e4::add(acc, term);
  }
  if (recipe.kind == BWD_SEG_COEFF_PLAN_SCALED)
    return e4::mul(acc, recipe.scalar);
  if (recipe.kind == BWD_SEG_COEFF_PLAN_LINEAR_BASIS) {
    bf basis[4] = {bf::ZERO(), bf::ZERO(), bf::ZERO(), bf::ZERO()};
    basis[recipe.limb] = bf::ONE();
    return e4::mul(acc, e4(basis));
  }
  return acc;
}

} // namespace airbender::gkr
