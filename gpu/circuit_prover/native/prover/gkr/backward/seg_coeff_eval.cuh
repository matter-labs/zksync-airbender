#pragma once

// The SEGMENTED lean VM's coefficient-bank evaluator: turn compiled coefficient
// RECIPES into the E4 values the executors index, on the device, from challenges
// the transcript squeezed on the device (cutover blocker 4).
//
// THIS FILE IS ONE HALF OF AN ABI. Its Rust half is
// `src/prover/gkr/backward/vm/seg_coeff_eval.rs`; the `static_assert`s below run
// under nvcc, the Rust half asserts the same sizes and offsets, and
// `seg_abi_tests` compares the mirrored literals as text. Neither half may move
// without the other in the same commit.
//
// # Why this is not `coeff.cuh`'s `immediate_factor_monomial`
//
// The flat lineage's recipe format was the first candidate, and the corpus does
// not fit it. Measured over all 114 coordinates of the twelve committed layouts
// (`seg_coeff_eval_tests::seg_coeff_eval_batching_shape_survey`):
//
//   * the claim-batching exponent reaches **694** — it IS the alpha spine's root
//     index (`root_0 + sum beta^i * root_i`), so it grows with the layer's root
//     count and overflows an `u8` power field;
//   * `gpu_recipe_header::batch_power` is per-RECIPE, so it can only carry the
//     power COMMON to every product. 4,094 of 11,878 products keep a residual
//     after that lift, up to 343; and
//   * a product carrying such a residual can ALSO name two other distinct
//     challenges, so the two-factor monomial is one factor short even with the
//     header's help.
//
// The fix is one field in one place: the batching power becomes PER-MONOMIAL and
// `u16`, which is exactly the quantity that did not fit. Everything else is the
// flat format's shape, so the two evaluators stay readable side by side.
//
// Widening `immediate_factor_monomial` itself was the alternative and was
// rejected: it is 8 bytes today, `gpu_flat_recipe_eval_desc` is 31,232 of its
// 32,768-byte inline ceiling, and 384 monomials times 4 more bytes lands exactly
// on the limit — no headroom, for a lineage that does not need the field.

#include "../support/descriptors.cuh"

namespace airbender::prover::gkr {

// One bank slot's recipe: a span of monomials in the layer's monomial table.
//
// Both fields are `u32`, where `immediate_factor_recipe_header` gets away with a
// `u16` offset and a `u8` count. That is the same measurement talking: a grouped
// Ext core coefficient is a POLYNOMIAL in the batching challenge — blake2 L0's
// widest is **297 monomials**, past a `u8` — and a bank of those runs the table
// past `u16` as well.
struct bwd_seg_coeff_recipe {
  u32 monomial_offset;
  u32 monomial_count;
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
// the incumbent's `ExternalChallengesTransfer` buffer verbatim (six permutation
// linearization challenges then the additive part), so a caller stages that as
// this slab's prefix.
constexpr u8 BWD_SEG_CHALLENGE_PERM_LINEARIZATION_BASE = 0;
constexpr u8 BWD_SEG_CHALLENGE_PERM_ADDITIVE = 6;
constexpr u8 BWD_SEG_CHALLENGE_LOOKUP_MULTIPLICATIVE = 7;
constexpr u8 BWD_SEG_CHALLENGE_LOOKUP_ADDITIVE = 8;
constexpr u8 BWD_SEG_CHALLENGE_CONSTRAINT_AGGREGATION = 9;
constexpr u8 BWD_SEG_CHALLENGE_CLAIM_BATCHING = 10;
constexpr unsigned BWD_SEG_CHALLENGE_SLOTS = 11;
constexpr u8 BWD_SEG_CHALLENGE_ABSENT = 0xff;

static_assert(sizeof(bwd_seg_coeff_recipe) == 8, "bwd_seg_coeff_recipe must be 8 bytes");
static_assert(sizeof(bwd_seg_coeff_monomial) == 12, "bwd_seg_coeff_monomial must be 12 bytes");
static_assert(__builtin_offsetof(bwd_seg_coeff_monomial, batch_power) == 4, "monomial batch_power ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_coeff_monomial, challenge_idx_0) == 6, "monomial challenge_idx_0 ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_coeff_monomial, power_0) == 8, "monomial power_0 ABI offset drift");

// Evaluate one bank slot.
//
// `pow` is square-and-multiply over Montgomery products, each reduced to the
// canonical representative, so the value is bit-identical to the host oracle's
// repeated multiplication of the individual challenge factors
// (`NormalizedCoefficientRecipe::evaluate`) even though neither the factor order
// nor the exponentiation shape matches. `seg_coeff_eval_matches_the_host_oracle`
// is what proves that rather than assumes it.
DEVICE_FORCEINLINE e4 bwd_seg_eval_coefficient(const bwd_seg_coeff_recipe &recipe, const bwd_seg_coeff_monomial *all_monomials, const e4 *challenges) {
  const e4 batch_base = challenges[BWD_SEG_CHALLENGE_CLAIM_BATCHING];
  e4 acc = e4::ZERO();
  for (u32 i = 0; i < recipe.monomial_count; i++) {
    const bwd_seg_coeff_monomial &mon = all_monomials[recipe.monomial_offset + i];
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

} // namespace airbender::prover::gkr
