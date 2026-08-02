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
//
// Like the flat one, and like this lineage's own executor descriptor, the tables
// ride the kernel's parameter space BY VALUE (see `bwd_seg_coeff_eval_desc`).

// The seg lineage's own header: `BWD_SEG_CONST_BANK` is the bank this evaluator
// fills, so the recipe array's size has one definition rather than two. No cycle —
// `segmented_vm.cuh` does not know this file exists.
#include "segmented_vm.cuh"

namespace airbender::prover::gkr {

// One bank slot's recipe: a span of monomials in the layer's monomial table.
//
// `u16` for both, which the INLINE descriptor below makes exact rather than
// merely sufficient: the monomial array is capped at
// `BWD_SEG_COEFF_MAX_MONOMIALS`, so an offset into it and a count within it both
// fit a `u16` by construction. (`immediate_factor_recipe_header` gets away with a
// `u8` count; this one cannot — a grouped Ext core coefficient is a POLYNOMIAL in
// the batching challenge and blake2 L0's widest holds **297** monomials.)
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

// The monomial table's inline capacity.
//
// Chosen against the by-value kernel-argument budget, not against the census: with
// the recipe array fixed at the constant bank's size, this is the largest round
// number the 32,764-byte parameter cap admits. The corpus's widest coordinate needs
// 1,662 (blake2 L0 Ext), so it carries 38% headroom — `seg_coeff_eval_covers_the_
// corpus` reports the realized maximum against it.
constexpr unsigned BWD_SEG_COEFF_MAX_MONOMIALS = 2304;

// The whole evaluator input, BY VALUE.
//
// The tables are a pure function of the compiled layer, so they are known at
// SCHEDULING time — which is the same standing `bwd_seg_desc` has, and it rides the
// parameter space for the same reason: no device allocation to own, no H2D to
// order, and no pinned-host staging obligation. Only the CHALLENGES are round-state
// and device-derived, so they stay a pointer.
//
// Sized for the CONSTANT bank. A `ptr`-loader bank may legally exceed
// `BWD_SEG_CONST_BANK`, and such a layer would need the device-pointer companion the
// flat lineage carries (`gpu_flat_recipe_eval_desc_devptr`); the host builder
// rejects it rather than truncating, and no corpus coordinate comes close (913 of
// 1,152 at the widest).
struct bwd_seg_coeff_eval_desc {
  bwd_seg_coeff_recipe recipes[BWD_SEG_CONST_BANK];
  bwd_seg_coeff_monomial monomials[BWD_SEG_COEFF_MAX_MONOMIALS];
  // Bank slots to fill, reserved literals included. Entries at and past it are
  // zero-filled and never read.
  u32 num_coefficients;
  u32 _pad;
};

static_assert(sizeof(bwd_seg_coeff_recipe) == 4, "bwd_seg_coeff_recipe must be 4 bytes");
static_assert(sizeof(bwd_seg_coeff_monomial) == 12, "bwd_seg_coeff_monomial must be 12 bytes");
static_assert(__builtin_offsetof(bwd_seg_coeff_monomial, batch_power) == 4, "monomial batch_power ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_coeff_monomial, challenge_idx_0) == 6, "monomial challenge_idx_0 ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_coeff_monomial, power_0) == 8, "monomial power_0 ABI offset drift");
static_assert(sizeof(bwd_seg_coeff_eval_desc) == 32264, "bwd_seg_coeff_eval_desc ABI size drift");
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

} // namespace airbender::prover::gkr
