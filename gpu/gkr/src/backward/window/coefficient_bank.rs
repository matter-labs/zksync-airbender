//! Device evaluation of backward window coefficient recipes.
//!
//! Claim-batching powers are stored per monomial. Powers on challenge kinds
//! whose resolver ignores powers are rejected as ambiguous.
use std::collections::BTreeMap;

use gpu_gkr_compiler::{CoeffProduct, NormalizedCoefficientRecipe};

use crate::upstream::{
    ChallengeKey, ChallengePower, ChallengeRef, PermutationSlot, PrimeField,
    NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES,
};

// ── The challenge slab ───────────────────────────────────────────────────────

pub(crate) const BWD_COEFF_CHALLENGE_PERM_LINEARIZATION_BASE: u8 = 0;
pub(crate) const BWD_COEFF_CHALLENGE_PERM_ADDITIVE: u8 =
    NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES as u8;
/// The lookup argument's multiplicative challenge (`alpha`).
pub(crate) const BWD_COEFF_CHALLENGE_LOOKUP_MULTIPLICATIVE: u8 = 7;
/// The lookup argument's additive challenge (`gamma`).
pub(crate) const BWD_COEFF_CHALLENGE_LOOKUP_ADDITIVE: u8 = 8;
/// The per-layer claim-batching challenge (`beta`).
///
/// Monomials carry its exponent in [`BankMonomial::batch_power`].
pub(crate) const BWD_COEFF_CHALLENGE_CLAIM_BATCHING: u8 = 9;

/// Slab length: every challenge kind a lean coefficient recipe can name.
pub(crate) const BWD_COEFF_CHALLENGE_SLOTS: usize = BWD_COEFF_CHALLENGE_CLAIM_BATCHING as usize + 1;

/// A monomial factor that is not present.
pub(crate) const BWD_COEFF_CHALLENGE_ABSENT: u8 = 0xff;

const _: () = {
    // The prefix claim in this module's docs, and the reason a production caller can
    // stage `ExternalChallengesTransfer`'s buffer as slots `0..=6` verbatim: the
    // additive part sits directly above the linearization block, and the four
    // backward challenges start above it.
    assert!(BWD_COEFF_CHALLENGE_PERM_LINEARIZATION_BASE == 0);
    assert!(BWD_COEFF_CHALLENGE_PERM_ADDITIVE == 6);
    assert!(BWD_COEFF_CHALLENGE_LOOKUP_MULTIPLICATIVE == BWD_COEFF_CHALLENGE_PERM_ADDITIVE + 1);
    // Every live slot must be addressable, and none may collide with the absent
    // sentinel.
    assert!(BWD_COEFF_CHALLENGE_SLOTS < BWD_COEFF_CHALLENGE_ABSENT as usize);
};

/// The slab slot and exponent one challenge reference resolves to.
///
/// The exponent is the reference's own power; a product's MULTIPLICITY is folded in
/// separately by [`translate_recipe_inner`].
pub(crate) fn coefficient_bank_challenge_slot(
    r: &ChallengeRef,
) -> Result<(u8, u32), CoefficientBankError> {
    let power = match r.power {
        ChallengePower::One => 1u32,
        ChallengePower::Static(p) => p,
    };
    let (slot, honours_power) = match &r.key {
        ChallengeKey::PermutationLinearization(slot) => (
            BWD_COEFF_CHALLENGE_PERM_LINEARIZATION_BASE + perm_slot_index(slot),
            false,
        ),
        ChallengeKey::PermutationAdditive => (BWD_COEFF_CHALLENGE_PERM_ADDITIVE, false),
        ChallengeKey::LookupMultiplicative => (BWD_COEFF_CHALLENGE_LOOKUP_MULTIPLICATIVE, true),
        ChallengeKey::LookupAdditive => (BWD_COEFF_CHALLENGE_LOOKUP_ADDITIVE, false),
        ChallengeKey::ClaimBatching => (BWD_COEFF_CHALLENGE_CLAIM_BATCHING, true),
    };
    // A power on a power-ignoring key is the one spelling this module refuses to
    // guess at (see the module docs).
    if !honours_power && power != 1 {
        return Err(CoefficientBankError::AmbiguousPower {
            key: format!("{:?}", r.key),
            power,
        });
    }
    Ok((slot, power))
}

/// `PermutationSlot` to its linearization-challenge index, the same mapping `cs`'s
/// `PERMUTATION_ARGUMENT_CHALLENGE_POWERS_*_IDX` constants fix and the forward VM's
/// resolver uses.
fn perm_slot_index(slot: &PermutationSlot) -> u8 {
    match slot {
        PermutationSlot::AddressLow => 0,
        PermutationSlot::AddressHigh => 1,
        PermutationSlot::TimestampLow => 2,
        PermutationSlot::TimestampHigh => 3,
        PermutationSlot::ValueLow => 4,
        PermutationSlot::ValueHigh => 5,
    }
}

// ── The device format ────────────────────────────────────────────────────────

/// Plan kind: the bank slot holds the recipe's own value.
pub(crate) const BWD_COEFF_PLAN_DIRECT: u8 = 0;
/// Plan kind: the recipe's value times [`BankRecipe::scalar`].
pub(crate) const BWD_COEFF_PLAN_SCALED: u8 = 1;
/// Plan kind: the recipe's value times the E4 basis element
/// [`BankRecipe::limb`] selects.
pub(crate) const BWD_COEFF_PLAN_LINEAR_BASIS: u8 = 2;
/// Basis elements a `LinearBasis` plan may name.
pub(crate) const BWD_COEFF_PLAN_LIMBS: usize = 4;

// ── Errors ───────────────────────────────────────────────────────────────────

/// Why a recipe (or a bank of them) does not fit the device evaluator's format.
///
/// Every variant rejects setup.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum CoefficientBankError {
    /// A product multiplies more non-batching challenges than the format holds.
    TooManyDistinctChallenges {
        recipe: usize,
        product: usize,
        distinct: usize,
    },
    /// A slot's accumulated exponent (reference power times multiplicity) overflows
    /// the monomial's `u8` power. The batching challenge is exempt — it has its own
    /// `u16` field — so this is some OTHER challenge raised past 255.
    ExponentOverflow {
        recipe: usize,
        product: usize,
        slot: u8,
        exponent: u32,
    },
    /// The batching exponent overflows the monomial's `u16`. Unreachable at any
    /// plausible root count — the power IS the batching-order root index — but it is
    /// the field's real limit.
    BatchPowerOverflow {
        recipe: usize,
        product: usize,
        power: u32,
    },
    /// `Static(p >= 2)` on a key whose resolvers disagree about whether `power` is an
    /// exponent at all.
    AmbiguousPower { key: String, power: u32 },
    MissingTopBits {
        recipe: usize,
        product: usize,
        set_index: usize,
        available: usize,
    },
    /// The bank's monomials do not fit the device monomial table.
    MonomialTableOverflow { monomials: usize, cap: usize },
    /// More bank slots than the output bank holds.
    BankOverflow { coefficients: usize, cap: usize },
    /// More bank slots than the device plan table describes.
    RecipeTableOverflow { recipes: usize, cap: usize },
    /// More window plans than the plan capacity admits.
    PlanTableOverflow { plans: usize, cap: usize },
    /// A `LinearBasis` plan names a limb outside the extension's basis.
    PlanLimbOutOfRange { plan: usize, limb: u8 },
}

/// Everything except the scalar: equal products merge under this ordered key.
pub(crate) type CoefficientMonomialKey = (u16, u8, u8, u8, u8);

/// Field-neutral recipe normalization; scalar conversion is the only field policy.
/// The BabyBear caller checks its per-recipe monomial capacity itself; the Proth120 caller
/// panics on any error.
pub(crate) fn translate_coefficient_recipe<F: PrimeField>(
    recipe: &NormalizedCoefficientRecipe,
    recipe_index: usize,
    runtime_top_bits: &[u32],
    convert_scalar: impl Fn(u128) -> F,
) -> Result<impl Iterator<Item = (F, CoefficientMonomialKey)>, CoefficientBankError> {
    let mut merged: BTreeMap<CoefficientMonomialKey, F> = BTreeMap::new();
    for (product_index, product) in recipe.terms.iter().enumerate() {
        let (mut scalar, key) =
            translate_coefficient_product(product, recipe_index, product_index, &convert_scalar)?;
        for reference in &product.inits_and_teardowns_top_bits {
            let bits = runtime_top_bits.get(reference.set_index).copied().ok_or(
                CoefficientBankError::MissingTopBits {
                    recipe: recipe_index,
                    product: product_index,
                    set_index: reference.set_index,
                    available: runtime_top_bits.len(),
                },
            )?;
            let shifted = bits.checked_shl(reference.shift).unwrap_or(0);
            scalar.mul_assign(&F::from_u32_with_reduction(shifted));
        }
        merged
            .entry(key)
            .and_modify(|value| {
                value.add_assign(&scalar);
            })
            .or_insert(scalar);
    }
    Ok(merged
        .into_iter()
        .filter(|(_, scalar)| !scalar.is_zero())
        .map(|(key, scalar)| (scalar, key)))
}

fn translate_coefficient_product<F: PrimeField>(
    product: &CoeffProduct,
    recipe_index: usize,
    product_index: usize,
    convert_scalar: &impl Fn(u128) -> F,
) -> Result<(F, CoefficientMonomialKey), CoefficientBankError> {
    let mut exponents: BTreeMap<u8, u32> = BTreeMap::new();
    for challenge in &product.challenges {
        let (slot, power) = coefficient_bank_challenge_slot(&challenge.0)?;
        *exponents.entry(slot).or_default() += power;
    }
    // Zero powers are identities and do not consume either factor slot.
    exponents.retain(|_, exponent| *exponent != 0);
    let batch = exponents
        .remove(&BWD_COEFF_CHALLENGE_CLAIM_BATCHING)
        .unwrap_or(0);
    if batch > u32::from(u16::MAX) {
        return Err(CoefficientBankError::BatchPowerOverflow {
            recipe: recipe_index,
            product: product_index,
            power: batch,
        });
    }
    if exponents.len() > 2 {
        return Err(CoefficientBankError::TooManyDistinctChallenges {
            recipe: recipe_index,
            product: product_index,
            distinct: exponents.len(),
        });
    }
    // Convert the scalar before the exponent overflow checks, so a non-canonical BabyBear scalar
    // panics (`babybear_from_canonical`) before an exponent error is returned.
    let scalar = convert_scalar(product.scalar);
    let mut key = (
        batch as u16,
        BWD_COEFF_CHALLENGE_ABSENT,
        0,
        BWD_COEFF_CHALLENGE_ABSENT,
        0,
    );
    for (position, (slot, exponent)) in exponents.into_iter().enumerate() {
        if exponent > u32::from(u8::MAX) {
            return Err(CoefficientBankError::ExponentOverflow {
                recipe: recipe_index,
                product: product_index,
                slot,
                exponent,
            });
        }
        if position == 0 {
            key.1 = slot;
            key.2 = exponent as u8;
        } else {
            key.3 = slot;
            key.4 = exponent as u8;
        }
    }
    Ok((scalar, key))
}

// ── The bank's tables ────────────────────────────────────────────────────────

/// Device plan-table capacity: one entry per output bank slot the fill can
/// address.
pub(crate) const BWD_COEFF_RECIPES: usize = 1_792;

/// Interned window plans one layer may name, reserved literals excluded.
pub(crate) const BWD_WINDOW_COEFF_PLANS: usize = 1_728;

/// CUDA mirror: `BWD_COEFF_CHUNK_RECIPES`. Recipes one by-value fill
/// chunk carries.
pub(crate) const BWD_COEFF_CHUNK_RECIPES: usize = 1_024;
/// CUDA mirror: `BWD_COEFF_CHUNK_MONOMIALS`. Monomials one by-value fill
/// chunk carries.
pub(crate) const BWD_COEFF_CHUNK_MONOMIALS: usize = 1_536;
