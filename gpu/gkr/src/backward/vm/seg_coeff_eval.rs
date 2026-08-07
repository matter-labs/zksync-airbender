//! Device evaluation of segmented backward coefficient recipes.
//!
//! Claim-batching powers are stored per monomial. Powers on challenge kinds
//! whose resolver ignores powers are rejected as ambiguous.
use std::collections::BTreeMap;

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use gpu_gkr_compiler::{CoeffProduct, CoefficientRecipeId, NormalizedCoefficientRecipe};

use super::seg_desc::BWD_SEG_CONST_BANK;
use super::seg_lower::zeroed_box;
use crate::upstream::{
    ChallengeKey, ChallengePower, ChallengeRef, Field, FieldExtension, PermutationSlot, PrimeField,
    NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES,
};
use gpu_core::primitives::field::{BF, E4};
use gpu_core::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};

// ── The challenge slab ───────────────────────────────────────────────────────

pub(crate) const BWD_SEG_CHALLENGE_PERM_LINEARIZATION_BASE: u8 = 0;
pub(crate) const BWD_SEG_CHALLENGE_PERM_ADDITIVE: u8 =
    NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES as u8;
/// The lookup argument's multiplicative challenge (`alpha`).
pub(crate) const BWD_SEG_CHALLENGE_LOOKUP_MULTIPLICATIVE: u8 = 7;
/// The lookup argument's additive challenge (`gamma`).
pub(crate) const BWD_SEG_CHALLENGE_LOOKUP_ADDITIVE: u8 = 8;
/// The per-layer claim-batching challenge (`beta`).
///
/// Monomials carry its exponent in [`SegCoeffMonomial::batch_power`].
pub(crate) const BWD_SEG_CHALLENGE_CLAIM_BATCHING: u8 = 9;

/// Slab length: every challenge kind a lean coefficient recipe can name.
pub(crate) const BWD_SEG_CHALLENGE_SLOTS: usize = BWD_SEG_CHALLENGE_CLAIM_BATCHING as usize + 1;

/// A monomial factor that is not present.
pub(crate) const BWD_SEG_CHALLENGE_ABSENT: u8 = 0xff;

const _: () = {
    // The prefix claim in this module's docs, and the reason a production caller can
    // stage `ExternalChallengesTransfer`'s buffer as slots `0..=6` verbatim: the
    // additive part sits directly above the linearization block, and the four
    // backward challenges start above it.
    assert!(BWD_SEG_CHALLENGE_PERM_LINEARIZATION_BASE == 0);
    assert!(BWD_SEG_CHALLENGE_PERM_ADDITIVE == 6);
    assert!(BWD_SEG_CHALLENGE_LOOKUP_MULTIPLICATIVE == BWD_SEG_CHALLENGE_PERM_ADDITIVE + 1);
    // Every live slot must be addressable, and none may collide with the absent
    // sentinel.
    assert!(BWD_SEG_CHALLENGE_SLOTS < BWD_SEG_CHALLENGE_ABSENT as usize);
};

/// The slab slot and exponent one challenge reference resolves to.
///
/// The exponent is the reference's own power; a product's MULTIPLICITY is folded in
/// separately by [`translate_recipe`].
pub(crate) fn bwd_seg_challenge_slot(r: &ChallengeRef) -> Result<(u8, u32), SegCoeffEvalError> {
    let power = match r.power {
        ChallengePower::One => 1u32,
        ChallengePower::Static(p) => p,
    };
    let (slot, honours_power) = match &r.key {
        ChallengeKey::PermutationLinearization(slot) => (
            BWD_SEG_CHALLENGE_PERM_LINEARIZATION_BASE + perm_slot_index(slot),
            false,
        ),
        ChallengeKey::PermutationAdditive => (BWD_SEG_CHALLENGE_PERM_ADDITIVE, false),
        ChallengeKey::LookupMultiplicative => (BWD_SEG_CHALLENGE_LOOKUP_MULTIPLICATIVE, true),
        ChallengeKey::LookupAdditive => (BWD_SEG_CHALLENGE_LOOKUP_ADDITIVE, false),
        ChallengeKey::ClaimBatching => (BWD_SEG_CHALLENGE_CLAIM_BATCHING, true),
    };
    // A power on a power-ignoring key is the one spelling this module refuses to
    // guess at (see the module docs).
    if !honours_power && power != 1 {
        return Err(SegCoeffEvalError::AmbiguousPower {
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

/// CUDA mirror: `bwd_seg_coeff_recipe`. One bank slot's span of monomials.
///
/// Both fields fit because [`SegCoeffEvalDesc::monomials`] is capped at
/// [`BWD_SEG_COEFF_MAX_MONOMIALS`].
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct SegCoeffRecipe {
    pub monomial_offset: u16,
    pub monomial_count: u16,
}

/// CUDA mirror: `bwd_seg_coeff_monomial`.
///
/// `coeff * beta^batch_power * challenge[idx_0]^power_0 * challenge[idx_1]^power_1`.
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct SegCoeffMonomial {
    pub coeff: BF,
    pub batch_power: u16,
    pub challenge_idx_0: u8,
    pub challenge_idx_1: u8,
    pub power_0: u8,
    pub power_1: u8,
    pub _pad: [u8; 2],
}

impl Default for SegCoeffMonomial {
    fn default() -> Self {
        Self {
            coeff: BF::ZERO,
            batch_power: 0,
            challenge_idx_0: BWD_SEG_CHALLENGE_ABSENT,
            challenge_idx_1: BWD_SEG_CHALLENGE_ABSENT,
            power_0: 0,
            power_1: 0,
            _pad: [0; 2],
        }
    }
}

const _: () = {
    // The CUDA half asserts the same two sizes and the same three offsets.
    assert!(std::mem::size_of::<SegCoeffRecipe>() == 4);
    assert!(std::mem::size_of::<SegCoeffMonomial>() == 12);
    assert!(std::mem::offset_of!(SegCoeffMonomial, batch_power) == 4);
    assert!(std::mem::offset_of!(SegCoeffMonomial, challenge_idx_0) == 6);
    assert!(std::mem::offset_of!(SegCoeffMonomial, power_0) == 8);
};

impl SegCoeffMonomial {
    /// The canonicalization key: everything except the scalar. Two monomials with
    /// the same key are the same product and their scalars merge.
    fn key(&self) -> (u16, u8, u8, u8, u8) {
        (
            self.batch_power,
            self.challenge_idx_0,
            self.power_0,
            self.challenge_idx_1,
            self.power_1,
        )
    }
}

// ── Errors ───────────────────────────────────────────────────────────────────

/// Why a recipe (or a bank of them) does not fit the device evaluator's format.
///
/// Every variant is a setup rejection; there is no runtime fallback.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum SegCoeffEvalError {
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
    /// The bank's monomials do not fit the inline descriptor.
    MonomialTableOverflow { monomials: usize, cap: usize },
    /// More bank slots than the constant bank holds.
    BankOverflow { coefficients: usize, cap: usize },
}

// ── Translation ──────────────────────────────────────────────────────────────

fn translate_recipe_inner(
    recipe: &NormalizedCoefficientRecipe,
    recipe_index: usize,
    runtime_top_bits: &[u32],
) -> Result<Vec<SegCoeffMonomial>, SegCoeffEvalError> {
    let mut merged: BTreeMap<(u16, u8, u8, u8, u8), BF> = BTreeMap::new();

    for (product_index, product) in recipe.terms.iter().enumerate() {
        let monomial = translate_product(product, recipe_index, product_index)?;
        let mut scalar = BF::from_u32_with_reduction(product.scalar);
        for reference in &product.inits_and_teardowns_top_bits {
            let top_bits = runtime_top_bits.get(reference.set_index).copied().ok_or(
                SegCoeffEvalError::MissingTopBits {
                    recipe: recipe_index,
                    product: product_index,
                    set_index: reference.set_index,
                    available: runtime_top_bits.len(),
                },
            )?;
            let shifted = top_bits.checked_shl(reference.shift).unwrap_or(0);
            scalar.mul_assign(&BF::from_u32_with_reduction(shifted));
        }
        merged
            .entry(monomial.key())
            .and_modify(|value| {
                value.add_assign(&scalar);
            })
            .or_insert(scalar);
    }

    let monomials = merged
        .into_iter()
        .filter(|(_, scalar)| !scalar.is_zero())
        .map(
            |((batch_power, challenge_idx_0, power_0, challenge_idx_1, power_1), coeff)| {
                SegCoeffMonomial {
                    coeff,
                    batch_power,
                    challenge_idx_0,
                    challenge_idx_1,
                    power_0,
                    power_1,
                    _pad: [0; 2],
                }
            },
        )
        .collect::<Vec<_>>();
    if monomials.len() > BWD_SEG_COEFF_MAX_MONOMIALS {
        return Err(SegCoeffEvalError::MonomialTableOverflow {
            monomials: monomials.len(),
            cap: BWD_SEG_COEFF_MAX_MONOMIALS,
        });
    }
    Ok(monomials)
}

/// One product as one monomial: the batching exponent to its own field, the other
/// challenges to the two factor slots.
fn translate_product(
    product: &CoeffProduct,
    recipe_index: usize,
    product_index: usize,
) -> Result<SegCoeffMonomial, SegCoeffEvalError> {
    let mut exponents: BTreeMap<u8, u32> = BTreeMap::new();
    for challenge in &product.challenges {
        let (slot, power) = bwd_seg_challenge_slot(&challenge.0)?;
        *exponents.entry(slot).or_default() += power;
    }
    // A zero total exponent is the multiplicative identity, so the factor is dropped
    // rather than emitted — and, more importantly, it must not consume one of the two
    // factor slots. Only reachable through an explicit `Static(0)` spelling on a
    // power-honouring key.
    exponents.retain(|_, exponent| *exponent != 0);

    let batch = exponents
        .remove(&BWD_SEG_CHALLENGE_CLAIM_BATCHING)
        .unwrap_or(0);
    if batch > u32::from(u16::MAX) {
        return Err(SegCoeffEvalError::BatchPowerOverflow {
            recipe: recipe_index,
            product: product_index,
            power: batch,
        });
    }
    if exponents.len() > 2 {
        return Err(SegCoeffEvalError::TooManyDistinctChallenges {
            recipe: recipe_index,
            product: product_index,
            distinct: exponents.len(),
        });
    }

    let mut monomial = SegCoeffMonomial {
        coeff: BF::from_u32_with_reduction(product.scalar),
        batch_power: batch as u16,
        ..SegCoeffMonomial::default()
    };
    // Ascending slot order, so two products with the same factor multiset always
    // produce the same key and merge.
    for (position, (slot, exponent)) in exponents.into_iter().enumerate() {
        if exponent > u32::from(u8::MAX) {
            return Err(SegCoeffEvalError::ExponentOverflow {
                recipe: recipe_index,
                product: product_index,
                slot,
                exponent,
            });
        }
        if position == 0 {
            monomial.challenge_idx_0 = slot;
            monomial.power_0 = exponent as u8;
        } else {
            monomial.challenge_idx_1 = slot;
            monomial.power_1 = exponent as u8;
        }
    }
    Ok(monomial)
}

// ── The bank's tables ────────────────────────────────────────────────────────

/// The monomial table's inline capacity.
///
/// Maximum that fits beside the recipe array in the by-value kernel argument.
pub(crate) const BWD_SEG_COEFF_MAX_MONOMIALS: usize = 2_304;

/// CUDA mirror: `bwd_seg_coeff_eval_desc`. The whole evaluator input, BY VALUE.
///
/// The tables are a pure function of the compiled layer, so they are known at
/// SCHEDULING time — the same standing [`BwdSegDesc`](super::seg_desc::BwdSegDesc)
/// has, and they ride the parameter space for the same reason: no device allocation
/// to own, no H2D to order, and no pinned-host staging obligation. Only the
/// CHALLENGES are round state the transcript squeezed on the device, so only they
/// stay a pointer.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct SegCoeffEvalDesc {
    /// One per bank slot, in bank order. Entries at and past
    /// [`Self::num_coefficients`] are zero-filled and never read.
    pub recipes: [SegCoeffRecipe; BWD_SEG_CONST_BANK],
    pub monomials: [SegCoeffMonomial; BWD_SEG_COEFF_MAX_MONOMIALS],
    /// Bank slots to fill, reserved literals included.
    pub num_coefficients: u32,
}

const _: () = {
    // The CUDA half asserts the same size and the same two offsets, and the same
    // parameter-list bound — which is what makes the capacities above a gate rather
    // than a hope.
    assert!(std::mem::size_of::<SegCoeffEvalDesc>() == 32_260);
    assert!(std::mem::offset_of!(SegCoeffEvalDesc, monomials) == 4_608);
    assert!(std::mem::offset_of!(SegCoeffEvalDesc, num_coefficients) == 32_256);
    assert!(
        std::mem::size_of::<SegCoeffEvalDesc>() + 2 * std::mem::size_of::<*const E4>() <= 32_764
    );
    assert!(BWD_SEG_COEFF_MAX_MONOMIALS <= u16::MAX as usize);
};

/// Boxed: the descriptor is 32 KiB and a by-value local would put it on the stack.
pub(crate) struct SegCoeffEvalTables {
    pub desc: Box<SegCoeffEvalDesc>,
}

/// Translate a lean layer's coefficient bank into the device evaluator's descriptor.
///
/// Reserved literals precede the compiled recipes in the device bank.
pub(crate) fn build_seg_coeff_eval_tables_with_top_bits(
    recipes: &[NormalizedCoefficientRecipe],
    runtime_top_bits: &[u32],
) -> Result<SegCoeffEvalTables, SegCoeffEvalError> {
    build_seg_coeff_eval_tables_inner(recipes, runtime_top_bits)
}

fn build_seg_coeff_eval_tables_inner(
    recipes: &[NormalizedCoefficientRecipe],
    runtime_top_bits: &[u32],
) -> Result<SegCoeffEvalTables, SegCoeffEvalError> {
    let slots = CoefficientRecipeId::RESERVED as usize + recipes.len();
    if slots > BWD_SEG_CONST_BANK {
        return Err(SegCoeffEvalError::BankOverflow {
            coefficients: slots,
            cap: BWD_SEG_CONST_BANK,
        });
    }
    // SAFETY: every field is a `Copy` POD of integers and base-field limbs, for which
    // the all-zero bit pattern is a valid value — an empty recipe span and a zero
    // coefficient. The same helper and the same reasoning `lower_bwd_seg` uses for
    // the executor descriptor.
    let mut desc: Box<SegCoeffEvalDesc> = unsafe { zeroed_box() };
    let mut filled = 0usize;

    let push = |translated: &[SegCoeffMonomial],
                desc: &mut SegCoeffEvalDesc,
                filled: &mut usize,
                slot: usize|
     -> Result<(), SegCoeffEvalError> {
        let end = *filled + translated.len();
        if end > BWD_SEG_COEFF_MAX_MONOMIALS {
            return Err(SegCoeffEvalError::MonomialTableOverflow {
                monomials: end,
                cap: BWD_SEG_COEFF_MAX_MONOMIALS,
            });
        }
        desc.recipes[slot] = SegCoeffRecipe {
            monomial_offset: *filled as u16,
            monomial_count: translated.len() as u16,
        };
        desc.monomials[*filled..end].copy_from_slice(translated);
        *filled = end;
        Ok(())
    };

    // The reserved literals are ordinary constant recipes to the device evaluator,
    // which is why one launch fills the whole payload and the caller stages nothing
    // by hand.
    for (slot, literal) in [CoefficientRecipeId::ONE, CoefficientRecipeId::NEG_ONE]
        .into_iter()
        .enumerate()
    {
        let value = literal.literal().expect("a reserved literal id");
        push(&[literal_monomial(value)], &mut desc, &mut filled, slot)?;
    }

    for (recipe_index, recipe) in recipes.iter().enumerate() {
        let translated = translate_recipe_inner(recipe, recipe_index, runtime_top_bits)?;
        let slot = CoefficientRecipeId::RESERVED as usize + recipe_index;
        push(&translated, &mut desc, &mut filled, slot)?;
    }

    // The one invariant the format's two spellings of `beta` could break.
    debug_assert!(
        desc.monomials[..filled].iter().all(|monomial| {
            monomial.challenge_idx_0 != BWD_SEG_CHALLENGE_CLAIM_BATCHING
                && monomial.challenge_idx_1 != BWD_SEG_CHALLENGE_CLAIM_BATCHING
        }),
        "the batching challenge must ride `batch_power`, never a factor slot"
    );

    desc.num_coefficients = slots as u32;
    Ok(SegCoeffEvalTables { desc })
}

#[cfg(test)]
fn build_seg_coeff_eval_tables(
    recipes: &[NormalizedCoefficientRecipe],
) -> Result<SegCoeffEvalTables, SegCoeffEvalError> {
    build_seg_coeff_eval_tables_inner(recipes, &[])
}

#[cfg(test)]
impl SegCoeffEvalTables {
    fn monomials_of(&self, index: usize) -> &[SegCoeffMonomial] {
        let recipe = self.desc.recipes[index];
        let start = usize::from(recipe.monomial_offset);
        &self.desc.monomials[start..start + usize::from(recipe.monomial_count)]
    }
}

/// A challenge-free monomial holding one field value.
fn literal_monomial(value: E4) -> SegCoeffMonomial {
    // The reserved literals are `±1`: base-field values in an E4 shell, so a
    // coefficient-only monomial holds them exactly. Derived from the id's own
    // `literal()` rather than restated as `±BF::ONE` so the two cannot drift; the
    // assert is what makes the derivation safe, since a non-base literal would leave
    // a tail no monomial can carry.
    let coeffs = <E4 as FieldExtension<BF>>::into_coeffs(value);
    let limbs: &[BF] = coeffs.as_ref();
    assert!(
        limbs[1..].iter().all(|limb| limb.is_zero()),
        "a reserved coefficient literal must be a base-field value"
    );
    SegCoeffMonomial {
        coeff: limbs[0],
        ..SegCoeffMonomial::default()
    }
}

// ── The device fill ──────────────────────────────────────────────────────────

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GkrBwdSegEvalCoefficients,
    desc: SegCoeffEvalDesc,
    challenges: *const E4,
    coefficients: *mut E4,
);
cuda_kernel_declaration!(
    pub(crate) ab_gkr_bwd_seg_eval_coefficients_kernel(
        desc: SegCoeffEvalDesc,
        challenges: *const E4,
        coefficients: *mut E4,
    )
);

/// Fill a coefficient bank from the round's challenges, on `stream`.
///
/// `slab` is a device pointer to [`BWD_SEG_CHALLENGE_SLOTS`] E4 values in slot order;
/// `bank` is the constant-bank symbol returned by
/// `super::seg::bwd_seg_coeff_bank_device_ptr()`.
///
/// Stages nothing and allocates nothing: the tables ride the parameter space, so this
/// adds no obligation to the GPU scheduling contract beyond the ordering below.
///
/// Enqueue after challenge writes and before the round's segment launches. All
/// segment reads must finish before the next round overwrites the bank.
pub(crate) fn schedule_bwd_seg_coeff_bank_fill(
    tables: &SegCoeffEvalTables,
    slab: *const E4,
    bank: *mut E4,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = tables.desc.num_coefficients;
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let function = GkrBwdSegEvalCoefficientsFunction(ab_gkr_bwd_seg_eval_coefficients_kernel);
    function.launch(
        &config,
        &GkrBwdSegEvalCoefficientsArguments::new(*tables.desc, slab, bank),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use gpu_gkr_compiler::CoeffChallenge;

    fn challenge(key: ChallengeKey, power: ChallengePower) -> CoeffChallenge {
        CoeffChallenge::new(ChallengeRef { key, power })
    }

    fn product(scalar: u32, challenges: Vec<CoeffChallenge>) -> CoeffProduct {
        CoeffProduct {
            scalar,
            challenges,
            inits_and_teardowns_top_bits: Vec::new(),
        }
    }

    fn recipe(terms: Vec<CoeffProduct>) -> NormalizedCoefficientRecipe {
        NormalizedCoefficientRecipe::from_terms(terms)
    }

    #[test]
    fn cpu_seg_coeff_eval_rejects_missing_runtime_top_bits() {
        let recipe = recipe(vec![CoeffProduct {
            scalar: 1,
            challenges: Vec::new(),
            inits_and_teardowns_top_bits: vec![gkr_eval_ir::InitsAndTeardownsTopBitsRef {
                set_index: 2,
                shift: 1,
            }],
        }]);

        assert!(
            build_seg_coeff_eval_tables_with_top_bits(&[recipe], &[7]).is_err(),
            "a missing runtime value must not be replaced with its set index"
        );
    }

    /// The monomials of bank slot `index` (reserved literals occupy 0 and 1).
    fn bank_monomials(tables: &SegCoeffEvalTables, index: usize) -> &[SegCoeffMonomial] {
        tables.monomials_of(index)
    }

    /// The slab layout the module's prefix claim rests on, spelled out once against
    /// the `cs` slot order rather than restated as literals.
    #[test]
    fn seg_challenge_slots_follow_the_incumbent_prefix() {
        for (index, slot) in [
            PermutationSlot::AddressLow,
            PermutationSlot::AddressHigh,
            PermutationSlot::TimestampLow,
            PermutationSlot::TimestampHigh,
            PermutationSlot::ValueLow,
            PermutationSlot::ValueHigh,
        ]
        .into_iter()
        .enumerate()
        {
            let reference = ChallengeRef {
                key: ChallengeKey::PermutationLinearization(slot),
                power: ChallengePower::One,
            };
            assert_eq!(
                bwd_seg_challenge_slot(&reference),
                Ok((index as u8, 1)),
                "linearization slot {index} must keep its own index"
            );
        }
        assert_eq!(
            bwd_seg_challenge_slot(&ChallengeRef {
                key: ChallengeKey::PermutationAdditive,
                power: ChallengePower::One,
            }),
            Ok((6, 1)),
            "the additive part sits directly above the linearization block"
        );
    }

    /// A power-honouring key carries its exponent into the monomial, and repeated
    /// factors accumulate — the two ways an exponent above one can arise.
    #[test]
    fn seg_coeff_eval_accumulates_exponents() {
        let alpha_cubed = challenge(
            ChallengeKey::LookupMultiplicative,
            ChallengePower::Static(3),
        );
        let gamma = challenge(ChallengeKey::LookupAdditive, ChallengePower::One);
        let tables = build_seg_coeff_eval_tables(&[recipe(vec![product(
            7,
            vec![alpha_cubed, gamma.clone(), gamma],
        )])])
        .expect("two distinct factors");
        let monomial = bank_monomials(&tables, 2)[0];
        assert_eq!(
            (
                monomial.challenge_idx_0,
                monomial.power_0,
                monomial.challenge_idx_1,
                monomial.power_1,
                monomial.batch_power
            ),
            (
                BWD_SEG_CHALLENGE_LOOKUP_MULTIPLICATIVE,
                3,
                BWD_SEG_CHALLENGE_LOOKUP_ADDITIVE,
                2,
                0
            ),
            "factors ride in ascending slot order, each with its accumulated exponent"
        );
    }

    #[test]
    fn seg_coeff_eval_carries_the_batching_power_per_monomial() {
        let tables = build_seg_coeff_eval_tables(&[recipe(vec![
            product(
                5,
                vec![
                    challenge(ChallengeKey::ClaimBatching, ChallengePower::Static(694)),
                    challenge(ChallengeKey::LookupAdditive, ChallengePower::One),
                    challenge(ChallengeKey::LookupMultiplicative, ChallengePower::One),
                ],
            ),
            product(
                3,
                vec![challenge(
                    ChallengeKey::ClaimBatching,
                    ChallengePower::Static(2),
                )],
            ),
        ])])
        .expect("the batching power never competes for a factor slot");
        let monomials = bank_monomials(&tables, 2);
        assert_eq!(monomials.len(), 2, "two products, two distinct keys");
        let powers: Vec<u16> = monomials.iter().map(|m| m.batch_power).collect();
        assert_eq!(
            powers,
            vec![2, 694],
            "each product keeps its OWN batching power — no common factoring needed"
        );
    }

    /// The format's hard limit: a third distinct non-batching challenge has nowhere
    /// to go, so it is a typed rejection rather than a dropped factor.
    #[test]
    fn seg_coeff_eval_rejects_a_three_challenge_product() {
        let error = build_seg_coeff_eval_tables(&[recipe(vec![product(
            1,
            vec![
                challenge(ChallengeKey::LookupMultiplicative, ChallengePower::One),
                challenge(ChallengeKey::LookupAdditive, ChallengePower::One),
                challenge(
                    ChallengeKey::PermutationLinearization(PermutationSlot::ValueLow),
                    ChallengePower::One,
                ),
            ],
        )])])
        .err()
        .expect("three distinct challenges do not fit one monomial");
        assert_eq!(
            error,
            SegCoeffEvalError::TooManyDistinctChallenges {
                recipe: 0,
                product: 0,
                distinct: 3,
            }
        );
    }

    /// `Static(p >= 2)` on a power-ignoring key has two readings in this repo, so the
    /// translation refuses it instead of picking one.
    #[test]
    fn seg_coeff_eval_rejects_an_ambiguous_power() {
        let error = build_seg_coeff_eval_tables(&[recipe(vec![product(
            1,
            vec![challenge(
                ChallengeKey::LookupAdditive,
                ChallengePower::Static(2),
            )],
        )])])
        .err()
        .expect("a power on a power-ignoring key is ambiguous");
        assert!(
            matches!(error, SegCoeffEvalError::AmbiguousPower { power: 2, .. }),
            "unexpected error {error:?}"
        );
        // `Static(1)` is the benign spelling `CoeffChallenge::new` folds to `One`, so
        // it stays accepted — the rejection is about exponents, not spellings.
        build_seg_coeff_eval_tables(&[recipe(vec![product(
            1,
            vec![challenge(
                ChallengeKey::LookupAdditive,
                ChallengePower::Static(1),
            )],
        )])])
        .expect("Static(1) is canonicalized to One");
    }

    /// Canonicalization: same factors merge their scalars, and a merge that cancels
    /// drops the monomial instead of encoding a zero.
    #[test]
    fn seg_coeff_eval_merges_and_cancels_like_the_model() {
        let alpha = challenge(ChallengeKey::LookupMultiplicative, ChallengePower::One);
        // `NormalizedCoefficientRecipe::from_terms` already merges same-multiset
        // products, so the interesting case for THIS layer is two products that
        // differ only in a spelling the slab collapses: `beta^2` and `beta * beta`.
        let beta_squared = vec![challenge(
            ChallengeKey::ClaimBatching,
            ChallengePower::Static(2),
        )];
        let beta_twice = {
            let beta = challenge(ChallengeKey::ClaimBatching, ChallengePower::One);
            vec![beta.clone(), beta]
        };
        let tables = build_seg_coeff_eval_tables(&[recipe(vec![
            product(4, beta_squared),
            product(6, beta_twice),
        ])])
        .expect("both spellings are one monomial");
        let monomials = bank_monomials(&tables, 2);
        assert_eq!(
            monomials.len(),
            1,
            "beta^2 and beta*beta are the same device monomial"
        );
        assert_eq!(monomials[0].batch_power, 2);
        assert_eq!(
            monomials[0].coeff,
            BF::from_u32_with_reduction(10),
            "the scalars merge"
        );

        // And the cancelling case: the same key with opposite scalars.
        let mut negative = BF::from_u32_with_reduction(4);
        negative.negate();
        let tables = build_seg_coeff_eval_tables(&[recipe(vec![
            product(4, vec![alpha.clone()]),
            product(negative.as_u32_reduced(), vec![alpha]),
        ])])
        .expect("a cancelling recipe still translates");
        assert!(
            bank_monomials(&tables, 2).is_empty(),
            "a cancelled monomial is dropped, not encoded as zero"
        );
    }

    /// The bank the device writes is reserved-INCLUSIVE, in the same order
    /// `lower_bwd_seg` materializes host-side: the wire's coefficient ids index it
    /// raw, so slots 0 and 1 must be `+1` and `-1` whatever the challenges are.
    #[test]
    fn seg_coeff_eval_leads_the_bank_with_the_reserved_literals() {
        let tables = build_seg_coeff_eval_tables(&[recipe(vec![product(
            3,
            vec![challenge(ChallengeKey::ClaimBatching, ChallengePower::One)],
        )])])
        .expect("a one-factor product fits");
        assert_eq!(
            tables.desc.num_coefficients, 3,
            "two literals plus the recipe"
        );
        for (slot, expected) in [
            (0usize, CoefficientRecipeId::ONE),
            (1, CoefficientRecipeId::NEG_ONE),
        ] {
            let monomials = bank_monomials(&tables, slot);
            assert_eq!(monomials.len(), 1, "a literal is one constant monomial");
            assert_eq!(
                (
                    monomials[0].challenge_idx_0,
                    monomials[0].challenge_idx_1,
                    monomials[0].batch_power
                ),
                (BWD_SEG_CHALLENGE_ABSENT, BWD_SEG_CHALLENGE_ABSENT, 0),
                "a literal has no factors at all"
            );
            assert_eq!(
                <E4 as FieldExtension<BF>>::from_base(monomials[0].coeff),
                expected.literal().expect("a reserved literal"),
                "bank slot {slot} must hold the reserved literal's own value"
            );
        }
    }

    #[test]
    fn seg_coeff_eval_rejects_a_bank_past_the_inline_arrays() {
        let scalar = |v: u32| recipe(vec![product(v, Vec::new())]);
        let over_bank: Vec<NormalizedCoefficientRecipe> =
            (1..=BWD_SEG_CONST_BANK as u32 + 1).map(scalar).collect();
        assert!(
            matches!(
                build_seg_coeff_eval_tables(&over_bank),
                Err(SegCoeffEvalError::BankOverflow { cap, .. }) if cap == BWD_SEG_CONST_BANK
            ),
            "a bank past the constant bank must be refused, not truncated"
        );

        // Monomials overflow on WIDTH rather than count, and the two caps are close
        // enough that it takes three terms: a full bank of TWO-term recipes needs
        // 2 + 2 * 1,150 = 2,302 monomials and fits the 2,304 array with two to spare.
        // Three-term recipes do not.
        let three_term = |v: u32| {
            recipe(vec![
                product(
                    v,
                    vec![challenge(ChallengeKey::ClaimBatching, ChallengePower::One)],
                ),
                product(
                    v + 1,
                    vec![challenge(
                        ChallengeKey::ClaimBatching,
                        ChallengePower::Static(2),
                    )],
                ),
                product(
                    v + 2,
                    vec![challenge(
                        ChallengeKey::ClaimBatching,
                        ChallengePower::Static(3),
                    )],
                ),
            ])
        };
        let wide: Vec<NormalizedCoefficientRecipe> = (1..=BWD_SEG_CONST_BANK as u32 - 2)
            .map(three_term)
            .collect();
        assert!(
            matches!(
                build_seg_coeff_eval_tables(&wide),
                Err(SegCoeffEvalError::MonomialTableOverflow { cap, .. })
                    if cap == BWD_SEG_COEFF_MAX_MONOMIALS
            ),
            "a monomial table past the inline array must be refused; a full bank of \
             three-term recipes needs more than {BWD_SEG_COEFF_MAX_MONOMIALS}"
        );
    }
}
