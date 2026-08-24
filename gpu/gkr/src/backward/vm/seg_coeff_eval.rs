//! Device evaluation of segmented backward coefficient recipes.
//!
//! Claim-batching powers are stored per monomial. Powers on challenge kinds
//! whose resolver ignores powers are rejected as ambiguous.
use std::collections::BTreeMap;

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use gpu_gkr_compiler::{
    CoeffProduct, CoefficientRecipeId, NormalizedCoefficientRecipe, WindowCoefficientPlan,
    WINDOW_COEFFICIENT_BANK_BIAS, WINDOW_MAX_COEFFICIENT_PLANS,
};

use super::seg_desc::BWD_SEG_OUTPUT_BANK;
use crate::upstream::{
    ChallengeKey, ChallengePower, ChallengeRef, Field, FieldExtension, PermutationSlot, PrimeField,
    NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES,
};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::{BF, E4};
use gpu_core::primitives::static_host::{alloc_static_pinned_box_from_slice, StaticPinnedBox};
use gpu_core::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
use gpu_prover_context::ProverContext;

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
/// separately by [`translate_recipe_inner`].
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

/// Plan kind: the bank slot holds the recipe's own value.
pub(crate) const BWD_SEG_COEFF_PLAN_DIRECT: u8 = 0;
/// Plan kind: the recipe's value times [`SegCoeffRecipe::scalar`].
pub(crate) const BWD_SEG_COEFF_PLAN_SCALED: u8 = 1;
/// Plan kind: the recipe's value times the E4 basis element
/// [`SegCoeffRecipe::limb`] selects.
pub(crate) const BWD_SEG_COEFF_PLAN_LINEAR_BASIS: u8 = 2;
/// Basis elements a `LinearBasis` plan may name.
pub(crate) const BWD_SEG_COEFF_PLAN_LIMBS: usize = 4;

/// CUDA mirror: `bwd_seg_coeff_recipe`. One bank slot's plan: a span of
/// monomials plus the post-multiply its kind selects.
///
/// The offset fits because the monomial table is capped at
/// [`BWD_SEG_EVAL_MONOMIALS`].
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct SegCoeffRecipe {
    pub scalar: BF,
    pub monomial_offset: u16,
    pub monomial_count: u16,
    pub kind: u8,
    pub limb: u8,
    pub _pad: [u8; 2],
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
    // The CUDA half asserts the same two sizes and the same six offsets.
    assert!(std::mem::size_of::<SegCoeffRecipe>() == 12);
    assert!(std::mem::offset_of!(SegCoeffRecipe, monomial_offset) == 4);
    assert!(std::mem::offset_of!(SegCoeffRecipe, kind) == 8);
    assert!(std::mem::offset_of!(SegCoeffRecipe, limb) == 9);
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
    if monomials.len() > BWD_SEG_EVAL_MONOMIALS {
        return Err(SegCoeffEvalError::MonomialTableOverflow {
            monomials: monomials.len(),
            cap: BWD_SEG_EVAL_MONOMIALS,
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

/// Device plan-table capacity: one entry per output bank slot the fill can
/// address.
pub(crate) const BWD_SEG_EVAL_RECIPES: usize = 1_792;

/// Device monomial-table capacity, over the whole layer's plans.
pub(crate) const BWD_SEG_EVAL_MONOMIALS: usize = 2_304;

/// Interned window plans one layer may name, reserved literals excluded.
pub(crate) const BWD_SEG_WINDOW_PLANS: usize = 1_728;

/// Byte offset of the plan section inside the device blob.
pub(crate) const BWD_SEG_BLOB_RECIPES_OFFSET: usize = 0;
/// Byte offset of the monomial section inside the device blob.
pub(crate) const BWD_SEG_BLOB_MONOMIALS_OFFSET: usize = 21_504;
/// The device blob's total size. Fixed by the capacities, not by a layer.
pub(crate) const BWD_SEG_BLOB_BYTES: usize = 49_152;

/// CUDA mirror: `bwd_seg_coeff_eval_desc`. The evaluator's LAUNCH HEADER.
///
/// The plan and monomial tables are a pure function of the compiled layer, so
/// they are known at SCHEDULING time — but they are far too large for the
/// by-value parameter space, so they live in a device blob staged once per layer
/// through `SchedulerHostAllocator` and reached through [`Self::tables`]. Only
/// the challenges are round state the transcript squeezed on the device.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct SegCoeffEvalDesc {
    /// Device base of the serialized blob.
    pub tables: *const u8,
    /// Bank slots to fill, reserved literals included.
    pub num_coefficients: u32,
    pub num_monomials: u32,
    pub recipes_offset: u32,
    pub monomials_offset: u32,
    pub blob_bytes: u32,
    pub _pad: u32,
}

const _: () = {
    // The CUDA half asserts the same size, the same four offsets, the same blob
    // layout, and the same header bound — which is what makes the capacities
    // above a gate rather than a hope.
    assert!(std::mem::size_of::<SegCoeffEvalDesc>() == 32);
    assert!(std::mem::offset_of!(SegCoeffEvalDesc, num_coefficients) == 8);
    assert!(std::mem::offset_of!(SegCoeffEvalDesc, recipes_offset) == 16);
    assert!(std::mem::offset_of!(SegCoeffEvalDesc, monomials_offset) == 20);
    assert!(std::mem::offset_of!(SegCoeffEvalDesc, blob_bytes) == 24);
    assert!(
        std::mem::size_of::<SegCoeffEvalDesc>() + 2 * std::mem::size_of::<*const E4>() < 4 * 1_024
    );

    assert!(BWD_SEG_BLOB_RECIPES_OFFSET == 0);
    assert!(
        BWD_SEG_BLOB_MONOMIALS_OFFSET
            == BWD_SEG_EVAL_RECIPES * std::mem::size_of::<SegCoeffRecipe>()
    );
    assert!(
        BWD_SEG_BLOB_BYTES
            == BWD_SEG_BLOB_MONOMIALS_OFFSET
                + BWD_SEG_EVAL_MONOMIALS * std::mem::size_of::<SegCoeffMonomial>()
    );
    assert!(BWD_SEG_BLOB_BYTES.is_multiple_of(std::mem::size_of::<E4>()));

    // Every filled bank slot needs a plan entry.
    assert!(BWD_SEG_EVAL_RECIPES >= BWD_SEG_OUTPUT_BANK);
    // A monomial offset rides the plan header as a u16.
    assert!(BWD_SEG_EVAL_MONOMIALS <= u16::MAX as usize);
    // The windowed arm's plan ids are biased past the reserved literals, and the
    // bias IS the reserved-literal count both arms share.
    assert!(BWD_SEG_WINDOW_PLANS == WINDOW_MAX_COEFFICIENT_PLANS);
    assert!(WINDOW_COEFFICIENT_BANK_BIAS as usize == CoefficientRecipeId::RESERVED as usize);
    assert!(BWD_SEG_WINDOW_PLANS + WINDOW_COEFFICIENT_BANK_BIAS as usize <= BWD_SEG_OUTPUT_BANK);
    assert!(BWD_SEG_COEFF_PLAN_LIMBS == 4);
};

/// The host-side plan and monomial tables of one arm's fill, before serialization.
pub(crate) struct SegCoeffEvalBlob {
    pub recipes: Vec<SegCoeffRecipe>,
    pub monomials: Vec<SegCoeffMonomial>,
}

impl SegCoeffEvalBlob {
    fn new(slots: usize) -> Result<Self, SegCoeffEvalError> {
        if slots > BWD_SEG_OUTPUT_BANK {
            return Err(SegCoeffEvalError::BankOverflow {
                coefficients: slots,
                cap: BWD_SEG_OUTPUT_BANK,
            });
        }
        if slots > BWD_SEG_EVAL_RECIPES {
            return Err(SegCoeffEvalError::RecipeTableOverflow {
                recipes: slots,
                cap: BWD_SEG_EVAL_RECIPES,
            });
        }
        Ok(Self {
            recipes: vec![SegCoeffRecipe::default(); slots],
            monomials: Vec::new(),
        })
    }

    fn push(
        &mut self,
        slot: usize,
        translated: &[SegCoeffMonomial],
        kind: u8,
        scalar: BF,
        limb: u8,
    ) -> Result<(), SegCoeffEvalError> {
        let offset = self.monomials.len();
        let end = offset + translated.len();
        if end > BWD_SEG_EVAL_MONOMIALS {
            return Err(SegCoeffEvalError::MonomialTableOverflow {
                monomials: end,
                cap: BWD_SEG_EVAL_MONOMIALS,
            });
        }
        self.monomials.extend_from_slice(translated);
        self.recipes[slot] = SegCoeffRecipe {
            scalar,
            monomial_offset: offset as u16,
            monomial_count: translated.len() as u16,
            kind,
            limb,
            _pad: [0; 2],
        };
        Ok(())
    }

    /// The reserved literals are ordinary constant plans to the device
    /// evaluator, which is why one launch fills the whole payload and the caller
    /// stages nothing by hand.
    fn push_reserved_literals(&mut self) -> Result<(), SegCoeffEvalError> {
        for (slot, literal) in [CoefficientRecipeId::ONE, CoefficientRecipeId::NEG_ONE]
            .into_iter()
            .enumerate()
        {
            let value = literal.literal().expect("a reserved literal id");
            self.push(
                slot,
                &[literal_monomial(value)],
                BWD_SEG_COEFF_PLAN_DIRECT,
                BF::ZERO,
                0,
            )?;
        }
        Ok(())
    }

    fn check_batching_invariant(&self) {
        // The one invariant the format's two spellings of `beta` could break.
        debug_assert!(
            self.monomials.iter().all(|monomial| {
                monomial.challenge_idx_0 != BWD_SEG_CHALLENGE_CLAIM_BATCHING
                    && monomial.challenge_idx_1 != BWD_SEG_CHALLENGE_CLAIM_BATCHING
            }),
            "the batching challenge must ride `batch_power`, never a factor slot"
        );
    }

    /// The blob's fixed serialized layout: the plan section at
    /// [`BWD_SEG_BLOB_RECIPES_OFFSET`], the monomial section at
    /// [`BWD_SEG_BLOB_MONOMIALS_OFFSET`], zeros everywhere else.
    fn serialize(&self) -> Vec<u8> {
        let mut bytes = vec![0u8; BWD_SEG_BLOB_BYTES];
        write_records(&mut bytes, BWD_SEG_BLOB_RECIPES_OFFSET, &self.recipes);
        write_records(&mut bytes, BWD_SEG_BLOB_MONOMIALS_OFFSET, &self.monomials);
        bytes
    }

    fn monomials_of(&self, slot: usize) -> &[SegCoeffMonomial] {
        let recipe = self.recipes[slot];
        let start = usize::from(recipe.monomial_offset);
        &self.monomials[start..start + usize::from(recipe.monomial_count)]
    }
}

fn write_records<T: Copy>(bytes: &mut [u8], offset: usize, records: &[T]) {
    let len = std::mem::size_of_val(records);
    // SAFETY: `T` is a `repr(C)` POD of integers and base-field limbs whose every
    // byte, explicit padding included, is initialized by construction.
    let source = unsafe { std::slice::from_raw_parts(records.as_ptr().cast::<u8>(), len) };
    bytes[offset..offset + len].copy_from_slice(source);
}

/// Translate a lean layer's coefficient bank into the per-round arm's blob.
///
/// Reserved literals precede the compiled recipes in the device bank, and every
/// compiled recipe is a `Direct` plan.
pub(crate) fn build_seg_coeff_eval_blob(
    recipes: &[NormalizedCoefficientRecipe],
    runtime_top_bits: &[u32],
) -> Result<SegCoeffEvalBlob, SegCoeffEvalError> {
    let mut blob =
        SegCoeffEvalBlob::new(CoefficientRecipeId::RESERVED as usize + recipes.len())?;
    blob.push_reserved_literals()?;
    for (recipe_index, recipe) in recipes.iter().enumerate() {
        let translated = translate_recipe_inner(recipe, recipe_index, runtime_top_bits)?;
        let slot = CoefficientRecipeId::RESERVED as usize + recipe_index;
        blob.push(
            slot,
            &translated,
            BWD_SEG_COEFF_PLAN_DIRECT,
            BF::ZERO,
            0,
        )?;
    }
    blob.check_batching_invariant();
    Ok(blob)
}

/// Translate a window program's interned coefficient plans into the windowed
/// arm's blob.
///
/// The reserved literals keep bank slots 0 and 1, which is what
/// `WINDOW_COEFFICIENT_BANK_BIAS` biases every plan id past.
pub(crate) fn build_seg_coeff_eval_window_blob(
    plans: &[WindowCoefficientPlan],
    runtime_top_bits: &[u32],
) -> Result<SegCoeffEvalBlob, SegCoeffEvalError> {
    if plans.len() > BWD_SEG_WINDOW_PLANS {
        return Err(SegCoeffEvalError::PlanTableOverflow {
            plans: plans.len(),
            cap: BWD_SEG_WINDOW_PLANS,
        });
    }
    let bias = WINDOW_COEFFICIENT_BANK_BIAS as usize;
    let mut blob = SegCoeffEvalBlob::new(bias + plans.len())?;
    blob.push_reserved_literals()?;
    for (index, plan) in plans.iter().enumerate() {
        let (recipe, kind, scalar, limb) = match plan {
            WindowCoefficientPlan::Direct(recipe) => {
                (recipe, BWD_SEG_COEFF_PLAN_DIRECT, BF::ZERO, 0)
            }
            WindowCoefficientPlan::Scaled { recipe, scalar } => (
                recipe,
                BWD_SEG_COEFF_PLAN_SCALED,
                BF::from_u32_with_reduction(*scalar),
                0,
            ),
            WindowCoefficientPlan::LinearBasis { recipe, limb } => {
                if usize::from(*limb) >= BWD_SEG_COEFF_PLAN_LIMBS {
                    return Err(SegCoeffEvalError::PlanLimbOutOfRange {
                        plan: index,
                        limb: *limb,
                    });
                }
                (recipe, BWD_SEG_COEFF_PLAN_LINEAR_BASIS, BF::ZERO, *limb)
            }
        };
        let translated = translate_recipe_inner(recipe, index, runtime_top_bits)?;
        blob.push(bias + index, &translated, kind, scalar, limb)?;
    }
    blob.check_batching_invariant();
    Ok(blob)
}

#[cfg(test)]
fn build_seg_coeff_eval_tables(
    recipes: &[NormalizedCoefficientRecipe],
) -> Result<SegCoeffEvalBlob, SegCoeffEvalError> {
    build_seg_coeff_eval_blob(recipes, &[])
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

// ── The device staging ───────────────────────────────────────────────────────

/// One arm's staged evaluator tables: the launch header, the pinned host blob
/// the H2D reads, and the device blob it lands in.
///
/// The host blob is `SchedulerHostAllocator`-backed and written ONCE here; every
/// stream operation afterwards only reads it. It must be moved into a keepalive
/// that outlives the scheduled copies, which is what
/// [`Self::take_host_staging`] is for.
pub(crate) struct SegCoeffEvalTables {
    desc: SegCoeffEvalDesc,
    host: Option<StaticPinnedBox<u8>>,
    device: DeviceAllocation<E4>,
    /// The exact table bytes and challenge slots one fill's evaluation reads,
    /// computed from the blob it stages.
    #[cfg(all(
        any(test, feature = "task8_continuation_differential_test"),
        not(no_cuda)
    ))]
    task8_reads: Task8CoeffEvalReads,
}

/// The byte ranges of the staged blob, and the challenge slots, that
/// `bwd_seg_eval_coefficient` reads for one staged program: the recipe record
/// of every live coefficient, each monomial those recipes reference, and the
/// batching slot plus the challenge indices those monomials name.
#[cfg(all(
    any(test, feature = "task8_continuation_differential_test"),
    not(no_cuda)
))]
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Task8CoeffEvalReads {
    pub(crate) table_ranges: Vec<std::ops::Range<usize>>,
    pub(crate) challenge_slots: Vec<usize>,
}

#[cfg(all(
    any(test, feature = "task8_continuation_differential_test"),
    not(no_cuda)
))]
/// The pointer arguments one coefficient-bank fill's evaluation names: the
/// recipe and monomial records it reads, the challenge slots those monomials
/// use, and the bank prefix it writes.
#[cfg(all(
    any(test, feature = "task8_continuation_differential_test"),
    not(no_cuda)
))]
pub(crate) fn task8_coeff_fill_spans(
    reads: &Task8CoeffEvalReads,
    tables_base: usize,
    slab: usize,
    bank: usize,
    bank_bytes: usize,
) -> Vec<crate::backward::task8_probe::Task8Span> {
    use crate::backward::task8_probe::Task8Span;
    let element = std::mem::size_of::<E4>();
    let mut spans = Vec::with_capacity(reads.table_ranges.len() + reads.challenge_slots.len() + 1);
    for range in &reads.table_ranges {
        spans.push(Task8Span::read(
            "coefficient_tables",
            tables_base + range.start,
            range.end - range.start,
        ));
    }
    for slot in &reads.challenge_slots {
        spans.push(Task8Span::read(
            "challenge_slab",
            slab + slot * element,
            element,
        ));
    }
    spans.push(Task8Span::write("coefficient_bank", bank, bank_bytes));
    spans
}

#[cfg(all(
    any(test, feature = "task8_continuation_differential_test"),
    not(no_cuda)
))]
pub(crate) fn task8_coeff_eval_reads(blob: &SegCoeffEvalBlob) -> Task8CoeffEvalReads {
    let recipe_bytes = std::mem::size_of::<SegCoeffRecipe>();
    let monomial_bytes = std::mem::size_of::<SegCoeffMonomial>();
    let mut table_ranges = Vec::new();
    if !blob.recipes.is_empty() {
        table_ranges.push(
            BWD_SEG_BLOB_RECIPES_OFFSET
                ..BWD_SEG_BLOB_RECIPES_OFFSET + blob.recipes.len() * recipe_bytes,
        );
    }
    let mut challenge_slots =
        std::collections::BTreeSet::from([BWD_SEG_CHALLENGE_CLAIM_BATCHING as usize]);
    let mut monomials: Vec<std::ops::Range<usize>> = Vec::new();
    for recipe in &blob.recipes {
        let start = recipe.monomial_offset as usize;
        let end = start + recipe.monomial_count as usize;
        if start == end {
            continue;
        }
        monomials.push(
            BWD_SEG_BLOB_MONOMIALS_OFFSET + start * monomial_bytes
                ..BWD_SEG_BLOB_MONOMIALS_OFFSET + end * monomial_bytes,
        );
        for monomial in &blob.monomials[start..end] {
            for index in [monomial.challenge_idx_0, monomial.challenge_idx_1] {
                if index != BWD_SEG_CHALLENGE_ABSENT {
                    challenge_slots.insert(index as usize);
                }
            }
        }
    }
    monomials.sort_by_key(|range| range.start);
    for range in monomials {
        match table_ranges.last_mut() {
            Some(last) if last.end >= range.start => last.end = last.end.max(range.end),
            _ => table_ranges.push(range),
        }
    }
    Task8CoeffEvalReads {
        table_ranges,
        challenge_slots: challenge_slots.into_iter().collect(),
    }
}

impl SegCoeffEvalTables {
    pub(crate) fn stage(blob: &SegCoeffEvalBlob, context: &ProverContext) -> CudaResult<Self> {
        let host = alloc_static_pinned_box_from_slice(&blob.serialize())?;
        let device: DeviceAllocation<E4> = context.alloc(
            BWD_SEG_BLOB_BYTES / std::mem::size_of::<E4>(),
            AllocationPlacement::BestFit,
        )?;
        let desc = SegCoeffEvalDesc {
            tables: device.as_ptr().cast::<u8>(),
            num_coefficients: blob.recipes.len() as u32,
            num_monomials: blob.monomials.len() as u32,
            recipes_offset: BWD_SEG_BLOB_RECIPES_OFFSET as u32,
            monomials_offset: BWD_SEG_BLOB_MONOMIALS_OFFSET as u32,
            blob_bytes: BWD_SEG_BLOB_BYTES as u32,
            _pad: 0,
        };
        Ok(Self {
            desc,
            host: Some(host),
            device,
            #[cfg(all(
                any(test, feature = "task8_continuation_differential_test"),
                not(no_cuda)
            ))]
            task8_reads: task8_coeff_eval_reads(blob),
        })
    }

    pub(crate) fn take_host_staging(&mut self) -> Option<StaticPinnedBox<u8>> {
        self.host.take()
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

/// What one coefficient-bank fill touches: the staged table blob it copies up,
/// and the bank prefix its evaluation writes. Returned so a caller that must
/// account for the fill's pointer arguments reuses the addresses and extents
/// this fill used.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct BwdSegCoeffBankFillSpans {
    pub(crate) tables: (usize, usize),
    pub(crate) bank: (usize, usize),
}

/// Copy one arm's table blob to device and fill the coefficient bank from the
/// round's challenges, on `stream`.
///
/// `slab` is a device pointer to [`BWD_SEG_CHALLENGE_SLOTS`] E4 values in slot order;
/// `bank` is the output-bank symbol returned by
/// `super::seg::bwd_seg_coeff_bank_device_ptr()`.
///
/// Enqueue after challenge writes and before the round's segment launches. All
/// segment reads must finish before the next fill overwrites the bank.
pub(crate) fn schedule_bwd_seg_coeff_bank_fill(
    tables: &mut SegCoeffEvalTables,
    slab: *const E4,
    bank: *mut E4,
    stream: &CudaStream,
) -> CudaResult<BwdSegCoeffBankFillSpans> {
    #[cfg(all(
        any(test, feature = "task8_continuation_differential_test"),
        not(no_cuda)
    ))]
    let task8_reads = tables.task8_reads.clone();
    let SegCoeffEvalTables {
        desc, host, device, ..
    } = tables;
    let host = host
        .as_ref()
        .expect("the coefficient blob's host staging must outlive its H2D copy");
    // SAFETY: the device allocation and the host blob are both exactly
    // `BWD_SEG_BLOB_BYTES` long, and E4 carries no invalid bit patterns.
    #[cfg(all(
        any(test, feature = "task8_continuation_differential_test"),
        not(no_cuda)
    ))]
    let tables_base = device.as_ptr() as usize;
    #[cfg(all(
        any(test, feature = "task8_continuation_differential_test"),
        not(no_cuda)
    ))]
    let bank_bytes = desc.num_coefficients as usize * std::mem::size_of::<E4>();
    #[cfg(all(
        any(test, feature = "task8_continuation_differential_test"),
        not(no_cuda)
    ))]
    crate::backward::task8_probe::task8_register_symbol(
        "ab_gkr_bwd_seg_coeff_bank",
        bank as usize,
        bank_bytes,
    );
    unsafe {
        let destination = (&mut device[..]).transmute_mut::<u8>();
        crate::backward::task8_enqueue_scope!(_task8, "coefficient-table-copy", Copy, {
            use crate::backward::task8_probe::Task8Span;
            vec![Task8Span::write(
                "coefficient_tables",
                tables_base,
                BWD_SEG_BLOB_BYTES,
            )]
        });
        memory_copy_async(destination, &host[..], stream)?;
    }
    let count = desc.num_coefficients;
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let function = GkrBwdSegEvalCoefficientsFunction(ab_gkr_bwd_seg_eval_coefficients_kernel);
    crate::backward::task8_enqueue_scope!(_task8, "coefficient-bank-fill", Kernel, {
        task8_coeff_fill_spans(
            &task8_reads,
            tables_base,
            slab as usize,
            bank as usize,
            bank_bytes,
        )
    });
    function.launch(
        &config,
        &GkrBwdSegEvalCoefficientsArguments::new(*desc, slab, bank),
    )?;
    Ok(BwdSegCoeffBankFillSpans {
        tables: (device.as_ptr() as usize, BWD_SEG_BLOB_BYTES),
        bank: (bank as usize, count as usize * std::mem::size_of::<E4>()),
    })
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
            build_seg_coeff_eval_blob(&[recipe], &[7]).is_err(),
            "a missing runtime value must not be replaced with its set index"
        );
    }

    /// The monomials of bank slot `index` (reserved literals occupy 0 and 1).
    fn bank_monomials(tables: &SegCoeffEvalBlob, index: usize) -> &[SegCoeffMonomial] {
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
        assert_eq!(tables.recipes.len(), 3, "two literals plus the recipe");
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
    fn seg_coeff_eval_rejects_a_bank_past_the_output_bank() {
        let scalar = |v: u32| recipe(vec![product(v, Vec::new())]);
        let over_bank: Vec<NormalizedCoefficientRecipe> =
            (1..=BWD_SEG_OUTPUT_BANK as u32 + 1).map(scalar).collect();
        assert!(
            matches!(
                build_seg_coeff_eval_tables(&over_bank),
                Err(SegCoeffEvalError::BankOverflow { cap, .. }) if cap == BWD_SEG_OUTPUT_BANK
            ),
            "a bank past the output bank must be refused, not truncated"
        );
    }

    /// The monomial table is a capacity of its OWN now, so a bank that fits can
    /// still overflow it: a full bank of three-term recipes needs
    /// 2 + 3 * 1,790 = 5,372 monomials against the 2,304-entry table.
    #[test]
    fn seg_coeff_eval_rejects_a_monomial_table_past_its_capacity() {
        let three_term = |v: u32| {
            recipe(
                (1..=3u32)
                    .map(|power| {
                        product(
                            v + power,
                            vec![challenge(
                                ChallengeKey::ClaimBatching,
                                ChallengePower::Static(power),
                            )],
                        )
                    })
                    .collect(),
            )
        };
        let wide: Vec<NormalizedCoefficientRecipe> = (1..=BWD_SEG_OUTPUT_BANK as u32 - 2)
            .map(three_term)
            .collect();
        assert!(
            matches!(
                build_seg_coeff_eval_tables(&wide),
                Err(SegCoeffEvalError::MonomialTableOverflow { cap, .. })
                    if cap == BWD_SEG_EVAL_MONOMIALS
            ),
            "a monomial table past its capacity must be refused; a full bank of \
             three-term recipes needs more than {BWD_SEG_EVAL_MONOMIALS}"
        );
    }

    /// The windowed arm's three plan kinds all reach the blob, biased past the
    /// reserved literals, with the post-multiply the kind selects.
    #[test]
    fn seg_coeff_eval_window_blob_carries_every_plan_kind() {
        let core = recipe(vec![product(
            7,
            vec![challenge(ChallengeKey::LookupAdditive, ChallengePower::One)],
        )]);
        let plans = vec![
            WindowCoefficientPlan::Direct(core.clone()),
            WindowCoefficientPlan::Scaled {
                recipe: core.clone(),
                scalar: 5,
            },
            WindowCoefficientPlan::LinearBasis {
                recipe: core.clone(),
                limb: 3,
            },
        ];
        let blob = build_seg_coeff_eval_window_blob(&plans, &[]).expect("three plans fit");
        let bias = WINDOW_COEFFICIENT_BANK_BIAS as usize;
        assert_eq!(blob.recipes.len(), bias + plans.len());
        let kinds: Vec<(u8, u8, BF)> = blob.recipes[bias..]
            .iter()
            .map(|entry| (entry.kind, entry.limb, entry.scalar))
            .collect();
        assert_eq!(
            kinds,
            vec![
                (BWD_SEG_COEFF_PLAN_DIRECT, 0, BF::ZERO),
                (
                    BWD_SEG_COEFF_PLAN_SCALED,
                    0,
                    BF::from_u32_with_reduction(5)
                ),
                (BWD_SEG_COEFF_PLAN_LINEAR_BASIS, 3, BF::ZERO),
            ]
        );
        for slot in bias..bias + plans.len() {
            assert_eq!(
                bank_monomials(&blob, slot).len(),
                1,
                "every plan carries its own copy of the recipe's monomials"
            );
        }
    }

    #[test]
    fn seg_coeff_eval_window_blob_rejects_a_plan_list_past_its_capacity() {
        let plan = |v: u32| WindowCoefficientPlan::Direct(recipe(vec![product(v, Vec::new())]));
        let over: Vec<WindowCoefficientPlan> =
            (1..=BWD_SEG_WINDOW_PLANS as u32 + 1).map(plan).collect();
        assert!(
            matches!(
                build_seg_coeff_eval_window_blob(&over, &[]),
                Err(SegCoeffEvalError::PlanTableOverflow { cap, .. }) if cap == BWD_SEG_WINDOW_PLANS
            ),
            "a plan list past the plan capacity must be refused"
        );
    }

    #[test]
    fn seg_coeff_eval_blob_serializes_at_the_pinned_offsets() {
        let blob = build_seg_coeff_eval_tables(&[recipe(vec![product(3, Vec::new())])])
            .expect("one recipe fits");
        let bytes = blob.serialize();
        assert_eq!(bytes.len(), BWD_SEG_BLOB_BYTES);
        let recipe_bytes = std::mem::size_of::<SegCoeffRecipe>() * blob.recipes.len();
        assert_eq!(
            &bytes[BWD_SEG_BLOB_RECIPES_OFFSET..BWD_SEG_BLOB_RECIPES_OFFSET + recipe_bytes],
            unsafe {
                std::slice::from_raw_parts(blob.recipes.as_ptr().cast::<u8>(), recipe_bytes)
            }
        );
        let monomial_bytes = std::mem::size_of::<SegCoeffMonomial>() * blob.monomials.len();
        assert_eq!(
            &bytes[BWD_SEG_BLOB_MONOMIALS_OFFSET..BWD_SEG_BLOB_MONOMIALS_OFFSET + monomial_bytes],
            unsafe {
                std::slice::from_raw_parts(blob.monomials.as_ptr().cast::<u8>(), monomial_bytes)
            }
        );
        assert!(
            bytes[BWD_SEG_BLOB_MONOMIALS_OFFSET - 16..BWD_SEG_BLOB_MONOMIALS_OFFSET]
                .iter()
                .all(|byte| *byte == 0),
            "the plan section's unfilled tail must stay zero"
        );
    }
}

/// The four capacities, measured against the committed circuit corpus. GPU-free:
/// the corpus is compiled and lowered on the CPU, and only counts are compared.
#[cfg(test)]
mod corpus_capacity_tests {
    use super::*;
    use crate::upstream::GKRCircuitArtifact;
    use gpu_gkr_compiler::{compile_continuations, compile_r0, lower_window_program};
    use std::path::PathBuf;
    use std::sync::OnceLock;

    const CORPUS: &[&str] = &[
        "add_sub_lui_auipc_mop_layout_gkr.json",
        "bigint_with_extended_control_layout_gkr.json",
        "blake2_g_function_layout_gkr.json",
        "blake2_with_extended_control_layout_gkr.json",
        "inits_and_teardowns_layout_gkr.json",
        "jump_branch_slt_layout_gkr.json",
        "keccak_special5_layout_gkr.json",
        "mem_subword_only_layout_gkr.json",
        "mem_word_only_layout_gkr.json",
        "shift_binop_layout_gkr.json",
        "unified_reduced_machine_layout_gkr.json",
        "unsigned_mul_div_layout_gkr.json",
    ];

    /// A teardown-set stand-in long enough for any corpus layer's references. The
    /// value cannot change a monomial COUNT — merging is keyed on the challenge
    /// structure, never on the scalar.
    const TOP_BITS: &[u32] = &[1; 64];

    #[derive(Default)]
    struct CorpusMaxima {
        coordinates: usize,
        bank_slots: usize,
        recipe_entries: usize,
        monomials: usize,
        window_plans: usize,
    }

    fn monomial_total(recipes: &[NormalizedCoefficientRecipe], label: &str) -> usize {
        CoefficientRecipeId::RESERVED as usize
            + recipes
                .iter()
                .enumerate()
                .map(|(index, recipe)| {
                    translate_recipe_inner(recipe, index, TOP_BITS)
                        .unwrap_or_else(|error| panic!("{label} recipe {index}: {error:?}"))
                        .len()
                })
                .sum::<usize>()
    }

    fn measure() -> &'static CorpusMaxima {
        static MEASURED: OnceLock<CorpusMaxima> = OnceLock::new();
        MEASURED.get_or_init(|| {
            let directory = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../cs/compiled_circuits");
            let mut maxima = CorpusMaxima::default();
            for layout in CORPUS {
                let artifact: GKRCircuitArtifact<BF> =
                    serde_json::from_slice(&std::fs::read(directory.join(layout)).unwrap())
                        .unwrap();
                let dag = gkr_eval_ir::lower_dag(&artifact)
                    .unwrap_or_else(|error| panic!("{layout}: {error}"));
                let r0 = compile_r0(&dag).unwrap_or_else(|error| panic!("{layout} R0: {error:?}"));
                let ext = compile_continuations(&dag)
                    .unwrap_or_else(|error| panic!("{layout} Ext: {error:?}"));
                for (r0_layer, ext_layer) in r0.layers.iter().zip(ext.layers.iter()) {
                    let label = format!("{layout} L{}", r0_layer.layer);
                    let window = lower_window_program(r0_layer)
                        .unwrap_or_else(|error| panic!("{label} window lowering: {error}"));
                    let plans = window.coefficient_plans.len();
                    let per_round_slots = CoefficientRecipeId::RESERVED as usize
                        + r0_layer
                            .coefficient_recipes
                            .len()
                            .max(ext_layer.coefficient_recipes.len());
                    let windowed_slots = WINDOW_COEFFICIENT_BANK_BIAS as usize + plans;
                    let slots = per_round_slots.max(windowed_slots);
                    let monomials = monomial_total(&r0_layer.coefficient_recipes, &label)
                        .max(monomial_total(&ext_layer.coefficient_recipes, &label))
                        .max(window_monomial_total(&window.coefficient_plans, &label));
                    maxima.coordinates += 1;
                    maxima.bank_slots = maxima.bank_slots.max(slots);
                    maxima.recipe_entries = maxima.recipe_entries.max(slots);
                    maxima.monomials = maxima.monomials.max(monomials);
                    maxima.window_plans = maxima.window_plans.max(plans);
                }
            }
            assert_eq!(maxima.coordinates, 57, "the retained corpus is 57 coordinates");
            maxima
        })
    }

    fn window_monomial_total(plans: &[WindowCoefficientPlan], label: &str) -> usize {
        WINDOW_COEFFICIENT_BANK_BIAS as usize
            + plans
                .iter()
                .enumerate()
                .map(|(index, plan)| {
                    let recipe = match plan {
                        WindowCoefficientPlan::Direct(recipe)
                        | WindowCoefficientPlan::Scaled { recipe, .. }
                        | WindowCoefficientPlan::LinearBasis { recipe, .. } => recipe,
                    };
                    translate_recipe_inner(recipe, index, TOP_BITS)
                        .unwrap_or_else(|error| panic!("{label} plan {index}: {error:?}"))
                        .len()
                })
                .sum::<usize>()
    }

    #[test]
    fn cpu_corpus_fits_the_output_bank() {
        let observed = measure().bank_slots;
        assert_eq!(observed, 1_667, "corpus maximum reserved-inclusive bank slots");
        assert!(observed <= BWD_SEG_OUTPUT_BANK);
    }

    #[test]
    fn cpu_corpus_fits_the_eval_recipe_table() {
        let observed = measure().recipe_entries;
        assert_eq!(observed, 1_667, "corpus maximum plan-table entries");
        assert!(observed <= BWD_SEG_EVAL_RECIPES);
    }

    #[test]
    fn cpu_corpus_fits_the_eval_monomial_table() {
        let observed = measure().monomials;
        assert_eq!(observed, 1_672, "corpus maximum monomials in one layer's tables");
        assert!(observed <= BWD_SEG_EVAL_MONOMIALS);
    }

    #[test]
    fn cpu_corpus_fits_the_window_plan_capacity() {
        let observed = measure().window_plans;
        assert_eq!(observed, 1_665, "corpus maximum interned window plans");
        assert!(observed <= BWD_SEG_WINDOW_PLANS);
    }
}
