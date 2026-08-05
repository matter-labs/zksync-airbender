//! The coefficient GROUPING transform (design §4.1-§4.2, §4.7): the single
//! authority that turns a lowered [`CoeffLayer`] into a GROUPED one.
//!
//! # What grouping is
//!
//! A banked coefficient recipe is a sum of scalar-times-challenge products. Two
//! terms whose recipes differ only by a BASE-FIELD scale share a challenge CORE:
//!
//! ```text
//! recipe_a = 3*gamma + 6*gamma*delta = 3 * (gamma + 2*gamma*delta)
//! recipe_b = 5*gamma + 10*gamma*delta = 5 * (gamma + 2*gamma*delta)
//! ```
//!
//! [`factor`] splits `recipe = immediate x core` with the core's LEADING scalar
//! normalized to one, so the core is a canonical group key. Terms sharing a core
//! become a [`CoeffGroup`]: one `Ext` core multiplication replaces one per member,
//! and each member keeps only its cheap base-field immediate.
//!
//! # What this pass does NOT do
//!
//! It prices nothing, orders nothing and encodes nothing — the atom order (§4.3),
//! the wire's group header (§4.4) and the descriptor deal (§4.5) are strictly later
//! passes reading the `groups` / `immediates` this one fills. It is a pure
//! `CoeffLayer -> CoeffLayer` function: same regime, same sources, same terms in
//! the same order with the same ids, only `coefficient` fields remapped.
//!
//! # Invariants it upholds
//!
//! * R0 layers pass through UNTOUCHED (§4.1: grouping is `Ext`-only).
//! * `coefficients` is rebuilt deduplicated and sorted — the [`CoeffLayer`]
//!   invariant — and holds group cores, singleton originals, and always the
//!   `c_init` recipe (§4.1: `c_init` is excluded from grouping, so its entry
//!   survives even when every term sharing it groups).
//! * Every member's `CoeffTerm::coefficient` equals its group's `core` id, and no
//!   id anywhere dangles.
//! * `immediates` is deduplicated and ascending; `+1` / `-1` consume no entry.
//! * Both caps re-check AFTER the rebuild: the 13-bit bank fence (the same
//!   [`CoeffError::CoefficientBankOverflow`] `lower` raises, which ran before this
//!   pass and therefore did not validate the rebuilt bank) and the wire-level
//!   [`LEAN_MAX_IMMEDIATES`].
//! * Every collection is a `BTreeMap` / `BTreeSet` / explicitly sorted `Vec`:
//!   grouping is a deterministic function of the input layer.

use std::collections::{BTreeMap, BTreeSet};

use field::{Field, PrimeField};
use gkr_eval_ir::Bf;

use super::limits::{LEAN_MAX_IMMEDIATES, MAX_COEFFICIENT_ENCODINGS};
use super::model::{
    CoeffError, CoeffGroup, CoeffGroupMember, CoeffLayer, CoeffProduct, CoeffTerm,
    CoefficientRecipeId, ImmediateId, NormalizedCoefficientRecipe, TermId,
};

fn bf(value: u32) -> Bf {
    Bf::from_u32_with_reduction(value)
}

/// The canonical reduced representative of `-1`, the second reserved immediate.
fn neg_one() -> u32 {
    let mut v = Bf::ONE;
    v.negate();
    v.as_u32_reduced()
}

/// Multiply every product's scalar by `scale` and re-canonicalize.
fn scale_by(recipe: &NormalizedCoefficientRecipe, scale: Bf) -> NormalizedCoefficientRecipe {
    NormalizedCoefficientRecipe::from_terms(
        recipe
            .terms
            .iter()
            .map(|product| {
                let mut scaled = bf(product.scalar);
                scaled.mul_assign(&scale);
                let challenges = product.challenges.clone();
                let inits_and_teardowns_top_bits = product.inits_and_teardowns_top_bits.clone();
                CoeffProduct {
                    scalar: scaled.as_u32_reduced(),
                    challenges,
                    inits_and_teardowns_top_bits,
                }
            })
            .collect(),
    )
}

/// Factor `recipe = immediate x core` (§4.1): `immediate` = the leading product's
/// scalar; `core` = every scalar multiplied by `immediate⁻¹`, so the core's leading
/// scalar is one.
///
/// The leading product is well defined without a tie-break because
/// [`NormalizedCoefficientRecipe::from_terms`] sorts products by challenge
/// multiset, so `terms[0]` is a canonical function of the recipe.
///
/// Returns `None` for the recipes that must NOT group and stay plain terms:
///
///   * a bare scalar (single product, no challenges) — its core would be the
///     multiplicative identity, which is not a bank entry at all; and
///   * the additive identity, which is never encoded.
///
/// Reference implementation: the `split()` closure of the fragment coefficient
/// census in `gpu/circuit_prover`'s `seg_report.rs`.
pub fn factor(recipe: &NormalizedCoefficientRecipe) -> Option<(u32, NormalizedCoefficientRecipe)> {
    let leading = recipe.terms.first()?;
    if recipe.terms.len() == 1
        && leading.challenges.is_empty()
        && leading.inits_and_teardowns_top_bits.is_empty()
    {
        return None; // bare scalar: the core would be ONE
    }
    let immediate = leading.scalar;
    // A canonical recipe never banks a zero scalar, so the inverse exists; a
    // violated invariant degrades to "does not group", never to a panic.
    let inverse = bf(immediate).inverse()?;
    Some((immediate, scale_by(recipe, inverse)))
}

/// The canonical BF value an [`ImmediateId`] denotes in `layer` (§4.4's id space:
/// `0 → +1`, `1 → −1`, `≥ 2 → immediates[id − 2]`), or `None` for an id past the
/// layer's table.
///
/// The only decoder of that id space in the crate, so a validator, the interpreter
/// and the tests cannot disagree with the transform that minted the ids.
pub fn immediate_value(layer: &CoeffLayer, id: ImmediateId) -> Option<u32> {
    match id.bank_index() {
        None => Some(if id == ImmediateId::NEG_ONE {
            neg_one()
        } else {
            Bf::ONE.as_u32_reduced()
        }),
        Some(index) => layer.immediates.get(index).copied(),
    }
}

/// Overwrite a term's coefficient id in place. The only mutation this pass makes
/// to a term — ids, sources, fields and order are preserved exactly.
fn set_coefficient(term: &mut CoeffTerm, id: CoefficientRecipeId) {
    match term {
        CoeffTerm::C0Linear { coefficient, .. }
        | CoeffTerm::C2Product { coefficient, .. }
        | CoeffTerm::DualProduct { coefficient, .. } => *coefficient = id,
    }
}

/// Which accumulator sides a term contributes to (§4.4's `has_c0` / `has_c2`).
fn term_sides(term: &CoeffTerm) -> (bool, bool) {
    match term {
        CoeffTerm::C0Linear { .. } => (true, false),
        CoeffTerm::C2Product { .. } => (false, true),
        CoeffTerm::DualProduct { .. } => (true, true),
    }
}

/// Group a lowered layer's coefficients (§4.1-§4.2, §4.7).
///
/// `Ext` only: an R0 layer is returned unchanged, so the caller's regime gate is
/// belt-and-braces rather than the only guard.
///
/// # Errors
///
/// [`CoeffError::CoefficientBankOverflow`] if the REBUILT bank plus the two
/// reserved literals exceeds the 13-bit coefficient field, and
/// [`CoeffError::ImmediateTableOverflow`] if the coordinate needs more distinct
/// non-`±1` immediates than the wire's table holds.
pub fn group_coeff_layer(layer: CoeffLayer) -> Result<CoeffLayer, CoeffError> {
    debug_assert!(
        layer.groups.is_empty() && layer.immediates.is_empty(),
        "grouping is not idempotent by re-entry: it consumes an UNGROUPED layer"
    );
    if layer.regime == crate::BwdRegime::R0 {
        return Ok(layer);
    }

    // 1. Factor every banked term recipe; collect candidates by core. Terms with
    //    literal ids (`ONE`/`NEG_ONE`) and bare-scalar recipes never group.
    let mut by_core: BTreeMap<NormalizedCoefficientRecipe, Vec<(TermId, u32)>> = BTreeMap::new();
    for term in &layer.terms {
        let Some(bank_index) = term.coefficient().bank_index() else {
            continue;
        };
        let Some(recipe) = layer.coefficients.get(bank_index) else {
            continue;
        };
        let Some((immediate, core)) = factor(recipe) else {
            continue;
        };
        by_core
            .entry(core)
            .or_default()
            .push((term.id(), immediate));
    }

    // 2. Keep only multi-member cores, ascending `TermId` (§4.2). One core is ONE
    //    MAXIMAL group: execution-time granularity is the consumer's decision (the
    //    segmented deal's `K`-aware chop), and a pre-chopped artifact would only
    //    put a floor under the consumer's header overhead.
    let mut proto_groups: Vec<(NormalizedCoefficientRecipe, Vec<(TermId, u32)>)> = Vec::new();
    for (core, mut members) in by_core {
        if members.len() < 2 {
            continue;
        }
        members.sort_unstable_by_key(|(term, _)| *term);
        proto_groups.push((core, members));
    }
    // Deterministic atom-key order: ascending minimum member `TermId`, which is
    // unique because the groups partition the terms.
    proto_groups.sort_by_key(|(_, members)| members[0].0);

    // Which group each grouped term belongs to. Every other term stays PLAIN and
    // keeps its own recipe.
    let mut group_of: BTreeMap<TermId, usize> = BTreeMap::new();
    for (index, (_, members)) in proto_groups.iter().enumerate() {
        for (term, _) in members {
            group_of.insert(*term, index);
        }
    }

    // 3. Rebuild the bank: singleton originals + `c_init`'s recipe + every group
    //    core. A grouped member's own recipe is DROPPED unless a plain term or
    //    `c_init` still needs it. `BTreeSet` iteration is sorted, which is exactly
    //    the `CoeffLayer` "sorted by normalized recipe" invariant.
    let mut bank: BTreeSet<NormalizedCoefficientRecipe> = BTreeSet::new();
    let banked = |id: CoefficientRecipeId| -> Option<&NormalizedCoefficientRecipe> {
        layer.coefficients.get(id.bank_index()?)
    };
    for term in &layer.terms {
        if group_of.contains_key(&term.id()) {
            continue;
        }
        if let Some(recipe) = banked(term.coefficient()) {
            bank.insert(recipe.clone());
        }
    }
    if let Some(recipe) = layer.c_init.and_then(banked) {
        bank.insert(recipe.clone());
    }
    for (core, _) in &proto_groups {
        bank.insert(core.clone());
    }
    let coefficients: Vec<NormalizedCoefficientRecipe> = bank.into_iter().collect();

    // 6a. §9.2's thirteen coefficient bits, re-checked on the REBUILT bank (the
    //     fence in `lower` ran before this pass). Same error as lower.rs.
    let reserved = CoefficientRecipeId::RESERVED as usize;
    if coefficients.len() + reserved > MAX_COEFFICIENT_ENCODINGS {
        return Err(CoeffError::CoefficientBankOverflow {
            recipes: coefficients.len(),
            reserved,
            limit: MAX_COEFFICIENT_ENCODINGS,
        });
    }
    // The bank is sorted and deduplicated, so a recipe's id is its position.
    let id_of = |recipe: &NormalizedCoefficientRecipe| -> CoefficientRecipeId {
        let index = coefficients
            .binary_search(recipe)
            .expect("the rebuilt bank contains every recipe it was built from");
        CoefficientRecipeId::from_bank_index(index)
    };

    // 4. The deduped ascending immediates table: non-`±1` values only.
    let one = Bf::ONE.as_u32_reduced();
    let minus_one = neg_one();
    let mut distinct: BTreeSet<u32> = BTreeSet::new();
    for (_, members) in &proto_groups {
        for (_, immediate) in members {
            if *immediate != one && *immediate != minus_one {
                distinct.insert(*immediate);
            }
        }
    }
    let immediates: Vec<u32> = distinct.into_iter().collect();
    // 6b. The wire-level cap (§4.5). Checked BEFORE any `ImmediateId` is minted,
    //     because the id is a u16 and would wrap silently.
    if immediates.len() > LEAN_MAX_IMMEDIATES {
        return Err(CoeffError::ImmediateTableOverflow {
            len: immediates.len(),
        });
    }
    let immediate_id = |value: u32| -> ImmediateId {
        if value == one {
            return ImmediateId::ONE;
        }
        if value == minus_one {
            return ImmediateId::NEG_ONE;
        }
        ImmediateId::banked(
            immediates
                .binary_search(&value)
                .expect("every member immediate is in the table"),
        )
    };

    // 5. Rewrite every coefficient id: a member's to its group's core (§4.1), a
    //    plain term's and `c_init`'s to their own recipe's new position, a literal's
    //    not at all. Collect the accumulator sides each group's core multiplies.
    let mut sides: Vec<(bool, bool)> = vec![(false, false); proto_groups.len()];
    let mut terms: Vec<CoeffTerm> = Vec::with_capacity(layer.terms.len());
    for term in &layer.terms {
        let mut rewritten = *term;
        let id = match group_of.get(&term.id()) {
            Some(&group) => {
                let (c0, c2) = term_sides(term);
                sides[group].0 |= c0;
                sides[group].1 |= c2;
                id_of(&proto_groups[group].0)
            }
            None => match banked(term.coefficient()) {
                Some(recipe) => id_of(recipe),
                None => term.coefficient(),
            },
        };
        set_coefficient(&mut rewritten, id);
        terms.push(rewritten);
    }
    let groups: Vec<CoeffGroup> = proto_groups
        .iter()
        .zip(sides)
        .map(|((core, members), (has_c0, has_c2))| CoeffGroup {
            core: id_of(core),
            members: members
                .iter()
                .map(|(term, immediate)| CoeffGroupMember {
                    term: *term,
                    immediate: immediate_id(*immediate),
                })
                .collect(),
            has_c0,
            has_c2,
        })
        .collect();
    let c_init = layer.c_init.map(|id| match banked(id) {
        Some(recipe) => id_of(recipe),
        None => id,
    });

    Ok(CoeffLayer {
        regime: layer.regime,
        c_init,
        coefficients,
        sources: layer.sources.clone(),
        terms,
        groups,
        immediates,
    })
}
