//! Groups continuation terms that share a coefficient core.
//!
//! Recipes that differ only by a base-field scale share a normalized challenge
//! core; each member retains its scale as an immediate.

use std::collections::{BTreeMap, BTreeSet};

use field::{Field, PrimeField};

use super::limits::{LEAN_MAX_IMMEDIATES, MAX_COEFFICIENT_ENCODINGS};
use super::model::{
    CoeffError, CoeffGroup, CoeffGroupMember, CoeffLayer, CoeffProduct, CoeffTerm,
    CoefficientRecipeId, ImmediateId, NormalizedCoefficientRecipe, TermId,
};
use super::Bf;

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

/// Factor `recipe = immediate * core`: `immediate` is the leading product's
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
fn factor(recipe: &NormalizedCoefficientRecipe) -> Option<(u32, NormalizedCoefficientRecipe)> {
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

/// The canonical BF value an [`ImmediateId`] denotes in `layer`:
/// `0 → +1`, `1 → −1`, `≥ 2 → immediates[id − 2]`), or `None` for an id past the
/// layer's table.
///
/// The only decoder of that id space in the crate, so a validator, the interpreter
/// and the tests cannot disagree with the transform that minted the ids.
#[cfg(test)]
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

/// Which accumulator sides a term contributes to.
fn term_sides(term: &CoeffTerm) -> (bool, bool) {
    match term {
        CoeffTerm::C0Linear { .. } => (true, false),
        CoeffTerm::C2Product { .. } => (false, true),
        CoeffTerm::DualProduct { .. } => (true, true),
    }
}

/// Group continuation terms that share a normalized coefficient core.
pub(crate) fn group_coeff_layer(layer: CoeffLayer) -> Result<CoeffLayer, CoeffError> {
    debug_assert_eq!(layer.regime, crate::BwdRegime::Ext);
    debug_assert!(
        layer.groups.is_empty() && layer.immediates.is_empty(),
        "grouping is not idempotent by re-entry: it consumes an UNGROUPED layer"
    );
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

    // Keep one maximal group per multi-member core.
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

    // Rebuild the bank from recipes that remain directly referenced.
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

    // Grouping changes the bank, so recheck the wire limit.
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

    // Build the sorted table of non-literal immediates.
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
    // Check before converting table positions to u16 ids.
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

    // Rewrite coefficient ids and collect the sides each group contributes to.
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
        sources: layer.sources,
        terms,
        groups,
        immediates,
    })
}
