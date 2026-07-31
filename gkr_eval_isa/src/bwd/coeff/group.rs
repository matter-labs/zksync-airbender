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

use cs::gkr_compiler::dag_ir::{Bf, BwdRegime};
use field::{Field, PrimeField};

use super::limits::{GROUP_SPLIT_MAX_MEMBERS, LEAN_MAX_IMMEDIATES, MAX_COEFFICIENT_ENCODINGS};
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

/// Multiply every product's scalar by `scale` and re-canonicalize. The one place
/// this pass scales a recipe — [`factor`] divides by the immediate, [`rescale`]
/// multiplies by it, and both must agree on canonicalization.
fn scale_by(recipe: &NormalizedCoefficientRecipe, scale: Bf) -> NormalizedCoefficientRecipe {
    NormalizedCoefficientRecipe::from_terms(
        recipe
            .terms
            .iter()
            .map(|product| {
                let mut scaled = bf(product.scalar);
                scaled.mul_assign(&scale);
                let challenges = product.challenges.clone();
                CoeffProduct { scalar: scaled.as_u32_reduced(), challenges }
            })
            .collect(),
    )
}

/// Multiply every product's scalar by `scale`, re-canonicalizing.
///
/// The inverse of [`factor`]'s scaling and the shape every validation uses:
/// `rescale(core, immediate) == recipe` is the structural statement of "this
/// member's recipe is this group's core times this immediate", and it needs no
/// challenge resolver to check.
pub fn rescale(recipe: &NormalizedCoefficientRecipe, scale: u32) -> NormalizedCoefficientRecipe {
    scale_by(recipe, bf(scale))
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
    if recipe.terms.len() == 1 && leading.challenges.is_empty() {
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
        None => Some(if id == ImmediateId::NEG_ONE { neg_one() } else { Bf::ONE.as_u32_reduced() }),
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
    if layer.regime == BwdRegime::R0 {
        return Ok(layer);
    }

    // 1. Factor every banked term recipe; collect candidates by core. Terms with
    //    literal ids (`ONE`/`NEG_ONE`) and bare-scalar recipes never group.
    let mut by_core: BTreeMap<NormalizedCoefficientRecipe, Vec<(TermId, u32)>> = BTreeMap::new();
    for term in &layer.terms {
        let Some(bank_index) = term.coefficient().bank_index() else { continue };
        let Some(recipe) = layer.coefficients.get(bank_index) else { continue };
        let Some((immediate, core)) = factor(recipe) else { continue };
        by_core.entry(core).or_default().push((term.id(), immediate));
    }

    // 2. Keep only multi-member cores; chop at `GROUP_SPLIT_MAX_MEMBERS` into even
    //    chunks of whole members, ascending `TermId` (§4.2).
    let mut proto_groups: Vec<(NormalizedCoefficientRecipe, Vec<(TermId, u32)>)> = Vec::new();
    for (core, mut members) in by_core {
        if members.len() < 2 {
            continue;
        }
        members.sort_unstable_by_key(|(term, _)| *term);
        let chunks = members.len().div_ceil(GROUP_SPLIT_MAX_MEMBERS);
        let base = members.len() / chunks;
        let extra = members.len() % chunks; // the first `extra` chunks get base+1
        let mut start = 0;
        for chunk in 0..chunks {
            let len = base + usize::from(chunk < extra);
            proto_groups.push((core.clone(), members[start..start + len].to_vec()));
            start += len;
        }
    }
    // Deterministic atom-key order: ascending minimum member `TermId`, which is
    // unique because the chunks partition the terms.
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
        return Err(CoeffError::ImmediateTableOverflow { len: immediates.len() });
    }
    let immediate_id = |value: u32| -> ImmediateId {
        if value == one {
            return ImmediateId::ONE;
        }
        if value == minus_one {
            return ImmediateId::NEG_ONE;
        }
        ImmediateId::banked(
            immediates.binary_search(&value).expect("every member immediate is in the table"),
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

#[cfg(test)]
mod tests {
    use cs::gkr_compiler::dag_ir::{
        ChallengeKey, ChallengePower, ChallengeRef, FieldKind, ReadPlace,
    };

    use super::*;
    use crate::bwd::coeff::model::{
        CoeffChallenge, CoeffProduct, CoeffSource, NormalizedCoefficientRecipe, ProjectionId,
        SourceId,
    };
    use crate::bwd::source::OriginLeaf;

    /// One challenge factor in canonical spelling. `LookupAdditive` (`gamma`) sorts
    /// before `PermutationAdditive` (`delta`) in the crate's factor order.
    fn gamma() -> CoeffChallenge {
        CoeffChallenge::new(ChallengeRef {
            key: ChallengeKey::LookupAdditive,
            power: ChallengePower::One,
        })
    }

    fn delta() -> CoeffChallenge {
        CoeffChallenge::new(ChallengeRef {
            key: ChallengeKey::PermutationAdditive,
            power: ChallengePower::One,
        })
    }

    fn product(scalar: u32, challenges: Vec<CoeffChallenge>) -> CoeffProduct {
        CoeffProduct { scalar, challenges }
    }

    /// `scalar_a * gamma + scalar_b * gamma * delta`.
    fn two_product(scalar_a: u32, scalar_b: u32) -> NormalizedCoefficientRecipe {
        NormalizedCoefficientRecipe::from_terms(vec![
            product(scalar_a, vec![gamma()]),
            product(scalar_b, vec![gamma(), delta()]),
        ])
    }

    #[test]
    fn factor_round_trip_rescales_back_to_the_original() {
        // 3*gamma + 6*gamma*delta  ->  imm = 3, core = gamma + 2*gamma*delta
        let recipe = two_product(3, 6);
        let (imm, core) = factor(&recipe).expect("a two-product recipe factors");
        assert_eq!(imm, 3, "the immediate is the leading product's scalar");
        assert_eq!(core.terms[0].scalar, 1, "the core's leading scalar is one");
        assert_eq!(core, two_product(1, 2));
        assert_eq!(rescale(&core, imm), recipe, "imm * core is the original recipe");
    }

    #[test]
    fn bare_scalars_do_not_factor() {
        assert_eq!(factor(&NormalizedCoefficientRecipe::scalar(bf(3))), None);
        assert_eq!(factor(&NormalizedCoefficientRecipe::one()), None);
        assert_eq!(factor(&NormalizedCoefficientRecipe::neg_one()), None);
    }

    /// An additive-identity recipe is never encoded, so it never groups either.
    #[test]
    fn the_zero_recipe_does_not_factor() {
        assert_eq!(factor(&NormalizedCoefficientRecipe::zero()), None);
    }

    /// Factoring is idempotent: a core factors to itself with immediate one, which
    /// is what makes the group key stable under repeated application.
    #[test]
    fn factoring_a_core_is_the_identity() {
        let (imm, core) = factor(&two_product(3, 6)).expect("factors");
        let (again_imm, again_core) = factor(&core).expect("a core still factors");
        assert_eq!((again_imm, again_core), (1, core.clone()));
        assert_eq!(imm, 3);
    }

    /// A single-product recipe that carries challenges DOES factor — its core is a
    /// challenge monomial, not the trivial core.
    #[test]
    fn a_single_product_with_challenges_factors() {
        let recipe = NormalizedCoefficientRecipe::from_terms(vec![product(5, vec![gamma()])]);
        let (imm, core) = factor(&recipe).expect("a challenge monomial factors");
        assert_eq!(imm, 5);
        assert_eq!(core, NormalizedCoefficientRecipe::from_terms(vec![product(1, vec![gamma()])]));
        assert_eq!(rescale(&core, imm), recipe);
    }

    // ── The transform ────────────────────────────────────────────────────────

    const SOURCES: usize = 4;

    #[derive(Clone, Copy)]
    enum Kind {
        C0,
        C2,
        Dual,
    }

    /// An `Ext` layer whose term `i` uses `recipes[spec[i].0]` as its coefficient
    /// (`None` = the `+1` literal) and has kind `spec[i].1`.
    ///
    /// The bank is deduplicated and SORTED, exactly as `lower_coeff_layer` builds
    /// it, so the ids the terms carry are the ones a real lowered layer would.
    fn ext_layer(
        recipes: &[NormalizedCoefficientRecipe],
        spec: &[(Option<usize>, Kind)],
    ) -> CoeffLayer {
        let bank: Vec<NormalizedCoefficientRecipe> =
            recipes.iter().cloned().collect::<BTreeSet<_>>().into_iter().collect();
        let terms = spec
            .iter()
            .enumerate()
            .map(|(index, (recipe, kind))| {
                let id = TermId(index as u32);
                let coefficient = match recipe {
                    None => CoefficientRecipeId::ONE,
                    Some(which) => CoefficientRecipeId::from_bank_index(
                        bank.binary_search(&recipes[*which]).expect("the bank holds every recipe"),
                    ),
                };
                let a = SourceId((index % SOURCES) as u32);
                let b = SourceId(((index + 1) % SOURCES) as u32);
                match kind {
                    Kind::C0 => CoeffTerm::C0Linear {
                        id,
                        coefficient,
                        value: ProjectionId::endpoint0(a),
                        field: FieldKind::Ext,
                    },
                    Kind::C2 => CoeffTerm::C2Product {
                        id,
                        coefficient,
                        lhs: ProjectionId::delta(a),
                        rhs: ProjectionId::delta(b),
                        lhs_field: FieldKind::Ext,
                        rhs_field: FieldKind::Ext,
                    },
                    Kind::Dual => CoeffTerm::DualProduct { id, coefficient, lhs: a, rhs: b },
                }
            })
            .collect();
        CoeffLayer {
            regime: BwdRegime::Ext,
            c_init: None,
            coefficients: bank,
            sources: (0..SOURCES)
                .map(|column| CoeffSource {
                    origin: OriginLeaf::Read(ReadPlace::BaseLayerWitness { column }),
                    field: FieldKind::Ext,
                })
                .collect(),
            terms,
            groups: Vec::new(),
            immediates: Vec::new(),
        }
    }

    fn bank_id(layer: &CoeffLayer, recipe: &NormalizedCoefficientRecipe) -> CoefficientRecipeId {
        CoefficientRecipeId::from_bank_index(
            layer.coefficients.binary_search(recipe).expect("the bank holds the recipe"),
        )
    }

    fn sorted(recipes: &[NormalizedCoefficientRecipe]) -> Vec<NormalizedCoefficientRecipe> {
        recipes.iter().cloned().collect::<BTreeSet<_>>().into_iter().collect()
    }

    /// `scalar * gamma + 2 * scalar * gamma * delta` — one family whose whole
    /// membership shares the core `gamma + 2*gamma*delta`, so the immediate is the
    /// only thing that varies.
    fn family(scalar: u32) -> NormalizedCoefficientRecipe {
        // The doubling is a FIELD double, so `family(-1)` is representable too.
        let mut doubled = bf(scalar);
        let same = doubled;
        doubled.add_assign(&same);
        two_product(scalar, doubled.as_u32_reduced())
    }

    fn core_of_family() -> NormalizedCoefficientRecipe {
        two_product(1, 2)
    }

    #[test]
    fn groups_form_only_from_two_plus_members_sharing_a_core() {
        // Terms 0/1 share the family core; term 2 has its own core; term 3 is a
        // bare scalar; term 4 is the `+1` literal.
        let other = two_product(7, 7);
        let bare = NormalizedCoefficientRecipe::scalar(bf(9));
        let recipes = [family(3), family(5), other.clone(), bare.clone()];
        let layer = ext_layer(
            &recipes,
            &[
                (Some(0), Kind::C0),
                (Some(1), Kind::C0),
                (Some(2), Kind::C0),
                (Some(3), Kind::C0),
                (None, Kind::C0),
            ],
        );
        let grouped = group_coeff_layer(layer).expect("grouping succeeds");

        assert_eq!(grouped.groups.len(), 1, "only the two-member core groups");
        let group = &grouped.groups[0];
        assert_eq!(
            group.members,
            vec![
                CoeffGroupMember { term: TermId(0), immediate: ImmediateId::banked(0) },
                CoeffGroupMember { term: TermId(1), immediate: ImmediateId::banked(1) },
            ]
        );
        assert_eq!((group.has_c0, group.has_c2), (true, false), "C0Linear members only");
        assert_eq!(grouped.immediates, vec![3, 5], "deduped, ascending, no ±1 entry");
        assert_eq!(grouped.banked_recipe(group.core), Some(&core_of_family()));

        // The three non-members keep their own coefficients, and the two member
        // recipes are gone from the bank.
        assert_eq!(
            grouped.coefficients,
            sorted(&[core_of_family(), other.clone(), bare.clone()]),
            "member recipes are dropped; core + singletons remain"
        );
        assert_eq!(grouped.banked_recipe(grouped.terms[2].coefficient()), Some(&other));
        assert_eq!(grouped.banked_recipe(grouped.terms[3].coefficient()), Some(&bare));
        assert_eq!(
            grouped.terms[4].coefficient(),
            CoefficientRecipeId::ONE,
            "a literal coefficient is left be"
        );

        // The transform touches NOTHING else.
        assert_eq!(grouped.terms.len(), 5);
        assert_eq!(grouped.sources.len(), SOURCES);
        assert_eq!(
            grouped.terms.iter().map(|t| t.id()).collect::<Vec<_>>(),
            (0..5).map(TermId).collect::<Vec<_>>()
        );
    }

    /// A group's `has_c0` / `has_c2` is the UNION over its members' term kinds
    /// (§4.4) — that is what tells the kernel which accumulator sides the one core
    /// multiplication feeds.
    #[test]
    fn group_sides_are_the_union_over_member_kinds() {
        let recipes = [family(3), family(5), family(7)];
        let all_kinds = ext_layer(
            &recipes,
            &[(Some(0), Kind::C0), (Some(1), Kind::C2), (Some(2), Kind::Dual)],
        );
        let grouped = group_coeff_layer(all_kinds).expect("grouping succeeds");
        assert_eq!(grouped.groups.len(), 1);
        assert_eq!((grouped.groups[0].has_c0, grouped.groups[0].has_c2), (true, true));

        let c2_only =
            ext_layer(&recipes[..2], &[(Some(0), Kind::C2), (Some(1), Kind::C2)]);
        let grouped = group_coeff_layer(c2_only).expect("grouping succeeds");
        assert_eq!((grouped.groups[0].has_c0, grouped.groups[0].has_c2), (false, true));
    }

    #[test]
    fn chop_splits_seventeen_members_into_nine_and_eight() {
        let recipes: Vec<NormalizedCoefficientRecipe> = (2..19).map(family).collect();
        assert_eq!(recipes.len(), 17);
        let spec: Vec<(Option<usize>, Kind)> =
            (0..17).map(|index| (Some(index), Kind::C0)).collect();
        let grouped = group_coeff_layer(ext_layer(&recipes, &spec)).expect("grouping succeeds");

        assert_eq!(grouped.groups.len(), 2, "17 > GROUP_SPLIT_MAX_MEMBERS chops in two");
        assert_eq!(
            grouped.groups.iter().map(|g| g.members.len()).collect::<Vec<_>>(),
            vec![9, 8],
            "even chunks of whole members, the first taking the remainder"
        );
        // Ascending TermId, contiguous, no member lost or duplicated.
        let members: Vec<TermId> =
            grouped.groups.iter().flat_map(|g| g.members.iter().map(|m| m.term)).collect();
        assert_eq!(members, (0..17).map(TermId).collect::<Vec<_>>());
        // Both chunks are the SAME core — one bank entry, two atoms.
        assert_eq!(grouped.groups[0].core, grouped.groups[1].core);
        assert_eq!(grouped.coefficients, vec![core_of_family()], "every original collapses");
        assert_eq!(grouped.immediates, (2..19).collect::<Vec<u32>>());
    }

    #[test]
    fn member_coefficients_are_rewritten_to_the_core_id() {
        let recipes: Vec<NormalizedCoefficientRecipe> = (2..19).map(family).collect();
        let spec: Vec<(Option<usize>, Kind)> =
            (0..17).map(|index| (Some(index), Kind::C0)).collect();
        let layer = ext_layer(&recipes, &spec);
        let originals: Vec<NormalizedCoefficientRecipe> = layer
            .terms
            .iter()
            .map(|t| layer.banked_recipe(t.coefficient()).expect("banked").clone())
            .collect();
        let grouped = group_coeff_layer(layer).expect("grouping succeeds");

        let mut seen = 0;
        for group in &grouped.groups {
            let core = grouped.banked_recipe(group.core).expect("a core is a live bank entry");
            for member in &group.members {
                let term = &grouped.terms[member.term.0 as usize];
                assert_eq!(term.coefficient(), group.core, "member points at its core");
                let immediate =
                    immediate_value(&grouped, member.immediate).expect("immediate in range");
                assert_eq!(
                    rescale(core, immediate),
                    originals[member.term.0 as usize],
                    "core * immediate reproduces the member's original recipe exactly"
                );
                seen += 1;
            }
        }
        assert_eq!(seen, 17, "every term is a member of exactly one group");
    }

    /// §4.1: `c_init` is excluded from grouping, so its bank entry survives even
    /// when every TERM that shared that recipe was rewritten to a core.
    #[test]
    fn c_init_recipe_survives_even_when_all_its_terms_group() {
        let recipes = [family(3), family(5)];
        let mut layer = ext_layer(&recipes, &[(Some(0), Kind::C0), (Some(1), Kind::C0)]);
        layer.c_init = Some(bank_id(&layer, &recipes[0]));
        let grouped = group_coeff_layer(layer).expect("grouping succeeds");

        assert_eq!(grouped.groups.len(), 1);
        assert_eq!(grouped.groups[0].members.len(), 2, "both terms still group");
        assert_eq!(
            grouped.coefficients,
            sorted(&[core_of_family(), family(3)]),
            "family(3) is retained for c_init, family(5) is dropped"
        );
        let c_init = grouped.c_init.expect("c_init survives");
        assert_eq!(grouped.banked_recipe(c_init), Some(&family(3)), "c_init keeps its own recipe");
        assert_ne!(c_init, grouped.groups[0].core, "c_init is not rewritten to a core");
    }

    #[test]
    fn bank_stays_sorted_and_ids_resolve() {
        let bare = NormalizedCoefficientRecipe::scalar(bf(9));
        let recipes = [family(3), family(5), family(7), two_product(7, 7), bare];
        let mut layer = ext_layer(
            &recipes,
            &[
                (Some(0), Kind::C0),
                (Some(1), Kind::Dual),
                (Some(2), Kind::C2),
                (Some(3), Kind::C0),
                (Some(4), Kind::C0),
                (None, Kind::C0),
            ],
        );
        layer.c_init = Some(bank_id(&layer, &recipes[3]));
        let grouped = group_coeff_layer(layer).expect("grouping succeeds");

        assert!(
            grouped.coefficients.windows(2).all(|w| w[0] < w[1]),
            "the rebuilt bank is strictly ascending — sorted and deduplicated"
        );
        assert!(!grouped.coefficients.is_empty());
        for term in &grouped.terms {
            let id = term.coefficient();
            match id.bank_index() {
                None => assert!(id.literal().is_some(), "a reserved id is a literal"),
                Some(_) => assert!(grouped.banked_recipe(id).is_some(), "{id:?} dangles"),
            }
        }
        assert!(grouped.banked_recipe(grouped.c_init.expect("c_init")).is_some());
        assert!(!grouped.groups.is_empty(), "this layer really does group");
        for group in &grouped.groups {
            assert!(group.core.bank_index().is_some(), "a core is never a literal id");
            assert!(grouped.banked_recipe(group.core).is_some());
            for member in &group.members {
                assert!(immediate_value(&grouped, member.immediate).is_some());
            }
        }
    }

    #[test]
    fn immediates_are_deduped_ascending_and_capped() {
        // Two distinct immediates over four members: the table holds each once.
        let recipes = [family(7), family(3)];
        let spec = [
            (Some(0), Kind::C0),
            (Some(1), Kind::C0),
            (Some(0), Kind::C0),
            (Some(1), Kind::C0),
        ];
        let grouped = group_coeff_layer(ext_layer(&recipes, &spec)).expect("grouping succeeds");
        assert_eq!(grouped.immediates, vec![3, 7], "deduplicated and ascending");
        assert_eq!(
            grouped.groups[0].members.iter().map(|m| m.immediate).collect::<Vec<_>>(),
            vec![
                ImmediateId::banked(1),
                ImmediateId::banked(0),
                ImmediateId::banked(1),
                ImmediateId::banked(0),
            ],
            "ids address the deduplicated table, not the member order"
        );

        // One more distinct immediate than the wire's table holds.
        let over = LEAN_MAX_IMMEDIATES + 1;
        let recipes: Vec<NormalizedCoefficientRecipe> =
            (2..(over as u32 + 2)).map(family).collect();
        assert_eq!(recipes.len(), over);
        let spec: Vec<(Option<usize>, Kind)> =
            (0..over).map(|index| (Some(index), Kind::C0)).collect();
        assert_eq!(
            group_coeff_layer(ext_layer(&recipes, &spec)),
            Err(CoeffError::ImmediateTableOverflow { len: over })
        );
    }

    /// `±1` immediates are the two RESERVED ids and consume no table entry (§4.4).
    #[test]
    fn plus_and_minus_one_immediates_consume_no_table_entry() {
        let recipes = [family(1), family(neg_one()), family(5)];
        let spec = [(Some(0), Kind::C0), (Some(1), Kind::C0), (Some(2), Kind::C0)];
        let grouped = group_coeff_layer(ext_layer(&recipes, &spec)).expect("grouping succeeds");
        assert_eq!(grouped.immediates, vec![5], "only the non-±1 immediate is banked");
        assert_eq!(
            grouped.groups[0].members.iter().map(|m| m.immediate).collect::<Vec<_>>(),
            vec![ImmediateId::ONE, ImmediateId::NEG_ONE, ImmediateId::banked(0)]
        );
        assert_eq!(immediate_value(&grouped, ImmediateId::ONE), Some(1));
        assert_eq!(immediate_value(&grouped, ImmediateId::NEG_ONE), Some(neg_one()));
    }

    #[test]
    fn r0_layers_pass_through_untouched() {
        let recipes = [family(3), family(5)];
        let mut layer = ext_layer(&recipes, &[(Some(0), Kind::C0), (Some(1), Kind::C0)]);
        layer.regime = BwdRegime::R0;
        let before = layer.clone();
        assert_eq!(group_coeff_layer(layer), Ok(before), "R0 never groups (§4.1)");
    }

    #[test]
    fn transform_is_deterministic() {
        let recipes: Vec<NormalizedCoefficientRecipe> =
            (2..40).map(family).chain([two_product(7, 7), two_product(11, 11)]).collect();
        let spec: Vec<(Option<usize>, Kind)> = (0..recipes.len())
            .map(|index| {
                let kind = match index % 3 {
                    0 => Kind::C0,
                    1 => Kind::C2,
                    _ => Kind::Dual,
                };
                (Some(index), kind)
            })
            .collect();
        let layer = ext_layer(&recipes, &spec);
        let first = group_coeff_layer(layer.clone()).expect("grouping succeeds");
        let second = group_coeff_layer(layer).expect("grouping succeeds");
        assert_eq!(first, second, "grouping is a pure function of the layer");
        assert!(first.groups.len() >= 3, "this layer exercises the chop and two singletons");
    }
}
