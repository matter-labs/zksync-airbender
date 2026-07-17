//! Backward fragment decomposition (CS-M5a Task 1, spec §3): the pure,
//! side-effect-free walk that decomposes a backward alpha-spine's addends
//! into FRAGMENTS — `acc = c_init + Σ recipe_i · value(fragment_i)` — so a
//! later stage (Task 2+) can lower each fragment's value once and its
//! summed coefficient recipe cheaply.
//!
//! Ported from the proven reference classifier
//! `.agents/experiments/2026-07-13-bwd-order-eviction/wsdump/src/bin/fragclass.rs`
//! (`analyze()`), adapted to build the real IR (not just stats) over this
//! crate's distilled-arena types ([`DagLayer`]/[`Expr`]/[`ExprId`]).
//!
//! Normative walk semantics:
//!  1. `scalar_pure` is a bottom-up per-expr flag: `Constant`/`Challenge`
//!     leaves are scalar-pure; an `Add`/`Mul` is scalar-pure iff every child
//!     is. `VirtualSetup` and every other `Source` kind (`Read`,
//!     `LookupValue`) are NEVER scalar-pure, regardless of shape.
//!  2. The spine addends are walked with an `(id, chain)` stack, `chain`
//!     being the accumulated scalar-pure factors seen so far (a
//!     [`ProductRecipe`] in progress):
//!       - `id` scalar-pure -> its value (chain ++ id) is a [`C_init`]
//!         contribution (`c_init` field).
//!       - `Add(children)` -> push every child with the SAME chain
//!         (occurrences are NEVER deduped — `A + A` walks `A` twice).
//!       - `Mul(_)` -> FLATTEN the whole Mul-nest first (scalar-pure
//!         factors at any depth are absorbed into the chain; non-scalar
//!         factors become sorted value atoms). If exactly one non-scalar
//!         atom remains AND it is an `Add`, DISTRIBUTE (push its children
//!         with the enriched chain, linearizing `c·(x+y) = c·x + c·y`).
//!         Otherwise, emit one fragment occurrence keyed by the sorted
//!         atom multiset (no distribution inside multi-atom products, even
//!         if one atom happens to be an `Add`).
//!       - bare non-scalar `Source` -> emit a singleton-atom fragment
//!         occurrence.
//!  3. Occurrences are merged by their sorted `atoms` (the fragment's value
//!     key): each occurrence appends its chain as one term of the
//!     fragment's [`MergedRecipe`] (sum of products; never collapsed —
//!     `A + A` yields ONE fragment with TWO empty-factor terms, not a
//!     single doubled term).
//!  4. [`MergedRecipe::is_trivial`] holds iff the recipe is exactly the
//!     scalar `1` (one term, no factors).
//!
//! [`C_init`]: FragmentTable::c_init

use std::collections::BTreeMap;

use cs::gkr_compiler::dag_ir::{
    eval_layer_expr, ChallengeKey, ChallengePower, ChallengeRef, DagLayer, Expr, ExprId, Ext,
    PermutationSlot, Resolvers, SourceKind,
};
use field::Field;

use super::distill::{DistilledLayer, StableBwdExprKey};

// ── Recipe / fragment types ──────────────────────────────────────────────────

/// A product of scalar-pure distilled expressions (`Constant`/`Challenge`
/// leaves, or Add/Mul closures thereof — see module docs). Empty = the
/// multiplicative identity `1`.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct ProductRecipe {
    pub factors: Vec<ExprId>,
}

/// A sum of [`ProductRecipe`] terms (`Σ Π factors`). Empty = the additive
/// identity `0`. Terms are never merged/collapsed across occurrences: two
/// identical unit ("1") terms stay two terms, not one term "2" (see
/// `repeated_operands_keep_multiplicity` below).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MergedRecipe {
    pub terms: Vec<ProductRecipe>,
}

impl MergedRecipe {
    /// `true` iff this recipe is exactly the scalar `1`: one term, no
    /// factors.
    pub fn is_trivial(&self) -> bool {
        self.terms.len() == 1 && self.terms[0].factors.is_empty()
    }

    /// Evaluate this coefficient recipe to the Ext element the backward interp
    /// serves for a `Coefficient`/`AccInit` descriptor: `Σ` over terms of `Π`
    /// over factors of `eval_layer_expr(layer, factor, 0, r)`.
    ///
    /// An empty recipe (no terms) is the additive identity `0`; a term with no
    /// factors is the multiplicative identity `1` (so a single empty-factor term
    /// evaluates to `1`, two of them to `2`, matching the never-collapsed
    /// multiplicity of the walk). Factors are scalar-pure `Constant`/`Challenge`
    /// nests (see the module walk), so the row index is irrelevant and pinned to
    /// `0`; the result is row- and role-invariant.
    pub fn evaluate(&self, layer: &DagLayer, r: &Resolvers<'_>) -> Ext {
        let mut sum = Ext::ZERO;
        for term in &self.terms {
            let mut prod = Ext::ONE;
            for &factor in &term.factors {
                prod.mul_assign(&eval_layer_expr(layer, factor, 0, r));
            }
            sum.add_assign(&prod);
        }
        sum
    }
}

/// One backward fragment: a non-scalar value (`atoms`, sorted ascending —
/// either a single Source/Add root, or the sorted factor multiset of an
/// opaque multi-atom product) paired with the summed coefficient recipe it
/// is read under, across every additive occurrence found in the spine.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FragmentSpec {
    pub atoms: Vec<ExprId>,
    pub recipe: MergedRecipe,
}

/// The full decomposition of a backward spine:
/// `acc = c_init + Σ_i fragments[i].recipe · value(fragments[i].atoms)`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FragmentTable {
    pub fragments: Vec<FragmentSpec>,
    pub c_init: MergedRecipe,
}

// ── Stable (order-independent) views ──────────────────────────────────────────

/// Order-independent identity of one coefficient factor in a fragment / `c_init`
/// recipe. Distilled `ExprId`s depend on relation-unit order, so a factor is
/// projected to its distilled-expr provenance ([`FactorKey::Expr`]) when it has
/// one. The alpha-batching beta powers distill SYNTHESIZES have no provenance
/// entry (`distill` :176-182), so they fall back STRUCTURALLY: a synthesized
/// `Challenge` leaf keeps its stable [`ChallengeRef`]; a `Constant` its interned
/// value. Both fallbacks read a value-stable handle from the Source node, never
/// an order-dependent arena index.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum FactorKey {
    Challenge(ChallengeRef),
    Constant(u32),
    Expr(StableBwdExprKey),
}

impl Ord for FactorKey {
    // `ChallengeRef` (and its `ChallengeKey`/`ChallengePower`) are not `Ord`, so
    // project each variant to a fully-ordered, injective tuple. The order itself
    // is arbitrary but total + deterministic — it exists only to CANONICALIZE the
    // factor lists so two runs compare equal.
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        fn rank(k: &FactorKey) -> u8 {
            match k {
                FactorKey::Challenge(_) => 0,
                FactorKey::Constant(_) => 1,
                FactorKey::Expr(_) => 2,
            }
        }
        match (self, other) {
            (FactorKey::Challenge(a), FactorKey::Challenge(b)) => {
                challenge_ord(a).cmp(&challenge_ord(b))
            }
            (FactorKey::Constant(a), FactorKey::Constant(b)) => a.cmp(b),
            (FactorKey::Expr(a), FactorKey::Expr(b)) => a.cmp(b),
            _ => rank(self).cmp(&rank(other)),
        }
    }
}

impl PartialOrd for FactorKey {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Injective, fully-ordered projection of a `ChallengeRef` (see [`FactorKey`]'s
/// `Ord`).
fn challenge_ord(r: &ChallengeRef) -> (u8, u8, u8, u32) {
    let (key_tag, key_sub) = match &r.key {
        ChallengeKey::LookupAdditive => (0u8, 0u8),
        ChallengeKey::LookupMultiplicative => (1, 0),
        ChallengeKey::PermutationAdditive => (2, 0),
        ChallengeKey::PermutationLinearization(slot) => (3, perm_slot_ord(slot)),
        ChallengeKey::ConstraintAggregation => (4, 0),
        ChallengeKey::ClaimBatching => (5, 0),
    };
    let (power_tag, power_val) = match &r.power {
        ChallengePower::One => (0u8, 0u32),
        ChallengePower::Static(i) => (1, *i),
    };
    (key_tag, key_sub, power_tag, power_val)
}

fn perm_slot_ord(slot: &PermutationSlot) -> u8 {
    match slot {
        PermutationSlot::AddressLow => 0,
        PermutationSlot::AddressHigh => 1,
        PermutationSlot::TimestampLow => 2,
        PermutationSlot::TimestampHigh => 3,
        PermutationSlot::ValueLow => 4,
        PermutationSlot::ValueHigh => 5,
    }
}

impl FragmentTable {
    /// Project every fragment to `(atoms → stable keys, recipe terms → factor-key
    /// lists)` — the ONLY cross-run comparison surface, since no raw distilled
    /// `ExprId` leaks. Fragment ATOMS are non-scalar reinterned canonical values
    /// and MUST carry provenance (a miss is a distillation bug and panics with
    /// context); recipe FACTORS fall back structurally for synthesized beta powers.
    ///
    /// The raw `atoms` / factor lists / recipe terms are sorted by DISTILLED
    /// `ExprId` (which is unit-order dependent), so this CANONICALIZES every level
    /// — atoms by stable key, factors within a term, terms within a recipe — so
    /// that the projection is a deterministic function of the layer's VALUE alone.
    /// Fragment-level ordering is still traversal-order dependent; compare the
    /// returned `Vec` as a multiset (or sort it) across runs.
    pub fn stable_view(
        &self,
        d: &DistilledLayer,
    ) -> Vec<(Vec<StableBwdExprKey>, Vec<Vec<FactorKey>>)> {
        self.fragments
            .iter()
            .map(|f| {
                let mut atoms: Vec<StableBwdExprKey> =
                    f.atoms.iter().map(|&a| atom_key(d, a)).collect();
                atoms.sort();
                (atoms, recipe_factor_keys(d, &f.recipe))
            })
            .collect()
    }

    /// The `c_init` recipe as order-independent factor-key term lists (one inner
    /// `Vec` per additive term; duplicates preserved — compare as a MULTISET, not
    /// a set, so `A + A`-style repeated units stay two entries). Canonicalized the
    /// same way as [`stable_view`](FragmentTable::stable_view).
    pub fn stable_c_init(&self, d: &DistilledLayer) -> Vec<Vec<FactorKey>> {
        recipe_factor_keys(d, &self.c_init)
    }
}

/// Each recipe term's factors projected to [`FactorKey`]s, then CANONICALIZED:
/// factors sorted within a term, terms sorted across the recipe (multiplicity
/// preserved — this is a multiset canonicalization, never a dedup).
fn recipe_factor_keys(d: &DistilledLayer, recipe: &MergedRecipe) -> Vec<Vec<FactorKey>> {
    let mut terms: Vec<Vec<FactorKey>> = recipe
        .terms
        .iter()
        .map(|t| {
            let mut factors: Vec<FactorKey> = t.factors.iter().map(|&e| factor_key(d, e)).collect();
            factors.sort();
            factors
        })
        .collect();
    terms.sort();
    terms
}

/// Stable identity of a fragment ATOM. Every atom is a non-scalar reinterned
/// canonical value, so it always carries distilled provenance — a miss is a
/// distillation bug (not a synthesized-leaf case), so panic with context.
fn atom_key(d: &DistilledLayer, atom: ExprId) -> StableBwdExprKey {
    d.stable_key(atom).unwrap_or_else(|| {
        panic!(
            "fragment atom {atom:?} lacks stable provenance (node {:?}); atoms must always be \
             reinterned canonical values",
            d.layer.exprs[atom.0 as usize]
        )
    })
}

/// Stable identity of a coefficient FACTOR. Prefers distilled provenance; falls
/// back to the Source node for the synthesized beta powers (`distill` :176-182),
/// reading a value-stable handle (constant value / challenge reference).
fn factor_key(d: &DistilledLayer, factor: ExprId) -> FactorKey {
    if let Some(key) = d.stable_key(factor) {
        return FactorKey::Expr(key);
    }
    match &d.layer.exprs[factor.0 as usize] {
        Expr::Source(sid) => match &d.layer.sources[sid.0 as usize].kind {
            SourceKind::Constant { value } => FactorKey::Constant(*value),
            SourceKind::Challenge { reference } => FactorKey::Challenge(reference.clone()),
            other => panic!(
                "factor {factor:?} has no stable provenance and is not a Constant/Challenge \
                 source (kind {other:?})"
            ),
        },
        other => panic!(
            "factor {factor:?} has no stable provenance and is not a source leaf (node {other:?})"
        ),
    }
}

// ── decompose_spine ───────────────────────────────────────────────────────────

/// Decompose `spine` (the addend roots of a backward alpha-spine, or any
/// list of expr roots over `layer`) into a [`FragmentTable`] per the
/// normative walk documented above.
pub fn decompose_spine(layer: &DagLayer, spine: &[ExprId]) -> FragmentTable {
    let exprs = &layer.exprs;
    let sources = &layer.sources;

    // 1. Bottom-up scalar-purity. `exprs` is arena order (children always
    // intern before parents), so a single forward pass suffices.
    let mut scalar_pure = vec![false; exprs.len()];
    for (i, expr) in exprs.iter().enumerate() {
        scalar_pure[i] = match expr {
            Expr::Source(s) => matches!(
                sources[s.0 as usize].kind,
                SourceKind::Constant { .. } | SourceKind::Challenge { .. }
            ),
            Expr::Add(ch) | Expr::Mul(ch) => ch.iter().all(|c| scalar_pure[c.0 as usize]),
        };
    }
    let is_pure = |id: ExprId| scalar_pure[id.0 as usize];

    // 2. Multiplicative flatten of the Mul-nest rooted at `root`: scalar-pure
    // subterms (any depth) are absorbed as coefficient factors; everything
    // else becomes a sorted value atom. Add nodes reached here are NOT
    // descended into (they become opaque atoms, possibly re-examined by the
    // distribute check below).
    let flatten = |root: ExprId| -> (Vec<ExprId>, Vec<ExprId>) {
        let mut atoms = Vec::new();
        let mut absorbed = Vec::new();
        let mut stack = vec![root];
        while let Some(id) = stack.pop() {
            if is_pure(id) {
                absorbed.push(id);
                continue;
            }
            match &exprs[id.0 as usize] {
                Expr::Mul(ch) => stack.extend(ch.iter().copied()),
                _ => atoms.push(id),
            }
        }
        atoms.sort();
        (atoms, absorbed)
    };

    // 3. Unified walk over the spine addends.
    let mut frags: Vec<(Vec<ExprId>, Vec<ExprId>)> = Vec::new();
    let mut c_init_terms: Vec<ProductRecipe> = Vec::new();
    let mut occurrences: usize = 0;
    // Final-review T1-M1: this single shared `(id, chain)` stack is semantically
    // equivalent to the reference classifier's per-term stack (one stack per spine
    // addend) — LIFO popping never interleaves chains across addends, since each
    // pushed entry carries its own complete `chain` snapshot.
    let mut work: Vec<(ExprId, Vec<ExprId>)> = spine.iter().map(|&t| (t, Vec::new())).collect();
    while let Some((id, chain)) = work.pop() {
        if is_pure(id) {
            let mut factors = chain;
            factors.push(id);
            factors.sort();
            c_init_terms.push(ProductRecipe { factors });
            occurrences += 1;
            assert!(occurrences < 100_000, "fragment decomposition occurrence guard exceeded");
            continue;
        }
        match &exprs[id.0 as usize] {
            Expr::Add(ch) => {
                for &c in ch {
                    work.push((c, chain.clone()));
                }
            }
            Expr::Mul(_) => {
                let (atoms, absorbed) = flatten(id);
                let mut enriched = chain;
                enriched.extend(absorbed);
                if atoms.len() == 1 && matches!(&exprs[atoms[0].0 as usize], Expr::Add(_)) {
                    // Linearize c·(x+y) = c·x + c·y: distribute into the
                    // single non-scalar Add atom with the enriched chain.
                    work.push((atoms[0], enriched));
                } else {
                    enriched.sort();
                    frags.push((atoms, enriched));
                    occurrences += 1;
                    assert!(
                        occurrences < 100_000,
                        "fragment decomposition occurrence guard exceeded"
                    );
                }
            }
            Expr::Source(_) => {
                let mut sig = chain;
                sig.sort();
                frags.push((vec![id], sig));
                occurrences += 1;
                assert!(occurrences < 100_000, "fragment decomposition occurrence guard exceeded");
            }
        }
    }

    // 4. Merge occurrences by sorted `atoms` (the value key); each
    // occurrence appends its chain as one MergedRecipe term.
    let mut merged: BTreeMap<Vec<ExprId>, Vec<ProductRecipe>> = BTreeMap::new();
    for (atoms, chain) in frags {
        merged.entry(atoms).or_default().push(ProductRecipe { factors: chain });
    }
    let fragments = merged
        .into_iter()
        .map(|(atoms, terms)| FragmentSpec { atoms, recipe: MergedRecipe { terms } })
        .collect();

    FragmentTable { fragments, c_init: MergedRecipe { terms: c_init_terms } }
}

// ── Tests ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use cs::gkr_compiler::dag_ir::{
        BatchingOrder, Bf, ChallengeKey, ChallengePower, ChallengeRef, ChallengeResolver,
        LookupResolver, LookupValueKind, ReadPlace, ReadResolver, Resolvers, SourceId, SourceInfo,
        VirtualSetupKind, VirtualSetupResolver,
    };
    use field::{Field, FieldExtension, PrimeField};

    // ── Fixture helpers (mirrors distill.rs's test-fixture pattern: literal
    // DagLayer construction, no separate arena-builder type) ────────────────

    fn read_src(column: usize) -> SourceInfo {
        SourceInfo { kind: SourceKind::Read { place: ReadPlace::BaseLayerWitness { column } } }
    }

    fn const_src(value: u32) -> SourceInfo {
        SourceInfo { kind: SourceKind::Constant { value } }
    }

    fn challenge_src(key: ChallengeKey) -> SourceInfo {
        SourceInfo { kind: SourceKind::Challenge { reference: ChallengeRef { key, power: ChallengePower::One } } }
    }

    fn vs_src(kind: VirtualSetupKind) -> SourceInfo {
        SourceInfo { kind: SourceKind::VirtualSetup { kind } }
    }

    /// Assembles a minimal `DagLayer` around `sources`/`exprs`; `roots`/
    /// `batching`/`resolutions` are irrelevant to `decompose_spine` (it only
    /// reads `exprs`/`sources`), so they stay empty.
    fn layer(sources: Vec<SourceInfo>, exprs: Vec<Expr>) -> DagLayer {
        DagLayer {
            sources,
            exprs,
            roots: vec![],
            batching: BatchingOrder { roots: vec![] },
            resolutions: BTreeMap::new(),
        }
    }

    #[test]
    fn distributes_scalar_coefficient_through_add() {
        // beta * (A + B) -> 2 frags, recipes [[beta]].
        let l = layer(
            vec![read_src(0), read_src(1), challenge_src(ChallengeKey::ClaimBatching)],
            vec![
                Expr::Source(SourceId(0)),             // 0 = A
                Expr::Source(SourceId(1)),             // 1 = B
                Expr::Source(SourceId(2)),             // 2 = beta
                Expr::Add(vec![ExprId(0), ExprId(1)]), // 3 = A + B
                Expr::Mul(vec![ExprId(2), ExprId(3)]), // 4 = beta * (A + B)
            ],
        );
        let table = decompose_spine(&l, &[ExprId(4)]);

        assert!(table.c_init.terms.is_empty(), "no scalar-pure addend here");
        assert_eq!(table.fragments.len(), 2, "distribution must yield exactly A and B");
        assert_eq!(table.fragments[0].atoms, vec![ExprId(0)]);
        assert_eq!(table.fragments[1].atoms, vec![ExprId(1)]);
        let expect = vec![ProductRecipe { factors: vec![ExprId(2)] }];
        assert_eq!(table.fragments[0].recipe.terms, expect);
        assert_eq!(table.fragments[1].recipe.terms, expect);
    }

    #[test]
    fn nested_scalar_products_close_recursively() {
        // ((c1*c2)*c3) * (A+B) === c * (A+B): the whole nested scalar-pure
        // coefficient tree is absorbed as ONE chain factor (the outermost
        // pure node id), never split back into its leaves.
        let l = layer(
            vec![read_src(0), read_src(1), const_src(3), const_src(5), const_src(7)],
            vec![
                Expr::Source(SourceId(0)),             // 0 = A
                Expr::Source(SourceId(1)),             // 1 = B
                Expr::Source(SourceId(2)),             // 2 = c1
                Expr::Source(SourceId(3)),             // 3 = c2
                Expr::Source(SourceId(4)),             // 4 = c3
                Expr::Mul(vec![ExprId(2), ExprId(3)]), // 5 = c1 * c2
                Expr::Mul(vec![ExprId(5), ExprId(4)]), // 6 = (c1*c2) * c3
                Expr::Add(vec![ExprId(0), ExprId(1)]), // 7 = A + B
                Expr::Mul(vec![ExprId(6), ExprId(7)]), // 8 = ((c1*c2)*c3) * (A+B)
            ],
        );
        let table = decompose_spine(&l, &[ExprId(8)]);

        assert!(table.c_init.terms.is_empty());
        assert_eq!(table.fragments.len(), 2);
        assert_eq!(table.fragments[0].atoms, vec![ExprId(0)]);
        assert_eq!(table.fragments[1].atoms, vec![ExprId(1)]);
        // Single absorbed factor = the outer nested-Mul node, not [c1,c2,c3].
        let expect = vec![ProductRecipe { factors: vec![ExprId(6)] }];
        assert_eq!(table.fragments[0].recipe.terms, expect);
        assert_eq!(table.fragments[1].recipe.terms, expect);
    }

    #[test]
    fn repeated_operands_keep_multiplicity() {
        // A + A -> 1 frag, TWO empty terms (never merged into a doubled term).
        let l = layer(
            vec![read_src(0)],
            vec![
                Expr::Source(SourceId(0)),             // 0 = A
                Expr::Add(vec![ExprId(0), ExprId(0)]), // 1 = A + A
            ],
        );
        let table = decompose_spine(&l, &[ExprId(1)]);

        assert_eq!(table.fragments.len(), 1);
        assert_eq!(table.fragments[0].atoms, vec![ExprId(0)]);
        assert_eq!(
            table.fragments[0].recipe.terms,
            vec![ProductRecipe::default(), ProductRecipe::default()],
            "two occurrences must stay two separate empty-factor terms"
        );
        assert!(
            !table.fragments[0].recipe.is_trivial(),
            "is_trivial requires EXACTLY one term, not two summed-to-1 terms"
        );
    }

    #[test]
    fn scalar_wrappers_merge_with_summed_recipes() {
        // 2*V + 3*V -> 1 frag, recipe [[2],[3]].
        let l = layer(
            vec![read_src(0), const_src(2), const_src(3)],
            vec![
                Expr::Source(SourceId(0)),             // 0 = V
                Expr::Source(SourceId(1)),             // 1 = 2
                Expr::Source(SourceId(2)),             // 2 = 3
                Expr::Mul(vec![ExprId(1), ExprId(0)]), // 3 = 2 * V
                Expr::Mul(vec![ExprId(2), ExprId(0)]), // 4 = 3 * V
                Expr::Add(vec![ExprId(3), ExprId(4)]), // 5 = 2V + 3V
            ],
        );
        let table = decompose_spine(&l, &[ExprId(5)]);

        assert_eq!(table.fragments.len(), 1);
        assert_eq!(table.fragments[0].atoms, vec![ExprId(0)]);
        let mut terms = table.fragments[0].recipe.terms.clone();
        terms.sort();
        assert_eq!(
            terms,
            vec![
                ProductRecipe { factors: vec![ExprId(1)] },
                ProductRecipe { factors: vec![ExprId(2)] },
            ]
        );
    }

    #[test]
    fn scalar_pure_addends_fold_into_c_init() {
        // Spine = [gamma, A] (two independent spine terms) -> frag {A} +
        // c_init [[gamma]].
        let l = layer(
            vec![challenge_src(ChallengeKey::ClaimBatching), read_src(0)],
            vec![
                Expr::Source(SourceId(0)), // 0 = gamma
                Expr::Source(SourceId(1)), // 1 = A
            ],
        );
        let table = decompose_spine(&l, &[ExprId(0), ExprId(1)]);

        assert_eq!(table.fragments.len(), 1);
        assert_eq!(table.fragments[0].atoms, vec![ExprId(1)]);
        assert!(table.fragments[0].recipe.is_trivial());
        assert_eq!(table.c_init.terms, vec![ProductRecipe { factors: vec![ExprId(0)] }]);
    }

    #[test]
    fn c_init_keeps_distributed_chain() {
        // c * (A + gamma), c and gamma scalar-pure, A non-scalar: distributing the
        // Mul into the Add must carry the chain `[c]` all the way to BOTH children —
        // frag {A} recipe [[c]], AND gamma's occurrence folds into c_init as the
        // FULL chain [c, gamma] (not just [gamma], and not dropped).
        let l = layer(
            vec![read_src(0), const_src(7), challenge_src(ChallengeKey::ClaimBatching)],
            vec![
                Expr::Source(SourceId(0)),             // 0 = A
                Expr::Source(SourceId(1)),             // 1 = c
                Expr::Source(SourceId(2)),             // 2 = gamma
                Expr::Add(vec![ExprId(0), ExprId(2)]), // 3 = A + gamma
                Expr::Mul(vec![ExprId(1), ExprId(3)]), // 4 = c * (A + gamma)
            ],
        );
        let table = decompose_spine(&l, &[ExprId(4)]);

        assert_eq!(table.fragments.len(), 1, "distribution must yield exactly A");
        assert_eq!(table.fragments[0].atoms, vec![ExprId(0)]);
        assert_eq!(
            table.fragments[0].recipe.terms,
            vec![ProductRecipe { factors: vec![ExprId(1)] }],
            "fragment {{A}} recipe must be [[c]]"
        );
        assert_eq!(
            table.c_init.terms.len(),
            1,
            "gamma's distributed occurrence must fold into c_init as one term"
        );
        let mut factors = table.c_init.terms[0].factors.clone();
        factors.sort();
        assert_eq!(
            factors,
            vec![ExprId(1), ExprId(2)],
            "c_init term must preserve the whole distributed chain [c, gamma], not just [gamma]"
        );
    }

    #[test]
    fn virtual_setup_is_never_scalar() {
        // VS addend alone -> singleton fragment {VS}.
        let vs_only = layer(
            vec![vs_src(VirtualSetupKind::RangeCheck16Bits)],
            vec![Expr::Source(SourceId(0))], // 0 = VS
        );
        let table = decompose_spine(&vs_only, &[ExprId(0)]);
        assert_eq!(table.fragments.len(), 1);
        assert_eq!(table.fragments[0].atoms, vec![ExprId(0)]);
        assert!(table.fragments[0].recipe.is_trivial());
        assert!(table.c_init.terms.is_empty(), "VS is never scalar-pure, never folds into c_init");

        // Mul[VS, A] -> ONE fragment over BOTH atoms (VS never absorbed as
        // a coefficient, since it is never scalar-pure).
        let vs_mul = layer(
            vec![vs_src(VirtualSetupKind::RangeCheck16Bits), read_src(0)],
            vec![
                Expr::Source(SourceId(0)),             // 0 = VS
                Expr::Source(SourceId(1)),             // 1 = A
                Expr::Mul(vec![ExprId(0), ExprId(1)]), // 2 = VS * A
            ],
        );
        let table = decompose_spine(&vs_mul, &[ExprId(2)]);
        assert_eq!(table.fragments.len(), 1);
        assert_eq!(table.fragments[0].atoms, vec![ExprId(0), ExprId(1)]);
        assert!(table.fragments[0].recipe.is_trivial());
    }

    #[test]
    fn no_distribution_inside_multi_atom_products() {
        // Mul[A, Add(B,C)] -> ONE frag {A, Add-node}, even though one atom
        // is an Add: distribution only applies when exactly ONE atom
        // remains after flattening.
        let l = layer(
            vec![read_src(0), read_src(1), read_src(2)],
            vec![
                Expr::Source(SourceId(0)),             // 0 = A
                Expr::Source(SourceId(1)),             // 1 = B
                Expr::Source(SourceId(2)),             // 2 = C
                Expr::Add(vec![ExprId(1), ExprId(2)]), // 3 = B + C
                Expr::Mul(vec![ExprId(0), ExprId(3)]), // 4 = A * (B + C)
            ],
        );
        let table = decompose_spine(&l, &[ExprId(4)]);

        assert_eq!(table.fragments.len(), 1, "must NOT distribute into A*B + A*C");
        assert_eq!(table.fragments[0].atoms, vec![ExprId(0), ExprId(3)]);
        assert!(table.fragments[0].recipe.is_trivial());
        assert!(table.c_init.terms.is_empty());
    }

    // ── MergedRecipe::evaluate (Task 3) ─────────────────────────────────────

    fn lift(b: Bf) -> Ext {
        <Ext as FieldExtension<Bf>>::from_base(b)
    }

    struct NoRead;
    impl ReadResolver for NoRead {
        fn read(&self, place: &ReadPlace, _row: usize) -> Ext {
            panic!("scalar-pure recipe must not read {place:?}")
        }
    }
    struct NoLookup;
    impl LookupResolver for NoLookup {
        fn lookup(&self, _: &LookupValueKind, _: usize, _: Ext, _: usize) -> Bf {
            panic!("scalar-pure recipe must not look up")
        }
    }
    struct NoVs;
    impl VirtualSetupResolver for NoVs {
        fn virtual_setup(&self, _: &VirtualSetupKind, _: usize) -> Bf {
            panic!("scalar-pure recipe must not touch virtual setup")
        }
    }
    /// Keyed challenge resolver: `ClaimBatching -> gamma`, `ConstraintAggregation -> beta`.
    struct KeyedChallenge {
        gamma: Ext,
        beta: Ext,
    }
    impl ChallengeResolver for KeyedChallenge {
        fn challenge(&self, r: &ChallengeRef) -> Ext {
            match &r.key {
                ChallengeKey::ClaimBatching => self.gamma,
                ChallengeKey::ConstraintAggregation => self.beta,
                other => panic!("unexpected challenge key {other:?}"),
            }
        }
    }

    #[test]
    fn evaluate_sum_of_products_matches_manual_field_arithmetic() {
        // Tiny arena: Constant c (=5), Challenge gamma (ClaimBatching),
        // Challenge beta (ConstraintAggregation). Recipe [[c, gamma], [beta, beta]]
        // must evaluate to c·gamma + beta².
        let l = layer(
            vec![
                const_src(5),
                challenge_src(ChallengeKey::ClaimBatching),
                challenge_src(ChallengeKey::ConstraintAggregation),
            ],
            vec![
                Expr::Source(SourceId(0)), // 0 = c
                Expr::Source(SourceId(1)), // 1 = gamma
                Expr::Source(SourceId(2)), // 2 = beta
            ],
        );
        let gamma = lift(Bf::from_u32_with_reduction(3));
        let beta = lift(Bf::from_u32_with_reduction(7));
        let ch = KeyedChallenge { gamma, beta };
        let no_read = NoRead;
        let no_lookup = NoLookup;
        let no_vs = NoVs;
        let r = Resolvers {
            read: &no_read,
            lookup: &no_lookup,
            virtual_setup: &no_vs,
            challenge: &ch,
        };

        let recipe = MergedRecipe {
            terms: vec![
                ProductRecipe { factors: vec![ExprId(0), ExprId(1)] },
                ProductRecipe { factors: vec![ExprId(2), ExprId(2)] },
            ],
        };
        // Manual: c·gamma + beta·beta.
        let mut expected = lift(Bf::from_u32_with_reduction(5));
        expected.mul_assign(&gamma);
        let mut beta_sq = beta;
        beta_sq.mul_assign(&beta);
        expected.add_assign(&beta_sq);
        assert_eq!(recipe.evaluate(&l, &r), expected, "Σ Π mismatch");

        // Empty recipe = additive identity 0.
        assert_eq!(MergedRecipe::default().evaluate(&l, &r), Ext::ZERO);

        // A single empty-factors term = multiplicative identity 1.
        let unit = MergedRecipe { terms: vec![ProductRecipe::default()] };
        assert_eq!(unit.evaluate(&l, &r), Ext::ONE);

        // Two empty-factors terms = 1 + 1 (multiplicity preserved, never collapsed).
        let two = MergedRecipe {
            terms: vec![ProductRecipe::default(), ProductRecipe::default()],
        };
        let mut expected_two = Ext::ONE;
        expected_two.add_assign(&Ext::ONE);
        assert_eq!(two.evaluate(&l, &r), expected_two);
    }
}
