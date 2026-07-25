//! Normalized lowering from the canonical DAG + distillation data to the
//! coefficient IR (design §5).
//!
//! # Inputs
//!
//! Both views the design's reusable seam (§5.1) names are required, which is why
//! [`lower_coeff_layer`] takes two arguments:
//!
//!   * [`DistilledLayer`] supplies the rebuilt cones, the [`FragmentTable`]
//!     (`acc = c_init + sum recipe_i * value(fragment_i)`), the per-root
//!     `root_terms` provenance, and the field overrides; and
//!   * the CANONICAL [`DagLayer`] supplies each backward root's claim origin and
//!     its optional materialized output address (`roots[rid].materialize`) — which
//!     `DistilledRootTerm` deliberately does not carry (it is `Copy`).
//!
//! # What each regime emits
//!
//! `R0` (§5.2): `X = 0` is still on the Boolean hypercube, so `acc_c0` comes
//! entirely from the canonical roots — one `Endpoint0` read of a materialized
//! root's OUTPUT COLUMN per claim-bearing output root, and nothing at all for a
//! claim-only constraint root (structurally zero on the hypercube). The
//! materialized root's cone is never re-evaluated at `Endpoint0`; that would be
//! value-equivalent but substantially more expensive. `acc_c2` comes from the
//! `FragmentTable`, where merging across roots is desirable. Fragment
//! contributions to `X^0` and `X^1` are therefore DROPPED at R0: `X^0` is already
//! covered by the root shortcut and `acc_c1` does not exist.
//!
//! `Ext` (§5.3): everything lowers from the `FragmentTable`. Scalar-only
//! contributions — the spine's own `c_init` PLUS every degree-0 residue that
//! distribution produces — merge into one `c_init` recipe used as the per-thread
//! `acc_c0` initializer. Degree-1 contributions become `C0Linear`; degree-2
//! contributions become NATIVE `DualProduct` (never a split c0/c2 pair).
//!
//! # Normalization order (§6), and why it is deterministic
//!
//! 1. Every scalar-pure expression is expanded into a canonical sum of products
//!    over primitive `Constant`/`Challenge` leaves, so constants, batch powers and
//!    challenge factors are combined, products and sums are sorted, signs cancel,
//!    like challenge multisets merge, and zero / one are eliminated
//!    ([`NormalizedCoefficientRecipe`]).
//! 2. Every non-scalar atom is linearized into `Endpoint0`/`Delta` and products of
//!    linear sums are distributed; degree above two is a typed compiler error.
//!    Unary `Add`/`Mul` aliases and multiply-by-one collapse here, which is where
//!    `CopyAlias`-shaped nodes are erased.
//! 3. Bodies (the arithmetic shape without the coefficient) are keyed by the
//!    STRUCTURAL source order [`source_order_key`] defines — not by rebuilt
//!    `ExprId`, not by traversal order — and accumulated in a `BTreeMap`, so
//!    identical bodies merge by summing their coefficient recipes.
//! 4. Bodies whose coefficient cancels to zero are removed; what survives is
//!    already in stable key order, and only then are `TermId`s assigned.
//! 5. `SourceId`s are assigned by walking the sorted set of origins the SURVIVING
//!    bodies reference; the coefficient bank is the sorted set of distinct
//!    non-literal recipes. Neither depends on emission order.
//!
//! [`FragmentTable`]: crate::bwd::fragment::FragmentTable

use std::collections::{BTreeMap, BTreeSet, HashMap};

use cs::gkr_compiler::dag_ir::{
    Bf, BwdRegime, DagLayer, Expr, ExprId, FieldKind, RootSlot, SourceId as DagSourceId,
    SourceKind, bwd_roots, read_place_field,
};
use field::PrimeField;

use super::model::{
    CoeffError, CoeffLayer, CoeffSource, CoeffTerm, CoefficientRecipeId,
    NormalizedCoefficientRecipe, ProjectionId, SourceId, TermId, sink_read_place, source_order_key,
};
use crate::bwd::distill::{DistilledLayer, DistilledRootTerm};
use crate::bwd::fragment::MergedRecipe;
use crate::bwd::source::OriginLeaf;

/// Order-stable handle on one structural source origin, used everywhere inside the
/// lowering in place of a [`SourceId`] (which only exists once the surviving
/// bodies are known). Injective by construction — see [`source_order_key`].
type SourceKey = (u8, u8, usize, usize);

type Recipe = NormalizedCoefficientRecipe;

/// Lower one distilled backward layer to coefficient terms.
pub fn lower_coeff_layer(
    canonical: &DagLayer,
    distilled: &DistilledLayer,
) -> Result<CoeffLayer, CoeffError> {
    let mut cx = Lowering {
        canonical,
        distilled,
        pure: scalar_pure_flags(&distilled.layer),
        origins: BTreeMap::new(),
        scalars: HashMap::new(),
        quads: HashMap::new(),
        bodies: BTreeMap::new(),
        c_init: Recipe::zero(),
        fragment: 0,
    };
    cx.run()?;
    cx.finish()
}

// ── Scalar purity ────────────────────────────────────────────────────────────

/// Bottom-up scalar purity of every expression in `layer`: a `Constant`/
/// `Challenge` leaf is scalar-pure, any other source leaf is not, and an
/// `Add`/`Mul` is scalar-pure iff every child is. The arena is in intern order
/// (children always precede parents), so one forward pass suffices — the same
/// argument `decompose_spine` uses for its identical flag.
///
/// This is the ONLY structural predicate the lowering precomputes. The degree
/// bound is enforced EXACTLY by [`Quad::mul`] on the pruned expansion, never
/// estimated from a syntactic degree: a conservative pre-pass would reject
/// fragments whose high-degree part cancels (e.g. an atom
/// `A*B + (-1)*A*B` has syntactic degree 2 but expands to zero), which on the
/// full corpus would be indistinguishable from a genuine overflow.
fn scalar_pure_flags(layer: &DagLayer) -> Vec<bool> {
    let mut pure = vec![false; layer.exprs.len()];
    for (i, expr) in layer.exprs.iter().enumerate() {
        pure[i] = match expr {
            Expr::Source(sid) => matches!(
                layer.sources[sid.0 as usize].kind,
                SourceKind::Constant { .. } | SourceKind::Challenge { .. }
            ),
            Expr::Add(children) | Expr::Mul(children) => {
                children.iter().all(|c| pure[c.0 as usize])
            }
        };
    }
    pure
}

// ── Degree-<=2 expansion ─────────────────────────────────────────────────────

/// A degree-at-most-two polynomial over source projections: a scalar part, a
/// linear part keyed by source, and a quadratic part keyed by an ORDERED source
/// pair (so `A*B` and `B*A` are the same body). Zero-coefficient entries are
/// pruned, so [`Quad::degree`] is exact.
#[derive(Clone, Debug)]
struct Quad {
    scalar: Recipe,
    linear: BTreeMap<SourceKey, Recipe>,
    quad: BTreeMap<(SourceKey, SourceKey), Recipe>,
}

fn bump<K: Ord>(map: &mut BTreeMap<K, Recipe>, key: K, add: Recipe) {
    if add.is_zero() {
        return;
    }
    let slot = map.entry(key).or_insert_with(Recipe::zero);
    *slot = slot.add(&add);
}

impl Quad {
    fn zero() -> Self {
        Quad { scalar: Recipe::zero(), linear: BTreeMap::new(), quad: BTreeMap::new() }
    }

    fn from_scalar(scalar: Recipe) -> Self {
        Quad { scalar, linear: BTreeMap::new(), quad: BTreeMap::new() }
    }

    fn one() -> Self {
        Self::from_scalar(Recipe::one())
    }

    fn from_leaf(key: SourceKey) -> Self {
        let mut linear = BTreeMap::new();
        linear.insert(key, Recipe::one());
        Quad { scalar: Recipe::zero(), linear, quad: BTreeMap::new() }
    }

    fn prune(&mut self) {
        self.linear.retain(|_, r| !r.is_zero());
        self.quad.retain(|_, r| !r.is_zero());
    }

    fn degree(&self) -> usize {
        if !self.quad.is_empty() {
            2
        } else if !self.linear.is_empty() {
            1
        } else {
            0
        }
    }

    fn add(&self, other: &Self) -> Self {
        let mut out = self.clone();
        out.scalar = out.scalar.add(&other.scalar);
        for (k, c) in &other.linear {
            bump(&mut out.linear, *k, c.clone());
        }
        for (k, c) in &other.quad {
            bump(&mut out.quad, *k, c.clone());
        }
        out.prune();
        out
    }

    /// `Err(degree)` when the product would exceed degree two. The degree is
    /// EXACT for this product, computed from both operands' pruned parts, so a
    /// part that cancelled to zero never inflates it.
    fn mul(&self, other: &Self) -> Result<Self, usize> {
        let degree = self.degree() + other.degree();
        if degree > 2 {
            return Err(degree);
        }
        let mut out = Quad::from_scalar(self.scalar.mul(&other.scalar));
        for (k, c) in &other.linear {
            bump(&mut out.linear, *k, self.scalar.mul(c));
        }
        for (k, c) in &self.linear {
            bump(&mut out.linear, *k, other.scalar.mul(c));
        }
        for (k, c) in &other.quad {
            bump(&mut out.quad, *k, self.scalar.mul(c));
        }
        for (k, c) in &self.quad {
            bump(&mut out.quad, *k, other.scalar.mul(c));
        }
        for (a, ca) in &self.linear {
            for (b, cb) in &other.linear {
                let key = if a <= b { (*a, *b) } else { (*b, *a) };
                bump(&mut out.quad, key, ca.mul(cb));
            }
        }
        out.prune();
        Ok(out)
    }
}

// ── Bodies ───────────────────────────────────────────────────────────────────

/// The arithmetic shape of a term WITHOUT its coefficient — the merge key.
///
/// The derived order is the emission order: all `C0Linear`, then `C2Product`, then
/// `DualProduct`, each by structural source identity. Because [`SourceId`]s are
/// later assigned in [`SourceKey`] order, this is identical to sorting by
/// `SourceId`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum BodyKey {
    C0Linear { source: SourceKey },
    C2Product { lhs: SourceKey, rhs: SourceKey },
    Dual { lhs: SourceKey, rhs: SourceKey },
}

impl BodyKey {
    fn sources(&self) -> [Option<SourceKey>; 2] {
        match self {
            BodyKey::C0Linear { source } => [Some(*source), None],
            BodyKey::C2Product { lhs, rhs } | BodyKey::Dual { lhs, rhs } => {
                [Some(*lhs), Some(*rhs)]
            }
        }
    }
}

// ── Lowering ─────────────────────────────────────────────────────────────────

struct Lowering<'a> {
    canonical: &'a DagLayer,
    distilled: &'a DistilledLayer,
    /// Bottom-up scalar purity, indexed by distilled `ExprId`.
    pure: Vec<bool>,
    origins: BTreeMap<SourceKey, CoeffSource>,
    scalars: HashMap<ExprId, Recipe>,
    quads: HashMap<ExprId, Quad>,
    bodies: BTreeMap<BodyKey, Recipe>,
    c_init: Recipe,
    /// Fragment index the current expansion belongs to, for error reporting.
    fragment: usize,
}

impl Lowering<'_> {
    fn run(&mut self) -> Result<(), CoeffError> {
        self.check_root_order()?;
        self.lower_c_init()?;
        if self.distilled.regime == BwdRegime::R0 {
            self.lower_r0_root_c0()?;
        }
        self.lower_fragments()
    }

    /// `bwd_roots` is the single source of truth for batching position, and
    /// `DistilledLayer::root_terms` is assembled in exactly that order. A mismatch
    /// means the two arguments describe different layers.
    fn check_root_order(&self) -> Result<(), CoeffError> {
        let order = bwd_roots(self.canonical);
        let terms = &self.distilled.root_terms;
        if order.len() != terms.len() {
            return Err(CoeffError::RootCountMismatch {
                canonical: order.len(),
                distilled: terms.len(),
            });
        }
        for (position, (&expected, term)) in order.iter().zip(terms).enumerate() {
            if term.canonical_root != expected {
                return Err(CoeffError::RootOrderMismatch {
                    position,
                    expected,
                    found: term.canonical_root,
                });
            }
        }
        Ok(())
    }

    /// The spine's own scalar-pure addends.
    ///
    /// At `Ext` they seed the per-thread `acc_c0` initializer (§5.3).
    ///
    /// At R0 they are DROPPED. Design §5.3 expected R0's `c_init` to be
    /// structurally empty and asked for "a documented parity explanation" for any
    /// exception; the exception is the common case (26 of the 57 pinned R0 layers
    /// have a non-empty spine `c_init`), so here is the explanation. A non-empty R0
    /// `c_init` is just the scalar ADDENDS of the claim cones — `FragmentTable`
    /// decomposes `beta^i * (A*B + k)` into a fragment plus the scalar `beta^i * k`.
    /// At R0 the whole `X^0` coefficient of the spine is
    /// `sum_i batch_i * cone_i(0)`, and `cone_i(0)` is either the materialized
    /// output column (read at `Endpoint0`) or structurally zero for a claim-only
    /// constraint. Either way the scalar addend is ALREADY inside that value, so
    /// adding `c_init` on top would double-count it. Dropping it is not an
    /// approximation — it is the only value-correct choice, and
    /// `r0_constant_addends_are_covered_by_the_output_shortcut` in
    /// `tests/bwd_coeff_parity.rs` pins it against the canonical DAG.
    fn lower_c_init(&mut self) -> Result<(), CoeffError> {
        let d = self.distilled;
        let spine_scalar = self.scalar_sum(&d.fragments.c_init)?;
        if d.regime == BwdRegime::Ext {
            self.c_init = self.c_init.add(&spine_scalar);
        }
        Ok(())
    }

    /// R0 `acc_c0`, per canonical claim-bearing root in `bwd_roots` order (§5.2).
    fn lower_r0_root_c0(&mut self) -> Result<(), CoeffError> {
        let canonical = self.canonical;
        let terms = &self.distilled.root_terms;
        for term in terms {
            let rid = term.canonical_root;
            let root = canonical
                .roots
                .get(rid.0 as usize)
                .ok_or(CoeffError::UnknownCanonicalRoot { root: rid })?;
            let claim =
                root.claim.as_ref().ok_or(CoeffError::RootNotClaimBearing { root: rid })?;
            let coefficient = self.batch_factor(term)?;
            match (&root.materialize, &claim.origin.slot) {
                (Some(sink), RootSlot::Output(_)) => {
                    let place = sink_read_place(&sink.kind).ok_or_else(|| {
                        CoeffError::UnsupportedSink { root: rid, sink: sink.kind.clone() }
                    })?;
                    let source = self.intern_source(OriginLeaf::Read(place), sink.field)?;
                    self.push_body(BodyKey::C0Linear { source }, coefficient);
                }
                // A claim-only constraint is structurally zero on the hypercube,
                // so it contributes no acc_c0 term and its cone is never read at
                // Endpoint0.
                (None, RootSlot::Constraint(_)) => {}
                (Some(_), RootSlot::Constraint(_)) => {
                    return Err(CoeffError::MaterializedConstraintRoot { root: rid });
                }
                (None, RootSlot::Output(_)) => {
                    return Err(CoeffError::MaterializedOutputMissing { root: rid });
                }
            }
        }
        Ok(())
    }

    /// A root's canonical batch/challenge factor: the multiplicative identity for
    /// root zero (`bwd_roots[0]`, unscaled by construction), else its
    /// `ClaimBatching` beta power.
    fn batch_factor(&self, term: &DistilledRootTerm) -> Result<Recipe, CoeffError> {
        let Some(expr) = term.batching_factor else { return Ok(Recipe::one()) };
        let d = &self.distilled.layer;
        let err = || CoeffError::BatchingFactorNotChallenge { root: term.canonical_root, expr };
        match &d.exprs[expr.0 as usize] {
            Expr::Source(sid) => match &d.sources[sid.0 as usize].kind {
                SourceKind::Challenge { reference } => Ok(Recipe::challenge(reference.clone())),
                _ => Err(err()),
            },
            _ => Err(err()),
        }
    }

    fn lower_fragments(&mut self) -> Result<(), CoeffError> {
        let d = self.distilled;
        for (index, fragment) in d.fragments.fragments.iter().enumerate() {
            self.fragment = index;
            let k = self.scalar_sum(&fragment.recipe)?;
            if k.is_zero() {
                // Additive/multiplicative zero: the whole fragment is annihilated
                // and never reaches the source table.
                continue;
            }
            // The degree bound is checked exactly, by the expansion itself.
            let mut value = Quad::one();
            for &atom in &fragment.atoms {
                let atom_value = self.expand(atom)?;
                value = value
                    .mul(&atom_value)
                    .map_err(|degree| CoeffError::DegreeTooHigh { fragment: index, degree })?;
            }
            self.emit(&k, value);
        }
        Ok(())
    }

    /// Route one fragment's expanded value into terms / `c_init`.
    fn emit(&mut self, k: &Recipe, value: Quad) {
        let r0 = self.distilled.regime == BwdRegime::R0;
        if !r0 {
            // Every scalar-only contribution merges into the one c_init recipe,
            // and every degree-1 contribution becomes one `C0Linear`. At R0 both
            // are dropped: `X^0` is already covered by the materialized-output
            // shortcut and `acc_c1` does not exist.
            self.c_init = self.c_init.add(&k.mul(&value.scalar));
            for (source, coefficient) in &value.linear {
                self.push_body(BodyKey::C0Linear { source: *source }, k.mul(coefficient));
            }
        }
        for ((lhs, rhs), coefficient) in &value.quad {
            let coefficient = k.mul(coefficient);
            let body = if r0 {
                BodyKey::C2Product { lhs: *lhs, rhs: *rhs }
            } else {
                BodyKey::Dual { lhs: *lhs, rhs: *rhs }
            };
            self.push_body(body, coefficient);
        }
    }

    // ── Expansion ────────────────────────────────────────────────────────────

    /// Degree-at-most-two expansion of a rebuilt expression over source
    /// projections. Unary `Add`/`Mul` nodes collapse to their child (the
    /// `CopyAlias` erasure) and multiplication by a scalar `1` folds away, because
    /// both are identities of [`Quad`]'s algebra.
    fn expand(&mut self, e: ExprId) -> Result<Quad, CoeffError> {
        if let Some(q) = self.quads.get(&e) {
            return Ok(q.clone());
        }
        let d = self.distilled;
        let q = if self.pure[e.0 as usize] {
            Quad::from_scalar(self.scalar_expr(e)?)
        } else {
            match &d.layer.exprs[e.0 as usize] {
                Expr::Source(sid) => Quad::from_leaf(self.leaf_source(e, *sid)?),
                Expr::Add(children) => {
                    let children = children.clone();
                    let mut acc = Quad::zero();
                    for c in children {
                        let part = self.expand(c)?;
                        acc = acc.add(&part);
                    }
                    acc
                }
                Expr::Mul(children) => {
                    let children = children.clone();
                    let mut acc = Quad::one();
                    let fragment = self.fragment;
                    for c in children {
                        let part = self.expand(c)?;
                        acc = acc
                            .mul(&part)
                            .map_err(|degree| CoeffError::DegreeTooHigh { fragment, degree })?;
                    }
                    acc
                }
            }
        };
        self.quads.insert(e, q.clone());
        Ok(q)
    }

    /// Canonical expansion of a scalar-pure expression into a normalized recipe.
    fn scalar_expr(&mut self, e: ExprId) -> Result<Recipe, CoeffError> {
        if let Some(r) = self.scalars.get(&e) {
            return Ok(r.clone());
        }
        let d = self.distilled;
        let r = match &d.layer.exprs[e.0 as usize] {
            Expr::Source(sid) => match &d.layer.sources[sid.0 as usize].kind {
                SourceKind::Constant { value } => {
                    Recipe::scalar(Bf::from_u32_with_reduction(*value))
                }
                SourceKind::Challenge { reference } => Recipe::challenge(reference.clone()),
                _ => return Err(CoeffError::NonScalarCoefficientFactor { expr: e }),
            },
            Expr::Add(children) => {
                let children = children.clone();
                let mut acc = Recipe::zero();
                for c in children {
                    let part = self.scalar_expr(c)?;
                    acc = acc.add(&part);
                }
                acc
            }
            Expr::Mul(children) => {
                let children = children.clone();
                let mut acc = Recipe::one();
                for c in children {
                    let part = self.scalar_expr(c)?;
                    acc = acc.mul(&part);
                }
                acc
            }
        };
        self.scalars.insert(e, r.clone());
        Ok(r)
    }

    /// A fragment's / `c_init`'s summed coefficient recipe (`sum` over terms of
    /// `product` over factors), normalized.
    fn scalar_sum(&mut self, recipe: &MergedRecipe) -> Result<Recipe, CoeffError> {
        let mut sum = Recipe::zero();
        for term in &recipe.terms {
            let mut product = Recipe::one();
            for &factor in &term.factors {
                if !self.pure[factor.0 as usize] {
                    return Err(CoeffError::NonScalarCoefficientFactor { expr: factor });
                }
                let part = self.scalar_expr(factor)?;
                product = product.mul(&part);
            }
            sum = sum.add(&product);
        }
        Ok(sum)
    }

    // ── Sources ──────────────────────────────────────────────────────────────

    fn leaf_source(&mut self, e: ExprId, sid: DagSourceId) -> Result<SourceKey, CoeffError> {
        let d = self.distilled;
        let origin = match &d.layer.sources[sid.0 as usize].kind {
            SourceKind::Read { place } => OriginLeaf::Read(place.clone()),
            SourceKind::VirtualSetup { kind } => OriginLeaf::VirtualSetup { kind: kind.clone() },
            // `LookupValue` leaves are erased by distillation (rule 2), and
            // `Constant`/`Challenge` are degree 0 and never reach here.
            _ => return Err(CoeffError::UnsupportedLeaf { expr: e }),
        };
        let field = self.leaf_field(e, &origin)?;
        self.intern_source(origin, field)
    }

    /// The stored width of one leaf: the distilled `Ext` fold override when
    /// present, else the native read width (cross-layer reads carry none in the
    /// model, so they come from `cross_fields`).
    fn leaf_field(&self, e: ExprId, origin: &OriginLeaf) -> Result<FieldKind, CoeffError> {
        if let Some(&f) = self.distilled.field_overrides.get(&e) {
            return Ok(f);
        }
        match origin {
            OriginLeaf::VirtualSetup { .. } => Ok(FieldKind::Base),
            OriginLeaf::Read(place) => match read_place_field(place) {
                Some(f) => Ok(f),
                None => self
                    .distilled
                    .cross_fields
                    .get(place)
                    .copied()
                    .ok_or_else(|| CoeffError::MissingCrossLayerField { place: place.clone() }),
            },
        }
    }

    fn intern_source(
        &mut self,
        origin: OriginLeaf,
        field: FieldKind,
    ) -> Result<SourceKey, CoeffError> {
        let key = source_order_key(&origin);
        match self.origins.get(&key) {
            Some(existing) if existing.field != field => {
                return Err(CoeffError::SourceFieldConflict {
                    origin,
                    first: existing.field,
                    second: field,
                });
            }
            Some(_) => {}
            None => {
                self.origins.insert(key, CoeffSource { origin, field });
            }
        }
        Ok(key)
    }

    fn push_body(&mut self, key: BodyKey, coefficient: Recipe) {
        let slot = self.bodies.entry(key).or_insert_with(Recipe::zero);
        *slot = slot.add(&coefficient);
    }

    // ── Assembly ─────────────────────────────────────────────────────────────

    fn finish(self) -> Result<CoeffLayer, CoeffError> {
        // A body whose coefficient cancels to zero is REMOVED (an encoded zero is
        // a compiler error, not a representable value).
        let live: Vec<(BodyKey, Recipe)> =
            self.bodies.into_iter().filter(|(_, r)| !r.is_zero()).collect();

        // `SourceId`s cover exactly the origins the surviving bodies reference.
        let mut used: BTreeSet<SourceKey> = BTreeSet::new();
        for (body, _) in &live {
            for key in body.sources().into_iter().flatten() {
                used.insert(key);
            }
        }
        let ids: BTreeMap<SourceKey, SourceId> =
            used.iter().enumerate().map(|(i, k)| (*k, SourceId(i as u32))).collect();
        let sources: Vec<CoeffSource> =
            used.iter().map(|k| self.origins[k].clone()).collect();

        // The evaluated bank: distinct non-literal recipes, sorted. `+1`/`-1` are
        // reserved semantic representations and consume no entry.
        let c_init_recipe = (!self.c_init.is_zero()).then(|| self.c_init.clone());
        let mut bank: BTreeSet<Recipe> = BTreeSet::new();
        for (_, r) in &live {
            if r.reserved_id().is_none() {
                bank.insert(r.clone());
            }
        }
        if let Some(r) = &c_init_recipe {
            if r.reserved_id().is_none() {
                bank.insert(r.clone());
            }
        }
        let coefficients: Vec<Recipe> = bank.into_iter().collect();

        let mut terms = Vec::with_capacity(live.len());
        for (index, (body, recipe)) in live.iter().enumerate() {
            let id = TermId(index as u32);
            let coefficient = coefficient_id(&coefficients, recipe);
            terms.push(match body {
                BodyKey::C0Linear { source } => {
                    let s = ids[source];
                    CoeffTerm::C0Linear {
                        id,
                        coefficient,
                        value: ProjectionId::endpoint0(s),
                        field: sources[s.0 as usize].field,
                    }
                }
                BodyKey::C2Product { lhs, rhs } => {
                    let (l, r) = (ids[lhs], ids[rhs]);
                    CoeffTerm::C2Product {
                        id,
                        coefficient,
                        lhs: ProjectionId::delta(l),
                        rhs: ProjectionId::delta(r),
                        lhs_field: sources[l.0 as usize].field,
                        rhs_field: sources[r.0 as usize].field,
                    }
                }
                BodyKey::Dual { lhs, rhs } => {
                    CoeffTerm::DualProduct { id, coefficient, lhs: ids[lhs], rhs: ids[rhs] }
                }
            });
        }
        let c_init = c_init_recipe.as_ref().map(|r| coefficient_id(&coefficients, r));

        Ok(CoeffLayer {
            regime: self.distilled.regime,
            c_init,
            coefficients,
            sources,
            terms,
        })
    }
}

/// The id addressing `recipe`: a reserved literal when it is `+1`/`-1`, else its
/// bank index (the bank is sorted, so this is a binary search).
fn coefficient_id(coefficients: &[Recipe], recipe: &Recipe) -> CoefficientRecipeId {
    recipe.reserved_id().unwrap_or_else(|| {
        CoefficientRecipeId::from_bank_index(
            coefficients
                .binary_search(recipe)
                .expect("every non-literal surviving recipe is banked"),
        )
    })
}
