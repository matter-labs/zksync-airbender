//! The backward coefficient IR's semantic model (design §4 / §6): stable
//! identities, the three semantic terms, normalized coefficient recipes, and the
//! typed compiler/interpreter errors.
//!
//! # Math contract (§4)
//!
//! A source has the affine form `S(X) = s0 + X*ds` over the current sumcheck
//! coordinate; the only named projections are `Endpoint0 = s0` and `Delta = ds`.
//! One logical row contributes `P(X) = c0 + c1*X + c2*X^2` and the interpreter
//! accumulates only
//!
//! ```text
//! acc_c0 = sum of X^0 coefficients
//! acc_c2 = sum of X^2 coefficients
//! ```
//!
//! `acc_c1` does not exist: the round update recovers `c1` from the normalized
//! claim. There are no `T0`/`T2` roles here and no generic arithmetic
//! accumulator.
//!
//! # What is NOT here
//!
//! Moves, physical cells, source-window bindings, and paging are SCHEDULE
//! instructions layered on top of this IR by later tasks; a [`CoeffTerm`] never
//! carries them. Only [`ProjectionId`] belongs to the local cache domain.

use std::cmp::Ordering;

use cs::gkr_compiler::dag_ir::{
    Bf, BwdRegime, ChallengePower, ChallengeRef, ChallengeResolver, ExprId, Ext, FieldKind,
    ReadPlace, RootId, SinkKind, VirtualSetupKind,
};
use field::{Field, FieldExtension, PrimeField};

use crate::bwd::fragment::FactorKey;
use crate::bwd::source::OriginLeaf;

// ── Stable identities (§6) ───────────────────────────────────────────────────

/// Dense index of a [`CoeffTerm`] in [`CoeffLayer::terms`]. Assigned only after
/// bodies are merged, pruned, and sorted by stable structural identity, so it
/// never depends on schedule order.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TermId(pub u32);

/// Dense index of a [`CoeffSource`] in [`CoeffLayer::sources`]. Derived from the
/// leaf's STRUCTURAL origin ([`OriginLeaf`]), never from the rebuilt `ExprId` or
/// from traversal order.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SourceId(pub u32);

/// Identity of one evaluated coefficient value.
///
/// [`CoefficientRecipeId::ONE`] and [`CoefficientRecipeId::NEG_ONE`] are RESERVED
/// semantic representations of the literals `+1` and `-1`: they consume no entry
/// in [`CoeffLayer::coefficients`] and are never served by a
/// [`CoeffResolver`](super::interp::CoeffResolver). Every other id addresses
/// `coefficients[id.0 - RESERVED]`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CoefficientRecipeId(pub u32);

impl CoefficientRecipeId {
    /// The literal `+1`. No bank entry, no resolver call.
    pub const ONE: Self = CoefficientRecipeId(0);
    /// The literal `-1`. No bank entry, no resolver call.
    pub const NEG_ONE: Self = CoefficientRecipeId(1);
    /// Number of reserved literal ids; bank entry `i` is id `RESERVED + i`.
    pub const RESERVED: u32 = 2;

    /// The field value of a reserved literal id, or `None` for a banked id.
    pub fn literal(self) -> Option<Ext> {
        if self == Self::ONE {
            return Some(Ext::ONE);
        }
        if self == Self::NEG_ONE {
            let mut v = Ext::ONE;
            v.negate();
            return Some(v);
        }
        None
    }

    /// Index into [`CoeffLayer::coefficients`], or `None` for a reserved literal.
    pub fn bank_index(self) -> Option<usize> {
        (self.0 >= Self::RESERVED).then(|| (self.0 - Self::RESERVED) as usize)
    }

    /// The id addressing bank entry `index`.
    pub fn from_bank_index(index: usize) -> Self {
        CoefficientRecipeId(Self::RESERVED + index as u32)
    }
}

/// The only two named source projections (§4). There is no "delta endpoint".
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Projection {
    Endpoint0,
    Delta,
}

/// One projection of one source — the only identity that belongs to the local
/// cache domain.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ProjectionId {
    pub source: SourceId,
    pub projection: Projection,
}

impl ProjectionId {
    pub fn endpoint0(source: SourceId) -> Self {
        ProjectionId { source, projection: Projection::Endpoint0 }
    }

    pub fn delta(source: SourceId) -> Self {
        ProjectionId { source, projection: Projection::Delta }
    }
}

// ── Sources ──────────────────────────────────────────────────────────────────

/// One resolvable backward source, identified by the structural fold/read origin
/// [`crate::bwd::source`] defines.
///
/// Materialized R0 root outputs are interned HERE too (as
/// `OriginLeaf::Read(LayerOutput|CacheOutput|Scratch)`), even though they are not
/// leaves of the rebuilt expression cone — one source table, one addressing
/// vocabulary for Tasks 5/6.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoeffSource {
    pub origin: OriginLeaf,
    /// Resolved storage width: the `Ext` fold override in the `Ext` regime, the
    /// native read width (or the sink's field, for a materialized output) at R0.
    pub field: FieldKind,
}

/// Total, injective order over structural source origins — the single reason
/// [`SourceId`] assignment is deterministic. Read families are ordered by their
/// `ReadPlace` variant, then by address; virtual-setup origins sort after every
/// read.
pub fn source_order_key(origin: &OriginLeaf) -> (u8, u8, usize, usize) {
    match origin {
        OriginLeaf::Read(place) => {
            let (variant, a, b) = match place {
                ReadPlace::BaseLayerMemory { column } => (0u8, *column, 0),
                ReadPlace::BaseLayerWitness { column } => (1, *column, 0),
                ReadPlace::Setup { column } => (2, *column, 0),
                ReadPlace::Scratch { slot } => (3, *slot, 0),
                ReadPlace::LayerOutput { layer, offset } => (4, *layer, *offset),
                ReadPlace::CacheOutput { layer, offset } => (5, *layer, *offset),
            };
            (0, variant, a, b)
        }
        OriginLeaf::VirtualSetup { kind } => {
            let variant = match kind {
                VirtualSetupKind::RangeCheck16Bits => 0u8,
                VirtualSetupKind::RangeCheckTimestamp => 1,
                VirtualSetupKind::InitsAndTeardownsLow => 2,
                VirtualSetupKind::InitsAndTeardownsHigh => 3,
            };
            (1, variant, 0, 0)
        }
    }
}

/// The `ReadPlace` a materialized sink is read back from (design §5.2: the R0
/// `acc_c0` shortcut reads the output COLUMN, not the cone). `Export` sinks have
/// no read counterpart.
pub fn sink_read_place(sink: &SinkKind) -> Option<ReadPlace> {
    match sink {
        SinkKind::Inner { layer, offset } => {
            Some(ReadPlace::LayerOutput { layer: *layer, offset: *offset })
        }
        SinkKind::Cache { layer, offset } => {
            Some(ReadPlace::CacheOutput { layer: *layer, offset: *offset })
        }
        SinkKind::Scratch { slot } => Some(ReadPlace::Scratch { slot: *slot }),
        SinkKind::Export { .. } => None,
    }
}

// ── Normalized coefficient recipes (§6) ──────────────────────────────────────

/// A challenge factor with a total order, in canonical spelling.
///
/// `ChallengeRef` is deliberately not `Ord`, so the order is delegated to
/// [`FactorKey`] — the crate's existing stable factor order — which keeps
/// coefficient canonicalization consistent with
/// [`FragmentTable::stable_view`](crate::bwd::fragment::FragmentTable::stable_view).
///
/// Construct through [`CoeffChallenge::new`], which folds the redundant
/// `Static(1)` spelling into `One`; [`NormalizedCoefficientRecipe::from_terms`]
/// re-applies it, so a recipe never holds a non-canonical reference.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CoeffChallenge(pub ChallengeRef);

impl CoeffChallenge {
    /// Canonical spelling of one challenge factor: `ChallengePower::Static(1)`
    /// becomes `ChallengePower::One`.
    ///
    /// Both spell the FIRST power, and every resolver in this repo maps them to
    /// the same element — `beta_pows[1] == beta`, `pow(beta, 1) == beta`, and the
    /// power-ignoring arms (`LookupAdditive`, `PermutationAdditive`,
    /// `PermutationLinearization`) are insensitive to `power` altogether. So this
    /// rewrite is value-preserving and it removes a real two-spelling redundancy
    /// from the coefficient bank (the pinned corpus spells
    /// `LookupMultiplicative` powers as `Static(1)`, `Static(2)`, `Static(3)`,
    /// never as `One`).
    ///
    /// HIGHER powers are deliberately NOT merged — see [`CoeffProduct`] for why
    /// that would be unsound.
    pub fn new(reference: ChallengeRef) -> Self {
        let power = match reference.power {
            ChallengePower::Static(1) => ChallengePower::One,
            other => other,
        };
        CoeffChallenge(ChallengeRef { key: reference.key, power })
    }
}

impl Ord for CoeffChallenge {
    fn cmp(&self, other: &Self) -> Ordering {
        FactorKey::Challenge(self.0.clone()).cmp(&FactorKey::Challenge(other.0.clone()))
    }
}

impl PartialOrd for CoeffChallenge {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// One product term of a normalized coefficient recipe: a canonical scalar times
/// a sorted multiset of challenge factors.
///
/// Invariants (upheld by [`NormalizedCoefficientRecipe`]'s constructors):
///   * `scalar` is a CANONICAL REDUCED BabyBear value and never `0` — an
///     annihilated product is dropped, not encoded;
///   * every challenge is in canonical spelling ([`CoeffChallenge::new`]);
///   * `challenges` is sorted ascending, with multiplicity PRESERVED; and
///   * a scalar `1` with no challenges is the multiplicative identity, which the
///     compiler represents with [`CoefficientRecipeId::ONE`] instead of a bank
///     entry — an "ordinary multiplication by one" is never encoded.
///
/// # Why repeated challenge factors are not merged into an exponent
///
/// Collapsing `gamma * gamma` into a single `Static(2)` reference looks like a
/// dedup win (it would make `beta * beta` and `beta^2` one recipe) but it is
/// UNSOUND here, because `ChallengePower` is only an exponent for the keys whose
/// resolver arm reads it. In this repo only `ClaimBatching`
/// (`pow(beta, i)` / `beta_pows[i]`) and `LookupMultiplicative`
/// (`alpha_pows[j]`) honour powers; `LookupAdditive`, `PermutationAdditive` and
/// `PermutationLinearization` ignore `power` entirely and return their single
/// challenge. Rewriting `gamma * gamma` as `{LookupAdditive, Static(2)}` would
/// therefore resolve to `gamma`, not `gamma^2` — a silent factor-of-gamma error.
///
/// On the pinned corpus the repeated-key products are EXCLUSIVELY on those
/// power-ignoring keys (334 `LookupAdditive x2`, 18 `PermutationAdditive x2`,
/// 176 `PermutationLinearization(..) x2`), while no product repeats a
/// power-honouring key at all — so the collapse would deduplicate nothing and
/// corrupt 528 products. `coefficient_products_never_repeat_a_power_honouring_key`
/// in `tests/bwd_coeff_corpus.rs` pins that, so if a future compiler change ever
/// does emit `beta * beta` the guard fires and the exponent merge can then be
/// introduced for that key alone, where it IS sound.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CoeffProduct {
    pub scalar: u32,
    pub challenges: Vec<CoeffChallenge>,
}

impl Ord for CoeffProduct {
    fn cmp(&self, other: &Self) -> Ordering {
        self.challenges.cmp(&other.challenges).then_with(|| self.scalar.cmp(&other.scalar))
    }
}

impl PartialOrd for CoeffProduct {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// A structurally normalized coefficient: `sum of (scalar * product of
/// challenges)`.
///
/// Normalization (§6) is total and order-free: scalar constants, batch powers and
/// challenge-derived factors are combined, commutative products and sums are
/// sorted, signs cancel, like challenge multisets are merged, and additive /
/// multiplicative zero is eliminated. An EMPTY `terms` is the additive identity
/// `0`, which is never encoded — a body whose coefficient cancels to zero is
/// removed instead.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NormalizedCoefficientRecipe {
    pub terms: Vec<CoeffProduct>,
}

impl NormalizedCoefficientRecipe {
    /// The additive identity. Never encoded.
    pub fn zero() -> Self {
        NormalizedCoefficientRecipe { terms: Vec::new() }
    }

    /// The multiplicative identity, represented by
    /// [`CoefficientRecipeId::ONE`] once interned.
    pub fn one() -> Self {
        Self::scalar(Bf::ONE)
    }

    /// `-1`, represented by [`CoefficientRecipeId::NEG_ONE`] once interned.
    pub fn neg_one() -> Self {
        let mut v = Bf::ONE;
        v.negate();
        Self::scalar(v)
    }

    /// A bare scalar (`0` collapses to [`zero`](Self::zero)).
    pub fn scalar(v: Bf) -> Self {
        Self::from_terms(vec![CoeffProduct { scalar: v.as_u32_reduced(), challenges: Vec::new() }])
    }

    /// A bare challenge factor.
    pub fn challenge(r: ChallengeRef) -> Self {
        Self::from_terms(vec![CoeffProduct {
            scalar: 1,
            challenges: vec![CoeffChallenge::new(r)],
        }])
    }

    /// Canonicalize `terms`: put each challenge in canonical spelling and sort a
    /// product's challenges, merge products that share a challenge multiset
    /// (summing their scalars), drop the ones whose scalar cancels to zero, and
    /// sort what remains.
    pub fn from_terms(mut terms: Vec<CoeffProduct>) -> Self {
        // Merge by challenge multiset. `BTreeMap` gives the canonical term order
        // for free.
        let mut merged: std::collections::BTreeMap<Vec<CoeffChallenge>, Bf> =
            std::collections::BTreeMap::new();
        for t in terms.drain(..) {
            if t.scalar == 0 {
                continue;
            }
            let mut challenges: Vec<CoeffChallenge> =
                t.challenges.into_iter().map(|c| CoeffChallenge::new(c.0)).collect();
            challenges.sort();
            let slot = merged.entry(challenges).or_insert(Bf::ZERO);
            slot.add_assign(&Bf::from_u32_with_reduction(t.scalar));
        }
        let terms = merged
            .into_iter()
            .filter(|(_, v)| v.as_u32_reduced() != 0)
            .map(|(challenges, v)| CoeffProduct { scalar: v.as_u32_reduced(), challenges })
            .collect();
        NormalizedCoefficientRecipe { terms }
    }

    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    pub fn is_one(&self) -> bool {
        *self == Self::one()
    }

    pub fn is_neg_one(&self) -> bool {
        *self == Self::neg_one()
    }

    /// The reserved literal id for `+1` / `-1`, or `None` when this recipe needs a
    /// bank entry (a zero recipe also returns `None` — it must never be encoded).
    pub fn reserved_id(&self) -> Option<CoefficientRecipeId> {
        if self.is_one() {
            return Some(CoefficientRecipeId::ONE);
        }
        if self.is_neg_one() {
            return Some(CoefficientRecipeId::NEG_ONE);
        }
        None
    }

    pub fn add(&self, other: &Self) -> Self {
        let mut terms = self.terms.clone();
        terms.extend(other.terms.iter().cloned());
        Self::from_terms(terms)
    }

    pub fn mul(&self, other: &Self) -> Self {
        let mut terms = Vec::with_capacity(self.terms.len() * other.terms.len());
        for a in &self.terms {
            for b in &other.terms {
                let mut scalar = Bf::from_u32_with_reduction(a.scalar);
                scalar.mul_assign(&Bf::from_u32_with_reduction(b.scalar));
                let mut challenges = a.challenges.clone();
                challenges.extend(b.challenges.iter().cloned());
                terms.push(CoeffProduct { scalar: scalar.as_u32_reduced(), challenges });
            }
        }
        Self::from_terms(terms)
    }

    /// Evaluate the recipe. Row- and role-invariant by construction: a normalized
    /// recipe holds only constants and challenge references, so this is the
    /// once-per-proof evaluation the coefficient bank is filled with.
    pub fn evaluate(&self, challenge: &dyn ChallengeResolver) -> Ext {
        let mut sum = Ext::ZERO;
        for t in &self.terms {
            let mut prod =
                <Ext as FieldExtension<Bf>>::from_base(Bf::from_u32_with_reduction(t.scalar));
            for c in &t.challenges {
                prod.mul_assign(&challenge.challenge(&c.0));
            }
            sum.add_assign(&prod);
        }
        sum
    }
}

// ── Terms (§6) ───────────────────────────────────────────────────────────────

/// One semantic coefficient term. Moves and physical cells are NOT here.
///
/// ```text
/// C0Linear(k, a0)        acc_c0 += k * a0
/// C2Product(k, da, db)   acc_c2 += k * da * db
/// DualProduct(k, A, B)   acc_c0 += k * A.s0 * B.s0 ; acc_c2 += k * A.ds * B.ds
/// ```
///
/// `DualProduct` is produced NATIVELY by continuation lowering: both coefficient
/// contributions are born with the same coefficient and the same factors, so they
/// are never split and re-fused.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CoeffTerm {
    C0Linear {
        id: TermId,
        coefficient: CoefficientRecipeId,
        /// Always an [`Projection::Endpoint0`] projection.
        value: ProjectionId,
        field: FieldKind,
    },
    C2Product {
        id: TermId,
        coefficient: CoefficientRecipeId,
        /// Always a [`Projection::Delta`] projection.
        lhs: ProjectionId,
        /// Always a [`Projection::Delta`] projection.
        rhs: ProjectionId,
        lhs_field: FieldKind,
        rhs_field: FieldKind,
    },
    DualProduct {
        id: TermId,
        coefficient: CoefficientRecipeId,
        /// A native dual factor consumes BOTH projections of this source in one
        /// physical source-pair resolution (§8).
        lhs: SourceId,
        rhs: SourceId,
    },
}

impl CoeffTerm {
    pub fn id(&self) -> TermId {
        match self {
            CoeffTerm::C0Linear { id, .. }
            | CoeffTerm::C2Product { id, .. }
            | CoeffTerm::DualProduct { id, .. } => *id,
        }
    }

    /// Operand SLOTS this term encodes: one for `C0Linear`, two for the two
    /// product forms. Not the number of projections it consumes — a native dual
    /// factor is ONE slot consuming TWO projections.
    pub fn arity(&self) -> usize {
        match self {
            CoeffTerm::C0Linear { .. } => 1,
            CoeffTerm::C2Product { .. } | CoeffTerm::DualProduct { .. } => 2,
        }
    }

    /// Every projection this term CONSUMES, once per operand-slot occurrence, in
    /// canonical operand order.
    ///
    /// The single definition of "consumed projection" in the crate: the census
    /// ([`census_coeff_layer`](super::stats::census_coeff_layer)) counts operand
    /// slots with it and the scheduler
    /// ([`schedule`](super::schedule)) builds its next-use queues from it, so the
    /// two cannot drift. A native dual factor contributes BOTH of its
    /// projections here (§8: the factor explicitly consumes the pair), while the
    /// physical grouping of those two into one source-pair resolution is a
    /// SCHEDULE concern and lives in `schedule`.
    ///
    /// Occurrences are NOT deduplicated: `C2Product { lhs: d, rhs: d }` yields
    /// `d` twice, which is what makes it a reusable projection in the census.
    pub fn for_each_projection_use(&self, mut f: impl FnMut(ProjectionId)) {
        match self {
            CoeffTerm::C0Linear { value, .. } => f(*value),
            CoeffTerm::C2Product { lhs, rhs, .. } => {
                f(*lhs);
                f(*rhs);
            }
            CoeffTerm::DualProduct { lhs, rhs, .. } => {
                for source in [*lhs, *rhs] {
                    f(ProjectionId::endpoint0(source));
                    f(ProjectionId::delta(source));
                }
            }
        }
    }

    pub fn coefficient(&self) -> CoefficientRecipeId {
        match self {
            CoeffTerm::C0Linear { coefficient, .. }
            | CoeffTerm::C2Product { coefficient, .. }
            | CoeffTerm::DualProduct { coefficient, .. } => *coefficient,
        }
    }
}

// ── Layer ────────────────────────────────────────────────────────────────────

/// One backward layer lowered to coefficient terms.
///
/// `terms` is dense and ordered: `terms[i].id() == TermId(i)`, with bodies sorted
/// by stable structural identity (all `C0Linear`, then `C2Product`, then
/// `DualProduct`, each by source identity). `coefficients` is the EVALUATED BANK:
/// it holds neither the reserved `+1`/`-1` literals nor a zero recipe, and it is
/// sorted by normalized recipe so its order does not depend on term order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoeffLayer {
    pub regime: BwdRegime,
    /// The per-thread `acc_c0` initializer (§5.3), evaluated once per
    /// proof/program. `None` = initialize to zero and consume no coefficient slot.
    pub c_init: Option<CoefficientRecipeId>,
    pub coefficients: Vec<NormalizedCoefficientRecipe>,
    pub sources: Vec<CoeffSource>,
    pub terms: Vec<CoeffTerm>,
}

impl CoeffLayer {
    /// The banked recipe behind `id`, or `None` for a reserved literal (which has
    /// no bank entry) or an out-of-range id.
    pub fn banked_recipe(&self, id: CoefficientRecipeId) -> Option<&NormalizedCoefficientRecipe> {
        self.coefficients.get(id.bank_index()?)
    }

    pub fn source(&self, id: SourceId) -> Option<&CoeffSource> {
        self.sources.get(id.0 as usize)
    }
}

// ── Errors ───────────────────────────────────────────────────────────────────

/// Compiler / interpreter errors of the coefficient lowering. Every variant is
/// derivable from the input data.
///
/// The module contains no `assert!` and no `debug_assert!`. Its only panicking
/// paths are an `expect` and a handful of index accesses on tables the lowering
/// itself just populated — the bank lookup for a recipe it interned, and the
/// `SourceId` / `CoeffSource` lookups for an origin it interned — none of which
/// can miss. Anything a caller's data can violate is one of the variants below.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CoeffError {
    /// The canonical layer and the distilled layer disagree on how many backward
    /// roots exist — they describe different layers.
    RootCountMismatch { canonical: usize, distilled: usize },
    /// `DistilledLayer::root_terms` disagrees with the canonical `bwd_roots`
    /// order (the single source of truth for batching position).
    RootOrderMismatch { position: usize, expected: RootId, found: RootId },
    /// A `root_terms` entry names a root outside the canonical layer.
    UnknownCanonicalRoot { root: RootId },
    /// A backward root that is not claim-bearing.
    RootNotClaimBearing { root: RootId },
    /// A claim-bearing `RootSlot::Output` root with no materialized sink: the R0
    /// `acc_c0` shortcut has no address to read.
    MaterializedOutputMissing { root: RootId },
    /// A materialized sink on a claim-only `RootSlot::Constraint` root — the two
    /// attributes are orthogonal, so this contradicts the canonical model.
    MaterializedConstraintRoot { root: RootId },
    /// A sink kind with no read counterpart (`Export`).
    UnsupportedSink { root: RootId, sink: SinkKind },
    /// A root's batching factor is not a `ClaimBatching` challenge leaf.
    BatchingFactorNotChallenge { root: RootId, expr: ExprId },
    /// Relation degree above two (§5.4). `degree` saturates at 3.
    DegreeTooHigh { fragment: usize, degree: usize },
    /// The deduplicated coefficient bank plus the two reserved literals does not
    /// fit the thirteen coefficient bits of the u16 header (§9.2).
    ///
    /// This is a COMPILER ERROR by design: there is no extended encoding, no
    /// version field, and no fallback format. For the conditional
    /// `blake2_with_compression` scope it triggers §3.1's whole-circuit exclusion;
    /// for any mandatory circuit it fails the build.
    CoefficientBankOverflow { recipes: usize, reserved: usize, limit: usize },
    /// A coefficient recipe factor that is not scalar-pure.
    NonScalarCoefficientFactor { expr: ExprId },
    /// A distilled leaf that cannot be a backward source (a `LookupValue` leaf
    /// should have been erased by distillation).
    UnsupportedLeaf { expr: ExprId },
    /// A cross-layer read whose width is absent from `DistilledLayer::cross_fields`.
    MissingCrossLayerField { place: ReadPlace },
    /// One structural origin resolved to two different widths.
    SourceFieldConflict { origin: OriginLeaf, first: FieldKind, second: FieldKind },
    /// The interpreter was handed a coefficient id with no bank entry.
    UnknownCoefficient { id: CoefficientRecipeId },
    /// The interpreter was handed a coefficient id whose recipe is the additive
    /// identity — an encoded zero is a compiler error, not a representable value.
    EncodedZeroCoefficient { id: CoefficientRecipeId },
    /// The interpreter was handed a source id outside `CoeffLayer::sources`.
    UnknownSource { id: SourceId },
    /// A term projects a role its opcode cannot consume (`C0Linear` over `Delta`,
    /// `C2Product` over `Endpoint0`).
    ProjectionRoleMismatch { term: TermId, expected: Projection, found: Projection },
    /// A claim-bearing root has no materialized sink and is not a
    /// `RootSlot::Constraint` root — so §5.2's "claim-only constraint roots
    /// contribute no `acc_c0`" accounting does not describe this layer.
    ///
    /// `lower_r0_root_c0` rejects the same contradiction as
    /// [`MaterializedOutputMissing`](Self::MaterializedOutputMissing) /
    /// [`MaterializedConstraintRoot`](Self::MaterializedConstraintRoot), but only
    /// in the R0 regime, because that lowering is R0-gated. In `Ext` a sinkless
    /// `RootSlot::Output` root lowers fine, so the census is the first place the
    /// contradiction becomes observable — and it is derivable purely from
    /// `DagLayer::roots`, which is why it is a typed error and not an assertion.
    ConstraintRootAccountingMismatch { sinkless_claim_roots: usize, constraint_slot_roots: usize },
    /// A lowered layer uses a term category its regime's opcode table cannot
    /// encode — a `DualProduct` at R0, or a base-field `C0Linear` in `Ext`
    /// (§9.2's opcode census).
    ///
    /// Derivable from `CoeffLayer::regime` and `CoeffLayer::terms` alone, so it is
    /// a typed error rather than a library-level assertion: a census must be able
    /// to report the offending coordinate as data and continue (§3.1).
    TermCategoryNotEncodable { regime: BwdRegime, category: super::limits::TermCategory },
}
