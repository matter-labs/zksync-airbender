//! Deterministic mixed-width projection paging (design §7.1, §7.2, §8) and its
//! independent replay certificate (§12.2, §12.4).
//!
//! This module answers exactly one question: for a FIXED term order and a
//! FIXED `c2`..`c16` shared-memory budget, which source projections stay
//! resident? Its output is a complete, replayable [`PagingPlan`] over
//! [`ProjectionId`]s plus a [`PagingCost`], and nothing else.
//!
//! # What is deliberately NOT here
//!
//! Physical cell numbers, lane indices, E4 quad alignment, `MoveBF`/`MoveE4`,
//! source-window binding, first-access bits, and the u16 encoding. Design §7.3
//! is explicit that placement is DERIVED from paging and "may not change those
//! decisions", so this module fixes admission, bypass, retention and eviction
//! and later tasks may only read them.
//!
//! # The model (§7.1)
//!
//! One cell is one 16-byte E4 bucket, i.e. four BF lanes. A budget of `n` cells
//! therefore holds `4 * n` BF-lane-equivalents: a BF projection occupies one, an
//! E4 projection four. Residency is chosen by priced farthest-in-future paging
//! with bypass:
//!
//!   * a `Delta` resolution reads two endpoints and subtracts, unless a resident
//!     `Endpoint0` supplies `s0` — then it reads only `s1`;
//!   * resolving `Delta` may EXPOSE `Endpoint0` at no extra source read, so such
//!     a miss may take the paired form;
//!   * a native dual factor is ONE source-pair resolution covering both
//!     projections, never two projection reads;
//!   * `Endpoint0` and `Delta` admissions from one paired resolution are
//!     INDEPENDENT — either, both, or neither may be retained;
//!   * bypass is legal on every miss; and
//!   * every tie is broken by stable lexical order.
//!
//! This is not a variable-size paging solver and there is no cache genome. Order
//! candidates are a bounded, deterministic set of three
//! ([`SeedKind`]) — never a mutation search.
//!
//! # Cost model provenance
//!
//! The BYTE side reuses [`crate::bwd::cost`] unchanged: `fold_element_bytes`
//! under the static materialization policy of §10.2. The ARITHMETIC side
//! (`bf`/`mixed`/`e4` op classes) is this module's own price model, named once in
//! [`source_prices`], because §7.2's fitness needs "source arithmetic by
//! BF/mixed/E4 class" and no earlier task produced one. Task 8's exact cost
//! parity supersedes it.

use std::cmp::Reverse;
use std::collections::{BTreeMap, BTreeSet};

use cs::gkr_compiler::dag_ir::{BwdRegime, FieldKind};

use super::model::{
    CoeffLayer, CoeffTerm, Projection, ProjectionId, SourceId, TermId,
};
use super::stats::backing_field;
use crate::bwd::cost::{CELL_BYTES, EXT_CELLS, fold_element_bytes};
use crate::bwd::distill::DistilledLayer;
use crate::bwd::source::{
    MaterializationPolicy, OriginLeaf, VIRTUAL_SETUP_MATERIALIZE_DEPTH,
};

// ── Budget (§7.3, §12.1: "the budget is c2 through c16") ─────────────────────

/// BF lanes one cell holds: a cell is one 16-byte E4 bucket, i.e. four 4-byte
/// BF lanes.
pub const LANES_PER_CELL: u32 = EXT_CELLS as u32;

const _: () = assert!(LANES_PER_CELL == 4);

/// A validated shared-memory cell budget, `c2` through `c16` (§12.1).
///
/// The `c`-prefixed spelling is the only sanctioned one: a budget counts CELLS,
/// and the old lane-counting spellings (`8`/`12`/`16`) named a different
/// quantity.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CellBudget(u8);

impl CellBudget {
    pub const MIN_CELLS: u8 = 2;
    pub const MAX_CELLS: u8 = 16;

    /// Every legal budget, ascending. The sweep order §7.2's preceding-winner
    /// seed is threaded through.
    pub const ALL: [CellBudget; 15] = [
        CellBudget(2),
        CellBudget(3),
        CellBudget(4),
        CellBudget(5),
        CellBudget(6),
        CellBudget(7),
        CellBudget(8),
        CellBudget(9),
        CellBudget(10),
        CellBudget(11),
        CellBudget(12),
        CellBudget(13),
        CellBudget(14),
        CellBudget(15),
        CellBudget(16),
    ];

    pub fn new(cells: u8) -> Result<Self, ScheduleError> {
        if !(Self::MIN_CELLS..=Self::MAX_CELLS).contains(&cells) {
            return Err(ScheduleError::BudgetOutOfRange { cells });
        }
        Ok(CellBudget(cells))
    }

    pub fn cells(self) -> u8 {
        self.0
    }

    /// BF-lane-equivalents this budget holds: `4 * cells`.
    pub fn lanes(self) -> u32 {
        u32::from(self.0) * LANES_PER_CELL
    }

    /// The `c2`..`c16` label, for reports and panic messages.
    pub fn label(self) -> &'static str {
        const LABELS: [&str; 15] = [
            "c2", "c3", "c4", "c5", "c6", "c7", "c8", "c9", "c10", "c11", "c12", "c13", "c14",
            "c15", "c16",
        ];
        LABELS[(self.0 - Self::MIN_CELLS) as usize]
    }
}

// ── Widths ───────────────────────────────────────────────────────────────────

/// Resident width of one projection. `Bf` sorts BELOW `E4` so the derived order
/// is "narrowest first" and `Reverse(width)` is "widest first" — the eviction
/// ranking's third key.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ValueWidth {
    Bf,
    E4,
}

impl ValueWidth {
    pub fn lanes(self) -> u32 {
        match self {
            ValueWidth::Bf => 1,
            ValueWidth::E4 => LANES_PER_CELL,
        }
    }

    pub fn of(field: FieldKind) -> Self {
        match field {
            FieldKind::Base => ValueWidth::Bf,
            FieldKind::Ext => ValueWidth::E4,
        }
    }
}

// ── Static fold materialization policy (§10.2) ───────────────────────────────

/// First target depth whose first physical access PUBLISHES (§10.2:
/// "target depth < 3: do not publish; target depth >= 3: publish on first
/// physical access").
///
/// One tunable constant, NOT a scheduling decision and NOT a search variable.
pub const PUBLISH_TARGET_DEPTH: u8 = VIRTUAL_SETUP_MATERIALIZE_DEPTH;

const _: () = assert!(PUBLISH_TARGET_DEPTH == 3);

/// §10.2's policy in the vocabulary [`crate::bwd::cost`] already speaks:
/// recompute lazily up to `PUBLISH_TARGET_DEPTH - 1`, read the published buffer
/// from `PUBLISH_TARGET_DEPTH` on.
pub const FOLD_POLICY: MaterializationPolicy =
    MaterializationPolicy::LazyUpTo(PUBLISH_TARGET_DEPTH - 1);

/// The fold depth one regime's program is priced at.
///
/// R0 is round zero, so its depth is exactly `0`. A continuation program is ONE
/// artifact per `(circuit, layer, Ext, budget)` (§13) and must therefore be
/// priced at a single depth; the published steady state is that depth, since it
/// covers every continuation round but the first
/// [`PUBLISH_TARGET_DEPTH`] of them. Callers that want a per-depth sweep pass
/// their own [`PagingRequest::target_depth`].
pub fn default_target_depth(regime: BwdRegime) -> u8 {
    match regime {
        BwdRegime::R0 => 0,
        BwdRegime::Ext => PUBLISH_TARGET_DEPTH,
    }
}

// ── Prices ───────────────────────────────────────────────────────────────────

/// Arithmetic by the three classes §7.2's fitness reports.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct OpCounts {
    pub bf: u32,
    pub mixed: u32,
    pub e4: u32,
}

impl OpCounts {
    pub const ZERO: Self = OpCounts { bf: 0, mixed: 0, e4: 0 };

    pub fn scale(self, n: u32) -> Self {
        OpCounts { bf: self.bf * n, mixed: self.mixed * n, e4: self.e4 * n }
    }

    pub fn plus(self, other: Self) -> Self {
        OpCounts {
            bf: self.bf.saturating_add(other.bf),
            mixed: self.mixed.saturating_add(other.mixed),
            e4: self.e4.saturating_add(other.e4),
        }
    }

    /// One subtraction in `width`'s field — the `ds = s1 - s0` of a `Delta`
    /// resolution (§8).
    pub fn subtraction(width: ValueWidth) -> Self {
        match width {
            ValueWidth::Bf => OpCounts { bf: 1, mixed: 0, e4: 0 },
            ValueWidth::E4 => OpCounts { bf: 0, mixed: 0, e4: 1 },
        }
    }
}

/// What one source costs to resolve, independent of residency and order.
///
/// Both projections of a source share `width`: `Endpoint0` is `s0` and `Delta`
/// is `s1 - s0`, both in the source's resolved storage field.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SourcePrice {
    /// Resident width of either projection of this source.
    pub width: ValueWidth,
    /// DRAM bytes ONE endpoint resolution moves. Zero for a procedural
    /// `VirtualSetup` origin, which the device evaluates in closed form with no
    /// DRAM at all (`bwd::cost`'s VS short-circuit).
    pub element_bytes: u64,
    /// Arithmetic ONE endpoint resolution costs — the lazy fold catch-up, or the
    /// procedural closed form. Zero for a plain load.
    pub endpoint_ops: OpCounts,
}

/// The price of rebuilding one projection FROM SCRATCH — the eviction ranking's
/// second key.
///
/// Lexicographic in DECLARED FIELD ORDER, via a derived `Ord`, so the field
/// order and the comparison order cannot drift apart.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RebuildPrice {
    pub source_read_bytes: u64,
    pub bf_ops: u32,
    pub mixed_ops: u32,
    pub e4_ops: u32,
}

impl RebuildPrice {
    /// Scalarization used ONLY by the seed constructor's knapsack frontier proxy
    /// ([`budget_aware_greedy_order`]), never by [`PagingCost`] or the
    /// certificate.
    ///
    /// The incumbent constructor scored a value by its DRAM bytes alone
    /// (`production.rs`'s `read_cost = demand.miss_cost.dram_bytes()`). Bytes
    /// therefore stay strictly dominant here — [`PROXY_BYTE_WEIGHT`] exceeds any
    /// op contribution a single projection can accumulate — and the op classes
    /// only separate values whose byte cost ties, ordered by relative expense.
    pub fn proxy_cost(self) -> u128 {
        u128::from(self.source_read_bytes) * PROXY_BYTE_WEIGHT
            + u128::from(self.e4_ops) * PROXY_E4_OP_WEIGHT
            + u128::from(self.mixed_ops) * PROXY_MIXED_OP_WEIGHT
            + u128::from(self.bf_ops) * PROXY_BF_OP_WEIGHT
    }
}

const PROXY_BYTE_WEIGHT: u128 = 64;
const PROXY_E4_OP_WEIGHT: u128 = 4;
const PROXY_MIXED_OP_WEIGHT: u128 = 2;
const PROXY_BF_OP_WEIGHT: u128 = 1;

/// Per-source prices for one lowered layer at one fold depth.
///
/// # Byte side (reused, not invented)
///
/// A `VirtualSetup` origin moves zero DRAM. Every other origin costs
/// `fold_element_bytes(read_fold_state(FOLD_POLICY, target_depth), w)` where `w`
/// is the origin's own BACKING width — [`backing_field`], the same resolution
/// `stats` uses, so an R0 materialized-sink read is measured at the sink's field
/// and not silently at base width.
///
/// # Arithmetic side (this module's price model)
///
/// Named here so it is greppable and replaceable by Task 8's exact parity:
///
///   * a plain load (depth 0, or a published buffer at
///     `target_depth >= PUBLISH_TARGET_DEPTH`) costs no arithmetic;
///   * a lazy Read-origin catch-up at depth `d` combines `2^d - 1` times, in the
///     `mixed` class for a base-valued backing (base originals against Ext fold
///     weights) and in the `e4` class for an Ext-valued one; and
///   * a procedural `VirtualSetup` origin uses the `O(k)` multilinear closed
///     form, `max(d, 1)` combines, `mixed` because the polynomial is base-valued
///     and the fold weights are not.
pub fn source_prices(
    lowered: &CoeffLayer,
    distilled: &DistilledLayer,
    target_depth: u8,
) -> Vec<SourcePrice> {
    let state = crate::bwd::cost::read_fold_state(FOLD_POLICY, target_depth);
    lowered
        .sources
        .iter()
        .map(|source| {
            let width = ValueWidth::of(source.field);
            match &source.origin {
                OriginLeaf::VirtualSetup { .. } => SourcePrice {
                    width,
                    element_bytes: 0,
                    endpoint_ops: OpCounts {
                        bf: 0,
                        mixed: u32::from(target_depth).max(1),
                        e4: 0,
                    },
                },
                OriginLeaf::Read(place) => {
                    let backing = backing_field(place, source, distilled);
                    let cells = match backing {
                        FieldKind::Base => 1,
                        FieldKind::Ext => EXT_CELLS,
                    };
                    let element_bytes = fold_element_bytes(state, cells) as u64;
                    let combines = match state {
                        crate::bwd::source::FoldState::Materialized => 0,
                        crate::bwd::source::FoldState::LazyFromOriginals { depth } => {
                            (1u32 << depth) - 1
                        }
                    };
                    let endpoint_ops = match backing {
                        FieldKind::Base => OpCounts { bf: 0, mixed: combines, e4: 0 },
                        FieldKind::Ext => OpCounts { bf: 0, mixed: 0, e4: combines },
                    };
                    SourcePrice { width, element_bytes, endpoint_ops }
                }
            }
        })
        .collect()
}

const _: () = assert!(CELL_BYTES == 4);

// ── Resolution groups (brief Task 4) ─────────────────────────────────────────

/// One PHYSICAL source resolution.
///
/// `Pair` is §8's `PlannedDelta`: one source-pair resolution producing both
/// projections, legal for a `Delta` miss (which reads `s0` anyway) and REQUIRED
/// for a native dual factor (which consumes both). An `Endpoint0`-only use never
/// resolves `s1` and so must stay `Single`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ResolutionGroup {
    Single(ProjectionId),
    Pair { source: SourceId, endpoint0: ProjectionId, delta: ProjectionId },
}

impl ResolutionGroup {
    pub fn source(&self) -> SourceId {
        match self {
            ResolutionGroup::Single(p) => p.source,
            ResolutionGroup::Pair { source, .. } => *source,
        }
    }

    /// The projections this group touches, in canonical order (`Endpoint0`
    /// before `Delta`).
    pub fn projections(&self) -> Vec<ProjectionId> {
        match self {
            ResolutionGroup::Single(p) => vec![*p],
            ResolutionGroup::Pair { endpoint0, delta, .. } => vec![*endpoint0, *delta],
        }
    }
}

// ── Plan ─────────────────────────────────────────────────────────────────────

/// What happened to one projection of one resolution group.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ProjectionOutcome {
    /// Served from the resident set; no source read.
    Hit,
    /// Resolved from source and RETAINED for a later use.
    Fill,
    /// Resolved from source and consumed without being stored (§7.1: "bypass is
    /// legal on every miss").
    Bypass,
}

impl ProjectionOutcome {
    pub fn is_hit(self) -> bool {
        self == ProjectionOutcome::Hit
    }
}

/// One projection's participation in a resolution group.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProjectionAction {
    pub projection: ProjectionId,
    /// `true` when the term actually reads this projection; `false` for an
    /// `Endpoint0` merely EXPOSED by a `Delta` resolution.
    pub consumed: bool,
    pub outcome: ProjectionOutcome,
}

/// One physical resolution, with every decision it caused.
///
/// Task 5 derives live intervals from `resident_after` and may not alter
/// `group`, `projections`, `evicted`, or `resident_after`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PagingAction {
    /// Dense index in [`PagingPlan::actions`].
    pub step: u32,
    pub term: TermId,
    /// Position of `term` in [`PagingPlan::order`] — the next-use clock.
    pub position: u32,
    /// Which deduplicated resolution group of `term` this is.
    pub slot: u8,
    pub group: ResolutionGroup,
    /// One entry per projection of `group`, in `group`'s canonical order.
    pub projections: Vec<ProjectionAction>,
    pub source_read_bytes: u64,
    pub bf_ops: u32,
    pub mixed_ops: u32,
    pub e4_ops: u32,
    /// Projections dropped at this step, in eviction order. A projection this
    /// step produced is BYPASSED instead of appearing here.
    pub evicted: Vec<ProjectionId>,
    /// The complete resident set after this step, ascending.
    pub resident_after: Vec<ProjectionId>,
    /// `resident_after`'s total width in BF-lane-equivalents.
    pub resident_lanes_after: u32,
}

/// Total modeled cost of a plan, in §7.2's vocabulary.
///
/// Emitted move count and encoded program bytes are absent because moves are
/// Task 5's and the encoding is Task 8's; the fitness components that exist at
/// this stage are complete.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PagingCost {
    pub source_read_bytes: u64,
    pub bf_ops: u64,
    pub mixed_ops: u64,
    pub e4_ops: u64,
    /// Physical source resolutions — a native dual factor counts ONCE (§12.3).
    pub source_resolutions: u64,
    pub hits: u64,
    pub misses: u64,
    pub fills: u64,
    pub bypasses: u64,
    pub evictions: u64,
    pub peak_resident_lanes: u32,
}

impl PagingCost {
    /// §7.2's fitness, restricted to the components this stage can measure.
    pub fn score(&self) -> PagingScore {
        PagingScore {
            source_read_bytes: self.source_read_bytes,
            e4_ops: self.e4_ops,
            mixed_ops: self.mixed_ops,
            bf_ops: self.bf_ops,
        }
    }
}

/// Comparable fitness: realized source-read bytes, then source arithmetic by
/// class from most to least expensive (§7.2). Derived `Ord` = that lexicographic
/// order.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct PagingScore {
    pub source_read_bytes: u64,
    pub e4_ops: u64,
    pub mixed_ops: u64,
    pub bf_ops: u64,
}

/// Which order the paging plan was built from.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PagingRequest {
    pub budget: CellBudget,
    /// Fold depth the prices were taken at — plan identity only; the pager reads
    /// prices, not depths.
    pub target_depth: u8,
}

/// A complete, replayable residency plan.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PagingPlan {
    pub regime: BwdRegime,
    pub request: PagingRequest,
    pub order: Vec<TermId>,
    pub actions: Vec<PagingAction>,
    pub cost: PagingCost,
}

impl PagingPlan {
    /// Canonical little-endian serialization of every decision in the plan.
    ///
    /// The determinism gate compares these bytes, so it must cover EVERY field a
    /// later task may read.
    pub fn canonical_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(64 + self.actions.len() * 48);
        out.push(match self.regime {
            BwdRegime::R0 => 0,
            BwdRegime::Ext => 1,
        });
        out.push(self.request.budget.cells());
        out.push(self.request.target_depth);
        push_u32(&mut out, self.order.len() as u32);
        for t in &self.order {
            push_u32(&mut out, t.0);
        }
        push_u32(&mut out, self.actions.len() as u32);
        for a in &self.actions {
            push_u32(&mut out, a.step);
            push_u32(&mut out, a.term.0);
            push_u32(&mut out, a.position);
            out.push(a.slot);
            match a.group {
                ResolutionGroup::Single(p) => {
                    out.push(0);
                    push_projection(&mut out, p);
                }
                ResolutionGroup::Pair { source, endpoint0, delta } => {
                    out.push(1);
                    push_u32(&mut out, source.0);
                    push_projection(&mut out, endpoint0);
                    push_projection(&mut out, delta);
                }
            }
            out.push(a.projections.len() as u8);
            for p in &a.projections {
                push_projection(&mut out, p.projection);
                out.push(u8::from(p.consumed));
                out.push(match p.outcome {
                    ProjectionOutcome::Hit => 0,
                    ProjectionOutcome::Fill => 1,
                    ProjectionOutcome::Bypass => 2,
                });
            }
            push_u64(&mut out, a.source_read_bytes);
            push_u32(&mut out, a.bf_ops);
            push_u32(&mut out, a.mixed_ops);
            push_u32(&mut out, a.e4_ops);
            push_u32(&mut out, a.evicted.len() as u32);
            for p in &a.evicted {
                push_projection(&mut out, *p);
            }
            push_u32(&mut out, a.resident_after.len() as u32);
            for p in &a.resident_after {
                push_projection(&mut out, *p);
            }
            push_u32(&mut out, a.resident_lanes_after);
        }
        let c = &self.cost;
        for v in [
            c.source_read_bytes,
            c.bf_ops,
            c.mixed_ops,
            c.e4_ops,
            c.source_resolutions,
            c.hits,
            c.misses,
            c.fills,
            c.bypasses,
            c.evictions,
        ] {
            push_u64(&mut out, v);
        }
        push_u32(&mut out, c.peak_resident_lanes);
        out
    }
}

fn push_u32(out: &mut Vec<u8>, v: u32) {
    out.extend_from_slice(&v.to_le_bytes());
}

fn push_u64(out: &mut Vec<u8>, v: u64) {
    out.extend_from_slice(&v.to_le_bytes());
}

fn push_projection(out: &mut Vec<u8>, p: ProjectionId) {
    push_u32(out, p.source.0);
    out.push(match p.projection {
        Projection::Endpoint0 => 0,
        Projection::Delta => 1,
    });
}

// ── Errors ───────────────────────────────────────────────────────────────────

/// Everything the pager can reject, all derivable from its inputs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ScheduleError {
    /// §12.1: the budget is c2 through c16.
    BudgetOutOfRange { cells: u8 },
    /// The order is not a permutation of `0..terms.len()`.
    OrderNotAPermutation { terms: usize, order: usize },
    /// The order names a term outside the layer.
    UnknownTerm { term: TermId },
    /// A term operand names a source outside `CoeffLayer::sources`, or the price
    /// table is shorter than the source table.
    UnknownSource { term: TermId, source: SourceId },
    /// The price table's resident width for a source disagrees with the layer's
    /// own [`CoeffSource::field`](super::model::CoeffSource::field).
    ///
    /// [`SourcePrice::width`] and `CoeffSource::field` are two spellings of one
    /// fact. [`source_prices`] derives the former FROM the latter and so cannot
    /// disagree, but a caller-built price table can — and then the eviction
    /// ranking, the lane accounting and the physical placement would all size a
    /// projection differently from its opcode category. Every entry point that
    /// reads `prices[..].width` validates the pair first, so the two can never
    /// silently drift.
    PriceWidthMismatch { source: SourceId, price: ValueWidth, layer: FieldKind },
    /// A term declares an operand field its source does not have, so the term's
    /// opcode category and the resident width would disagree.
    OperandFieldConflict {
        term: TermId,
        source: SourceId,
        term_field: FieldKind,
        source_field: FieldKind,
    },
    /// A term projects a role its opcode cannot consume (`C0Linear` over
    /// `Delta`, `C2Product` over `Endpoint0`).
    ProjectionRoleMismatch { term: TermId, expected: Projection, found: Projection },
    /// The projections a term's LATER operand slots still need do not themselves
    /// fit the budget, so no legal eviction exists.
    ///
    /// Unreachable for `c2` and above: a term has at most two operand slots, so
    /// at most one later slot pins at most one source pair, i.e. at most eight
    /// BF-lane-equivalents — exactly `c2`.
    PinnedSetExceedsBudget { term: TermId, pinned_lanes: u32, capacity_lanes: u32 },
}

/// Everything the independent certificate can reject.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PagingCertificateError {
    /// The plan's own header disagrees with the layer it is replayed against.
    RegimeMismatch { declared: BwdRegime, found: BwdRegime },
    /// The action stream is not the structural expansion of `order`.
    ActionCountMismatch { expected: usize, found: usize },
    StepMismatch { step: usize, declared: u32 },
    TermMismatch { step: usize, expected: TermId, found: TermId },
    PositionMismatch { step: usize, expected: u32, found: u32 },
    SlotMismatch { step: usize, expected: u8, found: u8 },
    /// The declared group is not a legal form for this operand slot: a paired
    /// resolution on an `Endpoint0`-only use, a single resolution on a native
    /// dual factor, or a group over the wrong source/projection.
    IllegalResolutionGroup { step: usize, term: TermId, group: ResolutionGroup },
    /// The declared projection list does not match the declared group.
    ProjectionListMismatch { step: usize },
    /// A projection is declared consumed when the term does not read it, or vice
    /// versa.
    ConsumptionMismatch { step: usize, projection: ProjectionId, declared: bool },
    /// A declared `Hit` on a non-resident projection, or a declared miss on a
    /// resident one.
    OutcomeMismatch { step: usize, projection: ProjectionId, declared: ProjectionOutcome },
    /// A `Fill` that is absent from `resident_after`, or a `Bypass`/`Hit`
    /// residency that contradicts it.
    ResidencyContradictsOutcome { step: usize, projection: ProjectionId },
    /// The declared per-step cost is not the cost the declared group and the
    /// certificate's own resident set imply.
    StepCostMismatch { step: usize, field: &'static str, declared: u64, derived: u64 },
    /// The declared resident set is not what the declared decisions produce.
    ResidentSetMismatch { step: usize, declared: Vec<ProjectionId>, derived: Vec<ProjectionId> },
    ResidentLanesMismatch { step: usize, declared: u32, derived: u32 },
    /// Residency exceeds `4 * cell_budget` after a step.
    CapacityExceeded { step: usize, lanes: u32, capacity: u32 },
    /// An eviction of a projection that was not resident.
    EvictedNotResident { step: usize, projection: ProjectionId },
    /// An eviction of a projection a later operand slot of the same term still
    /// needs (§12.2: "no term-side fill clobbers another input needed by that
    /// term").
    EvictedPinned { step: usize, projection: ProjectionId },
    /// A projection with no remaining use is still resident, so a later fill
    /// would be charged against a dead lifetime.
    ExpiredStillResident { step: usize, projection: ProjectionId },
    /// A resident projection was admitted twice (§12.2: "no duplicate resident
    /// copies violate the fixed paging plan").
    DuplicateResidentAdmission { step: usize, projection: ProjectionId },
    /// The declared total does not equal the replayed total.
    TotalCostMismatch { field: &'static str, declared: u64, derived: u64 },
    /// The plan's structure is itself rejected by the shared structural
    /// expansion.
    Structure(ScheduleError),
}

impl From<ScheduleError> for PagingCertificateError {
    fn from(e: ScheduleError) -> Self {
        PagingCertificateError::Structure(e)
    }
}

// ── Price-table validation ───────────────────────────────────────────────────

/// Reject a price table that does not describe `layer`.
///
/// Two independent facts are checked, both derivable from the inputs:
///
///   * the table covers every [`SourceId`] the layer names; and
///   * every [`SourcePrice::width`] equals the layer's own
///     [`CoeffSource::field`](super::model::CoeffSource::field) for that source.
///
/// The second check exists because width has two spellings. [`source_prices`]
/// keeps them in sync by construction (`ValueWidth::of(source.field)`), but
/// nothing else did: [`page_projections`], [`certify_paging_plan`],
/// [`budget_aware_greedy_order`] and the physical placement all read
/// `prices[..].width` for lane accounting, while `term_slots`'s own `agree()`
/// compares a term's DECLARED operand field against the source field — a
/// different pair. A price table claiming `Bf` for an `Ext` source would therefore
/// have been accepted, and every downstream lane count would be four times wrong.
///
/// Called by every entry point that reads a price width, so a mismatch is
/// impossible to smuggle past.
pub fn validate_prices(layer: &CoeffLayer, prices: &[SourcePrice]) -> Result<(), ScheduleError> {
    if prices.len() < layer.sources.len() {
        return Err(ScheduleError::UnknownSource {
            term: TermId(u32::MAX),
            source: SourceId(prices.len() as u32),
        });
    }
    for (index, source) in layer.sources.iter().enumerate() {
        let price = prices[index];
        let expected = ValueWidth::of(source.field);
        if price.width != expected {
            return Err(ScheduleError::PriceWidthMismatch {
                source: SourceId(index as u32),
                price: price.width,
                layer: source.field,
            });
        }
    }
    Ok(())
}

// ── Structural expansion: terms to resolution-group skeletons ────────────────
//
// PURELY structural: derived from `CoeffLayer` alone, with no reference to any
// residency, price, budget, or order. Both the pager and the certificate build
// it, which is what lets the certificate check the SHAPE of an action stream
// without re-deciding anything.

/// The legal forms one operand slot may take.
///
/// Public because physical placement (design §7.3) has to know, per emitted
/// resolution, whether the slot consumes `Endpoint0` only, `Delta` only, or both
/// projections of a native dual factor — and re-deriving that from
/// [`CoeffTerm`] in a second place would be a drift hazard. It is a
/// STRUCTURAL classification of the layer, never a decision.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SlotKind {
    /// A `C0Linear` operand: `Endpoint0` only, `Single` forever (§8).
    Endpoint0Only(ProjectionId),
    /// A `C2Product` operand: `Delta`; `Single`, or `Pair` when the resolution
    /// exposes `Endpoint0`.
    DeltaOnly(ProjectionId),
    /// A native dual factor: always `Pair`, both projections consumed.
    DualFactor(SourceId),
}

impl SlotKind {
    /// The projections the TERM reads through this slot. Crate-internal: the
    /// pager and the certificate need it, placement does not.
    fn consumed(self) -> Vec<ProjectionId> {
        match self {
            SlotKind::Endpoint0Only(p) | SlotKind::DeltaOnly(p) => vec![p],
            SlotKind::DualFactor(s) => {
                vec![ProjectionId::endpoint0(s), ProjectionId::delta(s)]
            }
        }
    }

    pub fn source(self) -> SourceId {
        match self {
            SlotKind::Endpoint0Only(p) | SlotKind::DeltaOnly(p) => p.source,
            SlotKind::DualFactor(s) => s,
        }
    }
}

/// One term's DEDUPLICATED operand slots, in canonical operand order.
///
/// A repeated operand (`C2Product { lhs: d, rhs: d }`, `DualProduct { lhs: s,
/// rhs: s }`) is ONE physical resolution, so it appears once. Because the two
/// product forms take operands of a single role, the surviving slots of a term
/// always consume DISJOINT projection sets — which is what makes per-slot
/// next-use bookkeeping unambiguous.
pub fn term_slots(layer: &CoeffLayer, term: &CoeffTerm) -> Result<Vec<SlotKind>, ScheduleError> {
    let id = term.id();
    let check = |p: ProjectionId, expected: Projection| -> Result<(), ScheduleError> {
        if p.projection != expected {
            return Err(ScheduleError::ProjectionRoleMismatch {
                term: id,
                expected,
                found: p.projection,
            });
        }
        Ok(())
    };
    let field_of = |source: SourceId| -> Result<FieldKind, ScheduleError> {
        layer
            .source(source)
            .map(|s| s.field)
            .ok_or(ScheduleError::UnknownSource { term: id, source })
    };
    let agree = |source: SourceId, term_field: FieldKind| -> Result<(), ScheduleError> {
        let source_field = field_of(source)?;
        if source_field != term_field {
            return Err(ScheduleError::OperandFieldConflict {
                term: id,
                source,
                term_field,
                source_field,
            });
        }
        Ok(())
    };

    let slots = match term {
        CoeffTerm::C0Linear { value, field, .. } => {
            check(*value, Projection::Endpoint0)?;
            agree(value.source, *field)?;
            vec![SlotKind::Endpoint0Only(*value)]
        }
        CoeffTerm::C2Product { lhs, rhs, lhs_field, rhs_field, .. } => {
            check(*lhs, Projection::Delta)?;
            check(*rhs, Projection::Delta)?;
            agree(lhs.source, *lhs_field)?;
            agree(rhs.source, *rhs_field)?;
            if lhs == rhs {
                vec![SlotKind::DeltaOnly(*lhs)]
            } else {
                vec![SlotKind::DeltaOnly(*lhs), SlotKind::DeltaOnly(*rhs)]
            }
        }
        CoeffTerm::DualProduct { lhs, rhs, .. } => {
            // §6: a native dual is continuation-only and every continuation
            // source is an Ext fold leaf; the field check keeps a base-valued
            // dual factor from silently claiming one lane.
            agree(*lhs, FieldKind::Ext)?;
            agree(*rhs, FieldKind::Ext)?;
            if lhs == rhs {
                vec![SlotKind::DualFactor(*lhs)]
            } else {
                vec![SlotKind::DualFactor(*lhs), SlotKind::DualFactor(*rhs)]
            }
        }
    };
    Ok(slots)
}

/// `(term position, slot index, slot kind)` for every physical resolution the
/// order implies, in execution sequence.
fn expand(layer: &CoeffLayer, order: &[TermId]) -> Result<Vec<(u32, u8, SlotKind)>, ScheduleError> {
    if order.len() != layer.terms.len() {
        return Err(ScheduleError::OrderNotAPermutation {
            terms: layer.terms.len(),
            order: order.len(),
        });
    }
    let mut seen = vec![false; layer.terms.len()];
    let mut out = Vec::with_capacity(layer.terms.len() * 2);
    for (position, &id) in order.iter().enumerate() {
        let index = id.0 as usize;
        let term = layer.terms.get(index).ok_or(ScheduleError::UnknownTerm { term: id })?;
        if std::mem::replace(&mut seen[index], true) {
            return Err(ScheduleError::OrderNotAPermutation {
                terms: layer.terms.len(),
                order: order.len(),
            });
        }
        // `?`, NOT `.into_iter().flatten()`: flattening a `Result` yields an
        // EMPTY iterator on `Err`, which would make `ProjectionRoleMismatch`,
        // `OperandFieldConflict` and `UnknownSource` inert and silently drop a
        // malformed term from the action stream — in the certificate as well as
        // the pager, since both expand through here.
        for (slot, kind) in term_slots(layer, term)?.into_iter().enumerate() {
            out.push((position as u32, slot as u8, kind));
        }
    }
    Ok(out)
}

/// Ascending DISTINCT term positions at which each projection is consumed.
///
/// Position, not step: a term is the ISA's unit of work, so two operands of one
/// term share a next-use distance. That is exactly why the eviction ranking
/// needs its price / width / id tie breaks at all.
fn next_use_queues(
    layer: &CoeffLayer,
    order: &[TermId],
) -> Result<Vec<Vec<u32>>, ScheduleError> {
    let mut queues = vec![Vec::new(); 2 * layer.sources.len()];
    for (position, &id) in order.iter().enumerate() {
        let term =
            layer.terms.get(id.0 as usize).ok_or(ScheduleError::UnknownTerm { term: id })?;
        let mut touched: BTreeSet<ProjectionId> = BTreeSet::new();
        term.for_each_projection_use(|p| {
            touched.insert(p);
        });
        for p in touched {
            let index = projection_index(p);
            if index >= queues.len() {
                return Err(ScheduleError::UnknownSource { term: id, source: p.source });
            }
            queues[index].push(position as u32);
        }
    }
    Ok(queues)
}

/// Dense index of a projection: `2 * source + role`. Task 5 may reuse it for its
/// own per-projection tables.
pub fn projection_index(p: ProjectionId) -> usize {
    2 * p.source.0 as usize
        + match p.projection {
            Projection::Endpoint0 => 0,
            Projection::Delta => 1,
        }
}

/// Static rebuild price of every projection, indexed by [`projection_index`].
///
/// `Endpoint0` resolves one endpoint. `Delta` resolves two and subtracts, so it
/// is never cheaper than its `Endpoint0` — the ranking's "cheapest rebuild"
/// key therefore prefers evicting endpoints over deltas at equal distance.
fn rebuild_prices(prices: &[SourcePrice]) -> Vec<RebuildPrice> {
    let mut out = Vec::with_capacity(2 * prices.len());
    for price in prices {
        let one = RebuildPrice {
            source_read_bytes: price.element_bytes,
            bf_ops: price.endpoint_ops.bf,
            mixed_ops: price.endpoint_ops.mixed,
            e4_ops: price.endpoint_ops.e4,
        };
        let two = price.endpoint_ops.scale(2).plus(OpCounts::subtraction(price.width));
        out.push(one);
        out.push(RebuildPrice {
            source_read_bytes: price.element_bytes.saturating_mul(2),
            bf_ops: two.bf,
            mixed_ops: two.mixed,
            e4_ops: two.e4,
        });
    }
    out
}

// ── Residency ────────────────────────────────────────────────────────────────

/// The eviction ranking, lexicographic in DECLARED FIELD ORDER: farthest next
/// use, then cheapest rebuild price, then widest value, then stable
/// `ProjectionId`. The BTreeSet's FIRST element is the top victim.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct EvictionKey {
    farthest_next_use: Reverse<u32>,
    cheapest_rebuild: RebuildPrice,
    widest_value: Reverse<ValueWidth>,
    projection: ProjectionId,
}

struct Residency {
    ranked: BTreeSet<EvictionKey>,
    keys: Vec<Option<EvictionKey>>,
    lanes: u32,
}

impl Residency {
    fn new(projections: usize) -> Self {
        Residency { ranked: BTreeSet::new(), keys: vec![None; projections], lanes: 0 }
    }

    fn contains(&self, p: ProjectionId) -> bool {
        self.keys[projection_index(p)].is_some()
    }

    fn insert(&mut self, key: EvictionKey, width: ValueWidth) {
        let slot = &mut self.keys[projection_index(key.projection)];
        debug_assert!(slot.is_none(), "admission of an already resident projection");
        *slot = Some(key);
        self.ranked.insert(key);
        self.lanes += width.lanes();
    }

    fn remove(&mut self, p: ProjectionId, width: ValueWidth) {
        if let Some(key) = self.keys[projection_index(p)].take() {
            self.ranked.remove(&key);
            self.lanes -= width.lanes();
        }
    }

    /// Re-key a resident projection whose next use advanced.
    fn rekey(&mut self, p: ProjectionId, next_use: u32) {
        let slot = &mut self.keys[projection_index(p)];
        if let Some(old) = *slot {
            self.ranked.remove(&old);
            let new = EvictionKey { farthest_next_use: Reverse(next_use), ..old };
            *slot = Some(new);
            self.ranked.insert(new);
        }
    }

    fn snapshot(&self) -> Vec<ProjectionId> {
        let mut out: Vec<ProjectionId> = self.ranked.iter().map(|k| k.projection).collect();
        out.sort_unstable();
        out
    }
}

// ── The pager ────────────────────────────────────────────────────────────────

/// Page one FIXED term order at one budget (§7.1).
///
/// Deterministic and total: no randomness, no clock, no environment. Complexity
/// is `O(U log P)` for `U` resolutions and `P` projections — `U <= 2 * terms`
/// and `P <= 2 * sources`, both of which the Task-3 census MEASURED
/// (`MAX_TERMS = 1791`, `MAX_PROJECTIONS = 1731`). Nothing here is sized by
/// fragments or monomials, so §5.4's 46x distribution expansion enters only
/// through those measured counts.
pub fn page_projections(
    layer: &CoeffLayer,
    prices: &[SourcePrice],
    request: PagingRequest,
    order: &[TermId],
) -> Result<PagingPlan, ScheduleError> {
    validate_prices(layer, prices)?;
    let capacity = request.budget.lanes();
    let sequence = expand(layer, order)?;
    let queues = next_use_queues(layer, order)?;
    let rebuild = rebuild_prices(prices);

    let mut cursor = vec![0usize; queues.len()];
    let mut residency = Residency::new(queues.len());
    let mut actions = Vec::with_capacity(sequence.len());
    let mut cost = PagingCost::default();

    let width_of = |p: ProjectionId| prices[p.source.0 as usize].width;
    let next_use = |cursor: &[usize], p: ProjectionId| -> Option<u32> {
        let i = projection_index(p);
        queues[i].get(cursor[i]).copied()
    };

    for (step, (position, slot, kind)) in sequence.iter().copied().enumerate() {
        // Step 1 — expire. A resident only loses its next use by being consumed,
        // and consumption expires it immediately below, so at the top of a step
        // every resident still has one. The invariant is validated EXTERNALLY by
        // the certificate's `ExpiredStillResident` check, not asserted here.

        // Every projection a LATER operand slot of this term still needs is
        // pinned, and pinning is applied BEFORE ranking so a pinned projection
        // can never be picked and then excused.
        let mut pinned: BTreeSet<ProjectionId> = BTreeSet::new();
        for (later_position, _, later) in sequence[step + 1..].iter() {
            if *later_position != position {
                break;
            }
            for p in later.consumed() {
                pinned.insert(p);
            }
        }
        let pinned_lanes: u32 =
            pinned.iter().filter(|p| residency.contains(**p)).map(|p| width_of(*p).lanes()).sum();
        if pinned_lanes > capacity {
            return Err(ScheduleError::PinnedSetExceedsBudget {
                term: order[position as usize],
                pinned_lanes,
                capacity_lanes: capacity,
            });
        }

        let source = kind.source();
        let price = prices[source.0 as usize];
        let e0 = ProjectionId::endpoint0(source);
        let ds = ProjectionId::delta(source);

        // Steps 2/3 — serve residents as hits, resolve misses directly. The
        // group form follows from the slot's legal forms and residency alone.
        let (group, consumed, endpoints_read, subtractions) = match kind {
            SlotKind::Endpoint0Only(p) => {
                let read = u32::from(!residency.contains(p));
                (ResolutionGroup::Single(p), vec![p], read, 0)
            }
            SlotKind::DeltaOnly(p) => {
                if residency.contains(p) {
                    (ResolutionGroup::Single(p), vec![p], 0, 0)
                } else if residency.contains(e0) {
                    // §8: `s0` comes from the resident Endpoint0, so only `s1` is
                    // read and Endpoint0 is not re-produced.
                    (ResolutionGroup::Single(p), vec![p], 1, 1)
                } else if next_use(&cursor, e0).is_some() {
                    // §7.1: resolving Delta exposes Endpoint0 without a second
                    // source resolution, and it is worth exposing exactly when a
                    // later term reads it.
                    (
                        ResolutionGroup::Pair { source, endpoint0: e0, delta: ds },
                        vec![p],
                        2,
                        1,
                    )
                } else {
                    (ResolutionGroup::Single(p), vec![p], 2, 1)
                }
            }
            SlotKind::DualFactor(s) => {
                let have_e0 = residency.contains(e0);
                let have_ds = residency.contains(ds);
                let read = match (have_e0, have_ds) {
                    (true, true) => 0,
                    // One endpoint suffices: the resident projection supplies the
                    // other half of the pair.
                    (true, false) | (false, true) => 1,
                    (false, false) => 2,
                };
                let subtract = u32::from(!have_ds);
                (
                    ResolutionGroup::Pair {
                        source: s,
                        endpoint0: e0,
                        delta: ds,
                    },
                    vec![e0, ds],
                    read,
                    subtract,
                )
            }
        };

        let step_bytes = price.element_bytes.saturating_mul(u64::from(endpoints_read));
        let step_ops = price
            .endpoint_ops
            .scale(endpoints_read)
            .plus(OpCounts::subtraction(price.width).scale(subtractions));
        if endpoints_read > 0 {
            cost.source_resolutions += 1;
        }
        cost.source_read_bytes = cost.source_read_bytes.saturating_add(step_bytes);
        cost.bf_ops = cost.bf_ops.saturating_add(u64::from(step_ops.bf));
        cost.mixed_ops = cost.mixed_ops.saturating_add(u64::from(step_ops.mixed));
        cost.e4_ops = cost.e4_ops.saturating_add(u64::from(step_ops.e4));

        let touched = group.projections();
        let hits: Vec<bool> = touched.iter().map(|p| residency.contains(*p)).collect();
        for (p, hit) in touched.iter().zip(&hits) {
            let counts = consumed.contains(p);
            if !counts {
                continue;
            }
            if *hit {
                cost.hits += 1;
            } else {
                cost.misses += 1;
            }
        }

        // Advance the next-use clock for everything this term reads, then expire
        // whatever that consumed for the last time.
        for p in &consumed {
            let i = projection_index(*p);
            if queues[i].get(cursor[i]) == Some(&position) {
                cursor[i] += 1;
            }
            match queues[i].get(cursor[i]).copied() {
                Some(next) => residency.rekey(*p, next),
                None => residency.remove(*p, width_of(*p)),
            }
        }

        // Step 4 — the post-use candidate set: current residents plus newly
        // produced projections that have another use. A produced projection with
        // no further use is never a candidate; it is bypassed by definition.
        let mut produced: BTreeSet<ProjectionId> = BTreeSet::new();
        for (p, hit) in touched.iter().zip(&hits) {
            if *hit || residency.contains(*p) {
                continue;
            }
            if let Some(next) = next_use(&cursor, *p) {
                residency.insert(
                    EvictionKey {
                        farthest_next_use: Reverse(next),
                        cheapest_rebuild: rebuild[projection_index(*p)],
                        widest_value: Reverse(price.width),
                        projection: *p,
                    },
                    price.width,
                );
                produced.insert(*p);
            }
        }

        // Steps 5/6/7 — rank, evict until the total width fits, and record a
        // just-produced victim as a bypass rather than a fill-then-evict.
        let mut evicted = Vec::new();
        while residency.lanes > capacity {
            let victim = residency
                .ranked
                .iter()
                .find(|key| !pinned.contains(&key.projection))
                .map(|key| key.projection);
            let Some(victim) = victim else {
                return Err(ScheduleError::PinnedSetExceedsBudget {
                    term: order[position as usize],
                    pinned_lanes: residency.lanes,
                    capacity_lanes: capacity,
                });
            };
            residency.remove(victim, width_of(victim));
            if produced.contains(&victim) {
                // Step 7: a projection this step produced and immediately
                // selected for eviction is BYPASSED — it was never stored, so it
                // is not an eviction. Its `Bypass` outcome follows from it no
                // longer being resident.
            } else {
                cost.evictions += 1;
                evicted.push(victim);
            }
        }

        let projections: Vec<ProjectionAction> = touched
            .iter()
            .zip(&hits)
            .map(|(p, hit)| {
                let outcome = if *hit {
                    ProjectionOutcome::Hit
                } else if residency.contains(*p) {
                    cost.fills += 1;
                    ProjectionOutcome::Fill
                } else {
                    cost.bypasses += 1;
                    ProjectionOutcome::Bypass
                };
                ProjectionAction { projection: *p, consumed: consumed.contains(p), outcome }
            })
            .collect();

        cost.peak_resident_lanes = cost.peak_resident_lanes.max(residency.lanes);
        actions.push(PagingAction {
            step: step as u32,
            term: order[position as usize],
            position,
            slot,
            group,
            projections,
            source_read_bytes: step_bytes,
            bf_ops: step_ops.bf,
            mixed_ops: step_ops.mixed,
            e4_ops: step_ops.e4,
            evicted,
            resident_after: residency.snapshot(),
            resident_lanes_after: residency.lanes,
        });
    }

    Ok(PagingPlan { regime: layer.regime, request, order: order.to_vec(), actions, cost })
}

// ── The independent certificate (§12.2, §12.4) ───────────────────────────────

/// Replay an emitted action stream and reject it unless every declared cost,
/// hit/miss state, width, paired resolution and resident set is exactly what the
/// stream's OWN decisions imply.
///
/// # Independence
///
/// This function shares NO decision code with [`page_projections`]. It calls
/// neither the eviction ranking ([`EvictionKey`]) nor the admission rule, and it
/// never consults a next-use distance to decide anything. What it shares is
/// three things that are not decisions:
///
///   * [`expand`] — the structural operand-slot expansion of the layer, which is
///     a function of `CoeffLayer` alone;
///   * [`next_use_queues`] — likewise structural, used ONLY to decide whether a
///     projection still has a use (expiry) and never to rank anything; and
///   * the caller's price table, which is an INPUT to both.
///
/// Everything else it maintains itself: its own resident set, built strictly
/// from the declared `outcome` / `evicted` fields, and its own cost, derived
/// from the declared group against that resident set. Mutating any declared
/// field therefore contradicts something.
///
/// It certifies VALIDITY, not optimality — §7.1 makes bypass legal on every
/// miss, so a differently-paged but self-consistent stream is a valid plan, and
/// a certificate has no business preferring one.
pub fn certify_paging_plan(
    layer: &CoeffLayer,
    prices: &[SourcePrice],
    plan: &PagingPlan,
) -> Result<PagingCost, PagingCertificateError> {
    if plan.regime != layer.regime {
        return Err(PagingCertificateError::RegimeMismatch {
            declared: plan.regime,
            found: layer.regime,
        });
    }
    validate_prices(layer, prices)?;
    let capacity = plan.request.budget.lanes();
    let sequence = expand(layer, &plan.order)?;
    let queues = next_use_queues(layer, &plan.order)?;
    if sequence.len() != plan.actions.len() {
        return Err(PagingCertificateError::ActionCountMismatch {
            expected: sequence.len(),
            found: plan.actions.len(),
        });
    }

    let width_of = |p: ProjectionId| prices[p.source.0 as usize].width;
    // Uses each projection has left, counted down as the STRUCTURAL sequence
    // consumes them. Liveness has to be counted this way and not as "some use at
    // a later POSITION": the two operand slots of one term share a position, so a
    // projection whose last use is the term currently executing is still live —
    // and pinned — while that term's earlier slot is being served. Purely
    // structural, so it borrows no decision from the pager.
    let mut remaining: Vec<usize> = queues.iter().map(Vec::len).collect();

    let mut resident: BTreeSet<ProjectionId> = BTreeSet::new();
    let mut lanes = 0u32;
    let mut derived = PagingCost::default();

    for (step, ((position, slot, kind), action)) in
        sequence.iter().copied().zip(&plan.actions).enumerate()
    {
        if action.step != step as u32 {
            return Err(PagingCertificateError::StepMismatch { step, declared: action.step });
        }
        let expected_term = plan.order[position as usize];
        if action.term != expected_term {
            return Err(PagingCertificateError::TermMismatch {
                step,
                expected: expected_term,
                found: action.term,
            });
        }
        if action.position != position {
            return Err(PagingCertificateError::PositionMismatch {
                step,
                expected: position,
                found: action.position,
            });
        }
        if action.slot != slot {
            return Err(PagingCertificateError::SlotMismatch {
                step,
                expected: slot,
                found: action.slot,
            });
        }

        let source = kind.source();
        let e0 = ProjectionId::endpoint0(source);
        let ds = ProjectionId::delta(source);
        let paired =
            ResolutionGroup::Pair { source, endpoint0: e0, delta: ds };

        // Paired resolution legality (§8): the ONLY forms this slot may take.
        let legal = match kind {
            SlotKind::Endpoint0Only(p) => action.group == ResolutionGroup::Single(p),
            SlotKind::DeltaOnly(p) => {
                action.group == ResolutionGroup::Single(p) || action.group == paired
            }
            SlotKind::DualFactor(_) => action.group == paired,
        };
        if !legal {
            return Err(PagingCertificateError::IllegalResolutionGroup {
                step,
                term: action.term,
                group: action.group,
            });
        }

        let touched = action.group.projections();
        if action.projections.len() != touched.len()
            || action.projections.iter().zip(&touched).any(|(a, p)| a.projection != *p)
        {
            return Err(PagingCertificateError::ProjectionListMismatch { step });
        }
        let consumed = kind.consumed();
        for a in &action.projections {
            let should = consumed.contains(&a.projection);
            if a.consumed != should {
                return Err(PagingCertificateError::ConsumptionMismatch {
                    step,
                    projection: a.projection,
                    declared: a.consumed,
                });
            }
        }

        // Hit/miss must agree with the certificate's OWN resident set.
        for a in &action.projections {
            let is_resident = resident.contains(&a.projection);
            if a.outcome.is_hit() != is_resident {
                return Err(PagingCertificateError::OutcomeMismatch {
                    step,
                    projection: a.projection,
                    declared: a.outcome,
                });
            }
        }

        // Cost from the declared group and the certificate's residency alone.
        let price = prices[source.0 as usize];
        let (endpoints_read, subtractions) = match action.group {
            ResolutionGroup::Single(p) if p.projection == Projection::Endpoint0 => {
                (u32::from(!resident.contains(&p)), 0)
            }
            ResolutionGroup::Single(p) => {
                if resident.contains(&p) {
                    (0, 0)
                } else if resident.contains(&e0) {
                    (1, 1)
                } else {
                    (2, 1)
                }
            }
            ResolutionGroup::Pair { .. } => {
                let have_e0 = resident.contains(&e0);
                let have_ds = resident.contains(&ds);
                let read = match (have_e0, have_ds) {
                    (true, true) => 0,
                    (true, false) | (false, true) => 1,
                    (false, false) => 2,
                };
                (read, u32::from(!have_ds))
            }
        };
        let want_bytes = price.element_bytes.saturating_mul(u64::from(endpoints_read));
        let want_ops = price
            .endpoint_ops
            .scale(endpoints_read)
            .plus(OpCounts::subtraction(price.width).scale(subtractions));
        for (field, declared, want) in [
            ("source_read_bytes", action.source_read_bytes, want_bytes),
            ("bf_ops", u64::from(action.bf_ops), u64::from(want_ops.bf)),
            ("mixed_ops", u64::from(action.mixed_ops), u64::from(want_ops.mixed)),
            ("e4_ops", u64::from(action.e4_ops), u64::from(want_ops.e4)),
        ] {
            if declared != want {
                return Err(PagingCertificateError::StepCostMismatch {
                    step,
                    field,
                    declared,
                    derived: want,
                });
            }
        }
        if endpoints_read > 0 {
            derived.source_resolutions += 1;
        }
        derived.source_read_bytes = derived.source_read_bytes.saturating_add(want_bytes);
        derived.bf_ops = derived.bf_ops.saturating_add(u64::from(want_ops.bf));
        derived.mixed_ops = derived.mixed_ops.saturating_add(u64::from(want_ops.mixed));
        derived.e4_ops = derived.e4_ops.saturating_add(u64::from(want_ops.e4));
        for a in &action.projections {
            if !a.consumed {
                continue;
            }
            if a.outcome.is_hit() {
                derived.hits += 1;
            } else {
                derived.misses += 1;
            }
        }

        // Apply the declared decisions. Consumption first: a projection whose
        // LAST remaining use this resolution was must leave the resident set, or
        // a later fill would be charged against a dead lifetime.
        for p in &consumed {
            let slot = &mut remaining[projection_index(*p)];
            *slot = slot.checked_sub(1).ok_or(
                PagingCertificateError::ProjectionListMismatch { step },
            )?;
            if *slot == 0 && resident.contains(p) {
                resident.remove(p);
                lanes -= width_of(*p).lanes();
            }
        }
        for a in &action.projections {
            match a.outcome {
                ProjectionOutcome::Hit | ProjectionOutcome::Bypass => {}
                ProjectionOutcome::Fill => {
                    if !resident.insert(a.projection) {
                        return Err(PagingCertificateError::DuplicateResidentAdmission {
                            step,
                            projection: a.projection,
                        });
                    }
                    lanes += width_of(a.projection).lanes();
                    derived.fills += 1;
                }
            }
            if a.outcome == ProjectionOutcome::Bypass {
                derived.bypasses += 1;
            }
        }

        // Pinning: a projection a later operand slot of this term still needs may
        // not be evicted.
        let mut pinned: BTreeSet<ProjectionId> = BTreeSet::new();
        for (later_position, _, later) in sequence[step + 1..].iter() {
            if *later_position != position {
                break;
            }
            for p in later.consumed() {
                pinned.insert(p);
            }
        }
        for p in &action.evicted {
            if pinned.contains(p) {
                return Err(PagingCertificateError::EvictedPinned { step, projection: *p });
            }
            if !resident.remove(p) {
                return Err(PagingCertificateError::EvictedNotResident { step, projection: *p });
            }
            lanes -= width_of(*p).lanes();
            derived.evictions += 1;
        }

        // A `Fill` must survive to `resident_after`; a `Bypass` must not be in it.
        for a in &action.projections {
            let is_resident = resident.contains(&a.projection);
            let should = match a.outcome {
                ProjectionOutcome::Fill => true,
                ProjectionOutcome::Bypass => false,
                ProjectionOutcome::Hit => is_resident,
            };
            if is_resident != should {
                return Err(PagingCertificateError::ResidencyContradictsOutcome {
                    step,
                    projection: a.projection,
                });
            }
        }

        // No resident may be dead: every resident still owes at least one
        // unconsumed use. This also rejects a stream that declares `Fill` on a
        // projection whose last use it just consumed.
        for p in resident.iter() {
            if remaining[projection_index(*p)] == 0 {
                return Err(PagingCertificateError::ExpiredStillResident {
                    step,
                    projection: *p,
                });
            }
        }

        if lanes > capacity {
            return Err(PagingCertificateError::CapacityExceeded { step, lanes, capacity });
        }
        let snapshot: Vec<ProjectionId> = resident.iter().copied().collect();
        if action.resident_after != snapshot {
            return Err(PagingCertificateError::ResidentSetMismatch {
                step,
                declared: action.resident_after.clone(),
                derived: snapshot,
            });
        }
        if action.resident_lanes_after != lanes {
            return Err(PagingCertificateError::ResidentLanesMismatch {
                step,
                declared: action.resident_lanes_after,
                derived: lanes,
            });
        }
        derived.peak_resident_lanes = derived.peak_resident_lanes.max(lanes);
    }

    let d = &derived;
    let c = &plan.cost;
    for (field, declared, want) in [
        ("source_read_bytes", c.source_read_bytes, d.source_read_bytes),
        ("bf_ops", c.bf_ops, d.bf_ops),
        ("mixed_ops", c.mixed_ops, d.mixed_ops),
        ("e4_ops", c.e4_ops, d.e4_ops),
        ("source_resolutions", c.source_resolutions, d.source_resolutions),
        ("hits", c.hits, d.hits),
        ("misses", c.misses, d.misses),
        ("fills", c.fills, d.fills),
        ("bypasses", c.bypasses, d.bypasses),
        ("evictions", c.evictions, d.evictions),
        ("peak_resident_lanes", u64::from(c.peak_resident_lanes), u64::from(d.peak_resident_lanes)),
    ] {
        if declared != want {
            return Err(PagingCertificateError::TotalCostMismatch { field, declared, derived: want });
        }
    }
    Ok(derived)
}

// ── Orders ───────────────────────────────────────────────────────────────────

/// The deterministic bring-up order: `TermId` order (§7.1: "the incumbent term
/// order is only a deterministic bring-up order").
pub fn stable_normalized_order(layer: &CoeffLayer) -> Vec<TermId> {
    (0..layer.terms.len() as u32).map(TermId).collect()
}

/// One shared projection, in the constructor's proxy model.
#[derive(Clone, Debug, PartialEq, Eq)]
struct ProxyValue {
    width: ValueWidth,
    read_cost: u128,
    /// Ascending distinct term indices that consume this projection.
    terms: Vec<usize>,
}

/// Build one deterministic, budget-aware alternative order.
///
/// A PORT of `eval_plan::backward_search::production::budget_aware_greedy_order`
/// (retired in Task 14), behaviour preserved:
///
///   * shared projections are grouped by the terms that use them and only
///     projections used by TWO OR MORE terms become proxy values;
///   * connected reuse components stay contiguous, visited in order of their
///     smallest member;
///   * terms are appended ONE at a time, never forced into pairs;
///   * each candidate is scored by the capacity-aware 0/1-knapsack frontier
///     proxy `(spill_cost, live_cost, live_width, term)`; and
///   * ties break on the stable term index, i.e. on `TermId`.
///
/// # Mixed-width adaptation
///
/// The incumbent knapsack was already width-aware (`ProxyValue::width_lanes`,
/// `if value.width_lanes > capacity_lanes { continue }`); what changes is the
/// PROJECTION of the problem into it:
///
///   * `width_lanes` is now `1` for a BF projection and `4` for an E4 one, from
///     [`ValueWidth::lanes`], instead of a demand's observed lane count;
///   * `read_cost` is now [`RebuildPrice::proxy_cost`] — DRAM bytes dominant, as
///     in the incumbent, plus the BF/mixed/E4 op classes as a sub-tie-break,
///     since a coefficient-term rebuild has arithmetic the incumbent demand
///     model did not carry; and
///   * `capacity_lanes` is the REAL `4 * cell_budget`, not the incumbent's
///     median observed inter-use gap capacity, because the budget is now given
///     rather than observed.
///
/// The frontier cost itself is computed by an exact reformulation of the
/// incumbent DP — see [`retained_cost`], whose equality with the DP is a gate.
pub fn budget_aware_greedy_order(
    layer: &CoeffLayer,
    prices: &[SourcePrice],
    budget: CellBudget,
) -> Result<Vec<TermId>, ScheduleError> {
    let term_count = layer.terms.len();
    if term_count == 0 {
        return Ok(Vec::new());
    }
    validate_prices(layer, prices)?;
    // Validate operand roles/fields exactly as the pager does, so a rejected
    // layer cannot silently produce an order.
    for term in &layer.terms {
        term_slots(layer, term)?;
    }

    let rebuild = rebuild_prices(prices);
    let mut by_projection: BTreeMap<ProjectionId, BTreeSet<usize>> = BTreeMap::new();
    for (index, term) in layer.terms.iter().enumerate() {
        term.for_each_projection_use(|p| {
            by_projection.entry(p).or_default().insert(index);
        });
    }
    let values: Vec<ProxyValue> = by_projection
        .into_iter()
        .filter(|(_, terms)| terms.len() > 1)
        .map(|(p, terms)| ProxyValue {
            width: prices[p.source.0 as usize].width,
            read_cost: rebuild[projection_index(p)].proxy_cost(),
            terms: terms.into_iter().collect(),
        })
        .collect();

    // Union-find over terms linked by a shared projection.
    let mut parent: Vec<usize> = (0..term_count).collect();
    fn find(parent: &mut [usize], mut item: usize) -> usize {
        while parent[item] != item {
            parent[item] = parent[parent[item]];
            item = parent[item];
        }
        item
    }
    for value in &values {
        if let Some((&first, rest)) = value.terms.split_first() {
            for &term in rest {
                let a = find(&mut parent, first);
                let b = find(&mut parent, term);
                if a != b {
                    parent[b] = a;
                }
            }
        }
    }
    let mut components: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for term in 0..term_count {
        let root = find(&mut parent, term);
        components.entry(root).or_default().push(term);
    }
    let mut components: Vec<Vec<usize>> = components.into_values().collect();
    components.sort_by_key(|component| component[0]);

    let mut values_by_term: Vec<Vec<usize>> = vec![Vec::new(); term_count];
    for (index, value) in values.iter().enumerate() {
        for &term in &value.terms {
            values_by_term[term].push(index);
        }
    }

    let mut frontier = Frontier::new(&values, budget.lanes() as usize);
    let mut order = Vec::with_capacity(term_count);
    let mut placed = vec![false; term_count];
    for component in components {
        for _ in 0..component.len() {
            let mut best: Option<((u128, u128, usize, usize), usize)> = None;
            for &term in &component {
                if placed[term] {
                    continue;
                }
                frontier.apply(&values_by_term[term], true);
                let key = frontier.key(term);
                frontier.apply(&values_by_term[term], false);
                if best.as_ref().is_none_or(|(best_key, _)| key < *best_key) {
                    best = Some((key, term));
                }
            }
            let (_, term) = best.expect("an unplaced component term remains");
            placed[term] = true;
            frontier.apply(&values_by_term[term], true);
            order.push(TermId(term as u32));
        }
    }
    Ok(order)
}

/// Incremental frontier state for the constructor's proxy.
///
/// A candidate evaluation touches at most four values (a term has at most two
/// operand slots and a native dual factor covers two projections), so the live
/// set, its cost, its width and the two width-class cost buckets are all
/// maintained in `O(1)` per trial instead of rebuilt.
struct Frontier<'a> {
    values: &'a [ProxyValue],
    placed: Vec<usize>,
    live: Vec<bool>,
    live_cost: u128,
    live_width: usize,
    /// Live BF / E4 costs as `cost -> multiplicity`. Ascending iteration order;
    /// [`retained_cost`] walks them in reverse.
    bf: BTreeMap<u128, usize>,
    e4: BTreeMap<u128, usize>,
    capacity_lanes: usize,
}

impl<'a> Frontier<'a> {
    fn new(values: &'a [ProxyValue], capacity_lanes: usize) -> Self {
        Frontier {
            values,
            placed: vec![0; values.len()],
            live: vec![false; values.len()],
            live_cost: 0,
            live_width: 0,
            bf: BTreeMap::new(),
            e4: BTreeMap::new(),
            capacity_lanes,
        }
    }

    fn bucket(&mut self, width: ValueWidth) -> &mut BTreeMap<u128, usize> {
        match width {
            ValueWidth::Bf => &mut self.bf,
            ValueWidth::E4 => &mut self.e4,
        }
    }

    /// Place (`add`) or un-place one term's values.
    fn apply(&mut self, values: &[usize], add: bool) {
        for &index in values {
            let value = &self.values[index];
            let total = value.terms.len();
            self.placed[index] = if add { self.placed[index] + 1 } else { self.placed[index] - 1 };
            // "Live" = partially placed, i.e. crossing this prefix boundary.
            let live = self.placed[index] != 0 && self.placed[index] < total;
            if live == self.live[index] {
                continue;
            }
            self.live[index] = live;
            let (cost, width) = (value.read_cost, value.width);
            if live {
                self.live_cost = self.live_cost.saturating_add(cost);
                self.live_width += width.lanes() as usize;
                *self.bucket(width).entry(cost).or_insert(0) += 1;
            } else {
                self.live_cost = self.live_cost.saturating_sub(cost);
                self.live_width -= width.lanes() as usize;
                let bucket = self.bucket(width);
                match bucket.get_mut(&cost) {
                    Some(1) => {
                        bucket.remove(&cost);
                    }
                    Some(n) => *n -= 1,
                    None => {}
                }
            }
        }
    }

    /// The incumbent's `(spill_cost, live_cost, live_width, fragment)` key.
    fn key(&self, term: usize) -> (u128, u128, usize, usize) {
        let retained = retained_cost(&self.bf, &self.e4, self.capacity_lanes);
        (self.live_cost.saturating_sub(retained), self.live_cost, self.live_width, term)
    }
}

/// The read cost that CAN remain resident across a prefix boundary: the maximum
/// total `read_cost` of a subset of live values whose widths fit
/// `capacity_lanes`.
///
/// The incumbent computed this with a `capacity_lanes`-wide 0/1-knapsack DP over
/// the live values. With exactly two widths (1 and 4) the same optimum has a
/// closed form: for each count `k` of retained E4 values take the `k`
/// highest-cost E4 values and the `capacity - 4k` highest-cost BF values, and
/// maximize over `k`. Within a width class higher cost always dominates, and all
/// costs are non-negative, so filling every remaining lane is never worse. This
/// is an exact reformulation, not an approximation — `retained_cost_matches_dp`
/// gates it against the DP itself.
fn retained_cost(
    bf: &BTreeMap<u128, usize>,
    e4: &BTreeMap<u128, usize>,
    capacity_lanes: usize,
) -> u128 {
    let e4_lanes = ValueWidth::E4.lanes() as usize;
    let max_e4 = capacity_lanes / e4_lanes;
    let e4_prefix = descending_prefix_sums(e4, max_e4);
    let bf_prefix = descending_prefix_sums(bf, capacity_lanes);
    let mut best = 0u128;
    for k in 0..e4_prefix.len() {
        let remaining = capacity_lanes - k * e4_lanes;
        let bf_take = remaining.min(bf_prefix.len() - 1);
        best = best.max(e4_prefix[k].saturating_add(bf_prefix[bf_take]));
    }
    best
}

/// `out[j]` = sum of the `j` highest costs in `bucket`, for `j` up to
/// `min(count, limit)`.
fn descending_prefix_sums(bucket: &BTreeMap<u128, usize>, limit: usize) -> Vec<u128> {
    let mut out = Vec::with_capacity(limit + 1);
    out.push(0u128);
    for (&cost, &multiplicity) in bucket.iter().rev() {
        for _ in 0..multiplicity {
            if out.len() > limit {
                return out;
            }
            let last = *out.last().expect("seeded with zero");
            out.push(last.saturating_add(cost));
        }
    }
    out
}

// ── Bounded seed selection (§7.2) ────────────────────────────────────────────

/// The three deterministic order candidates. There is no fourth: no mutation, no
/// restart, no genome (§7.1: "there is no cache genome").
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SeedKind {
    /// [`stable_normalized_order`].
    StableNormalized,
    /// [`budget_aware_greedy_order`] at THIS budget.
    BudgetAwareGreedy,
    /// The preceding budget's winning order, listed only when it is distinct
    /// from both of the above.
    PrecedingWinner,
}

/// One evaluated candidate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SeedEvaluation {
    pub seed: SeedKind,
    pub order: Vec<TermId>,
    pub score: PagingScore,
}

/// The winning plan at one budget, with every candidate it was chosen over.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BudgetOutcome {
    pub request: PagingRequest,
    /// Every evaluated candidate, in [`SeedKind`] declaration order, with
    /// duplicate orders removed.
    pub candidates: Vec<SeedEvaluation>,
    pub winner: SeedKind,
    pub plan: PagingPlan,
}

/// The whole `c2`..`c16` sweep, ascending.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BudgetSweep {
    pub outcomes: Vec<BudgetOutcome>,
}

/// Choose an order at one budget from the bounded candidate set, by EXACT best
/// score.
///
/// Every candidate is paged AND certified, so a candidate that cannot be
/// certified is a hard error rather than a silently discarded option. The
/// comparison is `(score, order)`: §7.2's fitness, then the stable lexical tie
/// break, which makes the winner unique.
pub fn select_paged_order(
    layer: &CoeffLayer,
    prices: &[SourcePrice],
    request: PagingRequest,
    preceding: Option<&[TermId]>,
) -> Result<BudgetOutcome, ScheduleError> {
    let stable = stable_normalized_order(layer);
    let greedy = budget_aware_greedy_order(layer, prices, request.budget)?;
    let mut seeds: Vec<(SeedKind, Vec<TermId>)> = vec![(SeedKind::StableNormalized, stable.clone())];
    if greedy != stable {
        seeds.push((SeedKind::BudgetAwareGreedy, greedy.clone()));
    }
    if let Some(preceding) = preceding {
        if preceding != stable.as_slice() && preceding != greedy.as_slice() {
            seeds.push((SeedKind::PrecedingWinner, preceding.to_vec()));
        }
    }

    let mut candidates = Vec::with_capacity(seeds.len());
    let mut best: Option<(SeedKind, PagingPlan)> = None;
    for (seed, order) in seeds {
        let plan = page_projections(layer, prices, request, &order)?;
        candidates.push(SeedEvaluation { seed, order, score: plan.cost.score() });
        let better = match &best {
            None => true,
            Some((_, current)) => {
                (plan.cost.score(), &plan.order) < (current.cost.score(), &current.order)
            }
        };
        if better {
            best = Some((seed, plan));
        }
    }
    let (winner, plan) = best.expect("the stable normalized order is always a candidate");
    Ok(BudgetOutcome { request, candidates, winner, plan })
}

/// Run [`select_paged_order`] over every budget `c2`..`c16`, threading each
/// winner into the next budget's candidate set (§7.2: "distinct equal-score tie
/// choices may seed independent candidates").
pub fn sweep_budgets(
    layer: &CoeffLayer,
    prices: &[SourcePrice],
    target_depth: u8,
) -> Result<BudgetSweep, ScheduleError> {
    let mut outcomes = Vec::with_capacity(CellBudget::ALL.len());
    let mut preceding: Option<Vec<TermId>> = None;
    for budget in CellBudget::ALL {
        let request = PagingRequest { budget, target_depth };
        let outcome = select_paged_order(layer, prices, request, preceding.as_deref())?;
        preceding = Some(outcome.plan.order.clone());
        outcomes.push(outcome);
    }
    Ok(BudgetSweep { outcomes })
}

// ── Unit gates ───────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    /// The incumbent `proxy_frontier_cost` knapsack, verbatim in shape: a
    /// `capacity_lanes`-wide 0/1 DP over the live values.
    fn retained_cost_dp(live: &[(usize, u128)], capacity_lanes: usize) -> u128 {
        let mut kept = vec![0u128; capacity_lanes + 1];
        for &(width, cost) in live {
            if width > capacity_lanes {
                continue;
            }
            for lanes in (width..=capacity_lanes).rev() {
                kept[lanes] = kept[lanes].max(kept[lanes - width].saturating_add(cost));
            }
        }
        kept.into_iter().max().unwrap_or(0)
    }

    /// The closed form must equal the incumbent DP on every shape, or the port
    /// changed behaviour.
    #[test]
    fn retained_cost_matches_dp() {
        let mut state = 0x1234_5678u64;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for capacity in [8usize, 12, 20, 36, 64] {
            for _ in 0..400 {
                let count = (next() % 14) as usize;
                let mut bf: BTreeMap<u128, usize> = BTreeMap::new();
                let mut e4: BTreeMap<u128, usize> = BTreeMap::new();
                let mut live = Vec::new();
                for _ in 0..count {
                    let cost = u128::from(next() % 200);
                    if next() % 2 == 0 {
                        *bf.entry(cost).or_insert(0) += 1;
                        live.push((1usize, cost));
                    } else {
                        *e4.entry(cost).or_insert(0) += 1;
                        live.push((ValueWidth::E4.lanes() as usize, cost));
                    }
                }
                assert_eq!(
                    retained_cost(&bf, &e4, capacity),
                    retained_cost_dp(&live, capacity),
                    "capacity {capacity}, live {live:?}"
                );
            }
        }
    }

    #[test]
    fn budget_range_is_c2_through_c16() {
        assert!(CellBudget::new(1).is_err());
        assert!(CellBudget::new(17).is_err());
        assert_eq!(CellBudget::new(2).unwrap().lanes(), 8);
        assert_eq!(CellBudget::new(16).unwrap().lanes(), 64);
        assert_eq!(CellBudget::ALL[0].label(), "c2");
        assert_eq!(CellBudget::ALL[14].label(), "c16");
        for (i, budget) in CellBudget::ALL.iter().enumerate() {
            assert_eq!(budget.cells(), CellBudget::MIN_CELLS + i as u8);
        }
    }

    #[test]
    fn rebuild_price_orders_lexicographically_in_field_order() {
        let cheap = RebuildPrice { source_read_bytes: 4, bf_ops: 9, mixed_ops: 9, e4_ops: 9 };
        let dear = RebuildPrice { source_read_bytes: 8, bf_ops: 0, mixed_ops: 0, e4_ops: 0 };
        assert!(cheap < dear, "bytes dominate every op class");
        let a = RebuildPrice { source_read_bytes: 4, bf_ops: 1, mixed_ops: 0, e4_ops: 9 };
        let b = RebuildPrice { source_read_bytes: 4, bf_ops: 2, mixed_ops: 0, e4_ops: 0 };
        assert!(a < b, "bf_ops precedes mixed_ops and e4_ops");
    }

    #[test]
    fn e4_is_the_widest_value() {
        assert!(ValueWidth::E4 > ValueWidth::Bf, "a 16-byte E4 bucket is wider than a BF lane");
        assert_eq!(ValueWidth::E4.lanes(), 4 * ValueWidth::Bf.lanes());
    }

    fn key(next_use: u32, price: RebuildPrice, width: ValueWidth, source: u32) -> EvictionKey {
        EvictionKey {
            farthest_next_use: Reverse(next_use),
            cheapest_rebuild: price,
            widest_value: Reverse(width),
            projection: ProjectionId::endpoint0(SourceId(source)),
        }
    }

    /// Each of the four keys must be decisive in turn, and the lower-priority
    /// keys must be set AGAINST the expected winner so they cannot be what
    /// actually decided. `BTreeSet`'s first element is the victim, so "sorts
    /// first" means "evicted first".
    #[test]
    fn eviction_ranking_is_lexicographic_in_the_declared_order() {
        let cheap = RebuildPrice { source_read_bytes: 4, bf_ops: 0, mixed_ops: 0, e4_ops: 0 };
        let dear = RebuildPrice { source_read_bytes: 16, bf_ops: 0, mixed_ops: 0, e4_ops: 0 };

        // 1. Farthest next use wins even when price, width and id all disagree.
        assert!(
            key(9, dear, ValueWidth::Bf, 9) < key(3, cheap, ValueWidth::E4, 0),
            "farthest next use is the primary key"
        );
        // 2. At equal distance, the cheapest rebuild goes first.
        assert!(
            key(5, cheap, ValueWidth::Bf, 9) < key(5, dear, ValueWidth::E4, 0),
            "cheapest rebuild price is the secondary key"
        );
        // 3. At equal distance AND equal price, the WIDEST value goes first. The
        //    E4 side carries the HIGHER id, so the id key cannot be what decided.
        assert!(
            key(5, cheap, ValueWidth::E4, 9) < key(5, cheap, ValueWidth::Bf, 0),
            "widest value is the tertiary key: a 16-byte E4 bucket outranks a BF lane"
        );
        // 4. Only a total tie falls through to the stable identity.
        assert!(
            key(5, cheap, ValueWidth::E4, 0) < key(5, cheap, ValueWidth::E4, 1),
            "stable ProjectionId is the final key"
        );
    }

    /// The width key is INERT for prices built by [`source_prices`], and this
    /// pins why — so a later task does not "fix" a ranking that is already
    /// correct, and knows the effective ladder is (distance, price, id).
    ///
    /// Two projections tie on next use only if ONE term consumes both, since a
    /// position holds one term. The terms that consume two projections of
    /// different sources are `C2Product` (two `Delta`s, widths may differ) and
    /// `DualProduct` (which §6 forces to Ext on both sides, so widths agree).
    /// That leaves `C2Product`, and there a width tie is arithmetically
    /// impossible: `Delta` adds one subtraction in its OWN field, so a BF delta
    /// has `bf_ops = 2*k + 1` and an E4 delta has `bf_ops = 2*k'`, which can
    /// never be equal. `bf_ops` precedes `widest_value`, so price always decides
    /// first.
    #[test]
    fn width_cannot_decide_between_two_deltas_of_different_widths() {
        for bf_endpoint_ops in 0..4u32 {
            for e4_endpoint_ops in 0..4u32 {
                let bf = SourcePrice {
                    width: ValueWidth::Bf,
                    element_bytes: 16,
                    endpoint_ops: OpCounts { bf: bf_endpoint_ops, mixed: 0, e4: 0 },
                };
                let e4 = SourcePrice {
                    width: ValueWidth::E4,
                    element_bytes: 16,
                    endpoint_ops: OpCounts { bf: e4_endpoint_ops, mixed: 0, e4: 0 },
                };
                let prices = rebuild_prices(&[bf, e4]);
                let bf_delta = prices[projection_index(ProjectionId::delta(SourceId(0)))];
                let e4_delta = prices[projection_index(ProjectionId::delta(SourceId(1)))];
                assert_ne!(
                    bf_delta.bf_ops % 2,
                    e4_delta.bf_ops % 2,
                    "a delta subtraction gives the two widths opposite bf_ops parity"
                );
                assert_ne!(bf_delta, e4_delta, "so two deltas of different widths never tie");
            }
        }
    }
}
