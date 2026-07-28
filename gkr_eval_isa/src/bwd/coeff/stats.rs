//! Per-coordinate census of the backward coefficient lowering (design §5.4,
//! §6, §9.2-§9.4), plus the two schedule-independent stream bounds the format
//! freeze was decided on.
//!
//! One [`CoeffCensus`] describes exactly one `(circuit, layer, regime)`
//! coordinate. Everything here is a pure function of `(DagLayer,
//! DistilledLayer, CoeffLayer, LoweringTrace)` — no scheduling, no placement, no
//! encoding — so the same code serves the crate-local committed-layout census
//! and the GPU crate's complete-corpus census, and both must agree.
//!
//! # What is deliberately NOT here
//!
//! Exact encoded word counts. This module reports the term POPULATION and two
//! a-priori bounds over it, never a program size:
//!
//!   * [`CoeffCensus::lower_bound_program_bytes`] — one header plus one word per
//!     source input. A true floor for any codec of this term set, so an overflow
//!     here is unrepairable by any encoder.
//!   * [`CoeffCensus::upper_bound_program_bytes`] — the CELL-era codec's
//!     worst-case shape (every input taking its canonical extension word, plus a
//!     budgeted move per reusable projection). See
//!     [`CoeffCensus::upper_bound_fits`] for what it does and does not prove.
//!
//! # These are census diagnostics, not the live sizing authority
//!
//! The live backward wire is the lean codec ([`lean`](super::lean)): a FIXED four
//! u16 words per term, no extension words, no moves. Nothing is sized from either
//! bound — the segmented descriptor's program array comes from
//! [`LEAN_DESCRIPTOR_PROGRAM_WORDS`](super::limits::LEAN_DESCRIPTOR_PROGRAM_WORDS),
//! a MEASUREMENT of the lean encoder over the whole corpus. The bounds survive
//! because they are the a-priori guard this census reports per coordinate, and
//! because a lower-bound overflow is still a real impossibility result.
//!
//! The cell-era pager, placement and codec those bounds describe were retired in
//! favour of the lean codec — see [`super`]'s module doc. Read "fills, plans,
//! moves and cell residency" below as the vocabulary of a format that no longer
//! exists.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use cs::gkr_compiler::dag_ir::{
    BwdRegime, DagLayer, FieldKind, ReadPlace, RootSlot, SinkKind, VirtualSetupKind, bwd_roots,
    read_place_field,
};
use serde::{Deserialize, Serialize};

use super::limits::{
    KERNEL_ARGUMENT_CEILING_BYTES, SOURCE_WINDOW_COLUMNS, TermCategory, lower_bound_program_words,
    program_bytes, term_category, upper_bound_program_words,
};
use super::lower::{LoweringTrace, lower_coeff_layer_traced};
use super::model::{
    CoeffError, CoeffLayer, CoeffSource, CoeffTerm, CoefficientRecipeId, ProjectionId,
};
use crate::bwd::distill::{DistilledLayer, distill};
use crate::bwd::source::OriginLeaf;

/// One logical DRAM matrix, in the identity final source binding assigns windows
/// over (§9.4). Field-qualified for cross-layer outputs and caches for the same
/// reason `fwd::binding::BackingKey` is: the base and extension columns of one
/// logical output live in different matrices and cannot share a window.
///
/// A `VirtualSetup` origin is procedurally resolved (§9.6: "procedural values
/// remain ordinary source coordinates whose window descriptor selects procedural
/// resolution"), so each distinct kind is its own single-column family.
///
/// `Serialize`/`Deserialize` because
/// [`LeanBoundWindow`](super::lean_bind::LeanBoundWindow) nests this inside a
/// serialized lean coordinate. The family is deliberately NOT mirrored into a
/// second serializable enum: this type is the SINGLE mapping from a source to its
/// backing, and a mirror would be a second answer to "what is a backing".
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum WindowFamily {
    BaseLayerMemory,
    BaseLayerWitness,
    Setup,
    Scratch,
    LayerOutput { layer: usize, ext: bool },
    CacheOutput { layer: usize, ext: bool },
    VirtualSetup { kind: u8 },
}

fn vs_tag(kind: &VirtualSetupKind) -> u8 {
    match kind {
        VirtualSetupKind::RangeCheck16Bits => 0,
        VirtualSetupKind::RangeCheckTimestamp => 1,
        VirtualSetupKind::InitsAndTeardownsLow => 2,
        VirtualSetupKind::InitsAndTeardownsHigh => 3,
    }
}

/// The BACKING field of one read place — the matrix's own width, never the
/// regime's fold override.
///
/// Resolution order: the natively typed families answer directly
/// (`read_place_field`), a cross-layer output/cache comes from
/// `DistilledLayer::cross_fields`, and the remaining case is an R0 materialized
/// sink read (interned from `roots[..].materialize`, which is not a cone leaf and
/// so has no `cross_fields` entry) — there the interned `CoeffSource::field` IS
/// the sink's own field, which is the backing field.
pub fn backing_field(
    place: &ReadPlace,
    source: &CoeffSource,
    distilled: &DistilledLayer,
) -> FieldKind {
    backing_field_in(place, source, &distilled.cross_fields)
}

/// [`backing_field`] against a bare cross-layer field map — the only part of a
/// [`DistilledLayer`] the resolution actually reads. Final binding
/// ([`crate::bwd::coeff::lean_bind`]) takes the map, so a caller that has already
/// dropped the distilled layer can still place a source in its matrix.
pub fn backing_field_in(
    place: &ReadPlace,
    source: &CoeffSource,
    cross_fields: &HashMap<ReadPlace, FieldKind>,
) -> FieldKind {
    if let Some(f) = read_place_field(place) {
        return f;
    }
    if let Some(&f) = cross_fields.get(place) {
        return f;
    }
    source.field
}

/// The logical matrix one source lives in, and its column there — the identity
/// final binding partitions windows over. The SINGLE mapping: the census and
/// [`crate::bwd::coeff::lean_bind`] must not disagree about what a backing is.
pub fn window_family(
    source: &CoeffSource,
    cross_fields: &HashMap<ReadPlace, FieldKind>,
) -> (WindowFamily, usize) {
    match &source.origin {
        OriginLeaf::VirtualSetup { kind } => (WindowFamily::VirtualSetup { kind: vs_tag(kind) }, 0),
        OriginLeaf::Read(place) => {
            let ext = backing_field_in(place, source, cross_fields) == FieldKind::Ext;
            match *place {
                ReadPlace::BaseLayerMemory { column } => (WindowFamily::BaseLayerMemory, column),
                ReadPlace::BaseLayerWitness { column } => (WindowFamily::BaseLayerWitness, column),
                ReadPlace::Setup { column } => (WindowFamily::Setup, column),
                ReadPlace::Scratch { slot } => (WindowFamily::Scratch, slot),
                ReadPlace::LayerOutput { layer, offset } => {
                    (WindowFamily::LayerOutput { layer, ext }, offset)
                }
                ReadPlace::CacheOutput { layer, offset } => {
                    (WindowFamily::CacheOutput { layer, ext }, offset)
                }
            }
        }
    }
}

/// Minimum freely based, contiguous 128-column windows covering `columns`
/// (§9.4: "windows are assigned freely and densely during final binding. Each
/// window covers at most 128 contiguous referenced columns").
///
/// Greedy first-fit over the sorted columns is optimal for a fixed span: opening
/// a window at the first uncovered column dominates any later start.
pub fn window_count(columns: &BTreeSet<usize>) -> usize {
    let mut windows = 0usize;
    let mut covered_through: Option<usize> = None;
    for &column in columns {
        if covered_through.is_none_or(|end| column > end) {
            windows += 1;
            covered_through = Some(column + SOURCE_WINDOW_COLUMNS - 1);
        }
    }
    windows
}

/// Endpoint resolutions of each source that NO schedule can avoid, indexed by
/// [`SourceId`](super::model::SourceId).
///
/// A pure function of the term set — no prices, no order, no residency — which is
/// what makes it a floor rather than a measurement:
///
///   * a source nothing consumes is read zero times;
///   * a source consumed only at `Endpoint0` needs `s0` once; and
///   * a source any term consumes at `Delta` needs both `s0` and `s1`, because
///     `ds = s1 - s0` (§8) cannot be formed from one of them — and once both are
///     read, a cache can serve every later use of EITHER projection, including an
///     `Endpoint0` use that a `Delta` resolution exposes for free (§7.1).
///
/// Multiplying entry `i` by source `i`'s per-endpoint byte price gives the layer's
/// compulsory read floor in bytes. The bound is TIGHT: an evaluator that retains
/// every projection with a later use realizes exactly it.
pub fn compulsory_endpoint_reads(lowered: &CoeffLayer) -> Vec<u8> {
    let mut reads = vec![0u8; lowered.sources.len()];
    for term in &lowered.terms {
        term.for_each_projection_use(|p| {
            let Some(slot) = reads.get_mut(p.source.0 as usize) else {
                return;
            };
            let needed = match p.projection {
                crate::bwd::coeff::model::Projection::Endpoint0 => 1,
                crate::bwd::coeff::model::Projection::Delta => 2,
            };
            *slot = (*slot).max(needed);
        });
    }
    reads
}

/// Windows the whole source table needs under the fixed 128-column rule.
pub fn source_window_count(lowered: &CoeffLayer, distilled: &DistilledLayer) -> usize {
    let mut per_family: BTreeMap<WindowFamily, BTreeSet<usize>> = BTreeMap::new();
    for source in &lowered.sources {
        let (family, column) = window_family(source, &distilled.cross_fields);
        per_family.entry(family).or_default().insert(column);
    }
    per_family.values().map(window_count).sum()
}

// ── Census ───────────────────────────────────────────────────────────────────

/// Everything Task 3 pins for one `(circuit, layer, regime)` coordinate.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CoeffCensus {
    // ── canonical structure ──────────────────────────────────────────────
    /// `bwd_roots(canonical).len()` — the canonical batching order's length.
    pub canonical_roots: usize,
    /// Claim-bearing roots carrying a materialized output sink.
    pub materialized_roots: usize,
    /// Claim-only constraint roots (structurally zero on the hypercube).
    pub constraint_only_roots: usize,
    /// Claim roots by materialized-sink family, for the `sink_read_place`
    /// coverage argument.
    pub sinks_inner: usize,
    pub sinks_cache: usize,
    pub sinks_scratch: usize,
    pub sinks_export: usize,

    // ── pre-distribution (§5.4) ──────────────────────────────────────────
    pub fragments_total: usize,
    pub fragments_live: usize,
    pub pre_distribution_atoms: usize,
    pub pre_distribution_products: usize,
    pub distributed_monomials: usize,
    pub distributed_degree0_residues: usize,
    /// Maximum monomials a single pre-distribution product expanded to.
    pub max_expansion_factor: usize,
    pub max_fragment_atoms: usize,

    // ── post-distribution term set (§6) ──────────────────────────────────
    pub terms: usize,
    /// R0: `C0Linear` reading a BF `Endpoint0`.
    pub r0_c0_linear_bf: usize,
    /// R0: `C0Linear` reading an E4 `Endpoint0`.
    pub r0_c0_linear_e4: usize,
    pub r0_c2_bf_bf: usize,
    pub r0_c2_bf_e4: usize,
    pub r0_c2_e4_e4: usize,
    /// Mixed-field R0 products whose `lhs` is the E4 side. Structural-order
    /// artifacts: the `BF_E4` opcode is canonical, so the encoder must swap
    /// these operands. Zero would mean no swap is ever needed.
    pub r0_c2_mixed_needing_swap: usize,
    /// Continuation `C0Linear` (always E4).
    pub cont_c0_linear: usize,
    /// Continuation native `DualProduct`.
    pub cont_dual_product: usize,
    /// Continuation STANDALONE product terms — a `C2Product`/`C0Product` that is
    /// not a native dual. §6 makes this category a structural compiler error
    /// unless the census proves it live.
    pub cont_standalone_product: usize,
    /// Continuation `C0Linear` over a BF `Endpoint0` — must be zero, every
    /// continuation source is an Ext fold leaf.
    pub cont_c0_linear_bf: usize,

    // ── stable identities (§6) ───────────────────────────────────────────
    pub sources: usize,
    pub projections: usize,
    /// Distinct BANKED recipes (the `+1`/`-1` literals consume no entry).
    pub coefficient_recipes: usize,
    /// Distinct coefficient IDS the terms reference, including reserved literals.
    pub coefficient_ids_used: usize,
    pub reserved_literal_terms: usize,
    pub has_c_init: bool,
    /// Projections referenced by two or more term operand slots — the ones a
    /// schedule may want to keep resident and therefore may need to move.
    pub reusable_projections: usize,
    pub source_windows: usize,

    // ── stream bounds (§9.1, §9.6) ───────────────────────────────────────
    pub lower_bound_program_bytes: usize,
    pub upper_bound_program_bytes: usize,
}

impl CoeffCensus {
    /// R0 `C0Linear` total.
    pub fn r0_c0_linear(&self) -> usize {
        self.r0_c0_linear_bf + self.r0_c0_linear_e4
    }

    /// R0 `C2Product` total.
    pub fn r0_c2_product(&self) -> usize {
        self.r0_c2_bf_bf + self.r0_c2_bf_e4 + self.r0_c2_e4_e4
    }

    /// `true` when the minimum-possible stream fits the kernel-argument cap. A
    /// `false` here is TERMINAL: no codec, paging or placement decision in Tasks
    /// 4-9 can make the term set smaller than one header plus one word per source
    /// input.
    pub fn lower_bound_fits(&self) -> bool {
        self.lower_bound_program_bytes <= KERNEL_ARGUMENT_CEILING_BYTES
    }

    /// `true` when the CELL-era codec's conservative stream fits, under the ONE
    /// assumption [`upper_bound_program_words`](super::limits::upper_bound_program_words)
    /// documents: [`ASSUMED_MOVES_PER_REUSABLE_PROJECTION`] move per reusable
    /// projection. The term-word half is maximal for that codec; the move half is
    /// an assumption, because design §7.3 never capped the moves placement repair
    /// could emit.
    ///
    /// **Two things this does NOT prove.** It is not "no schedule can overflow" —
    /// read it as "fits with the assumed move budget" (the exposure is quantified
    /// on `upper_bound_program_words`: 3.64x headroom on the worst coordinate). And
    /// it is not a bound on the LIVE lean codec, which is a different format and is
    /// not dominated by this one in general: the bound charges `1 + arity` words per
    /// term plus moves, while the lean wire charges a flat four, so an all-unary
    /// layer with no reusable projections gives `4u` lean words against a `3u`
    /// bound. The two maxima happen to sit the right way round on this corpus
    /// (14,328 B of lean program against a 19,396 B worst-case bound), but that is
    /// a corpus fact about two separately-maximized numbers, not a theorem — and
    /// nothing relies on it, because the descriptor is sized from the lean
    /// measurement directly.
    ///
    /// [`ASSUMED_MOVES_PER_REUSABLE_PROJECTION`]: super::limits::ASSUMED_MOVES_PER_REUSABLE_PROJECTION
    pub fn upper_bound_fits(&self) -> bool {
        self.upper_bound_program_bytes <= KERNEL_ARGUMENT_CEILING_BYTES
    }

    /// Neither proven to fit nor proven to overflow — Task 8's real encoder
    /// decides it.
    pub fn inconclusive(&self) -> bool {
        self.lower_bound_fits() && !self.upper_bound_fits()
    }

    pub fn merge_max(&mut self, other: &Self) {
        macro_rules! max_fields {
            ($($f:ident),* $(,)?) => { $( self.$f = self.$f.max(other.$f); )* };
        }
        max_fields!(
            canonical_roots,
            materialized_roots,
            constraint_only_roots,
            sinks_inner,
            sinks_cache,
            sinks_scratch,
            sinks_export,
            fragments_total,
            fragments_live,
            pre_distribution_atoms,
            pre_distribution_products,
            distributed_monomials,
            distributed_degree0_residues,
            max_expansion_factor,
            max_fragment_atoms,
            terms,
            r0_c0_linear_bf,
            r0_c0_linear_e4,
            r0_c2_bf_bf,
            r0_c2_bf_e4,
            r0_c2_e4_e4,
            r0_c2_mixed_needing_swap,
            cont_c0_linear,
            cont_dual_product,
            cont_standalone_product,
            cont_c0_linear_bf,
            sources,
            projections,
            coefficient_recipes,
            coefficient_ids_used,
            reserved_literal_terms,
            reusable_projections,
            source_windows,
            lower_bound_program_bytes,
            upper_bound_program_bytes,
        );
        self.has_c_init |= other.has_c_init;
    }
}

/// Census one lowered coordinate.
///
/// `canonical` and `distilled` must be the same pair `lowered` was produced from;
/// `trace` must be that lowering's [`LoweringTrace`].
///
/// TOTAL: the only failure is
/// [`CoeffError::ConstraintRootAccountingMismatch`], which is derivable from
/// `canonical.roots` alone. This function is called by every downstream task, so
/// it must not abort a caller's corpus sweep on input data — the crate
/// convention is typed errors for anything derivable from input and assertions
/// only for invariants unreachable by construction.
pub fn census_coeff_layer(
    canonical: &DagLayer,
    distilled: &DistilledLayer,
    lowered: &CoeffLayer,
    trace: &LoweringTrace,
) -> Result<CoeffCensus, CoeffError> {
    let mut c = CoeffCensus {
        canonical_roots: bwd_roots(canonical).len(),
        fragments_total: trace.fragments_total,
        fragments_live: trace.fragments_live,
        pre_distribution_atoms: trace.pre_distribution_atoms,
        pre_distribution_products: trace.pre_distribution_products,
        distributed_monomials: trace.distributed_monomials,
        distributed_degree0_residues: trace.distributed_degree0_residues,
        max_expansion_factor: trace.max_expansion_factor,
        max_fragment_atoms: trace.max_fragment_atoms,
        terms: lowered.terms.len(),
        sources: lowered.sources.len(),
        coefficient_recipes: lowered.coefficients.len(),
        has_c_init: lowered.c_init.is_some(),
        ..Default::default()
    };

    for root in &canonical.roots {
        if root.claim.is_none() {
            continue;
        }
        match &root.materialize {
            None => c.constraint_only_roots += 1,
            Some(sink) => {
                c.materialized_roots += 1;
                match sink.kind {
                    SinkKind::Inner { .. } => c.sinks_inner += 1,
                    SinkKind::Cache { .. } => c.sinks_cache += 1,
                    SinkKind::Scratch { .. } => c.sinks_scratch += 1,
                    SinkKind::Export { .. } => c.sinks_export += 1,
                }
            }
        }
    }
    // `constraint_only_roots` is reported as "the roots §5.2 says contribute no
    // `acc_c0`", so it must actually BE the claim-only CONSTRAINT roots.
    //
    // Reachable, not decorative: `lower_r0_root_c0` rejects a sinkless
    // `RootSlot::Output` root (`MaterializedOutputMissing`) and a materialized
    // `RootSlot::Constraint` root (`MaterializedConstraintRoot`), but that check
    // runs in the R0 regime ONLY. In `Ext` a sinkless output root lowers fine and
    // would silently inflate this field.
    //
    // A RETURNED error, not an assertion: the guarded condition is a pure
    // function of `canonical.roots`, so it belongs in `CoeffError` next to the two
    // R0-gated variants that reject the very same contradiction. A hard `assert!`
    // here would abort the corpus sweep of every caller in Tasks 4-9 instead of
    // reporting the offending coordinate as data (`CoeffCensusFailure`), which is
    // exactly what §3.1's conditional-circuit handling needs.
    let constraint_slot_roots = canonical
        .roots
        .iter()
        .filter(|r| {
            r.claim
                .as_ref()
                .is_some_and(|claim| matches!(claim.origin.slot, RootSlot::Constraint(_)))
        })
        .count();
    if c.constraint_only_roots != constraint_slot_roots {
        return Err(CoeffError::ConstraintRootAccountingMismatch {
            sinkless_claim_roots: c.constraint_only_roots,
            constraint_slot_roots,
        });
    }

    let r0 = lowered.regime == BwdRegime::R0;
    let mut projection_uses: BTreeMap<ProjectionId, usize> = BTreeMap::new();
    let mut coefficient_ids: BTreeSet<_> = BTreeSet::new();
    // The two stream bounds are computed by `limits::{lower,upper}_bound_program_words`,
    // which own the reasoning and the exposure documentation. All this census
    // contributes is the term arity population they take.
    let mut unary_terms = 0usize;
    let mut binary_terms = 0usize;

    for term in &lowered.terms {
        coefficient_ids.insert(term.coefficient());
        if term.coefficient().literal().is_some() {
            c.reserved_literal_terms += 1;
        }
        // ONE definition of "consumed projection", shared with the scheduler
        // (`CoeffTerm::for_each_projection_use`), so the census's reuse counter and
        // the pager's next-use queues cannot disagree about what a term reads.
        term.for_each_projection_use(|p| *projection_uses.entry(p).or_default() += 1);
        let arity = match term {
            CoeffTerm::C0Linear { field, .. } => {
                if r0 {
                    match field {
                        FieldKind::Base => c.r0_c0_linear_bf += 1,
                        FieldKind::Ext => c.r0_c0_linear_e4 += 1,
                    }
                } else {
                    c.cont_c0_linear += 1;
                    if *field == FieldKind::Base {
                        c.cont_c0_linear_bf += 1;
                    }
                }
                1
            }
            CoeffTerm::C2Product { lhs_field, rhs_field, .. } => {
                if r0 {
                    match (lhs_field, rhs_field) {
                        (FieldKind::Base, FieldKind::Base) => c.r0_c2_bf_bf += 1,
                        (FieldKind::Ext, FieldKind::Ext) => c.r0_c2_e4_e4 += 1,
                        (FieldKind::Base, FieldKind::Ext) => c.r0_c2_bf_e4 += 1,
                        (FieldKind::Ext, FieldKind::Base) => {
                            c.r0_c2_bf_e4 += 1;
                            c.r0_c2_mixed_needing_swap += 1;
                        }
                    }
                } else {
                    // §6: a continuation product that is not a native dual.
                    c.cont_standalone_product += 1;
                }
                2
            }
            CoeffTerm::DualProduct { .. } => {
                // A native dual consumes BOTH projections of each factor in one
                // source-pair resolution (§8) — tallied by
                // `for_each_projection_use` above.
                if r0 {
                    // Structurally impossible: R0 emits `C2Product`, never a dual.
                    c.cont_standalone_product += 1;
                } else {
                    c.cont_dual_product += 1;
                }
                2
            }
        };
        match arity {
            1 => unary_terms += 1,
            2 => binary_terms += 1,
            other => unreachable!("the arity match above yields only 1 or 2, not {other}"),
        }
    }

    c.projections = projection_uses.len();
    c.reusable_projections = projection_uses.values().filter(|&&uses| uses >= 2).count();
    c.coefficient_ids_used = coefficient_ids.len();
    c.source_windows = source_window_count(lowered, distilled);

    // ── stream bounds ────────────────────────────────────────────────────
    //
    // ONE definition of each bound, in `limits`. Both are FROZEN, and a frozen
    // bound with two implementations is exactly the drift the freeze exists to
    // prevent — so this census supplies the term population and nothing else. The
    // strength of each half (the lower bound terminal, the upper bound's proven
    // term words plus its ASSUMED move budget and 3.64x exposure) is documented on
    // `limits::lower_bound_program_words` / `limits::upper_bound_program_words`;
    // read it there before treating a `fits` verdict as a proof.
    c.lower_bound_program_bytes =
        program_bytes(lower_bound_program_words(unary_terms, binary_terms));
    c.upper_bound_program_bytes = program_bytes(upper_bound_program_words(
        unary_terms,
        binary_terms,
        c.reusable_projections,
    ));

    Ok(c)
}

// ── Corpus rows ──────────────────────────────────────────────────────────────

/// One censused coordinate, tagged so rows from any corpus sort and print
/// identically. Both Task-3 censuses build their report out of these, which is
/// what makes the crate-local and the GPU-crate numbers directly comparable.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoeffCensusRow {
    pub circuit: String,
    pub layer: usize,
    pub regime: BwdRegime,
    pub live_categories: BTreeSet<TermCategory>,
    pub census: CoeffCensus,
}

impl CoeffCensusRow {
    pub fn regime_label(&self) -> &'static str {
        if self.regime == BwdRegime::R0 { "R0" } else { "Ext" }
    }

    /// Total, lexical order over coordinates. Two runs that agree on the row set
    /// therefore produce byte-identical reports.
    pub fn sort_key(&self) -> (&str, usize, &'static str) {
        (self.circuit.as_str(), self.layer, self.regime_label())
    }
}

/// A coordinate the lowering REJECTED. Kept as data (never a panic) so a census
/// can report the exact first failing coordinate of a conditional circuit and
/// continue with the rest of the corpus (§3.1).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoeffCensusFailure {
    pub circuit: String,
    pub layer: usize,
    pub regime: BwdRegime,
    pub error: CoeffError,
}

/// Distill, lower and census one canonical layer in BOTH regimes.
///
/// This is the whole per-coordinate pipeline, deliberately in the library rather
/// than in either test, so the crate-local committed-layout census and the GPU
/// crate's complete-corpus census cannot drift apart.
pub fn census_layer(
    circuit: &str,
    layer_index: usize,
    canonical: &DagLayer,
    cross_fields: &HashMap<ReadPlace, FieldKind>,
) -> (Vec<CoeffCensusRow>, Vec<CoeffCensusFailure>) {
    let mut rows = Vec::with_capacity(2);
    let mut failures = Vec::new();
    for regime in [BwdRegime::R0, BwdRegime::Ext] {
        let distilled = distill(canonical, regime, cross_fields, None);
        let censused = lower_coeff_layer_traced(canonical, &distilled).and_then(
            |(lowered, trace)| {
                let census = census_coeff_layer(canonical, &distilled, &lowered, &trace)?;
                let live_categories = live_term_categories(&lowered)?;
                Ok((live_categories, census))
            },
        );
        match censused {
            Ok((live_categories, census)) => rows.push(CoeffCensusRow {
                circuit: circuit.to_string(),
                layer: layer_index,
                regime,
                live_categories,
                census,
            }),
            Err(error) => failures.push(CoeffCensusFailure {
                circuit: circuit.to_string(),
                layer: layer_index,
                regime,
                error,
            }),
        }
    }
    (rows, failures)
}

/// CSV column names, in [`csv_line`](csv_line) order.
pub const CSV_HEADER: &str = "circuit,layer,regime,\
canonical_roots,materialized_roots,constraint_only_roots,\
sinks_inner,sinks_cache,sinks_scratch,sinks_export,\
fragments_total,fragments_live,pre_distribution_atoms,pre_distribution_products,\
distributed_monomials,distributed_degree0_residues,max_expansion_factor,max_fragment_atoms,\
terms,r0_c0_linear_bf,r0_c0_linear_e4,r0_c2_bf_bf,r0_c2_bf_e4,r0_c2_e4_e4,\
r0_c2_mixed_needing_swap,cont_c0_linear,cont_dual_product,cont_standalone_product,\
sources,projections,coefficient_recipes,coefficient_ids_used,reserved_literal_terms,\
has_c_init,reusable_projections,source_windows,\
lower_bound_program_bytes,upper_bound_program_bytes,lower_bound_fits,upper_bound_fits,\
live_categories";

/// One CSV record for `row`.
pub fn csv_line(row: &CoeffCensusRow) -> String {
    let c = &row.census;
    let categories = row
        .live_categories
        .iter()
        .map(|category| category.label())
        .collect::<Vec<_>>()
        .join("|");
    format!(
        "{},{},{},\
{},{},{},\
{},{},{},{},\
{},{},{},{},\
{},{},{},{},\
{},{},{},{},{},{},\
{},{},{},{},\
{},{},{},{},{},\
{},{},{},\
{},{},{},{},\
{}",
        row.circuit,
        row.layer,
        row.regime_label(),
        c.canonical_roots,
        c.materialized_roots,
        c.constraint_only_roots,
        c.sinks_inner,
        c.sinks_cache,
        c.sinks_scratch,
        c.sinks_export,
        c.fragments_total,
        c.fragments_live,
        c.pre_distribution_atoms,
        c.pre_distribution_products,
        c.distributed_monomials,
        c.distributed_degree0_residues,
        c.max_expansion_factor,
        c.max_fragment_atoms,
        c.terms,
        c.r0_c0_linear_bf,
        c.r0_c0_linear_e4,
        c.r0_c2_bf_bf,
        c.r0_c2_bf_e4,
        c.r0_c2_e4_e4,
        c.r0_c2_mixed_needing_swap,
        c.cont_c0_linear,
        c.cont_dual_product,
        c.cont_standalone_product,
        c.sources,
        c.projections,
        c.coefficient_recipes,
        c.coefficient_ids_used,
        c.reserved_literal_terms,
        u8::from(c.has_c_init),
        c.reusable_projections,
        c.source_windows,
        c.lower_bound_program_bytes,
        c.upper_bound_program_bytes,
        u8::from(c.lower_bound_fits()),
        u8::from(c.upper_bound_fits()),
        categories,
    )
}

/// The whole census as a CSV document. `rows` must already be sorted by
/// [`CoeffCensusRow::sort_key`].
pub fn census_csv(rows: &[CoeffCensusRow]) -> String {
    let mut out = String::with_capacity(CSV_HEADER.len() + rows.len() * 160);
    out.push_str(CSV_HEADER);
    out.push('\n');
    for row in rows {
        out.push_str(&csv_line(row));
        out.push('\n');
    }
    out
}

/// The live opcode categories one lowered layer uses, for the opcode-table
/// freeze.
///
/// Every returned category is a legal category of `lowered.regime`. Reachable,
/// not decorative: a `DualProduct` in an R0 layer or a base-field `C0Linear` in an
/// `Ext` layer maps to a category its regime's opcode table cannot encode, and
/// this is the library-level guard for any caller (both censuses additionally
/// check it per row, where they can name the coordinate).
///
/// A RETURNED [`CoeffError::TermCategoryNotEncodable`], not an `assert!`: the
/// guarded condition is a pure function of `lowered.regime` and `lowered.terms`,
/// i.e. of input data, so the crate convention makes it a typed error — exactly
/// as [`census_coeff_layer`]'s
/// [`CoeffError::ConstraintRootAccountingMismatch`] already is. A library-level
/// assertion here would abort the corpus sweep of every caller in Tasks 5-9
/// instead of reporting the offending coordinate as data
/// ([`CoeffCensusFailure`]), which is what §3.1's conditional-circuit handling
/// needs.
pub fn live_term_categories(lowered: &CoeffLayer) -> Result<BTreeSet<TermCategory>, CoeffError> {
    let r0 = lowered.regime == BwdRegime::R0;
    let mut live = BTreeSet::new();
    for term in &lowered.terms {
        live.insert(match term {
            CoeffTerm::C0Linear { field: FieldKind::Base, .. } => TermCategory::C0LinearBf,
            CoeffTerm::C0Linear { field: FieldKind::Ext, .. } => TermCategory::C0LinearE4,
            CoeffTerm::C2Product { lhs_field, rhs_field, .. } => {
                match (lhs_field, rhs_field) {
                    (FieldKind::Base, FieldKind::Base) => TermCategory::C2ProductBfBf,
                    (FieldKind::Ext, FieldKind::Ext) => TermCategory::C2ProductE4E4,
                    _ => TermCategory::C2ProductBfE4,
                }
            }
            CoeffTerm::DualProduct { .. } => TermCategory::DualProductE4,
        });
    }
    for category in &live {
        if !category.is_legal_in(r0) {
            return Err(CoeffError::TermCategoryNotEncodable {
                regime: lowered.regime,
                category: *category,
            });
        }
    }
    Ok(live)
}

// ── The NEG_ONE census (segmented-lean-VM design §8) ─────────────────────────

/// [`NEG_ONE`](CoefficientRecipeId::NEG_ONE)-coefficient terms of one layer, by
/// category.
///
/// The input to the `fnma` (`z - x*y`) adoption decision. Signs live in
/// coefficients, so a `NEG_ONE` term is a SUBTRACT-shaped accumulate: `acc - x*y`
/// rather than `acc + k*x*y`, which fuses into one instruction per width class
/// instead of a multiply followed by an add. How much that is worth is exactly the
/// frequency of those terms per width class, which is what this measures.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct NegOneCensus {
    /// `(category, NEG_ONE terms)`, ascending by category. A category with no
    /// `NEG_ONE` term is ABSENT rather than zero, so the vector is the census's
    /// support and its sum is the layer's `NEG_ONE` term count.
    pub per_category: Vec<(TermCategory, u64)>,
    /// ALL terms of the layer — the denominator. Reported even when
    /// [`NegOneCensus::per_category`] is empty, so a layer with no `NEG_ONE` term is
    /// distinguishable from a layer nobody censused.
    pub total_terms: u64,
}

/// Count one layer's [`NEG_ONE`](CoefficientRecipeId::NEG_ONE) terms per category.
///
/// The category is [`term_category`]'s — the same width classification the wire
/// encodes — so the result is directly the per-width-class frequency the `fnma`
/// decision needs, and not a re-derivation of it.
pub fn neg_one_census(layer: &CoeffLayer) -> NegOneCensus {
    let mut per_category: BTreeMap<TermCategory, u64> = BTreeMap::new();
    for term in &layer.terms {
        if term.coefficient() == CoefficientRecipeId::NEG_ONE {
            *per_category.entry(term_category(term)).or_default() += 1;
        }
    }
    NegOneCensus {
        per_category: per_category.into_iter().collect(),
        total_terms: layer.terms.len() as u64,
    }
}
