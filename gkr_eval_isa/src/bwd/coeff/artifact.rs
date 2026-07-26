//! Deterministic `c2`-`c16` schedule artifacts, their replay, and the exact
//! per-program report (design §7.2, §13, §15 "static quality").
//!
//! # What an artifact is
//!
//! §13: "artifacts contain term order and deterministic paging decisions. They do
//! not contain a genome, physical pointers, or pre-bound source windows. Placement
//! and final binding occur after the complete schedule is known."
//!
//! The schema is therefore UNVERSIONED and MINIMAL. Per
//! `(circuit, layer, R0|Ext, c2..c16)` it stores exactly three things:
//!
//!   1. the normalized term order;
//!   2. the [`digest`] of the deterministic paging plan's
//!      [`PagingPlan::canonical_bytes`] — every paging action and the whole
//!      certified cost, in one number; and
//!   3. the exact modeled score, §7.2's fitness tuple.
//!
//! Nothing physical is stored: no cells, no lanes, no windows, no columns, no
//! program words, no genome. [`replay_coordinate`] RECONSTRUCTS the paging plan,
//! the placement, the final binding, the canonical encoding and every certificate
//! from the canonical DAG plus those three fields, and rejects the artifact unless
//! the reconstruction reproduces the stored digest and score exactly. That round
//! trip is the artifact's whole correctness argument, so it is proven over the
//! complete corpus rather than sampled.
//!
//! # Reporting vocabulary (§15)
//!
//! Bytes are BYTES. There is no "weighted" byte count anywhere in this module:
//! arithmetic classes are separate counters ([`ProgramReport::bf_ops`] /
//! `mixed_ops` / `e4_ops`) and materialization writes
//! ([`ProgramReport::materialization_write_bytes`]) are reported separately and
//! never enter the read-overhead numerator. Percent above floor is exactly
//! `(realized_total_read_bytes / total_read_floor_bytes - 1) * 100`.
//!
//! # Scope
//!
//! `blake2_with_compression` is NOT a distinct circuit: its delegation wrapper
//! compiles `define_blake2_with_extended_control_delegation_circuit` at
//! `DOMAIN_SIZE_LOG2 = 20`, which is the call that produced the committed
//! `blake2_with_extended_control_layout_gkr.json`, and Task 3's census measured
//! byte-identical serialized layouts and field-for-field identical census rows.
//! [`limits::in_scope`] (114 coordinates / 57 layers / 12 circuits) therefore
//! already covers it, §3.1's conditional exclusion cannot trigger, and this module
//! has no conditional artifact family, no all-or-nothing gate and no exclusion
//! path — dead code the plan's global constraints forbid.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use cs::gkr_compiler::dag_ir::{BwdRegime, DagLayer, FieldKind, ReadPlace};
use serde::{Deserialize, Serialize};

use super::bind::{
    CoeffSourceBinding, SourceBindError, SourceCertificateError, bind_coeff_sources,
    certify_source_binding,
};
use super::encode::{CoeffCodecError, EncodedProgram, certify_encoding, encode_program};
use super::limits;
use super::model::{CoeffError, CoeffLayer, TermId};
use super::place::{
    CoeffPlacement, LivenessError, PlacementError, ScheduledInstr, ValueUse, certify_cell_liveness,
    place_paging_plan,
};
use super::schedule::{
    CellBudget, PagingCertificateError, PagingPlan, PagingRequest, ScheduleError, SeedKind,
    SourcePrice, certify_paging_plan, default_target_depth, page_projections, select_paged_order,
    source_prices,
};
use super::stats::compulsory_endpoint_reads;
use crate::bwd::cost::EXT_BYTES;
use crate::bwd::distill::distill;
use crate::bwd::coeff::lower::lower_coeff_layer;

// ── Digest ───────────────────────────────────────────────────────────────────

const FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

/// FNV-1a-64, the crate's stable digest convention (`bwd::plan`, `bwd::trace`).
///
/// A digest, not a signature: it exists so an artifact can name a paging plan in
/// eight bytes and so replay can reject a plan that is not the one the artifact
/// was compiled from. Replay re-derives the plan itself, so a collision cannot
/// smuggle in a *different* plan's behaviour — every downstream certificate runs
/// against the reconstructed plan, not against the digest.
pub fn digest(bytes: &[u8]) -> u64 {
    let mut hash = FNV_OFFSET;
    for &byte in bytes {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    hash
}

/// [`digest`] of a complete encoded program: its regime, budget, `c_init` and
/// every u16 word, little-endian.
///
/// The header fields are folded in because two programs with identical words but
/// different `c_init` are different programs (§5.3's per-thread initializer).
pub fn program_digest(program: &EncodedProgram) -> u64 {
    let mut bytes = Vec::with_capacity(4 + program.words.len() * 2);
    bytes.push(match program.regime {
        BwdRegime::R0 => 0,
        BwdRegime::Ext => 1,
    });
    bytes.push(program.budget.cells());
    // A fixed five-byte field either way, so a present recipe can never collide
    // with an absent one followed by the first program word.
    match program.c_init {
        None => bytes.extend_from_slice(&[0; 5]),
        Some(recipe) => {
            bytes.push(1);
            bytes.extend_from_slice(&recipe.0.to_le_bytes());
        }
    }
    for word in &program.words {
        bytes.extend_from_slice(&word.to_le_bytes());
    }
    digest(&bytes)
}

// ── Schema ───────────────────────────────────────────────────────────────────

/// The serialized spelling of [`BwdRegime`], which is not `serde`-derived
/// upstream. `R0` / `Ext`, the same two labels every report in this crate uses.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum ArtifactRegime {
    R0,
    Ext,
}

impl ArtifactRegime {
    pub fn of(regime: BwdRegime) -> Self {
        match regime {
            BwdRegime::R0 => ArtifactRegime::R0,
            BwdRegime::Ext => ArtifactRegime::Ext,
        }
    }

    pub fn regime(self) -> BwdRegime {
        match self {
            ArtifactRegime::R0 => BwdRegime::R0,
            ArtifactRegime::Ext => BwdRegime::Ext,
        }
    }

    pub fn label(self) -> &'static str {
        match self {
            ArtifactRegime::R0 => "R0",
            ArtifactRegime::Ext => "Ext",
        }
    }
}

/// §7.2's fitness tuple, exactly.
///
/// The design defines the score as
/// `(realized source-read bytes, source arithmetic by BF/mixed/E4 class, emitted
/// move count, encoded program bytes, stable lexical tie break)`. The tie break IS
/// the order, which the artifact stores next to this, so the five components are
/// complete between the two fields.
///
/// Storing the last two components matters: they are the only part of the score
/// that depends on placement and encoding, so a replay that reproduced the paging
/// plan but a different program would otherwise pass.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ArtifactScore {
    pub source_read_bytes: u64,
    pub e4_ops: u64,
    pub mixed_ops: u64,
    pub bf_ops: u64,
    pub moves: usize,
    pub program_bytes: usize,
}

/// One `(layer, regime, budget)` schedule.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BudgetSchedule {
    /// `2..=16`.
    pub cells: u8,
    /// The normalized term order, as dense [`TermId`] indices.
    pub order: Vec<u32>,
    /// [`digest`] of the paging plan's [`PagingPlan::canonical_bytes`].
    pub paging_digest: u64,
    pub score: ArtifactScore,
}

/// One `(layer, regime)` coordinate: its whole `c2`..`c16` family.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoordinateArtifact {
    pub layer: usize,
    pub regime: ArtifactRegime,
    /// The fold depth the schedule was priced at (§10.2). A schedule input, not a
    /// physical binding: the round bindings supply the actual depths (§13).
    pub target_depth: u8,
    /// One entry per budget, ascending `c2`..`c16`.
    pub budgets: Vec<BudgetSchedule>,
}

/// One circuit's complete artifact.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CircuitArtifact {
    /// The committed layout file name — the circuit's identity.
    pub circuit: String,
    /// Ascending by `(layer, regime)`.
    pub coordinates: Vec<CoordinateArtifact>,
}

impl CircuitArtifact {
    /// Assemble one circuit's artifact, sorted into its canonical order.
    pub fn new(circuit: &str, mut coordinates: Vec<CoordinateArtifact>) -> Self {
        coordinates.sort_by_key(|c| (c.layer, c.regime));
        CircuitArtifact { circuit: circuit.to_string(), coordinates }
    }
}

/// The artifact file name for one circuit, mirroring the committed-schedule
/// spelling `{stem}_bwd_eval_plan_c2-c16_gkr.json`.
pub fn artifact_file_name(circuit: &str) -> String {
    format!("{}_bwd_coeff_c2-c16.json", circuit.trim_end_matches(".json"))
}

/// Serialize one circuit artifact to its canonical bytes: pretty JSON plus a
/// trailing newline.
///
/// Deterministic by construction — every container in the schema is a `Vec` in a
/// fixed order, so two runs that agree on the schedules agree on the bytes.
pub fn artifact_bytes(artifact: &CircuitArtifact) -> Vec<u8> {
    let mut bytes = serde_json::to_vec_pretty(artifact).expect("the schema is plain data");
    bytes.push(b'\n');
    bytes
}

/// Write one circuit's artifact ONCE, after its complete chain has succeeded.
///
/// No checkpoint file and no atomic rename: deterministic generation of an
/// ordinary circuit is fast, a failed chain returns an error before this is
/// reached, and a half-written file would be replaced wholesale by the next run
/// anyway.
pub fn write_circuit_artifact(
    directory: &Path,
    artifact: &CircuitArtifact,
) -> std::io::Result<PathBuf> {
    std::fs::create_dir_all(directory)?;
    let path = directory.join(artifact_file_name(&artifact.circuit));
    std::fs::write(&path, artifact_bytes(artifact))?;
    Ok(path)
}

/// Read back one circuit's artifact.
pub fn read_circuit_artifact(path: &Path) -> std::io::Result<CircuitArtifact> {
    let bytes = std::fs::read(path)?;
    serde_json::from_slice(&bytes).map_err(std::io::Error::other)
}

// ── Errors ───────────────────────────────────────────────────────────────────

/// Everything artifact compilation and replay can reject. Every variant is
/// derivable from the inputs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArtifactError {
    /// The canonical layer does not lower.
    Lowering(CoeffError),
    /// The pager rejected the order.
    Schedule(ScheduleError),
    /// The paging certificate rejected the plan.
    PagingCertificate(PagingCertificateError),
    Placement(PlacementError),
    /// The cell-liveness certificate (§12.2) rejected the placement.
    Liveness(LivenessError),
    Binding(SourceBindError),
    /// The source/materialization certificate (§12.3) rejected the binding.
    SourceCertificate(SourceCertificateError),
    /// The codec, or the §12.1 encoding certificate, rejected the program.
    Codec(CoeffCodecError),
    /// The artifact names a budget outside `c2`..`c16`, or does not name all
    /// fifteen exactly once ascending.
    BudgetFamilyMalformed { cells: Vec<u8> },
    /// The artifact declares a fold depth that is not the one its regime prices
    /// at (§10.2).
    ///
    /// The depth is a schedule INPUT: every source price, and therefore the whole
    /// modeled score, is computed against it. An artifact that named a depth its
    /// regime does not use would replay a different physical layer than the one it
    /// claims to describe, so this is rejected before anything is realized.
    TargetDepthMismatch { regime: ArtifactRegime, expected: u8, found: u8 },
    /// Replay re-derived a different paging plan than the artifact names.
    DigestMismatch { cells: u8, expected: u64, found: u64 },
    /// Replay re-derived a different score than the artifact declares.
    ScoreMismatch { cells: u8, expected: Box<ArtifactScore>, found: Box<ArtifactScore> },
    /// The realized program does not fit the by-value kernel-argument cap (§9.1).
    /// There is no device-pointer fallback: this is terminal.
    ProgramExceedsKernelArgumentCap { cells: u8, bytes: usize },
}

macro_rules! artifact_from {
    ($($ty:ty => $variant:ident),* $(,)?) => {
        $(impl From<$ty> for ArtifactError {
            fn from(e: $ty) -> Self {
                ArtifactError::$variant(e)
            }
        })*
    };
}

artifact_from!(
    CoeffError => Lowering,
    ScheduleError => Schedule,
    PagingCertificateError => PagingCertificate,
    PlacementError => Placement,
    LivenessError => Liveness,
    SourceBindError => Binding,
    SourceCertificateError => SourceCertificate,
    CoeffCodecError => Codec,
);

// ── The read floor (§15) ─────────────────────────────────────────────────────

/// The schedule-independent read floor of one lowered layer, in DRAM bytes.
///
/// A source's endpoints have to be read at least
/// [`compulsory_endpoint_reads`]-many times by ANY schedule: `Endpoint0` needs
/// `s0`, `Delta` needs `s0` and `s1`, and a cache can serve every later use of
/// both. Multiplying by the per-endpoint byte price gives the traffic no cell
/// budget can remove.
///
/// This is a true lower bound on [`PagingCost::source_read_bytes`] and, with
/// enough lanes, it is ACHIEVED — which is why the percent-above-floor column
/// tends to zero as the budget grows.
pub fn total_read_floor_bytes(layer: &CoeffLayer, prices: &[SourcePrice]) -> u64 {
    compulsory_endpoint_reads(layer)
        .iter()
        .enumerate()
        .map(|(index, &reads)| {
            prices
                .get(index)
                .map_or(0, |price| price.element_bytes.saturating_mul(u64::from(reads)))
        })
        .sum()
}

// ── The per-program report (§15) ─────────────────────────────────────────────

/// One `(coordinate, budget)`'s exact static cost.
///
/// Bytes are bytes: [`ProgramReport::materialization_write_bytes`] is a WRITE
/// counter and never enters any read numerator, and the three arithmetic classes
/// are counts of operations, never bytes.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ProgramReport {
    pub cells: u8,
    pub terms: usize,

    // ── reads ────────────────────────────────────────────────────────────
    /// The traffic every schedule must move at least once — one endpoint read per
    /// `Endpoint0`-only source, two for a source whose `Delta` is consumed.
    pub compulsory_read_once_bytes: u64,
    /// Read bytes above the floor: traffic a larger cell budget could have served
    /// from a resident lane. `realized - floor`, never negative
    /// ([`total_read_floor_bytes`] is a true lower bound).
    pub cacheable_reread_bytes: u64,
    /// `compulsory_read_once_bytes`. Named separately because §15's percentage is
    /// defined against "the total read floor", and a reader must not have to infer
    /// which of the two numbers that is.
    pub total_read_floor_bytes: u64,
    /// What the schedule actually reads.
    pub realized_total_read_bytes: u64,

    // ── writes, kept out of the read numerator ───────────────────────────
    /// Publication traffic (§10.2). Zero when the program does not materialize.
    pub materialization_write_bytes: u64,

    // ── arithmetic, by class ─────────────────────────────────────────────
    pub bf_ops: u64,
    pub mixed_ops: u64,
    pub e4_ops: u64,

    // ── shared memory (the cell file) ────────────────────────────────────
    /// Cell-file reads. One access per value: §11 resolves an E4 cell with a
    /// single sixteen-byte vector load, not four.
    pub shared_loads: u64,
    /// Cell-file writes, same accounting.
    pub shared_stores: u64,

    // ── program ──────────────────────────────────────────────────────────
    pub moves: usize,
    pub words: usize,
    pub bytes: usize,
    /// [`program_digest`] of the canonical encoding.
    ///
    /// Carried in the REPORT, never in the artifact — the artifact stores
    /// decisions, and a program is a consequence of them. Its job is to make
    /// "replay reproduces the canonical encoding" a whole-corpus property for
    /// free: comparing a replayed [`CoordinateReport`] against the compiled one
    /// compares this field, and it is a function of every lane, window, column,
    /// opcode and coefficient the encoder emitted. Two runs that agree on it
    /// agree on placement and final binding too, because nothing else could
    /// produce the same words.
    pub program_digest: u64,

    // ── residency diagnostics ────────────────────────────────────────────
    pub source_resolutions: u64,
    pub hits: u64,
    pub misses: u64,
    pub fills: u64,
    pub bypasses: u64,
    pub evictions: u64,
    pub peak_resident_lanes: u32,
    pub lanes_used: u32,
}

impl ProgramReport {
    /// §15's headline: `(realized / floor - 1) * 100`.
    ///
    /// A layer whose every source is procedural moves no DRAM at all; its floor
    /// and its realized traffic are both zero and it is exactly AT the floor.
    pub fn percent_above_floor(&self) -> f64 {
        if self.total_read_floor_bytes == 0 {
            return if self.realized_total_read_bytes == 0 { 0.0 } else { f64::INFINITY };
        }
        (self.realized_total_read_bytes as f64 / self.total_read_floor_bytes as f64 - 1.0) * 100.0
    }

    pub fn score(&self) -> ArtifactScore {
        ArtifactScore {
            source_read_bytes: self.realized_total_read_bytes,
            e4_ops: self.e4_ops,
            mixed_ops: self.mixed_ops,
            bf_ops: self.bf_ops,
            moves: self.moves,
            program_bytes: self.bytes,
        }
    }
}

/// One coordinate's whole `c2`..`c16` report.
#[derive(Clone, Debug, PartialEq)]
pub struct CoordinateReport {
    pub circuit: String,
    pub layer: usize,
    pub regime: ArtifactRegime,
    pub budgets: Vec<ProgramReport>,
}

impl CoordinateReport {
    pub fn sort_key(&self) -> (&str, usize, ArtifactRegime) {
        (self.circuit.as_str(), self.layer, self.regime)
    }

    pub fn label(&self) -> String {
        format!("{} L{} {}", self.circuit, self.layer, self.regime.label())
    }
}

// ── Realization: the one path both compilation and replay run ────────────────

/// A complete realized program: the paging plan, its placement, its final binding
/// and its canonical encoding, each certified.
pub struct Realization {
    pub plan: PagingPlan,
    pub placement: CoeffPlacement,
    pub binding: CoeffSourceBinding,
    pub program: EncodedProgram,
    pub report: ProgramReport,
}

/// Shared-memory traffic of one placed program, from the instruction stream that
/// actually executes.
fn shared_traffic(placement: &CoeffPlacement) -> (u64, u64) {
    let mut loads = 0u64;
    let mut stores = 0u64;
    for instr in &placement.instrs {
        match instr {
            ScheduledInstr::Term { uses, .. } => {
                for use_ in uses {
                    match use_ {
                        ValueUse::Direct { .. } => {}
                        ValueUse::Fill { .. } => stores += 1,
                        ValueUse::Cell(super::place::CellRead::Single { .. }) => loads += 1,
                        // The packed native-dual form reads two lanes.
                        ValueUse::Cell(super::place::CellRead::Pair { .. }) => loads += 2,
                        ValueUse::PlannedDelta { endpoint0, delta, .. } => {
                            for action in [endpoint0, delta] {
                                match action {
                                    super::place::PlanAction::UseResident { .. } => loads += 1,
                                    super::place::PlanAction::Fill { .. } => stores += 1,
                                    super::place::PlanAction::Direct
                                    | super::place::PlanAction::Invalid => {}
                                }
                            }
                        }
                    }
                }
            }
            // A move reads its source lane and writes its destination lane.
            ScheduledInstr::MoveBF { .. } | ScheduledInstr::MoveE4 { .. } => {
                loads += 1;
                stores += 1;
            }
        }
    }
    (loads, stores)
}

/// Publication traffic (§10.2), in bytes.
///
/// A materializing program publishes each DRAM-backed source once, on its marked
/// first physical access, and a materialized fold buffer element is Ext-width
/// regardless of the origin's own width — the same rule
/// [`crate::bwd::cost::round_cost`] tallies fold stores under. A procedural
/// `VirtualSetup` window moves no DRAM in either direction ([`source_prices`]
/// prices it at zero element bytes at every depth), so it publishes nothing.
///
/// Reported SEPARATELY and never added to a read counter.
fn materialization_write_bytes(binding: &CoeffSourceBinding) -> u64 {
    if !binding.materialize {
        return 0;
    }
    let published = binding
        .uses
        .iter()
        .filter(|use_| use_.first_access)
        .filter(|use_| {
            binding
                .windows
                .get(usize::from(use_.window))
                .is_some_and(|window| !window.is_procedural())
        })
        .count();
    (published as u64).saturating_mul(EXT_BYTES as u64)
}

/// Page, place, bind and encode one order, proving every certificate on the way.
///
/// The ONE realization path: [`compile_coordinate`] and [`replay_coordinate`] both
/// call it, so a replay cannot accidentally exercise a different pipeline than the
/// compilation it is checking.
pub fn realize(
    layer: &CoeffLayer,
    prices: &[SourcePrice],
    cross_fields: &HashMap<ReadPlace, FieldKind>,
    request: PagingRequest,
    order: &[TermId],
    floor_bytes: u64,
) -> Result<Realization, ArtifactError> {
    let plan = page_projections(layer, prices, request, order)?;
    certify_paging_plan(layer, prices, &plan)?;

    // §7.3: "paging fixes admission, bypass, retention, and eviction before
    // placement. Placement may not change those decisions." Enforced by the TYPE:
    // `place_paging_plan` takes `&PagingPlan`, so the plan is immutable across the
    // call and no runtime check could ever fail. An earlier revision compared the
    // canonical bytes either side under `debug_assert_eq!`, which was both
    // tautological and — since this path runs `--release` — never executed.
    let placement = place_paging_plan(layer, prices, &plan)?;
    certify_cell_liveness(layer, prices, &plan, &placement)?;

    let binding = bind_coeff_sources(layer, cross_fields, &placement)?;
    certify_source_binding(layer, cross_fields, &placement, &binding)?;

    let program = encode_program(layer, &placement, &binding)?;
    // §11.6: `certify_encoding`, never `validate_program`. `TrailingWords` is only
    // decidable against a DECLARED record count, and `num_words` does not supply
    // one — a stream with extra trailing records decodes and validates happily.
    certify_encoding(layer, &placement, &binding, &program)?;

    // §9.1: "the program AND all other by-value descriptor metadata must fit the
    // existing 32,764-byte kernel-argument cap". So a program that exactly fills
    // the cap already violates it — there would be nothing left for the metadata
    // that has to travel with it. The gate is `>=`, not `>`. There is no
    // device-pointer fallback: an overflow requires a tighter encoding.
    if program.bytes() >= limits::KERNEL_ARGUMENT_CEILING_BYTES {
        return Err(ArtifactError::ProgramExceedsKernelArgumentCap {
            cells: request.budget.cells(),
            bytes: program.bytes(),
        });
    }

    let (shared_loads, shared_stores) = shared_traffic(&placement);
    let realized = plan.cost.source_read_bytes;
    let report = ProgramReport {
        cells: request.budget.cells(),
        terms: layer.terms.len(),
        compulsory_read_once_bytes: floor_bytes,
        cacheable_reread_bytes: realized.saturating_sub(floor_bytes),
        total_read_floor_bytes: floor_bytes,
        realized_total_read_bytes: realized,
        materialization_write_bytes: materialization_write_bytes(&binding),
        bf_ops: plan.cost.bf_ops,
        mixed_ops: plan.cost.mixed_ops,
        e4_ops: plan.cost.e4_ops,
        shared_loads,
        shared_stores,
        moves: placement.stats.bf_moves + placement.stats.e4_moves,
        words: program.words.len(),
        bytes: program.bytes(),
        program_digest: program_digest(&program),
        source_resolutions: plan.cost.source_resolutions,
        hits: plan.cost.hits,
        misses: plan.cost.misses,
        fills: plan.cost.fills,
        bypasses: plan.cost.bypasses,
        evictions: plan.cost.evictions,
        peak_resident_lanes: plan.cost.peak_resident_lanes,
        lanes_used: placement.stats.lanes_used,
    };
    Ok(Realization { plan, placement, binding, program, report })
}

// ── Compilation ──────────────────────────────────────────────────────────────

/// Everything one coordinate's compilation produces.
pub struct CompiledCoordinate {
    pub artifact: CoordinateArtifact,
    pub report: CoordinateReport,
    /// The winning seed per budget, ascending. Provenance for the sweep report;
    /// deliberately NOT part of the artifact, which stores decisions and not how
    /// they were found.
    pub winners: Vec<SeedKind>,
}

/// Lower one canonical layer in one regime and price it at its regime's depth.
pub fn lower_and_price(
    canonical: &DagLayer,
    cross_fields: &HashMap<ReadPlace, FieldKind>,
    regime: BwdRegime,
) -> Result<(CoeffLayer, Vec<SourcePrice>, u8), ArtifactError> {
    let distilled = distill(canonical, regime, cross_fields, None);
    let layer = lower_coeff_layer(canonical, &distilled)?;
    let target_depth = default_target_depth(regime);
    let prices = source_prices(&layer, &distilled, target_depth);
    Ok((layer, prices, target_depth))
}

/// Compile one `(circuit, layer, regime)` chain: every budget `c2`..`c16`, each
/// ordered by the bounded deterministic seed selection of §7.2, realized in full
/// and certified.
///
/// The chain either succeeds whole or returns the first failure. Nothing is
/// written from here — the caller writes one circuit's artifact once its
/// coordinates have all succeeded.
pub fn compile_coordinate(
    circuit: &str,
    layer_index: usize,
    canonical: &DagLayer,
    cross_fields: &HashMap<ReadPlace, FieldKind>,
    regime: BwdRegime,
) -> Result<CompiledCoordinate, ArtifactError> {
    let (layer, prices, target_depth) = lower_and_price(canonical, cross_fields, regime)?;
    let floor_bytes = total_read_floor_bytes(&layer, &prices);

    let mut budgets = Vec::with_capacity(CellBudget::ALL.len());
    let mut reports = Vec::with_capacity(CellBudget::ALL.len());
    let mut winners = Vec::with_capacity(CellBudget::ALL.len());
    let mut preceding: Option<Vec<TermId>> = None;

    for budget in CellBudget::ALL {
        let request = PagingRequest { budget, target_depth };
        let outcome = select_paged_order(&layer, &prices, request, preceding.as_deref())?;
        let order = outcome.plan.order.clone();
        let chosen = digest(&outcome.plan.canonical_bytes());

        let realization =
            realize(&layer, &prices, cross_fields, request, &order, floor_bytes)?;
        let paging_digest = digest(&realization.plan.canonical_bytes());
        // Re-paging the winning order reproduces the winning plan byte for byte.
        // Cheap, and it is the determinism property the artifact rests on.
        if paging_digest != chosen {
            return Err(ArtifactError::DigestMismatch {
                cells: budget.cells(),
                expected: chosen,
                found: paging_digest,
            });
        }

        budgets.push(BudgetSchedule {
            cells: budget.cells(),
            order: order.iter().map(|t| t.0).collect(),
            paging_digest,
            score: realization.report.score(),
        });
        reports.push(realization.report);
        winners.push(outcome.winner);
        preceding = Some(order);
    }

    Ok(CompiledCoordinate {
        artifact: CoordinateArtifact {
            layer: layer_index,
            regime: ArtifactRegime::of(regime),
            target_depth,
            budgets,
        },
        report: CoordinateReport {
            circuit: circuit.to_string(),
            layer: layer_index,
            regime: ArtifactRegime::of(regime),
            budgets: reports,
        },
        winners,
    })
}

// ── Replay ───────────────────────────────────────────────────────────────────

/// Reconstruct one coordinate's whole budget family from the artifact and the
/// canonical DAG, and reject it on any mismatch.
///
/// Everything physical is REBUILT here: the paging plan (from the stored order),
/// the placement, the final source binding, the canonical u16 encoding, and all
/// four certificates. The artifact only has to be right about the term order; the
/// digest and the score then prove that the rebuild is the schedule the artifact
/// was compiled from.
pub fn replay_coordinate(
    canonical: &DagLayer,
    cross_fields: &HashMap<ReadPlace, FieldKind>,
    coordinate: &CoordinateArtifact,
) -> Result<CoordinateReport, ArtifactError> {
    let regime = coordinate.regime.regime();
    let (layer, prices, target_depth) = lower_and_price(canonical, cross_fields, regime)?;
    if target_depth != coordinate.target_depth {
        return Err(ArtifactError::TargetDepthMismatch {
            regime: coordinate.regime,
            expected: target_depth,
            found: coordinate.target_depth,
        });
    }
    let floor_bytes = total_read_floor_bytes(&layer, &prices);

    // §13 compiles an artifact for every budget, so a family missing one — or
    // naming one twice, or out of order — is malformed rather than partial.
    let declared: Vec<u8> = coordinate.budgets.iter().map(|b| b.cells).collect();
    let expected: Vec<u8> = CellBudget::ALL.iter().map(|b| b.cells()).collect();
    if declared != expected {
        return Err(ArtifactError::BudgetFamilyMalformed { cells: declared });
    }

    let mut reports = Vec::with_capacity(coordinate.budgets.len());
    for entry in &coordinate.budgets {
        let budget = CellBudget::new(entry.cells)?;
        let request = PagingRequest { budget, target_depth };
        let order: Vec<TermId> = entry.order.iter().copied().map(TermId).collect();
        let realization = realize(&layer, &prices, cross_fields, request, &order, floor_bytes)?;

        let found = digest(&realization.plan.canonical_bytes());
        if found != entry.paging_digest {
            return Err(ArtifactError::DigestMismatch {
                cells: entry.cells,
                expected: entry.paging_digest,
                found,
            });
        }
        let score = realization.report.score();
        if score != entry.score {
            return Err(ArtifactError::ScoreMismatch {
                cells: entry.cells,
                expected: Box::new(entry.score),
                found: Box::new(score),
            });
        }
        reports.push(realization.report);
    }

    Ok(CoordinateReport {
        circuit: String::new(),
        layer: coordinate.layer,
        regime: coordinate.regime,
        budgets: reports,
    })
}

// ── Aggregate reporting ──────────────────────────────────────────────────────

/// The corpus-wide numbers Task 9 and the acceptance gates read.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CorpusSummary {
    pub coordinates: usize,
    pub programs: usize,
    /// The largest realized encoded program, over every coordinate and budget.
    pub max_program_words: usize,
    pub max_program_bytes: usize,
    /// Which `(coordinate, budget)` realizes it.
    pub max_program_at: String,
    pub max_program_cells: u8,
    /// Moves the whole corpus emits.
    pub total_moves: usize,
    /// Coordinates whose realized read traffic sits exactly on the floor, per
    /// budget, ascending `c2`..`c16`.
    pub at_floor_per_budget: Vec<usize>,
    /// One number over every encoded program in the corpus, in report order.
    ///
    /// The determinism claim in a single value: two runs that agree on it emitted
    /// the same 1,710 canonical encodings, lane for lane and window for window.
    pub corpus_program_digest: u64,
}

/// Summarize a whole corpus of coordinate reports. `reports` must already be
/// sorted by [`CoordinateReport::sort_key`].
pub fn summarize(reports: &[CoordinateReport]) -> CorpusSummary {
    let mut summary = CorpusSummary {
        coordinates: reports.len(),
        at_floor_per_budget: vec![0; CellBudget::ALL.len()],
        ..Default::default()
    };
    let mut folded: Vec<u8> = Vec::with_capacity(reports.len() * 8);
    for report in reports {
        for (index, program) in report.budgets.iter().enumerate() {
            summary.programs += 1;
            summary.total_moves += program.moves;
            folded.extend_from_slice(&program.program_digest.to_le_bytes());
            if program.realized_total_read_bytes == program.total_read_floor_bytes
                && let Some(slot) = summary.at_floor_per_budget.get_mut(index)
            {
                *slot += 1;
            }
            if program.words > summary.max_program_words {
                summary.max_program_words = program.words;
                summary.max_program_bytes = program.bytes;
                summary.max_program_at = report.label();
                summary.max_program_cells = program.cells;
            }
        }
    }
    summary.corpus_program_digest = digest(&folded);
    summary
}

/// The percent-above-floor table: `(circuit, layer, regime)` down, `c2`..`c16`
/// across.
///
/// Every cell is `(realized / floor - 1) * 100` for that program. Materialization
/// writes are absent from it by construction — they are not read bytes.
pub fn percent_above_floor_table(reports: &[CoordinateReport]) -> String {
    let mut out = String::new();
    out.push_str(&format!("{:<58}", "coordinate"));
    for budget in CellBudget::ALL {
        out.push_str(&format!("{:>9}", budget.label()));
    }
    out.push('\n');
    for report in reports {
        out.push_str(&format!("{:<58}", report.label()));
        for program in &report.budgets {
            out.push_str(&format!("{:>9.2}", program.percent_above_floor()));
        }
        out.push('\n');
    }
    out
}

/// Corpus totals per budget, in the same column order as
/// [`percent_above_floor_table`].
///
/// The whole-corpus percentage is computed from the SUMMED bytes, not as a mean of
/// per-coordinate percentages: a mean of ratios would weight a 200-byte layer like
/// a 200-kilobyte one.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct BudgetTotals {
    pub cells: u8,
    pub compulsory_read_once_bytes: u64,
    pub cacheable_reread_bytes: u64,
    pub total_read_floor_bytes: u64,
    pub realized_total_read_bytes: u64,
    pub materialization_write_bytes: u64,
    pub bf_ops: u64,
    pub mixed_ops: u64,
    pub e4_ops: u64,
    pub shared_loads: u64,
    pub shared_stores: u64,
    pub moves: usize,
    pub words: usize,
    pub bytes: usize,
    pub max_words: usize,
}

impl BudgetTotals {
    pub fn percent_above_floor(&self) -> f64 {
        if self.total_read_floor_bytes == 0 {
            return if self.realized_total_read_bytes == 0 { 0.0 } else { f64::INFINITY };
        }
        (self.realized_total_read_bytes as f64 / self.total_read_floor_bytes as f64 - 1.0) * 100.0
    }
}

/// Per-budget corpus totals, ascending `c2`..`c16`.
pub fn budget_totals(reports: &[CoordinateReport]) -> Vec<BudgetTotals> {
    let mut totals: Vec<BudgetTotals> = CellBudget::ALL
        .iter()
        .map(|budget| BudgetTotals { cells: budget.cells(), ..Default::default() })
        .collect();
    for report in reports {
        for (index, program) in report.budgets.iter().enumerate() {
            let Some(total) = totals.get_mut(index) else { continue };
            total.compulsory_read_once_bytes += program.compulsory_read_once_bytes;
            total.cacheable_reread_bytes += program.cacheable_reread_bytes;
            total.total_read_floor_bytes += program.total_read_floor_bytes;
            total.realized_total_read_bytes += program.realized_total_read_bytes;
            total.materialization_write_bytes += program.materialization_write_bytes;
            total.bf_ops += program.bf_ops;
            total.mixed_ops += program.mixed_ops;
            total.e4_ops += program.e4_ops;
            total.shared_loads += program.shared_loads;
            total.shared_stores += program.shared_stores;
            total.moves += program.moves;
            total.words += program.words;
            total.bytes += program.bytes;
            total.max_words = total.max_words.max(program.words);
        }
    }
    totals
}

// ── Progress ─────────────────────────────────────────────────────────────────

/// One completed `(circuit, layer, regime)` chain (§14: "compute-heavy
/// compilation ... expose durable progress").
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChainProgress {
    pub circuit: String,
    pub layer: usize,
    pub regime: ArtifactRegime,
    pub budgets: usize,
    pub terms: usize,
    pub max_words: usize,
}

impl std::fmt::Display for ChainProgress {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "[chain] {} L{} {:<3} budgets={} terms={} max_words={}",
            self.circuit, self.layer, self.regime.label(), self.budgets, self.terms, self.max_words
        )
    }
}

impl ChainProgress {
    pub fn of(compiled: &CompiledCoordinate) -> Self {
        ChainProgress {
            circuit: compiled.report.circuit.clone(),
            layer: compiled.report.layer,
            regime: compiled.report.regime,
            budgets: compiled.report.budgets.len(),
            terms: compiled.report.budgets.first().map_or(0, |b| b.terms),
            max_words: compiled.report.budgets.iter().map(|b| b.words).max().unwrap_or(0),
        }
    }
}

