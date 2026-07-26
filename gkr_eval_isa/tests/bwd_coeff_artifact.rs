//! Task 8 gates: the deterministic `c2`-`c16` schedule artifacts and their replay
//! (design §7.2, §13, §12).
//!
//! Two properties are proven here, and the second is the reason the first is
//! allowed to be so small:
//!
//!   1. **The schema carries nothing physical.** §13: artifacts contain term order
//!      and deterministic paging decisions, and "do not contain a genome, physical
//!      pointers, or pre-bound source windows". `an_artifact_carries_nothing_but_
//!      decisions` pins the serialized key set EXACTLY, over the whole corpus, so a
//!      field cannot be added by accident.
//!   2. **Replay reconstructs everything else and rejects any disagreement.** From
//!      the canonical DAG plus (order, paging digest, score), replay re-derives the
//!      paging plan, the placement, the final source binding, the canonical u16
//!      encoding and all four certificates. The tamper tests show each rejection
//!      path individually; the corpus test proves the round trip over all 114
//!      coordinates × 15 budgets rather than on samples.
//!
//! Determinism is BYTE equality across two complete, independent generations —
//! `run-a` and `run-b` below — not a spot check of a digest.
//!
//! # Scope
//!
//! There is no conditional artifact family. `blake2_with_compression` is not a
//! distinct circuit: `Blake2sWithCompressionDelegationCircuit` has
//! `DOMAIN_SIZE_LOG2 = 20` and its `define_delegation_circuit` calls
//! `define_blake2_with_extended_control_delegation_circuit`, which is the call that
//! produced the committed `blake2_with_extended_control_layout_gkr.json`; Task 3's
//! census measured byte-identical serialized layouts and field-for-field identical
//! rows. §3.1's exclusion therefore cannot trigger, `limits::in_scope` already
//! covers the circuit, and an all-or-nothing gate here would be dead code.

mod common;

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use common::{CrossFields, FIXTURES, layers_with_bwd_roots};
use cs::gkr_compiler::dag_ir::{BwdRegime, DagLayer, FieldKind, ReadPlace};
use gkr_eval_isa::bwd::coeff::artifact::{
    ArtifactError, ArtifactRegime, ArtifactScore, ChainProgress, CircuitArtifact,
    CoordinateArtifact, CoordinateReport, CorpusSummary, artifact_bytes, artifact_file_name,
    compile_coordinate, read_circuit_artifact, realize, replay_coordinate, summarize,
    write_circuit_artifact,
};
use gkr_eval_isa::bwd::coeff::encode::CoeffCodecError;
use gkr_eval_isa::bwd::coeff::limits::{
    DESCRIPTOR_ALIGNMENT_BYTES, KERNEL_ARGUMENT_CEILING_BYTES, in_scope,
};
use gkr_eval_isa::bwd::coeff::schedule::{
    CellBudget, OpCounts, PagingRequest, SourcePrice, ValueWidth, default_target_depth,
};
use gkr_eval_isa::bwd::coeff::{
    CoeffLayer, CoeffSource, CoeffTerm, CoefficientRecipeId, ProjectionId, SourceId, TermId,
};
use gkr_eval_isa::bwd::source::OriginLeaf;
use rayon::prelude::*;

// ── Relations between the pinned constants ───────────────────────────────────
//
// Const-vs-const, so they hold at COMPILE time rather than as runtime assertions
// that cannot fail. The runtime assertions in this file are the ones with a
// MEASUREMENT on one side.

/// The descriptor array is 16-byte aligned and carries no speculative headroom
/// beyond that alignment.
const _: () = assert!(
    in_scope::DESCRIPTOR_PROGRAM_BYTES - in_scope::MAX_REALIZED_PROGRAM_BYTES
        < DESCRIPTOR_ALIGNMENT_BYTES
);
const _: () = assert!(in_scope::DESCRIPTOR_PROGRAM_BYTES < KERNEL_ARGUMENT_CEILING_BYTES);

// ── One small real coordinate, for the rejection paths ───────────────────────

/// The smallest committed layer that still bears backward roots, compiled whole.
///
/// A real coordinate and not a synthetic one on purpose: the rejection paths have
/// to fire against an artifact that is otherwise completely valid.
fn small_coordinate() -> (DagLayer, CrossFields, CoordinateArtifact) {
    let name = "shift_binop_layout_gkr.json";
    let (layer_index, canonical, cross) =
        layers_with_bwd_roots(name).last().expect("shift_binop has backward layers");
    let compiled = compile_coordinate(name, layer_index, &canonical, &cross, BwdRegime::R0)
        .expect("the smallest coordinate compiles");
    (canonical, cross, compiled.artifact)
}

// ── The by-value kernel-argument cap (§9.1) ──────────────────────────────────

/// §9.1: "the program AND all other by-value descriptor metadata must fit the
/// existing 32,764-byte kernel-argument cap. There is no device-pointer program
/// representation or overflow fallback."
///
/// The production corpus is nowhere near it — 11,518 bytes is the worst — so the
/// boundary can only be exercised synthetically. It is worth exercising: it is the
/// one terminal failure of the whole artifact path, and an untested terminal path
/// is a path that fires wrong the first time it fires.
///
/// There are TWO gates, one strictly tighter than the other, and the test pins
/// where each takes over:
///
///   * Task 7's codec rejects a program **above** the cap
///     (`CoeffCodecError::ProgramExceedsKernelArgumentCap`); and
///   * this task's `realize` rejects a program **at or above** it, because §9.1
///     requires the program *and all other by-value descriptor metadata* to fit —
///     a program that exactly fills the cap leaves the metadata nowhere to go.
///
/// So exactly one program size, 32,764 bytes, is accepted by the codec and refused
/// here. That one size is what makes this gate more than a duplicate, so the test
/// hits it exactly rather than merely overshooting.
const SOURCES: u32 = 64;

fn cap_probe(terms: u32) -> (CoeffLayer, Vec<SourcePrice>, Vec<TermId>) {
    let sources = (0..SOURCES as usize)
        .map(|column| CoeffSource {
            origin: OriginLeaf::Read(ReadPlace::BaseLayerMemory { column }),
            field: FieldKind::Base,
        })
        .collect();
    let prices = (0..SOURCES)
        .map(|_| SourcePrice {
            width: ValueWidth::Bf,
            element_bytes: 4,
            endpoint_ops: OpCounts::ZERO,
        })
        .collect();
    let layer = CoeffLayer {
        regime: BwdRegime::R0,
        c_init: None,
        coefficients: Vec::new(),
        sources,
        terms: (0..terms)
            .map(|id| CoeffTerm::C0Linear {
                id: TermId(id),
                coefficient: CoefficientRecipeId::ONE,
                value: ProjectionId::endpoint0(SourceId(id % SOURCES)),
                field: FieldKind::Base,
            })
            .collect(),
    };
    (layer, prices, (0..terms).map(TermId).collect())
}

fn cap_probe_request() -> PagingRequest {
    PagingRequest {
        budget: CellBudget::new(16).expect("c16"),
        target_depth: default_target_depth(BwdRegime::R0),
    }
}

fn cap_probe_realize(terms: u32) -> Result<usize, ArtifactError> {
    let (layer, prices, order) = cap_probe(terms);
    realize(&layer, &prices, &CrossFields::new(), cap_probe_request(), &order, 0)
        .map(|realized| realized.report.bytes)
}

#[test]
fn a_program_at_or_above_the_kernel_argument_cap_is_rejected() {
    // Encoded size is affine in the term count for this shape — the first
    // `SOURCES` terms fill a lane, every later one reads a resident — so two
    // measurements predict the term count that lands EXACTLY on the cap.
    let low = cap_probe_realize(1_000).expect("well under the cap");
    let high = cap_probe_realize(2_000).expect("well under the cap");
    let slope = (high - low) / 1_000;
    let intercept = low - slope * 1_000;
    let at_cap_terms = ((KERNEL_ARGUMENT_CEILING_BYTES - intercept) / slope) as u32;
    assert_eq!(
        slope * at_cap_terms as usize + intercept,
        KERNEL_ARGUMENT_CEILING_BYTES,
        "the probe shape is not affine in the term count; re-derive the boundary"
    );

    // One term short: the largest program the artifact path accepts.
    let under = cap_probe_realize(at_cap_terms - 1).expect("under the cap");
    assert_eq!(under, KERNEL_ARGUMENT_CEILING_BYTES - slope);

    // Exactly at the cap: the codec is happy, this gate is not. This is the whole
    // reason the gate exists.
    match cap_probe_realize(at_cap_terms) {
        Err(ArtifactError::ProgramExceedsKernelArgumentCap { cells, bytes }) => {
            assert_eq!(cells, 16);
            assert_eq!(bytes, KERNEL_ARGUMENT_CEILING_BYTES);
        }
        other => panic!("a program exactly at the cap must be rejected here, got {other:?}"),
    }

    // Above the cap: Task 7's codec gets there first, and it is equally terminal.
    match cap_probe_realize(at_cap_terms + 1_000) {
        Err(ArtifactError::Codec(CoeffCodecError::ProgramExceedsKernelArgumentCap { bytes })) => {
            assert!(bytes > KERNEL_ARGUMENT_CEILING_BYTES);
        }
        other => panic!("a program past the cap must be terminal, got {other:?}"),
    }
}

// ── The schema ───────────────────────────────────────────────────────────────

/// Exactly the fields §13 permits, and no others.
///
/// Spelled as literal key sets rather than as a "does not contain 'lane'" scan:
/// a substring scan passes for a field nobody thought to name, and this must fail
/// for ANY new field. Adding one is then a deliberate act with a test to change.
const COORDINATE_KEYS: &[&str] = &["layer", "regime", "target_depth", "budgets"];
const BUDGET_KEYS: &[&str] = &["cells", "order", "paging_digest", "score"];
const SCORE_KEYS: &[&str] =
    &["source_read_bytes", "e4_ops", "mixed_ops", "bf_ops", "moves", "program_bytes"];

fn keys(value: &serde_json::Value, path: &str) -> BTreeSet<String> {
    value
        .as_object()
        .unwrap_or_else(|| panic!("{path} is not an object"))
        .keys()
        .cloned()
        .collect()
}

fn expected(names: &[&str]) -> BTreeSet<String> {
    names.iter().map(|n| (*n).to_string()).collect()
}

/// Every artifact the corpus produces carries decisions and nothing else.
fn assert_schema_is_minimal(bytes: &[u8], label: &str) {
    let value: serde_json::Value = serde_json::from_slice(bytes).expect("artifacts are JSON");
    assert_eq!(keys(&value, label), expected(&["circuit", "coordinates"]));
    for (index, coordinate) in
        value["coordinates"].as_array().expect("coordinates is an array").iter().enumerate()
    {
        let at = format!("{label}[{index}]");
        assert_eq!(keys(coordinate, &at), expected(COORDINATE_KEYS), "{at}");
        for budget in coordinate["budgets"].as_array().expect("budgets is an array") {
            assert_eq!(keys(budget, &at), expected(BUDGET_KEYS), "{at} budget");
            assert_eq!(keys(&budget["score"], &at), expected(SCORE_KEYS), "{at} score");
            // The order is a term permutation — dense indices, nothing physical.
            assert!(
                budget["order"].as_array().expect("order is an array").iter().all(|t| t.is_u64()),
                "{at} order must be plain term indices"
            );
        }
    }
}

#[test]
fn an_artifact_carries_nothing_but_decisions() {
    let (_, _, coordinate) = small_coordinate();
    let artifact = CircuitArtifact::new("shift_binop_layout_gkr.json", vec![coordinate]);
    assert_schema_is_minimal(&artifact_bytes(&artifact), "shift_binop");
}

#[test]
fn an_artifact_round_trips_through_disk() {
    let (_, _, coordinate) = small_coordinate();
    let artifact = CircuitArtifact::new("shift_binop_layout_gkr.json", vec![coordinate]);
    let root = scratch_root("round-trip");
    let path = write_circuit_artifact(&root, &artifact).expect("write");
    assert_eq!(
        path.file_name().and_then(|n| n.to_str()),
        Some(artifact_file_name("shift_binop_layout_gkr.json").as_str())
    );
    assert_eq!(read_circuit_artifact(&path).expect("read"), artifact);
    // Written once, whole, with no checkpoint or rename residue beside it.
    let siblings: Vec<_> = std::fs::read_dir(&root).expect("dir").filter_map(Result::ok).collect();
    assert_eq!(siblings.len(), 1, "one artifact, one file");
}

// ── Replay rejects every disagreement ────────────────────────────────────────

/// A named mutation of one score component.
type ScoreMutation = (&'static str, fn(&mut ArtifactScore));

fn replay_err(
    canonical: &DagLayer,
    cross: &CrossFields,
    coordinate: &CoordinateArtifact,
) -> ArtifactError {
    replay_coordinate(canonical, cross, coordinate).expect_err("replay must reject this artifact")
}

#[test]
fn replay_accepts_the_artifact_it_was_compiled_from() {
    let (canonical, cross, coordinate) = small_coordinate();
    let report = replay_coordinate(&canonical, &cross, &coordinate).expect("clean replay");
    assert_eq!(report.budgets.len(), CellBudget::ALL.len());
    assert_eq!(report.layer, coordinate.layer);
    assert_eq!(report.regime, coordinate.regime);
}

/// A permuted order is a DIFFERENT schedule, and the paging digest says so:
/// `PagingPlan::canonical_bytes` serializes the order itself, so no permutation
/// can reproduce the stored digest.
#[test]
fn replay_rejects_a_permuted_order() {
    let (canonical, cross, mut coordinate) = small_coordinate();
    let order = &mut coordinate.budgets[0].order;
    assert!(order.len() >= 2, "the fixture needs at least two terms");
    order.swap(0, 1);
    match replay_err(&canonical, &cross, &coordinate) {
        ArtifactError::DigestMismatch { cells, expected, found } => {
            assert_eq!(cells, 2);
            assert_ne!(expected, found);
        }
        other => panic!("a permuted order must be a digest mismatch, got {other:?}"),
    }
}

/// An order that is not a permutation at all is rejected structurally, before any
/// digest is computed.
#[test]
fn replay_rejects_an_order_that_is_not_a_permutation() {
    let (canonical, cross, mut coordinate) = small_coordinate();
    coordinate.budgets[0].order[0] = coordinate.budgets[0].order[1];
    assert!(matches!(
        replay_err(&canonical, &cross, &coordinate),
        ArtifactError::Schedule(_)
    ));
}

#[test]
fn replay_rejects_a_tampered_paging_digest() {
    let (canonical, cross, mut coordinate) = small_coordinate();
    let real = coordinate.budgets[3].paging_digest;
    coordinate.budgets[3].paging_digest ^= 1;
    match replay_err(&canonical, &cross, &coordinate) {
        ArtifactError::DigestMismatch { cells, expected, found } => {
            assert_eq!(cells, 5);
            assert_eq!(found, real);
            assert_eq!(expected, real ^ 1);
        }
        other => panic!("expected a digest mismatch, got {other:?}"),
    }
}

/// Every component of §7.2's fitness tuple is checked, not just the first: a
/// score is only useful as an artifact if replay refuses to accept a different
/// one.
#[test]
fn replay_rejects_a_tampered_score_in_any_component() {
    let (canonical, cross, coordinate) = small_coordinate();
    let mutations: [ScoreMutation; 6] = [
        ("source_read_bytes", |s| s.source_read_bytes += 1),
        ("e4_ops", |s| s.e4_ops += 1),
        ("mixed_ops", |s| s.mixed_ops += 1),
        ("bf_ops", |s| s.bf_ops += 1),
        ("moves", |s| s.moves += 1),
        ("program_bytes", |s| s.program_bytes += 1),
    ];
    for (name, mutate) in mutations {
        let mut tampered = coordinate.clone();
        mutate(&mut tampered.budgets[7].score);
        match replay_err(&canonical, &cross, &tampered) {
            ArtifactError::ScoreMismatch { cells, expected, found } => {
                assert_eq!(cells, 9, "[{name}]");
                assert_ne!(expected, found, "[{name}]");
            }
            other => panic!("[{name}] expected a score mismatch, got {other:?}"),
        }
    }
}

#[test]
fn replay_rejects_an_incomplete_budget_family() {
    let (canonical, cross, coordinate) = small_coordinate();
    for (label, mut tampered) in [
        ("missing c16", {
            let mut t = coordinate.clone();
            t.budgets.pop();
            t
        }),
        ("duplicated c2", {
            let mut t = coordinate.clone();
            t.budgets[1] = t.budgets[0].clone();
            t
        }),
        ("descending", {
            let mut t = coordinate.clone();
            t.budgets.reverse();
            t
        }),
    ] {
        tampered.layer = coordinate.layer;
        assert!(
            matches!(
                replay_err(&canonical, &cross, &tampered),
                ArtifactError::BudgetFamilyMalformed { .. }
            ),
            "[{label}] must be malformed, not partially replayed"
        );
    }
}

/// The fold depth is a schedule INPUT: it prices every source. An artifact that
/// declares a depth its regime does not use is describing a different physical
/// layer, and is rejected before anything is realized.
#[test]
fn replay_rejects_a_tampered_target_depth() {
    let (canonical, cross, mut coordinate) = small_coordinate();
    let real = coordinate.target_depth;
    coordinate.target_depth = real.wrapping_add(1);
    assert_eq!(
        replay_err(&canonical, &cross, &coordinate),
        ArtifactError::TargetDepthMismatch {
            regime: coordinate.regime,
            expected: real,
            found: real.wrapping_add(1),
        }
    );
}

// ── The corpus: generation, determinism, replay ──────────────────────────────

fn scratch_root(label: &str) -> PathBuf {
    let root = match std::env::var_os("GKR_COEFF_ARTIFACT_DIR") {
        Some(dir) => PathBuf::from(dir).join(label),
        None => std::env::temp_dir()
            .join(format!("gkr-coeff-artifact-{}-{label}", std::process::id())),
    };
    let _ = std::fs::remove_dir_all(&root);
    std::fs::create_dir_all(&root).expect("scratch root");
    root
}

/// One circuit's complete artifact, plus its reports.
///
/// The whole `(circuit, layer, regime)` chain is compiled before anything is
/// written, and a failure anywhere in it propagates as a panic — so the file, when
/// it appears, is a complete circuit. No checkpoint file and no atomic rename:
/// generation is a couple of seconds and a partial file is overwritten wholesale
/// by the next run.
fn compile_circuit(name: &str, progress: bool) -> (CircuitArtifact, Vec<CoordinateReport>) {
    let layers: Vec<(usize, DagLayer, CrossFields)> = layers_with_bwd_roots(name).collect();
    let compiled: Vec<_> = layers
        .par_iter()
        .flat_map_iter(|(index, layer, cross)| {
            [BwdRegime::R0, BwdRegime::Ext]
                .into_iter()
                .map(move |regime| (*index, layer, cross, regime))
        })
        .map(|(index, layer, cross, regime)| {
            let compiled = compile_coordinate(name, index, layer, cross, regime)
                .unwrap_or_else(|e| panic!("[{name} L{index} {regime:?}] chain: {e:?}"));
            if progress {
                println!("{}", ChainProgress::of(&compiled));
            }
            (compiled.artifact, compiled.report)
        })
        .collect();

    let mut coordinates = Vec::with_capacity(compiled.len());
    let mut reports = Vec::with_capacity(compiled.len());
    for (coordinate, report) in compiled {
        coordinates.push(coordinate);
        reports.push(report);
    }
    reports.sort_by(|a, b| a.sort_key().cmp(&b.sort_key()));
    (CircuitArtifact::new(name, coordinates), reports)
}

/// Generate the whole corpus into `root`, one file per circuit.
fn generate(root: &Path, progress: bool) -> (Vec<PathBuf>, Vec<CoordinateReport>) {
    let produced: Vec<(PathBuf, Vec<CoordinateReport>)> = FIXTURES
        .par_iter()
        .map(|name| {
            let (artifact, reports) = compile_circuit(name, progress);
            let path = write_circuit_artifact(root, &artifact).expect("write artifact");
            (path, reports)
        })
        .collect();

    let mut paths = Vec::with_capacity(produced.len());
    let mut reports = Vec::new();
    for (path, circuit_reports) in produced {
        paths.push(path);
        reports.extend(circuit_reports);
    }
    paths.sort();
    reports.sort_by(|a, b| a.sort_key().cmp(&b.sort_key()));
    (paths, reports)
}

/// Replay every coordinate of every written artifact, from DISK.
fn replay(paths: &[PathBuf]) -> Vec<CoordinateReport> {
    let mut reports: Vec<CoordinateReport> = paths
        .par_iter()
        .flat_map_iter(|path| {
            let artifact = read_circuit_artifact(path).expect("read artifact");
            let name = artifact.circuit.clone();
            let layers: Vec<(usize, DagLayer, CrossFields)> =
                layers_with_bwd_roots(&name).collect();
            artifact
                .coordinates
                .into_iter()
                .map(move |coordinate| {
                    let (_, canonical, cross) = layers
                        .iter()
                        .find(|(index, _, _)| *index == coordinate.layer)
                        .expect("the artifact names a layer of its own circuit");
                    let mut report = replay_coordinate(canonical, cross, &coordinate)
                        .unwrap_or_else(|e| {
                            panic!("[{name} L{} {:?}] replay: {e:?}", coordinate.layer, coordinate.regime)
                        });
                    report.circuit = name.clone();
                    report
                })
                .collect::<Vec<_>>()
        })
        .collect();
    reports.sort_by(|a, b| a.sort_key().cmp(&b.sort_key()));
    reports
}

fn read_all(paths: &[PathBuf]) -> Vec<(String, Vec<u8>)> {
    paths
        .iter()
        .map(|path| {
            let name = path.file_name().expect("named").to_string_lossy().into_owned();
            (name, std::fs::read(path).expect("read back"))
        })
        .collect()
}

fn print_summary(label: &str, summary: &CorpusSummary) {
    println!(
        "[{label}] {} coordinates / {} programs, max {} words ({} B) at {} c{}, moves {}, digest {:#018x}",
        summary.coordinates,
        summary.programs,
        summary.max_program_words,
        summary.max_program_bytes,
        summary.max_program_at,
        summary.max_program_cells,
        summary.total_moves,
        summary.corpus_program_digest,
    );
}

#[test]
fn bwd_coeff_artifacts_are_deterministic_and_replay_exactly() {
    // ── two complete, independent generations ────────────────────────────
    let root_a = scratch_root("run-a");
    let (paths_a, reports_a) = generate(&root_a, true);
    let root_b = scratch_root("run-b");
    let (paths_b, reports_b) = generate(&root_b, false);

    assert_eq!(paths_a.len(), in_scope::CIRCUITS, "one artifact per committed layout");
    assert_eq!(reports_a.len(), in_scope::COORDINATES);
    assert_eq!(
        reports_a.iter().map(|r| r.budgets.len()).sum::<usize>(),
        in_scope::REALIZED_PLACEMENTS,
        "c2..c16 for every coordinate"
    );

    let bytes_a = read_all(&paths_a);
    let bytes_b = read_all(&paths_b);
    assert_eq!(
        bytes_a.iter().map(|(n, _)| n.clone()).collect::<Vec<_>>(),
        bytes_b.iter().map(|(n, _)| n.clone()).collect::<Vec<_>>(),
    );
    for ((name, a), (_, b)) in bytes_a.iter().zip(&bytes_b) {
        assert_eq!(a.len(), b.len(), "[{name}] two runs disagree on artifact length");
        assert!(a == b, "[{name}] two runs produced different artifact bytes");
    }
    println!(
        "[determinism] {} artifacts, {} bytes, byte-identical across two full runs",
        bytes_a.len(),
        bytes_a.iter().map(|(_, b)| b.len()).sum::<usize>(),
    );

    // The schema stays minimal for every circuit, not just the sample above.
    for (name, bytes) in &bytes_a {
        assert_schema_is_minimal(bytes, name);
    }

    // ── replay reproduces every report, exactly ──────────────────────────
    let replayed = replay(&paths_a);
    assert_eq!(replayed.len(), reports_a.len());
    for (compiled, replayed) in reports_a.iter().zip(&replayed) {
        assert_eq!(compiled.sort_key(), replayed.sort_key());
        // Every field: the read floor and realized traffic, all three arithmetic
        // classes, shared-memory traffic, moves, program length AND the digest of
        // the canonical encoding itself. Reproducing the last one is what makes
        // "replay rebuilds placement, binding and encoding" a whole-corpus claim
        // rather than a description.
        assert_eq!(
            compiled.budgets, replayed.budgets,
            "[{}] replay did not reproduce the compiled programs",
            compiled.label()
        );
    }
    assert_eq!(reports_a, reports_b, "the two generations agree on every report");

    let summary = summarize(&reports_a);
    let replayed_summary = summarize(&replayed);
    print_summary("compile", &summary);
    print_summary("replay ", &replayed_summary);
    assert_eq!(summary, replayed_summary);
    assert_eq!(summary, summarize(&reports_b));

    // ── the pins Task 9 consumes ─────────────────────────────────────────
    assert_eq!(summary.max_program_words, in_scope::MAX_REALIZED_PROGRAM_WORDS);
    assert_eq!(summary.max_program_bytes, in_scope::MAX_REALIZED_PROGRAM_BYTES);
    assert_eq!(summary.max_program_at, in_scope::MAX_REALIZED_PROGRAM_COORDINATE);
    assert_eq!(summary.max_program_cells, in_scope::MAX_REALIZED_PROGRAM_CELLS);
    assert_eq!(summary.total_moves, in_scope::REALIZED_MOVES);

    // Every realized program fits the array Task 9 will size from the pin, and the
    // pin is the measurement rounded up by strictly less than one 16-byte quantum.
    for report in &reports_a {
        for program in &report.budgets {
            assert!(
                program.bytes <= in_scope::DESCRIPTOR_PROGRAM_BYTES,
                "[{} c{}] {} B exceeds the descriptor's program array",
                report.label(),
                program.cells,
                program.bytes,
            );
        }
    }
    println!(
        "[abi] Task 9 sizes the program array at {} u16 words = {} bytes \
         (measured max {} words = {} B, cap {} B)",
        in_scope::DESCRIPTOR_PROGRAM_WORDS,
        in_scope::DESCRIPTOR_PROGRAM_BYTES,
        in_scope::MAX_REALIZED_PROGRAM_WORDS,
        in_scope::MAX_REALIZED_PROGRAM_BYTES,
        KERNEL_ARGUMENT_CEILING_BYTES,
    );

    // ── every coordinate is present at every budget ──────────────────────
    //
    // §13 compiles an artifact for `(circuit, layer, regime, c2..c16)`. This is the
    // assertion that decides whether Task 5's strict `NoLegalRelocation` rule has
    // to be relaxed: it does not, because nothing is missing.
    let mut seen: BTreeSet<(String, usize, ArtifactRegime, u8)> = BTreeSet::new();
    for path in &paths_a {
        let artifact = read_circuit_artifact(path).expect("read");
        for coordinate in &artifact.coordinates {
            for budget in &coordinate.budgets {
                seen.insert((
                    artifact.circuit.clone(),
                    coordinate.layer,
                    coordinate.regime,
                    budget.cells,
                ));
            }
        }
    }
    assert_eq!(seen.len(), in_scope::REALIZED_PLACEMENTS, "an artifact at every budget");
}
