//! Task 4 gates for the segmented lean VM: the per-layer lean coordinate
//! artifacts, the program-word census the descriptor is sized from, and the
//! `NEG_ONE` census the `fnma` adoption decision reads (design §4, §8).
//!
//! Three properties, and the first is the one the other two rest on:
//!
//!   1. **The corpus is deterministic ACROSS PROCESSES.** The lean pipeline is
//!      `lower_coeff_layer -> order_terms -> encode_program -> bind_lean_sources
//!      -> validate_program`, and every container in it is a `Vec` or a `BTreeMap`
//!      in a fixed order. This file regenerates the whole corpus in a re-exec'd
//!      child of the test binary and asserts BYTE equality against the in-process
//!      build, which two in-process runs cannot prove: a fresh process has fresh
//!      `HashMap` seeds and fresh allocator addresses, so an accidental dependence
//!      on either shows up here and nowhere else.
//!   2. **The program-word census pins the descriptor.** The lean wire is fixed at
//!      [`LEAN_WORDS_PER_TERM`] words per term, so a coordinate's program length is
//!      `4 * terms` exactly and the corpus maximum is `4 * max terms`. That
//!      identity is asserted, not assumed, and the measured maximum is what
//!      `LEAN_MAX_REALIZED_PROGRAM_WORDS` states.
//!   3. **`NEG_ONE` is live.** Signs live in coefficients (design §8), so the
//!      `fnma` (`z - x*y`) adoption decision needs the per-category frequency of
//!      the `NEG_ONE` recipe. It is censused here and pinned exactly.
//!
//! Scope is the same 12 committed layouts / 57 backward-bearing layers / 114
//! coordinates every other coefficient gate uses.

mod common;

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use common::{CrossFields, FIXTURES, layers_with_bwd_roots};
use cs::gkr_compiler::dag_ir::{BwdRegime, DagLayer, FieldKind, ReadPlace};
use gkr_eval_isa::bwd::coeff::lean::LEAN_WORDS_PER_TERM;
use gkr_eval_isa::bwd::coeff::lean_artifact::{
    LeanCircuitArtifact, LeanCoordinateArtifact, compile_lean_coordinate, lean_artifact_bytes,
    read_lean_circuit_artifact, write_lean_circuit_artifact,
};
use gkr_eval_isa::bwd::coeff::limits::{
    DESCRIPTOR_ALIGNMENT_WORDS, KERNEL_ARGUMENT_CEILING_BYTES, LEAN_DESCRIPTOR_PROGRAM_BYTES,
    LEAN_DESCRIPTOR_PROGRAM_WORDS, LEAN_MAX_REALIZED_PROGRAM_WORDS, TermCategory, in_scope,
};
use gkr_eval_isa::bwd::coeff::stats::neg_one_census;
use gkr_eval_isa::bwd::coeff::{
    ArtifactRegime, CoeffLayer, CoeffSource, CoeffTerm, CoefficientRecipeId, ProjectionId,
    SourceId, TermId, lower_coeff_layer,
};
use gkr_eval_isa::bwd::distill::distill;
use gkr_eval_isa::bwd::source::OriginLeaf;
use rayon::prelude::*;

// ── Relations between the pinned constants ───────────────────────────────────
//
// Const-vs-const, so they hold at COMPILE time. The runtime assertions below are
// the ones with a MEASUREMENT on one side.

/// The descriptor array is the measurement rounded up by strictly less than one
/// 16-byte quantum, and it fits the by-value kernel-argument cap.
const _: () = assert!(
    LEAN_DESCRIPTOR_PROGRAM_WORDS - LEAN_MAX_REALIZED_PROGRAM_WORDS < DESCRIPTOR_ALIGNMENT_WORDS
);
const _: () = assert!(LEAN_DESCRIPTOR_PROGRAM_BYTES < KERNEL_ARGUMENT_CEILING_BYTES);

// ── The corpus ───────────────────────────────────────────────────────────────

/// One circuit's complete lean artifact.
///
/// The whole `(layer, regime)` chain is compiled before anything is written, so
/// the file, when it appears, is a complete circuit.
fn compile_circuit(name: &str) -> LeanCircuitArtifact {
    let layers: Vec<(usize, DagLayer, CrossFields)> = layers_with_bwd_roots(name).collect();
    let coordinates: Vec<LeanCoordinateArtifact> = layers
        .par_iter()
        .flat_map_iter(|(index, layer, cross)| {
            [BwdRegime::R0, BwdRegime::Ext]
                .into_iter()
                .map(move |regime| (*index, layer, cross, regime))
        })
        .map(|(index, layer, cross, regime)| {
            compile_lean_coordinate(name, index, layer, cross, regime)
                .unwrap_or_else(|e| panic!("[{name} L{index} {regime:?}] lean chain: {e:?}"))
        })
        .collect();
    LeanCircuitArtifact::new(name, coordinates)
}

/// Generate the whole corpus into `root`, one file per circuit. Returns the
/// written paths, sorted.
fn generate(root: &Path) -> Vec<PathBuf> {
    std::fs::create_dir_all(root).expect("scratch root");
    let mut paths: Vec<PathBuf> = FIXTURES
        .par_iter()
        .map(|name| {
            let artifact = compile_circuit(name);
            write_lean_circuit_artifact(root, &artifact).expect("write lean artifact")
        })
        .collect();
    paths.sort();
    paths
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

fn scratch_root(label: &str) -> PathBuf {
    let root =
        std::env::temp_dir().join(format!("gkr-lean-artifact-{}-{label}", std::process::id()));
    let _ = std::fs::remove_dir_all(&root);
    std::fs::create_dir_all(&root).expect("scratch root");
    root
}

/// Every lean coordinate of the 12 committed layouts, built once and shared: the
/// whole point of the census gates is that ONE corpus backs every number.
fn corpus() -> &'static Vec<(String, LeanCoordinateArtifact)> {
    static CORPUS: OnceLock<Vec<(String, LeanCoordinateArtifact)>> = OnceLock::new();
    CORPUS.get_or_init(|| {
        let mut rows: Vec<(String, LeanCoordinateArtifact)> = FIXTURES
            .par_iter()
            .flat_map_iter(|name| {
                compile_circuit(name)
                    .coordinates
                    .into_iter()
                    .map(move |coordinate| ((*name).to_string(), coordinate))
            })
            .collect();
        rows.sort_by(|a, b| (&a.0, a.1.layer, a.1.regime).cmp(&(&b.0, b.1.layer, b.1.regime)));
        rows
    })
}

/// Re-lower one coordinate's `CoeffLayer` — the artifact stores decisions, not
/// the IR, so the term-level censuses re-derive it.
fn lowered(name: &str, layer_index: usize, regime: BwdRegime) -> CoeffLayer {
    let (_, canonical, cross) = layers_with_bwd_roots(name)
        .find(|(index, _, _)| *index == layer_index)
        .expect("the corpus names a layer of its own circuit");
    let distilled = distill(&canonical, regime, &cross, None);
    lower_coeff_layer(&canonical, &distilled).expect("every corpus layer lowers")
}

// ── (a) determinism across processes ─────────────────────────────────────────

/// Env guard: when set, the test body is the CHILD and generates the corpus into
/// the named directory instead of comparing anything.
const CHILD_ROOT: &str = "GKR_LEAN_ARTIFACT_CHILD_ROOT";

#[test]
fn bwd_lean_artifacts_are_byte_identical_across_processes() {
    if let Some(root) = std::env::var_os(CHILD_ROOT) {
        let paths = generate(Path::new(&root));
        assert_eq!(paths.len(), in_scope::CIRCUITS, "the child wrote a partial corpus");
        return;
    }

    let in_process = generate(&scratch_root("in-process"));
    let child_root = scratch_root("subprocess");
    let status = std::process::Command::new(std::env::current_exe().unwrap())
        .arg("bwd_lean_artifacts_are_byte_identical_across_processes")
        .arg("--exact")
        .env(CHILD_ROOT, &child_root)
        .status()
        .expect("re-exec the test binary");
    assert!(status.success(), "the child generation failed");

    let mut subprocess: Vec<PathBuf> =
        std::fs::read_dir(&child_root).expect("child root").map(|e| e.unwrap().path()).collect();
    subprocess.sort();

    let a = read_all(&in_process);
    let b = read_all(&subprocess);
    assert_eq!(a.len(), in_scope::CIRCUITS, "one artifact per committed layout");
    assert_eq!(
        a.iter().map(|(n, _)| n.clone()).collect::<Vec<_>>(),
        b.iter().map(|(n, _)| n.clone()).collect::<Vec<_>>(),
        "the two generations disagree on the file set"
    );
    for ((name, x), (_, y)) in a.iter().zip(&b) {
        assert_eq!(x.len(), y.len(), "[{name}] the two processes disagree on artifact length");
        assert!(x == y, "[{name}] the two processes produced different artifact bytes");
    }
    println!(
        "[determinism] {} artifacts, {} bytes, byte-identical in-process vs subprocess",
        a.len(),
        a.iter().map(|(_, bytes)| bytes.len()).sum::<usize>(),
    );

    // The written bytes are the canonical serialization, and they read back into
    // exactly the artifact they were written from.
    for path in &in_process {
        let artifact = read_lean_circuit_artifact(path).expect("read back");
        assert_eq!(
            lean_artifact_bytes(&artifact),
            std::fs::read(path).expect("read bytes"),
            "[{}] round trip is not byte-stable",
            artifact.circuit,
        );
    }
}

// ── (b) the program-word census ──────────────────────────────────────────────

#[test]
fn bwd_lean_program_word_census_sizes_the_descriptor() {
    let rows = corpus();
    assert_eq!(rows.len(), in_scope::COORDINATES, "57 layers x 2 regimes");

    let mut max_words = 0usize;
    let mut max_terms = 0usize;
    let mut max_at = String::new();
    for (circuit, coordinate) in rows {
        let words = coordinate.program.words.len();
        let terms = coordinate.program.term_count;
        // The fixed-width wire, per coordinate: no coordinate can be off-identity.
        assert_eq!(
            words,
            terms * LEAN_WORDS_PER_TERM,
            "[{circuit} L{} {}] the lean wire is fixed width",
            coordinate.layer,
            coordinate.regime.label(),
        );
        assert_eq!(coordinate.order.len(), terms, "the committed order covers every term");
        if words > max_words {
            max_words = words;
            max_at = format!("{circuit} L{} {}", coordinate.layer, coordinate.regime.label());
        }
        max_terms = max_terms.max(terms);
    }

    println!(
        "[lean census] max {max_words} words ({} B) at {max_at}; max {max_terms} terms",
        2 * max_words,
    );

    // The corpus maximum IS `4 * max terms` — the identity the fixed-width wire
    // makes structural, measured rather than assumed.
    assert_eq!(max_words, LEAN_WORDS_PER_TERM * max_terms);
    assert_eq!(max_terms, in_scope::MAX_TERMS, "the lean corpus is the censused corpus");
    // The pin the descriptor is sized from.
    assert_eq!(max_words, LEAN_MAX_REALIZED_PROGRAM_WORDS);
    assert_eq!(LEAN_DESCRIPTOR_PROGRAM_BYTES, 2 * LEAN_DESCRIPTOR_PROGRAM_WORDS);
    assert!(
        LEAN_MAX_REALIZED_PROGRAM_WORDS <= LEAN_WORDS_PER_TERM * in_scope::MAX_TERMS,
        "the measurement must sit inside the format bound"
    );
    for (circuit, coordinate) in rows {
        assert!(
            coordinate.program.bytes() <= LEAN_DESCRIPTOR_PROGRAM_BYTES,
            "[{circuit} L{}] {} B exceeds the descriptor's program array",
            coordinate.layer,
            coordinate.program.bytes(),
        );
    }
}

/// The binding is dense over the source table and inside the frozen window
/// geometry, corpus-wide — the property Task 5's per-source record array rests on.
#[test]
fn bwd_lean_bindings_cover_every_source_within_the_window_geometry() {
    let rows = corpus();
    let mut max_windows = 0usize;
    for (circuit, coordinate) in rows {
        let label = format!("{circuit} L{} {}", coordinate.layer, coordinate.regime.label());
        let binding = &coordinate.binding;
        let sources = lowered(circuit, coordinate.layer, coordinate.regime.regime()).sources.len();
        assert_eq!(binding.source_slots.len(), sources, "[{label}] one slot per source");
        for slot in &binding.source_slots {
            assert!((slot.window as usize) < binding.windows.len(), "[{label}] window in range");
            let window = &binding.windows[slot.window as usize];
            let absolute = window.first_column + slot.column as usize;
            assert!(
                window.columns.iter().any(|c| c.column == absolute),
                "[{label}] a slot must address a referenced column",
            );
        }
        max_windows = max_windows.max(binding.windows.len());
    }
    println!("[lean binding] max {max_windows} windows over the corpus");
    assert_eq!(
        max_windows,
        in_scope::MAX_SOURCE_WINDOWS_USED,
        "the lean binder partitions the same source table the census measured",
    );
}

// ── (c) the NEG_ONE census ───────────────────────────────────────────────────

/// The `fnma` adoption census, and its verdict.
///
/// `fnma` (`z - x*y`) fuses a SUBTRACT-shaped accumulate, which is what a term
/// whose coefficient is the reserved `NEG_ONE` literal performs. This gate measures
/// how many such terms the corpus has, and the answer is **ZERO**.
///
/// The `+1` counterpart is what makes that zero interpretable: 149 corpus terms DO
/// carry the reserved `ONE` literal, so the reserved-literal path is live and
/// exercised — the corpus simply never produces a bare `-1`. Every other
/// coefficient carries at least one challenge factor (a batching `beta` power on an
/// output root, `ConstraintAggregation` on a constraint root) and is therefore a
/// banked recipe, whose sign is inside the recipe rather than on the term. There is
/// consequently no `fnma` opportunity at the coefficient level, and these counts
/// are the evidence — pinned exactly, so a lowering change that starts emitting
/// bare `-1` shows up as a signal rather than as noise.
#[test]
fn bwd_lean_neg_one_census_is_zero_on_the_corpus() {
    let mut per_category: BTreeMap<TermCategory, u64> = BTreeMap::new();
    let mut total_terms = 0u64;
    let mut neg_one_terms = 0u64;
    // The two counterparts that make the zero interpretable: a corpus where the
    // reserved `+1` were live but `-1` were not is a different fact from one where
    // NO term carries a reserved literal at all.
    let mut one_terms = 0u64;
    let mut banked_terms = 0u64;

    for (circuit, coordinate) in corpus() {
        let layer = lowered(circuit, coordinate.layer, coordinate.regime.regime());
        let census = neg_one_census(&layer);
        assert_eq!(census.total_terms, layer.terms.len() as u64, "the denominator is every term");
        total_terms += census.total_terms;
        for (category, count) in &census.per_category {
            assert_ne!(*count, 0, "a censused category carries at least one NEG_ONE term");
            *per_category.entry(*category).or_default() += count;
            neg_one_terms += count;
        }
        for term in &layer.terms {
            match term.coefficient() {
                CoefficientRecipeId::ONE => one_terms += 1,
                CoefficientRecipeId::NEG_ONE => {}
                _ => banked_terms += 1,
            }
        }
    }

    println!(
        "[NEG_ONE census] {neg_one_terms}/{total_terms} terms ({:.2}%); per category \
         {per_category:?}; reserved +1 {one_terms}, banked {banked_terms}",
        100.0 * neg_one_terms as f64 / total_terms as f64,
    );

    assert_eq!(total_terms, 15_860, "R0 + Ext terms over the 114 coordinates");
    assert_eq!(neg_one_terms + one_terms + banked_terms, total_terms, "every term is accounted");
    assert_eq!(per_category, BTreeMap::new(), "no corpus term carries a bare -1");
    assert_eq!(neg_one_terms, 0, "the fnma opportunity at the coefficient level is empty");
    assert_eq!(
        one_terms, 149,
        "the reserved-literal path IS live, which is what makes the -1 zero a measurement",
    );
    assert_eq!(
        banked_terms, 15_711,
        "every other corpus coefficient carries a challenge factor, so it is banked",
    );
}

/// The census itself, on a layer that DOES carry negative coefficients.
///
/// The corpus has none, so the counting rule cannot be exercised there — and an
/// uncounted rule is an unmeasured one. This builds the case by hand: `NEG_ONE`
/// terms in two categories plus a banked and a `+1` term that must not be counted.
#[test]
fn neg_one_census_counts_negative_coefficients_per_category() {
    let source = |field| CoeffSource {
        origin: OriginLeaf::Read(ReadPlace::BaseLayerWitness { column: 0 }),
        field,
    };
    let banked = CoefficientRecipeId::from_bank_index(0);
    let layer = CoeffLayer {
        regime: BwdRegime::Ext,
        c_init: None,
        coefficients: Vec::new(),
        sources: vec![source(FieldKind::Ext), source(FieldKind::Base)],
        terms: vec![
            CoeffTerm::C0Linear {
                id: TermId(0),
                coefficient: CoefficientRecipeId::NEG_ONE,
                value: ProjectionId::endpoint0(SourceId(0)),
                field: FieldKind::Ext,
            },
            CoeffTerm::DualProduct {
                id: TermId(1),
                coefficient: CoefficientRecipeId::NEG_ONE,
                lhs: SourceId(0),
                rhs: SourceId(1),
            },
            CoeffTerm::DualProduct {
                id: TermId(2),
                coefficient: CoefficientRecipeId::NEG_ONE,
                lhs: SourceId(1),
                rhs: SourceId(1),
            },
            CoeffTerm::C0Linear {
                id: TermId(3),
                coefficient: CoefficientRecipeId::ONE,
                value: ProjectionId::endpoint0(SourceId(0)),
                field: FieldKind::Ext,
            },
            CoeffTerm::C0Linear {
                id: TermId(4),
                coefficient: banked,
                value: ProjectionId::endpoint0(SourceId(1)),
                field: FieldKind::Base,
            },
        ],
    };

    let census = neg_one_census(&layer);
    assert_eq!(
        census.per_category,
        vec![(TermCategory::C0LinearE4, 1), (TermCategory::DualProductE4, 2)],
        "ascending by category, and only the NEG_ONE terms",
    );
    assert_eq!(census.total_terms, 5, "the denominator is EVERY term, not the counted ones");
    assert_eq!(census.per_category.iter().map(|(_, n)| n).sum::<u64>(), 3);
}

/// A layer with no `NEG_ONE` term still reports its denominator, so a zero
/// numerator is distinguishable from a layer nobody censused.
#[test]
fn neg_one_census_of_a_layer_without_negative_coefficients_reports_its_denominator() {
    let layer = lowered("shift_binop_layout_gkr.json", 0, BwdRegime::R0);
    let census = neg_one_census(&layer);
    assert!(census.per_category.is_empty());
    assert_eq!(census.total_terms, layer.terms.len() as u64);
    assert!(census.total_terms > 0, "the layer is not empty");
}

/// The regime label the artifact serializes is the regime it was compiled at.
#[test]
fn bwd_lean_coordinates_are_labelled_by_regime() {
    let r0 = corpus().iter().filter(|(_, c)| c.regime == ArtifactRegime::R0).count();
    let ext = corpus().iter().filter(|(_, c)| c.regime == ArtifactRegime::Ext).count();
    assert_eq!(r0, in_scope::LAYERS);
    assert_eq!(ext, in_scope::LAYERS);
    for (_, coordinate) in corpus() {
        let expected = match coordinate.regime {
            ArtifactRegime::R0 => 0,
            ArtifactRegime::Ext => 3,
        };
        assert_eq!(coordinate.target_depth, expected, "the depth a regime's program is bound at");
    }
}
