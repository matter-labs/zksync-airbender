//! Task-3 freeze gate: census the COMPLETE backward production corpus through
//! the coefficient lowering and pin the exact maxima the u16 ISA is sized from.
//!
//! This is the only census that can see the whole corpus. `gkr_eval_isa` reaches
//! the committed `cs/compiled_circuits/*_layout_gkr.json` layouts;
//! `blake2_with_compression` has no committed layout at all and exists only behind
//! `setups::circuits::get_blake2_with_compression_circuit_setup`, which lives on
//! this side of the dependency graph. The per-coordinate arithmetic is
//! deliberately NOT reimplemented here — every row comes from
//! `gkr_eval_isa::bwd::coeff::census_layer`, the same entry point
//! `bwd_coeff_corpus.rs` uses, so the two censuses cannot drift.
//!
//! # Scope (design §3.1)
//!
//! Twelve committed layouts are MANDATORY. `blake2_with_compression` is
//! CONDITIONAL: attempted with the same compiler and format, included only if
//! every required coordinate fits every frozen bound, and otherwise excluded as a
//! WHOLE circuit with its first failing coordinate recorded. There is no partial
//! eligibility and no second storage path.
//!
//! # The `blake2_with_compression` naming trap
//!
//! `get_blake2_with_compression_circuit_setup` and
//! `prepare_blake2_with_compression_proof_fixture` are not two views of one thing.
//! The former builds `Blake2sWithCompressionDelegationCircuit`, whose
//! `circuit_fn` is `define_blake2_with_extended_control_delegation_circuit` at
//! `DOMAIN_SIZE_LOG2 = 20` with caches on — byte-for-byte the call that generated
//! the committed `blake2_with_extended_control_layout_gkr.json`.
//! `conditional_blake2_setup_is_the_extended_control_circuit` proves that
//! equality on the artifact itself rather than asserting it from the source read.

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;
use std::sync::OnceLock;

use cs::definitions::{GKRAddress, VirtualSetupPoly};
use cs::gkr_compiler::dag_ir::{
    bwd_roots, lower_dag, validate, BwdRegime, DagLayer, ReadPlace, VirtualSetupKind,
};
use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;
use gkr_eval_isa::bwd::coeff::limits::{in_scope, with_conditional_blake2};
use gkr_eval_isa::bwd::coeff::stats::{csv_line, CSV_HEADER};
use gkr_eval_isa::bwd::coeff::{
    census_csv, census_layer, continuation_opcode, lower_coeff_layer, r0_opcode, sink_read_place,
    CoeffCensus, CoeffCensusFailure, CoeffCensusRow, CoefficientRecipeId,
    KERNEL_ARGUMENT_CEILING_BYTES, MAX_COEFFICIENT_ENCODINGS, MAX_SOURCE_WINDOWS,
};
use gkr_eval_isa::bwd::distill::distill;
use gkr_eval_isa::bwd::source::OriginLeaf;
use gkr_eval_isa::fwd::compile::build_cross_layer_field_map;
use rayon::prelude::*;

/// The MANDATORY production corpus, identical to `gkr_eval_isa`'s pinned
/// `common::FIXTURES` (same names, same order) so every row of this census is
/// directly comparable with `bwd_coeff_committed_layout_census`.
const MANDATORY_LAYOUTS: &[&str] = &[
    "add_sub_lui_auipc_mop_layout_gkr.json",
    "bigint_with_extended_control_layout_gkr.json",
    "blake2_g_function_layout_gkr.json",
    "blake2_with_extended_control_layout_gkr.json",
    "inits_and_teardowns_preprocessed_layout_gkr.json",
    "jump_branch_slt_layout_gkr.json",
    "keccak_special5_layout_gkr.json",
    "mem_subword_only_layout_gkr.json",
    "mem_word_only_layout_gkr.json",
    "shift_binop_layout_gkr.json",
    "unsigned_mul_div_layout_gkr.json",
    "unified_reduced_machine_layout_gkr.json",
];

/// A SECOND committed layout of a circuit already in [`MANDATORY_LAYOUTS`]:
/// `inits_and_teardowns` commits both a preprocessed and a plain variant, and the
/// incumbent flat audit (`tests.rs`) walks the plain one while the whole
/// `gkr_eval_isa` corpus pins the preprocessed one. Censused so neither variant is
/// a blind spot, but it sizes nothing — it is the same circuit.
const VARIANT_LAYOUTS: &[&str] = &["inits_and_teardowns_layout_gkr.json"];

/// Row label of the conditional circuit (§3.1). Not a file: it has no committed
/// layout.
const CONDITIONAL_CIRCUIT: &str = "blake2_with_compression_setup";

// ── Corpus construction ──────────────────────────────────────────────────────

fn workspace_path(relative: &str) -> PathBuf {
    // Crate lives at gpu/circuit_prover/, so two "..".
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join(relative)
}

fn load_layout(name: &str) -> GKRCircuitArtifact<BabyBearField> {
    let relative = format!("cs/compiled_circuits/{name}");
    let path = workspace_path(&relative);
    let file =
        std::fs::File::open(&path).unwrap_or_else(|e| panic!("opening {}: {}", path.display(), e));
    serde_json::from_reader(std::io::BufReader::new(file))
        .unwrap_or_else(|e| panic!("parsing {}: {}", path.display(), e))
}

/// The conditional circuit, built through the PRODUCTION setup constructor.
///
/// Cached because the constructor also builds the `GKRSetup` over `1 << 20` rows;
/// every test in this module shares the one construction.
fn conditional_setup() -> &'static GKRCircuitArtifact<BabyBearField> {
    static SETUP: OnceLock<GKRCircuitArtifact<BabyBearField>> = OnceLock::new();
    SETUP.get_or_init(|| {
        let worker = worker::Worker::new();
        crate::upstream::get_blake2_with_compression_circuit_setup(true, &worker).compiled_circuit
    })
}

/// Every backward-bearing layer of one artifact, as
/// `(layer_index, canonical_layer, cross_layer_field_map)`.
fn bearing_layers(
    circuit: &str,
    artifact: &GKRCircuitArtifact<BabyBearField>,
) -> Vec<(
    usize,
    DagLayer,
    std::collections::HashMap<
        cs::gkr_compiler::dag_ir::ReadPlace,
        cs::gkr_compiler::dag_ir::FieldKind,
    >,
)> {
    let dag = lower_dag(artifact).unwrap_or_else(|e| panic!("[{circuit}] lower_dag: {e}"));
    validate(&dag).unwrap_or_else(|e| panic!("[{circuit}] validate: {e}"));
    let cross = build_cross_layer_field_map(&dag);
    dag.layers
        .iter()
        .enumerate()
        .filter(|(_, layer)| !bwd_roots(layer).is_empty())
        .map(|(li, layer)| (li, layer.clone(), cross.clone()))
        .collect()
}

fn census_artifact(
    circuit: &str,
    artifact: &GKRCircuitArtifact<BabyBearField>,
) -> (Vec<CoeffCensusRow>, Vec<CoeffCensusFailure>) {
    let layers = bearing_layers(circuit, artifact);
    let (rows, failures): (Vec<_>, Vec<_>) = layers
        .par_iter()
        .map(|(li, layer, cross)| census_layer(circuit, *li, layer, cross))
        .unzip();
    (
        rows.into_iter().flatten().collect(),
        failures.into_iter().flatten().collect(),
    )
}

/// The complete corpus: mandatory layouts, the variant layout, and the
/// conditional circuit. Rows are lexically sorted, so two runs are byte-identical.
struct Corpus {
    mandatory: Vec<CoeffCensusRow>,
    variant: Vec<CoeffCensusRow>,
    conditional: Vec<CoeffCensusRow>,
    /// Coordinates the lowering REJECTED, as data. Empty on this corpus, which is
    /// why the §3.1 exclude-and-continue branch is unreachable today — see the
    /// comment on the assertion in `bwd_coeff_complete_corpus_census`. Kept because
    /// §3.1 requires the first failing coordinate to be reportable.
    failures: Vec<CoeffCensusFailure>,
}

impl Corpus {
    /// Mandatory + conditional, which is what the diagnostic maxima cover.
    fn diagnostic_rows(&self) -> Vec<&CoeffCensusRow> {
        self.mandatory
            .iter()
            .chain(self.conditional.iter())
            .collect()
    }

    /// Every censused row, in lexical order — the durable CSV.
    fn all_rows(&self) -> Vec<CoeffCensusRow> {
        let mut rows: Vec<CoeffCensusRow> = self
            .mandatory
            .iter()
            .chain(self.variant.iter())
            .chain(self.conditional.iter())
            .cloned()
            .collect();
        rows.sort_by(|a, b| a.sort_key().cmp(&b.sort_key()));
        rows
    }
}

fn corpus() -> &'static Corpus {
    static CORPUS: OnceLock<Corpus> = OnceLock::new();
    CORPUS.get_or_init(|| {
        let mut failures = Vec::new();

        let mut census_all = |names: &[&'static str]| -> Vec<CoeffCensusRow> {
            let mut collected: Vec<(Vec<CoeffCensusRow>, Vec<CoeffCensusFailure>)> = names
                .par_iter()
                .map(|name| {
                    let artifact = load_layout(name);
                    census_artifact(name, &artifact)
                })
                .collect();
            let mut rows = Vec::new();
            for (r, f) in collected.drain(..) {
                rows.extend(r);
                failures.extend(f);
            }
            rows.sort_by(|a, b| a.sort_key().cmp(&b.sort_key()));
            rows
        };

        let mandatory = census_all(MANDATORY_LAYOUTS);
        let variant = census_all(VARIANT_LAYOUTS);

        let (mut conditional, conditional_failures) =
            census_artifact(CONDITIONAL_CIRCUIT, conditional_setup());
        conditional.sort_by(|a, b| a.sort_key().cmp(&b.sort_key()));
        failures.extend(conditional_failures);

        Corpus {
            mandatory,
            variant,
            conditional,
            failures,
        }
    })
}

fn maxima<'a>(rows: impl IntoIterator<Item = &'a CoeffCensusRow>) -> CoeffCensus {
    let mut max = CoeffCensus::default();
    for row in rows {
        max.merge_max(&row.census);
    }
    max
}

// ── Gate 1: the complete-corpus census ───────────────────────────────────────

/// Freeze the term categories, the header width, and every corpus maximum the
/// u16 ISA is sized from.
#[test]
fn bwd_coeff_complete_corpus_census() {
    let corpus = corpus();

    // A lowering rejection anywhere is a finding, not a layer to skip.
    //
    // As of this census there are ZERO rejections across all 138 coordinates, and
    // this assertion is unconditional — so the §3.1 "exclude the conditional
    // circuit and continue with the rest of the corpus" branch is currently
    // UNREACHABLE, for the conditional circuit as much as for a mandatory one.
    // `census_layer` still returns rejections as `CoeffCensusFailure` DATA rather
    // than panicking, and `Corpus::failures` still carries them per coordinate,
    // because §3.1 mandates that recording path: the day a conditional coordinate
    // does fail, the first failing coordinate has to be reportable rather than a
    // stack trace. Do not collapse the data path into a panic just because nothing
    // reaches it today.
    assert_eq!(
        corpus.failures,
        Vec::new(),
        "every coordinate of the complete corpus must lower"
    );

    // ── durable report ───────────────────────────────────────────────────
    let rows = corpus.all_rows();
    let csv = census_csv(&rows);
    let out_dir = workspace_path("target/gkr");
    std::fs::create_dir_all(&out_dir).unwrap_or_else(|e| panic!("mkdir {out_dir:?}: {e}"));
    let out = out_dir.join("bwd_coeff_corpus_census.csv");
    std::fs::write(&out, &csv).unwrap_or_else(|e| panic!("write {out:?}: {e}"));
    log::info!(
        "[coeff-census] wrote {} rows to {}",
        rows.len(),
        out.display()
    );
    println!("{CSV_HEADER}");
    for row in &rows {
        println!("{}", csv_line(row));
    }
    println!("[coeff-census] durable report: {}", out.display());

    // ── corpus shape ─────────────────────────────────────────────────────
    assert_eq!(MANDATORY_LAYOUTS.len(), in_scope::CIRCUITS);
    assert_eq!(corpus.mandatory.len(), in_scope::COORDINATES);
    assert_eq!(corpus.mandatory.len() / 2, in_scope::LAYERS);
    assert_eq!(
        corpus.mandatory.len() + corpus.conditional.len(),
        with_conditional_blake2::COORDINATES
    );
    assert_eq!(
        (corpus.mandatory.len() + corpus.conditional.len()) / 2,
        with_conditional_blake2::LAYERS
    );

    // ── in-scope maxima: the ONLY numbers Tasks 4-9 size from ─────────────
    let in_scope_max = maxima(corpus.mandatory.iter());
    println!("[coeff-census] in-scope maxima: {in_scope_max:#?}");
    assert_eq!(
        in_scope_max.coefficient_recipes,
        in_scope::MAX_COEFFICIENT_RECIPES
    );
    assert_eq!(in_scope_max.sources, in_scope::MAX_SOURCES);
    assert_eq!(in_scope_max.projections, in_scope::MAX_PROJECTIONS);
    assert_eq!(in_scope_max.terms, in_scope::MAX_TERMS);
    assert_eq!(
        in_scope_max.max_expansion_factor,
        in_scope::MAX_EXPANSION_FACTOR
    );
    assert_eq!(
        in_scope_max.max_fragment_atoms,
        in_scope::MAX_FRAGMENT_ATOMS
    );
    assert_eq!(
        in_scope_max.source_windows,
        in_scope::MAX_SOURCE_WINDOWS_USED
    );
    assert_eq!(
        in_scope_max.lower_bound_program_bytes,
        in_scope::MAX_LOWER_BOUND_PROGRAM_BYTES
    );
    assert_eq!(
        in_scope_max.upper_bound_program_bytes,
        in_scope::MAX_UPPER_BOUND_PROGRAM_BYTES
    );
    assert_eq!(
        in_scope_max.cont_standalone_product,
        in_scope::MAX_CONTINUATION_STANDALONE_PRODUCTS
    );

    // ── diagnostic maxima, kept STRICTLY separate ────────────────────────
    let diagnostic_max = maxima(corpus.diagnostic_rows());
    println!("[coeff-census] diagnostic maxima (incl. conditional): {diagnostic_max:#?}");
    assert_eq!(
        diagnostic_max.coefficient_recipes,
        with_conditional_blake2::MAX_COEFFICIENT_RECIPES
    );
    assert_eq!(diagnostic_max.sources, with_conditional_blake2::MAX_SOURCES);
    assert_eq!(
        diagnostic_max.projections,
        with_conditional_blake2::MAX_PROJECTIONS
    );
    assert_eq!(diagnostic_max.terms, with_conditional_blake2::MAX_TERMS);
    assert_eq!(
        diagnostic_max.max_expansion_factor,
        with_conditional_blake2::MAX_EXPANSION_FACTOR
    );
    assert_eq!(
        diagnostic_max.source_windows,
        with_conditional_blake2::MAX_SOURCE_WINDOWS_USED
    );
    assert_eq!(
        diagnostic_max.lower_bound_program_bytes,
        with_conditional_blake2::MAX_LOWER_BOUND_PROGRAM_BYTES
    );
    assert_eq!(
        diagnostic_max.upper_bound_program_bytes,
        with_conditional_blake2::MAX_UPPER_BOUND_PROGRAM_BYTES
    );

    // The second committed `inits_and_teardowns` layout must not exceed the
    // in-scope maxima; if it ever does, the two variants are not the same circuit
    // and the corpus definition needs revisiting.
    let variant_max = maxima(corpus.variant.iter());
    println!("[coeff-census] variant-layout maxima: {variant_max:#?}");
    for (label, variant, pinned) in [
        (
            "coefficient_recipes",
            variant_max.coefficient_recipes,
            in_scope::MAX_COEFFICIENT_RECIPES,
        ),
        ("sources", variant_max.sources, in_scope::MAX_SOURCES),
        ("terms", variant_max.terms, in_scope::MAX_TERMS),
        (
            "source_windows",
            variant_max.source_windows,
            in_scope::MAX_SOURCE_WINDOWS_USED,
        ),
        (
            "lower_bound_program_bytes",
            variant_max.lower_bound_program_bytes,
            in_scope::MAX_LOWER_BOUND_PROGRAM_BYTES,
        ),
    ] {
        assert!(
            variant <= pinned,
            "the plain inits_and_teardowns layout exceeds the in-scope {label} maximum \
             ({variant} > {pinned})"
        );
    }

    // ── encoding limits, asserted SEPARATELY from the measurements ────────
    assert!(
        diagnostic_max.coefficient_recipes + CoefficientRecipeId::RESERVED as usize
            <= MAX_COEFFICIENT_ENCODINGS,
        "deduplicated_bank_recipe_count + 2 must fit thirteen bits"
    );
    assert!(
        diagnostic_max.source_windows <= MAX_SOURCE_WINDOWS,
        "the maximum final source-window count must be at most 64"
    );

    // ── the terminal bound ───────────────────────────────────────────────
    let mandatory_overflow: Vec<_> = corpus
        .mandatory
        .iter()
        .filter(|row| !row.census.lower_bound_fits())
        .map(|row| (row.sort_key(), row.census.lower_bound_program_bytes))
        .collect();
    assert_eq!(
        mandatory_overflow,
        Vec::new(),
        "a mandatory coordinate whose MINIMUM stream overflows {KERNEL_ARGUMENT_CEILING_BYTES} B \
         cannot be repaired by any later codec — the gate fails here"
    );
    let conditional_overflow: Vec<_> = corpus
        .conditional
        .iter()
        .filter(|row| !row.census.lower_bound_fits())
        .map(|row| (row.sort_key(), row.census.lower_bound_program_bytes))
        .collect();
    println!(
        "[coeff-census] conditional hard-bound failures: {:?}",
        conditional_overflow
    );
    assert_eq!(
        conditional_overflow.len(),
        with_conditional_blake2::CONDITIONAL_HARD_BOUND_FAILURES,
        "the conditional circuit is either wholly excluded by a recorded hard failure or \
         remains one conditional circuit pending Task 8"
    );
    // §3.1 admits no PARTIAL eligibility: the conditional scope is one whole
    // circuit, either fully retained or fully excluded. With zero hard failures and
    // zero lowering rejections it is fully retained, pending Task 8's real-encoding
    // decision.
    let conditional_circuits: BTreeSet<&str> = corpus
        .conditional
        .iter()
        .map(|row| row.circuit.as_str())
        .collect();
    assert_eq!(
        conditional_circuits,
        BTreeSet::from([CONDITIONAL_CIRCUIT]),
        "the conditional scope must be exactly one circuit"
    );
    assert!(
        corpus
            .conditional
            .iter()
            .all(|row| row.census.lower_bound_fits() && row.census.upper_bound_fits()),
        "all-or-nothing: with no hard failure every conditional coordinate is retained"
    );

    let inconclusive: Vec<_> = corpus
        .diagnostic_rows()
        .into_iter()
        .filter(|row| row.census.inconclusive())
        .map(|row| row.sort_key())
        .collect();
    println!(
        "[coeff-census] program-stream verdict: proven-fit={} inconclusive={:?} \
         (worst-case headroom for the rest of the descriptor: {} B)",
        corpus.diagnostic_rows().len() - inconclusive.len(),
        inconclusive,
        KERNEL_ARGUMENT_CEILING_BYTES - diagnostic_max.upper_bound_program_bytes,
    );
    assert_eq!(
        inconclusive.len(),
        with_conditional_blake2::INCONCLUSIVE_COORDINATES
    );

    // ── frozen opcode tables ─────────────────────────────────────────────
    let mut live: BTreeMap<(&'static str, &'static str), usize> = BTreeMap::new();
    for row in corpus.diagnostic_rows() {
        let regime = row.regime_label();
        for category in &row.live_categories {
            let opcode = if row.regime == BwdRegime::R0 {
                r0_opcode(*category)
            } else {
                continuation_opcode(*category)
            };
            assert!(
                opcode.is_some(),
                "{:?} emitted {} which the {regime} opcode table does not encode",
                row.sort_key(),
                category.label()
            );
            *live.entry((regime, category.label())).or_default() += 1;
        }
    }
    println!("[coeff-census] live categories: {live:?}");
    let live_ext: BTreeSet<&str> = live
        .keys()
        .filter(|(r, _)| *r == "Ext")
        .map(|(_, c)| *c)
        .collect();
    assert_eq!(
        live_ext,
        BTreeSet::from(["C0LinearE4", "DualProductE4"]),
        "continuation emits only C0Linear and native DualProduct across the COMPLETE corpus, \
         so continuation opcodes 3..7 stay invalid and nothing is pre-allocated"
    );
    let live_r0: BTreeSet<&str> = live
        .keys()
        .filter(|(r, _)| *r == "R0")
        .map(|(_, c)| *c)
        .collect();
    assert_eq!(
        live_r0,
        BTreeSet::from([
            "C0LinearBF",
            "C0LinearE4",
            "C2ProductBF_BF",
            "C2ProductBF_E4",
            "C2ProductE4_E4"
        ]),
        "all five R0 arithmetic categories are live; with MoveBF/MoveE4 that is seven opcodes"
    );
}

// ── Gate 2: the conditional circuit's identity ───────────────────────────────

/// `get_blake2_with_compression_circuit_setup` returns the SAME GKR circuit as
/// the committed `blake2_with_extended_control_layout_gkr.json`.
///
/// Proved on the artifact, not inferred from the source: same layer count, same
/// per-layer gate/cache-relation counts, same trace length, and — the decisive
/// one — the same canonical JSON. A later task that assumes
/// `prepare_blake2_with_compression_proof_fixture` gates a DISTINCT circuit is
/// working from a false premise, and this is where that shows up.
#[test]
fn bwd_coeff_complete_corpus_census_conditional_blake2_identity() {
    let conditional = conditional_setup();
    let committed = load_layout("blake2_with_extended_control_layout_gkr.json");

    println!(
        "[coeff-census] conditional: layers={} trace_len={} | committed: layers={} trace_len={}",
        conditional.layers.len(),
        conditional.trace_len,
        committed.layers.len(),
        committed.trace_len,
    );
    assert_eq!(conditional.layers.len(), committed.layers.len());
    assert_eq!(conditional.trace_len, committed.trace_len);
    for (li, (a, b)) in conditional
        .layers
        .iter()
        .zip(committed.layers.iter())
        .enumerate()
    {
        assert_eq!(
            (
                a.layer,
                a.gates.len(),
                a.gates_with_external_connections.len(),
                a.cached_relations.len()
            ),
            (
                b.layer,
                b.gates.len(),
                b.gates_with_external_connections.len(),
                b.cached_relations.len()
            ),
            "layer {li} shape differs"
        );
    }
    let a = serde_json::to_string(conditional).expect("serialize conditional");
    let b = serde_json::to_string(&committed).expect("serialize committed");
    assert_eq!(
        a.len(),
        b.len(),
        "conditional and committed artifacts differ in serialized length"
    );
    assert!(
        a == b,
        "conditional and committed artifacts differ in content at equal length"
    );

    // Consequently the two censuses agree row-for-row.
    let corpus = corpus();
    let committed_rows: Vec<_> = corpus
        .mandatory
        .iter()
        .filter(|row| row.circuit == "blake2_with_extended_control_layout_gkr.json")
        .collect();
    assert_eq!(committed_rows.len(), corpus.conditional.len());
    for (conditional_row, committed_row) in corpus.conditional.iter().zip(committed_rows) {
        assert_eq!(
            (conditional_row.layer, conditional_row.regime),
            (committed_row.layer, committed_row.regime)
        );
        assert_eq!(
            conditional_row.census, committed_row.census,
            "layer {} {:?}: the conditional circuit must census identically to the committed one",
            conditional_row.layer, conditional_row.regime
        );
    }
}

// ── Gate 3: the incumbent comparison ─────────────────────────────────────────

/// The incumbent's static round-0 term projection for one layer.
#[derive(Debug, Clone, PartialEq, Eq)]
struct IncumbentR0 {
    c0_bf: usize,
    c0_ext: usize,
    c1_bf_bf: usize,
    c1_bf_e4: usize,
    c1_e4_e4: usize,
    c1_linear: usize,
    /// Distinct non-placeholder kernel INPUT addresses — what
    /// `gather_e_addresses` would carry.
    gather: BTreeSet<GKRAddress>,
}

impl IncumbentR0 {
    fn c0(&self) -> usize {
        self.c0_bf + self.c0_ext
    }

    fn products(&self) -> usize {
        self.c1_bf_bf + self.c1_bf_e4 + self.c1_e4_e4
    }

    fn gather_sources(&self) -> usize {
        self.gather.len()
    }

    /// Static field multiplications: one per linear term's coefficient, two per
    /// product term (coefficient times the two factors, fused). Identical formula
    /// on both sides, so the comparison is on the term categories themselves.
    fn muls(&self) -> usize {
        self.c0() + 2 * self.products()
    }
}

fn new_muls(census: &CoeffCensus) -> usize {
    census.r0_c0_linear() + 2 * census.r0_c2_product()
}

/// Build the production main-layer blueprints for one layer and project the
/// incumbent round-0 counts. Mirrors the four existing walkers in `tests.rs`.
fn incumbent_r0(
    artifact: &GKRCircuitArtifact<BabyBearField>,
    layer_idx: usize,
) -> Option<IncumbentR0> {
    use crate::prover::gkr::backward::{
        build_main_layer_kernel_blueprints_static, canonical_inits_and_teardowns_top_bits,
    };
    use crate::prover::gkr::storage_layout::{FieldType, GpuGKRStorageLayout};
    use field::baby_bear::ext4::BabyBearExt4;
    use prover::definitions::GKRExternalChallenges;
    use prover::gkr::high_bits_offset_for_inits_and_teardowns;

    let layer = &artifact.layers[layer_idx];
    if super::tests::layer_has_unsupported_relations(layer) {
        return None;
    }
    let layout = GpuGKRStorageLayout::from_artifact(artifact);
    let inits_top_bits =
        canonical_inits_and_teardowns_top_bits(artifact.memory_layout.teardown_sets.len());
    let inits_high_bits_shift = if artifact.memory_layout.teardown_sets.is_empty() {
        0
    } else {
        high_bits_offset_for_inits_and_teardowns::<2>(artifact.trace_len)
    };
    let external_challenges = GKRExternalChallenges::<BabyBearField, BabyBearExt4>::default();
    let is_base_field_at_layer = |addr: &cs::definitions::GKRAddress| -> bool {
        layout
            .layers
            .get(layer_idx)
            .and_then(|l| l.lookup(addr))
            .map(|(_, ft, _)| ft == FieldType::Base)
            .unwrap_or(false)
    };
    let blueprints = build_main_layer_kernel_blueprints_static::<BabyBearExt4>(
        layer,
        layer_idx,
        &is_base_field_at_layer,
        &external_challenges,
        &inits_top_bits,
        inits_high_bits_shift,
        artifact.memory_layout.total_width,
        artifact.witness_layout.total_width,
    );
    let counts = super::project_layer_flat_round0_term_counts(&blueprints);
    Some(IncumbentR0 {
        c0_bf: counts.c0_bf as usize,
        c0_ext: counts.c0_ext as usize,
        c1_bf_bf: counts.c1_bf_bf as usize,
        c1_bf_e4: counts.c1_bf_e4 as usize,
        c1_e4_e4: counts.c1_e4_e4 as usize,
        c1_linear: counts.c1_linear as usize,
        gather: gather_addresses(&blueprints),
    })
}

/// The distinct non-placeholder input addresses of one layer's blueprints — the
/// SET behind `project_layer_main_gather_num_addresses`'s count, so a source-count
/// delta can be diffed structurally instead of guessed at from the numbers.
fn gather_addresses<E>(
    blueprints: &[crate::prover::gkr::backward::kernels::GpuGKRMainLayerKernelBlueprint<E>],
) -> BTreeSet<GKRAddress> {
    let placeholder = GKRAddress::placeholder();
    let mut seen = BTreeSet::new();
    for bp in blueprints {
        for addr in bp
            .inputs
            .inputs_in_base
            .iter()
            .chain(bp.inputs.inputs_in_extension.iter())
        {
            if *addr != placeholder {
                seen.insert(*addr);
            }
        }
    }
    seen
}

/// `OriginLeaf` -> `GKRAddress`. The DAG's `ReadPlace` was lowered FROM a
/// `GKRAddress` one-to-one (`dag_ir::lower::map_virtual_setup` and the read-place
/// constructors), so this is the exact inverse and the two source vocabularies are
/// directly comparable.
fn address_of(origin: &OriginLeaf) -> GKRAddress {
    match origin {
        OriginLeaf::Read(ReadPlace::BaseLayerMemory { column }) => {
            GKRAddress::BaseLayerMemory(*column)
        }
        OriginLeaf::Read(ReadPlace::BaseLayerWitness { column }) => {
            GKRAddress::BaseLayerWitness(*column)
        }
        OriginLeaf::Read(ReadPlace::Setup { column }) => GKRAddress::Setup(*column),
        OriginLeaf::Read(ReadPlace::Scratch { slot }) => GKRAddress::ScratchSpace(*slot),
        OriginLeaf::Read(ReadPlace::LayerOutput { layer, offset }) => GKRAddress::InnerLayer {
            layer: *layer,
            offset: *offset,
        },
        OriginLeaf::Read(ReadPlace::CacheOutput { layer, offset }) => GKRAddress::Cached {
            layer: *layer,
            offset: *offset,
        },
        OriginLeaf::VirtualSetup { kind } => GKRAddress::VirtualSetup(match kind {
            VirtualSetupKind::RangeCheck16Bits => VirtualSetupPoly::RangeCheck16Bits,
            VirtualSetupKind::RangeCheckTimestamp => VirtualSetupPoly::RangeCheckTimestamp,
            VirtualSetupKind::InitsAndTeardownsLow => VirtualSetupPoly::InitsAndTeardownsLow,
            VirtualSetupKind::InitsAndTeardownsHigh => VirtualSetupPoly::InitsAndTeardownsHigh,
        }),
    }
}

/// How one layer's new source sets relate to the incumbent's gather set.
///
/// The incumbent gathers every kernel INPUT of the layer regardless of which round
/// consumes it, so it is the full cone-leaf vocabulary. The new lowering splits
/// that vocabulary by regime, which is where both delta directions come from.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
struct SourceSetDelta {
    /// `Ext`-regime sources not in the incumbent's gather set, by family. Expected
    /// EMPTY: continuation reads exactly the cone leaves.
    ext_extra: BTreeMap<&'static str, usize>,
    /// Incumbent gather addresses the `Ext` regime never reads, by family. Expected
    /// EMPTY for the same reason.
    ext_missing: BTreeMap<&'static str, usize>,
    /// R0 sources the incumbent's gather set does not contain, by family.
    r0_extra: BTreeMap<&'static str, usize>,
    /// Of `r0_extra`, those that ARE a materialized sink of a claim-bearing root of
    /// this layer — introduced by the §5.2 `acc_c0` output shortcut, which the
    /// incumbent reads too but does not route through `gather_e_addresses` (that
    /// list carries kernel INPUTS only).
    r0_extra_from_output_shortcut: usize,
    /// Incumbent gather addresses R0 does not read, by family.
    r0_missing: BTreeMap<&'static str, usize>,
    /// Of `r0_missing`, those the SAME layer reads in the `Ext` regime — i.e. leaves
    /// that occur only in degree-0/degree-1 fragment monomials, which R0 drops by
    /// design (§5.2: `X^0` is the output shortcut and `acc_c1` does not exist).
    /// They are not dropped from the program, only from R0's read set.
    r0_missing_read_in_continuation: usize,
}

fn family(address: &GKRAddress) -> &'static str {
    match address {
        GKRAddress::BaseLayerWitness(_) => "BaseLayerWitness",
        GKRAddress::BaseLayerMemory(_) => "BaseLayerMemory",
        GKRAddress::InnerLayer { .. } => "InnerLayer",
        GKRAddress::Setup(_) => "Setup",
        GKRAddress::VirtualSetup(_) => "VirtualSetup",
        GKRAddress::ScratchSpace(_) => "ScratchSpace",
        GKRAddress::Cached { .. } => "Cached",
    }
}

/// Compare the new R0 lowering against the incumbent flat audit on every layer
/// the incumbent can project, and pin the delta structure.
///
/// The incumbent is a CROSS-REFERENCE, not an oracle. Its static projection is
/// count-granular (it never materializes per-term source identities), so the
/// comparison is on the category multiset plus the distinct-source and static
/// multiplication counts — the finest granularity the incumbent exposes.
///
/// Two deltas are STRUCTURAL and expected:
///
///   * the incumbent counts one `c0` term per kernel OUTPUT COLUMN, while the new
///     lowering emits one `C0Linear` per claim-bearing materialized ROOT (§5.2).
///     Both read the materialized output column — neither recomputes the cone —
///     so this is a batching-granularity difference, not a cost regression; and
///   * the new lowering MERGES bodies that share a source pair and DROPS bodies
///     whose coefficient cancels, which the incumbent's per-gate emission cannot
///     do. Every product delta must therefore be `new <= incumbent`.
///
/// A delta in the other direction on products, or any `C0Linear` that reads a
/// source other than a materialized output, would be a real regression.
#[test]
fn bwd_coeff_complete_corpus_census_incumbent_parity() {
    let corpus = corpus();
    let mut compared = 0usize;
    let mut unsupported = 0usize;
    let mut new_exceeds_incumbent: Vec<String> = Vec::new();
    let mut deltas: Vec<String> = Vec::new();
    let mut total_new_muls = 0usize;
    let mut total_incumbent_muls = 0usize;
    let mut unexplained_sources: Vec<String> = Vec::new();
    let mut missing_sources: Vec<String> = Vec::new();
    let mut extra_by_family: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut r0_omitted_but_continued = 0usize;

    // Only the MANDATORY layouts: the conditional circuit is a byte-identical
    // copy of one of them (gate 2) and the variant layout is a second layout of
    // another, so including either would double-count deltas.
    for name in MANDATORY_LAYOUTS {
        let artifact = load_layout(name);
        let layers = bearing_layers(name, &artifact);
        let rows: Vec<&CoeffCensusRow> = corpus
            .mandatory
            .iter()
            .filter(|row| row.circuit == **name && row.regime == BwdRegime::R0)
            .collect();
        assert_eq!(rows.len(), layers.len());
        for (row, (li, canonical, cross)) in rows.iter().zip(layers.iter()) {
            assert_eq!(row.layer, *li);
            let Some(incumbent) = incumbent_r0(&artifact, row.layer) else {
                unsupported += 1;
                println!(
                    "[coeff-census] {name} L{} R0: incumbent-unsupported layer, censused anyway \
                     (terms={} sources={} windows={})",
                    row.layer, row.census.terms, row.census.sources, row.census.source_windows
                );
                continue;
            };
            compared += 1;
            let c = &row.census;
            total_new_muls += new_muls(c);
            total_incumbent_muls += incumbent.muls();

            assert_eq!(
                incumbent.c1_linear, 0,
                "{name} L{}: the corrected incumbent emits no round-0 materialize linear form",
                row.layer
            );

            // Structural source diff (see `SourceSetDelta`).
            let delta = source_set_delta(canonical, cross, &incumbent.gather);
            for (fam, n) in &delta.r0_extra {
                *extra_by_family.entry(fam).or_default() += n;
            }
            // The continuation source vocabulary must be EXACTLY the incumbent's
            // gather set: same addresses, no additions, no omissions.
            if !delta.ext_extra.is_empty() || !delta.ext_missing.is_empty() {
                missing_sources.push(format!(
                    "{name} L{} Ext: continuation source set diverges from the incumbent gather \
                     set (extra={:?} missing={:?})",
                    row.layer, delta.ext_extra, delta.ext_missing
                ));
            }
            // Every R0 addition must be a materialized root output.
            let r0_extra_total: usize = delta.r0_extra.values().sum();
            if r0_extra_total != delta.r0_extra_from_output_shortcut {
                unexplained_sources.push(format!(
                    "{name} L{} R0: {} extra sources, only {} explained by the acc_c0 output \
                     shortcut: {:?}",
                    row.layer, r0_extra_total, delta.r0_extra_from_output_shortcut, delta.r0_extra
                ));
            }
            // Every R0 omission must still be read in continuation rounds.
            let r0_missing_total: usize = delta.r0_missing.values().sum();
            if r0_missing_total != delta.r0_missing_read_in_continuation {
                missing_sources.push(format!(
                    "{name} L{} R0: {} omitted sources, only {} of them read in continuation: {:?}",
                    row.layer,
                    r0_missing_total,
                    delta.r0_missing_read_in_continuation,
                    delta.r0_missing
                ));
            }
            r0_omitted_but_continued += delta.r0_missing_read_in_continuation;

            let pairs = [
                ("c0", c.r0_c0_linear(), incumbent.c0()),
                ("bf_bf", c.r0_c2_bf_bf, incumbent.c1_bf_bf),
                ("bf_e4", c.r0_c2_bf_e4, incumbent.c1_bf_e4),
                ("e4_e4", c.r0_c2_e4_e4, incumbent.c1_e4_e4),
                ("products", c.r0_c2_product(), incumbent.products()),
                ("sources", c.sources, incumbent.gather_sources()),
                ("muls", new_muls(c), incumbent.muls()),
            ];
            let line: Vec<String> = pairs
                .iter()
                .filter(|(_, new, inc)| new != inc)
                .map(|(label, new, inc)| {
                    format!(
                        "{label}: new={new} incumbent={inc} delta={}",
                        *new as i64 - *inc as i64
                    )
                })
                .collect();
            if !line.is_empty() {
                deltas.push(format!("{name} L{} R0 | {}", row.layer, line.join(", ")));
            }
            // Merging and zero-elimination can only REMOVE product terms.
            if c.r0_c2_product() > incumbent.products() {
                new_exceeds_incumbent.push(format!(
                    "{name} L{} R0: products new={} > incumbent={}",
                    row.layer,
                    c.r0_c2_product(),
                    incumbent.products()
                ));
            }
            // Every R0 `C0Linear` must read a materialized root's output column,
            // one per materialized root — the §5.2 shortcut, never a cone.
            assert_eq!(
                c.r0_c0_linear(),
                c.materialized_roots,
                "{name} L{}: R0 acc_c0 must be exactly one output read per materialized root",
                row.layer
            );
            assert_eq!(c.sinks_inner, c.materialized_roots);
        }
    }

    println!("[coeff-census] incumbent comparison: {compared} layers compared, {unsupported} incumbent-unsupported");
    println!(
        "[coeff-census] static R0 multiplications: new={total_new_muls} incumbent={total_incumbent_muls} \
         delta={}",
        total_new_muls as i64 - total_incumbent_muls as i64
    );
    println!(
        "[coeff-census] R0 extra-source families across the 49 layers: {extra_by_family:?} \
         (all materialized root outputs); R0 sources omitted vs the incumbent gather list but \
         read in continuation: {r0_omitted_but_continued}"
    );
    println!("[coeff-census] per-layer deltas ({}):", deltas.len());
    for line in &deltas {
        println!("[coeff-census]   {line}");
    }

    assert_eq!(
        new_exceeds_incumbent,
        Vec::<String>::new(),
        "the new lowering may only ever emit FEWER product terms than the incumbent — merging \
         and zero-elimination cannot add terms"
    );
    // Every source-count delta is accounted for, in both directions: the new
    // lowering never reads an address the incumbent does not, and every address it
    // reads beyond the incumbent's gather list is a materialized ROOT OUTPUT the
    // §5.2 `acc_c0` shortcut reads instead of recomputing the cone. The incumbent
    // reads those columns too; they simply are not routed through
    // `gather_e_addresses`, which carries kernel INPUTS only.
    assert_eq!(
        unexplained_sources,
        Vec::<String>::new(),
        "an extra source that is not a materialized root output would mean the new lowering \
         touches data the incumbent does not"
    );
    assert_eq!(
        missing_sources,
        Vec::<String>::new(),
        "the continuation source vocabulary must equal the incumbent's gather set exactly, and \
         every address R0 omits must still be read in continuation rounds — otherwise an input \
         was genuinely dropped"
    );
    assert_eq!(compared, 49, "the incumbent-comparable layer count drifted");
    assert_eq!(
        unsupported, 8,
        "the incumbent-unsupported layer count drifted"
    );
    assert!(
        total_new_muls <= total_incumbent_muls,
        "the new R0 lowering must not cost more static multiplications than the incumbent"
    );
}

/// Diff one layer's new per-regime source sets against the incumbent's gather set
/// and classify every difference.
fn source_set_delta(
    canonical: &DagLayer,
    cross: &std::collections::HashMap<ReadPlace, cs::gkr_compiler::dag_ir::FieldKind>,
    gather: &BTreeSet<GKRAddress>,
) -> SourceSetDelta {
    let sources_of = |regime| -> BTreeSet<GKRAddress> {
        let distilled = distill(canonical, regime, cross, None);
        lower_coeff_layer(canonical, &distilled)
            .expect("lowering")
            .sources
            .iter()
            .map(|source| address_of(&source.origin))
            .collect()
    };
    let r0 = sources_of(BwdRegime::R0);
    let ext = sources_of(BwdRegime::Ext);

    // The output columns the R0 `acc_c0` shortcut reads.
    let shortcut: BTreeSet<GKRAddress> = canonical
        .roots
        .iter()
        .filter(|root| root.claim.is_some())
        .filter_map(|root| root.materialize.as_ref())
        .filter_map(|sink| sink_read_place(&sink.kind))
        .map(|place| address_of(&OriginLeaf::Read(place)))
        .collect();

    let mut delta = SourceSetDelta::default();
    for address in ext.difference(gather) {
        *delta.ext_extra.entry(family(address)).or_default() += 1;
    }
    for address in gather.difference(&ext) {
        *delta.ext_missing.entry(family(address)).or_default() += 1;
    }
    for address in r0.difference(gather) {
        *delta.r0_extra.entry(family(address)).or_default() += 1;
        if shortcut.contains(address) {
            delta.r0_extra_from_output_shortcut += 1;
        }
    }
    for address in gather.difference(&r0) {
        *delta.r0_missing.entry(family(address)).or_default() += 1;
        if ext.contains(address) {
            delta.r0_missing_read_in_continuation += 1;
        }
    }
    delta
}
