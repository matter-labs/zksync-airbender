//! Stage-3 target tests (plan Task 3, Step 1): the schedule-driven
//! `compile_circuit` loads + validates a committed schedule and produces a
//! value-correct forward program for every layer (spec §6.1 cone-value gate).
//!
//! Tests/ binary: lib items via `gkr_eval_isa::`, shared fixture helpers via
//! `mod common`.

mod common;
use common::{load_dag_sched, resolvers, sample_rows, schedule_path, SyntheticResolvers};

use cs::gkr_compiler::dag_ir::CircuitSchedule;
use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;
use gkr_eval_isa::fwd::compile::decisions::SiteDecisions;
use gkr_eval_isa::fwd::compile::{
    build_cross_layer_field_map, compile_circuit, compile_layer, layer_needs_compile,
};
use gkr_eval_isa::fwd::context::CompiledLayer;
use gkr_eval_isa::fwd::error::CompileError;
use gkr_eval_isa::fwd::interp::interpret_layer_row;

/// Production driver refuses an invalid schedule (spec §2.1): truncating one
/// layer's stored sites must fail validate_circuit_schedule via compile_circuit.
#[test]
fn compile_circuit_rejects_stale_sites() {
    // COMMITTED_CORPUS[0]: fixture name INCLUDES `.json`, stem does not (common::load_fixture
    // vs common::schedule_path contracts — tests/common/mod.rs:105-115).
    let (dag, mut sched, artifact) =
        load_committed("add_sub_lui_auipc_mop_layout_gkr.json", "add_sub_lui_auipc_mop");
    let li = sched
        .layers
        .iter()
        .position(|ls| !ls.sites.is_empty())
        .expect("some layer has sites");
    sched.layers[li].sites.pop();
    match compile_circuit(&dag, &sched, &artifact) {
        Err(CompileError::InvalidSchedule(msg)) => {
            assert!(msg.contains("site"), "validator message should name the site domain: {msg}")
        }
        other => panic!("expected InvalidSchedule, got {other:?}"),
    }
}

/// The promoted loader round-trips a committed artifact and errors loudly on a
/// missing path (no produce-on-missing fallback, spec §2.3).
#[test]
fn load_committed_schedule_roundtrip_and_missing() {
    let ok = gkr_eval_isa::fwd::compile::load_committed_schedule(&schedule_path(
        "add_sub_lui_auipc_mop",
    ))
    .expect("committed add_sub schedule loads");
    assert!(!ok.layers.is_empty());
    let err = gkr_eval_isa::fwd::compile::load_committed_schedule(std::path::Path::new(
        "/nonexistent/nope_schedule_b16_gkr.json",
    ));
    assert!(matches!(err, Err(CompileError::InvalidSchedule(_))));
}

// ── Task 8: committed corpus + Decisions compile of a committed schedule ──────────

/// (fixture file, committed schedule stem) for all 11 cache-layout circuits. The
/// schedule stem differs from the fixture stem only for `inits_and_teardowns`
/// (fixture: `..._preprocessed_layout_gkr.json`, schedule: `inits_and_teardowns`).
const COMMITTED_CORPUS: &[(&str, &str)] = &[
    ("add_sub_lui_auipc_mop_layout_gkr.json", "add_sub_lui_auipc_mop"),
    ("bigint_with_extended_control_layout_gkr.json", "bigint_with_extended_control"),
    ("blake2_g_function_layout_gkr.json", "blake2_g_function"),
    ("blake2_with_extended_control_layout_gkr.json", "blake2_with_extended_control"),
    ("inits_and_teardowns_preprocessed_layout_gkr.json", "inits_and_teardowns"),
    ("jump_branch_slt_layout_gkr.json", "jump_branch_slt"),
    ("keccak_special5_layout_gkr.json", "keccak_special5"),
    ("mem_subword_only_layout_gkr.json", "mem_subword_only"),
    ("mem_word_only_layout_gkr.json", "mem_word_only"),
    ("shift_binop_layout_gkr.json", "shift_binop"),
    ("unsigned_mul_div_layout_gkr.json", "unsigned_mul_div"),
];

// `compile_committed_decisions` (the hand-rolled per-layer Decisions-compile helper)
// is DELETED (Task 3, T3-flip): GATE-V/GATE-D/GATE-F now drive the production
// `compile_circuit` directly — it performs the identical stored-`sites` Decisions
// compile per layer (plus the `validate_circuit_schedule` preflight `load_committed`
// used to run separately). Consumers key off `layer_needs_compile` themselves to
// find the same skipped-layer set `compile_circuit` skips (its `CompiledCircuit.layers`
// is index-aligned with `dag.layers`; skipped layers are empty `CompiledLayer`s).

/// **Load-bearing** (Task 8b): the demand-driven eviction tracker in `lower.rs`
/// must never UNDERESTIMATE relative to `plan_placement`'s independent liveness
/// model — i.e. "the tracker admitted this" must imply "`plan_placement` fits it
/// at the same budget". `compile_layer` (`mod.rs`) already chains the
/// two: it runs the tracker-driven emitter FIRST, then calls `plan_placement` on
/// the resulting instruction stream at the SAME `budget`, and only returns `Ok`
/// if BOTH succeed — so any tracker/placement disagreement surfaces as an `Err`
/// here (never a silently-wrong compile), which this test turns into a loud,
/// dedicated failure across the ENTIRE committed corpus rather than relying on
/// the incidental panics inside GATE-V/GATE-D's own compiles.
#[test]
fn tracker_admission_implies_placement_feasible_on_committed_corpus() {
    let mut layers_checked = 0usize;
    for (name, stem) in COMMITTED_CORPUS {
        let (dag, sched, artifact) = load_committed(name, stem);
        let cross = build_cross_layer_field_map(&dag);
        for (li, (layer, ls)) in dag.layers.iter().zip(&sched.layers).enumerate() {
            if !layer_needs_compile(ls.units.is_empty(), layer) {
                continue;
            }
            let decisions = SiteDecisions::new(ls.sites.iter().copied());
            let compiled = compile_layer(
                layer,
                &artifact.layers[li],
                &artifact.scratch_space_mapping,
                &cross,
                ls,
                sched.budget,
                Some(&decisions),
            );
            assert!(
                compiled.is_ok(),
                "{name} L{li}: demand-driven tracker admitted a schedule that \
                 plan_placement's independent model rejects at budget {}: {:?}",
                sched.budget,
                compiled.err()
            );
            assert!(
                compiled.unwrap().stats.max_live_cells <= sched.budget,
                "{name} L{li}: placement peak exceeds the budget the tracker admitted at"
            );
            layers_checked += 1;
        }
    }
    // Pinned to the exact corpus layer count (11 fixtures / 53 scheduled
    // layers) rather than a vacuous `> 0`, per Task 8b review: a `> 0` bound
    // can't catch a silent skip if a future corpus/fixture change starts
    // dropping layers (e.g. a `layer_needs_compile` regression that skips
    // more than the genuinely-skippable ones).
    assert_eq!(
        layers_checked, 53,
        "expected exactly 53 scheduled layers across the 11-fixture corpus; \
         a different count means layers are being silently skipped or added \
         (layer_needs_compile drift, corpus edit, etc.) — update this pin \
         deliberately if the corpus itself changed"
    );
    eprintln!(
        "[tracker-placement-agreement] {layers_checked} layers across {} fixtures: OK",
        COMMITTED_CORPUS.len()
    );
}

// ── Task 1 (event-local materialization-policy cache-produce-vs-fuse variant) ──
//
// DELETED (Task 4, schema v2): this module hand-built `StepPlan`/`ReplayEvent`/
// `DemandKind` schedules and drove the (since-deleted) event-local materialize
// variant, both deleted along with the v1 event-replay schema
// (`.superpowers/sdd/task-4-brief.md`). The enum that once carried this — plus its
// legacy-recompute/decisions cases — is itself gone (Task 2's public collapse):
// `compile_layer`'s `decisions: Option<&SiteDecisions>` now carries the
// `None`/`Some` distinction.

// ── Task 8: emitter coverage for preserved nested same-op shapes ───────────────────
//
// The DAG simplify pipeline now PRESERVES fan-out>=2 same-op nested nodes (an
// `Add` directly inside an `Add`, a `Mul` directly inside a `Mul`) instead of
// unconditionally flattening them — a shape the emitter's uncached (`decisions: None`)
// lowering (`compile_add_virtual`/`compile_mul_virtual`, `lower.rs:431-465`)
// never saw under the old flatten. These tests hand-build a synthetic layer with
// each shape (shared nested node consumed by two roots — one same-op, one
// cross-op) and pin that `compile_layer` under `decisions: None`
// still produces value-correct rows for both roots.
mod task8_nested_shapes {
    use std::collections::{BTreeMap, HashMap};

    use cs::gkr_compiler::dag_ir::{
        eval_layer_root, BatchingOrder, ClaimInfo, DagLayer, Expr, ExprId, FieldKind,
        LayerSchedule, ReadPlace, Root, RootGroup, RootId, RootOrigin, RootSlot, SinkInfo,
        SinkKind, SourceId, SourceInfo, SourceKind,
    };
    use cs::gkr_compiler::{
        GKRLayerDescription, GateArtifacts, NoFieldGKRRelation, NoFieldMaxQuadraticGKRRelation,
        NoFieldStructuredExpression,
    };

    use gkr_eval_isa::fwd::compile::compile_layer;
    use gkr_eval_isa::fwd::interp::interpret_layer_row;

    use crate::common::{resolvers, SyntheticResolvers};

    fn witness(col: usize) -> SourceInfo {
        SourceInfo { kind: SourceKind::Read { place: ReadPlace::BaseLayerWitness { column: col } } }
    }

    /// An atom (Output+claim) root over `expr`, materialized to `Export { slot }`.
    fn atom_root(expr: ExprId, slot: usize) -> Root {
        Root {
            expr,
            materialize: Some(SinkInfo { kind: SinkKind::Export { slot }, field: FieldKind::Base }),
            claim: Some(ClaimInfo {
                origin: RootOrigin {
                    group: RootGroup::Gates,
                    relation_index: 0,
                    slot: RootSlot::Output(slot),
                },
            }),
        }
    }

    /// An artifact layer whose single gate classifies to `ForwardAction::Compute`;
    /// every atom root here uses `relation_index = 0`, so one gate serves both roots.
    fn compute_artifact_layer() -> GKRLayerDescription {
        let relation = NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint {
            input: NoFieldMaxQuadraticGKRRelation {
                quadratic_terms: Box::new([]),
                linear_terms: Box::new([]),
                constant: 0,
            },
            expression: NoFieldStructuredExpression::Constant(0),
        };
        GKRLayerDescription {
            layer: 0,
            gates: vec![GateArtifacts { output_layer: 0, enforced_relation: relation }],
            gates_with_external_connections: vec![],
            cached_relations: BTreeMap::new(),
            intermediate_layer_width: None,
        }
    }

    /// A trivial no-op schedule: no `sites` genome (schema v2 has no persisted
    /// per-step residency at all) — only the atom order drives root-compile order
    /// under the uncached (`decisions: None`) path, which lazily recomputes from
    /// the DAG shape. Phase 1: the flat `order` is carried as one `RelationUnit`'s
    /// `atom_roots` (these tests' roots all share `(Gates, 0)`, so this matches the
    /// canonical single-unit decomposition), giving `atom_order() == order`.
    fn trivial_schedule(order: Vec<RootId>) -> LayerSchedule {
        use cs::gkr_compiler::dag_ir::RelationUnit;
        let units = if order.is_empty() {
            vec![]
        } else {
            vec![RelationUnit {
                group: RootGroup::Gates,
                relation_index: 0,
                atom_roots: order,
                cache_roots: vec![],
            }]
        };
        LayerSchedule { units, sites: vec![], predicted_traffic: 0, floor: 0 }
    }

    /// Compile `layer` under `decisions: None` and assert every exposed root's
    /// interpreted value matches `eval_layer_root` on every row in `rows`.
    fn assert_compiles_and_matches_oracle(layer: &DagLayer, sched: &LayerSchedule, rows: &[usize]) {
        let art = compute_artifact_layer();
        let cross: HashMap<ReadPlace, FieldKind> = HashMap::new();
        let compiled = compile_layer(layer, &art, &BTreeMap::new(), &cross, sched, 16, None)
            .expect("compile_layer");
        let sr = SyntheticResolvers;
        let mut checks = 0usize;
        for &row in rows {
            let outs = interpret_layer_row(&compiled, layer, &resolvers(&sr), row).unwrap();
            for (rid, _) in &compiled.root_outputs {
                let got = outs.by_root[rid];
                let want = eval_layer_root(layer, *rid, row, &resolvers(&sr));
                assert_eq!(got, want, "nested-shape {rid:?} row {row}");
                checks += 1;
            }
        }
        assert!(checks > 0, "vacuous");
    }

    // ── (a) Add-inside-Add: shared `xy = Add(x,y)` consumed by `Add(xy,z)`
    //    (same-op nesting) AND `Mul(xy,xy)` (cross-op). ─────────────────────────
    #[test]
    fn shared_nested_add_in_add_and_mul() {
        let layer = DagLayer {
            sources: vec![witness(0), witness(1), witness(2)],
            exprs: vec![
                Expr::Source(SourceId(0)),             // 0 = x
                Expr::Source(SourceId(1)),             // 1 = y
                Expr::Source(SourceId(2)),              // 2 = z
                Expr::Add(vec![ExprId(0), ExprId(1)]),  // 3 = xy = x + y   (shared)
                Expr::Add(vec![ExprId(3), ExprId(2)]),  // 4 = rootA = xy + z
                Expr::Mul(vec![ExprId(3), ExprId(3)]),  // 5 = rootB = xy * xy
            ],
            roots: vec![atom_root(ExprId(4), 0), atom_root(ExprId(5), 1)],
            batching: BatchingOrder { roots: vec![RootId(0), RootId(1)] },
            resolutions: BTreeMap::new(),
        };
        let sched = trivial_schedule(vec![RootId(0), RootId(1)]);
        assert_compiles_and_matches_oracle(&layer, &sched, &[0, 1, 2, 3, 7]);
    }

    // ── (b) Mul-inside-Mul: shared `xy = Mul(x,y)` consumed by `Mul(xy,z)`
    //    (same-op nesting) AND `Add(xy,xy)` (cross-op). ─────────────────────────
    #[test]
    fn shared_nested_mul_in_mul_and_add() {
        let layer = DagLayer {
            sources: vec![witness(0), witness(1), witness(2)],
            exprs: vec![
                Expr::Source(SourceId(0)),             // 0 = x
                Expr::Source(SourceId(1)),             // 1 = y
                Expr::Source(SourceId(2)),              // 2 = z
                Expr::Mul(vec![ExprId(0), ExprId(1)]),  // 3 = xy = x * y   (shared)
                Expr::Mul(vec![ExprId(3), ExprId(2)]),  // 4 = rootA = xy * z
                Expr::Add(vec![ExprId(3), ExprId(3)]),  // 5 = rootB = xy + xy
            ],
            roots: vec![atom_root(ExprId(4), 0), atom_root(ExprId(5), 1)],
            batching: BatchingOrder { roots: vec![RootId(0), RootId(1)] },
            resolutions: BTreeMap::new(),
        };
        let sched = trivial_schedule(vec![RootId(0), RootId(1)]);
        assert_compiles_and_matches_oracle(&layer, &sched, &[0, 1, 2, 3, 7]);
    }

    // ── Task 5 (fwd v2): negation emission. The committed corpus never reaches the
    //    unary-negate path (all corpus negations fold into ADD/FMA `Sign::Minus`
    //    bits), so this synthetic layer is the POSITIVE coverage for it: a root
    //    `(-1) * x` peels the `-1` factor at ExprId level and must emit the v2
    //    zero-arity `Mul{negate_acc}` (never the retired unary `Mul Special(NegOne)`
    //    idiom), while still matching the eval oracle bit-for-bit. ────────────────
    #[test]
    fn negation_emits_zero_arity_mul_negate_acc() {
        use gkr_eval_isa::fwd::isa::{Instr, LdcSub, OperandLine, Special};
        const BABYBEAR_NEG_ONE: u32 = 0x78000001 - 1;
        let layer = DagLayer {
            sources: vec![
                witness(0),
                SourceInfo { kind: SourceKind::Constant { value: BABYBEAR_NEG_ONE } },
            ],
            exprs: vec![
                Expr::Source(SourceId(0)),             // 0 = x
                Expr::Source(SourceId(1)),             // 1 = -1
                Expr::Mul(vec![ExprId(1), ExprId(0)]), // 2 = root = (-1) * x
            ],
            roots: vec![atom_root(ExprId(2), 0)],
            batching: BatchingOrder { roots: vec![RootId(0)] },
            resolutions: BTreeMap::new(),
        };
        let sched = trivial_schedule(vec![RootId(0)]);

        // Value parity vs the oracle (negation is value-preserving).
        assert_compiles_and_matches_oracle(&layer, &sched, &[0, 1, 2, 3, 7]);

        // Emission shape: exactly the v2 negation, never the NegOne-mul idiom.
        let art = compute_artifact_layer();
        let cross: HashMap<ReadPlace, FieldKind> = HashMap::new();
        let compiled = compile_layer(&layer, &art, &BTreeMap::new(), &cross, &sched, 16, None)
            .expect("compile_layer");
        let mut negates = 0usize;
        for instr in &compiled.program.instrs {
            if let Instr::Mul { operands, negate_acc, .. } = instr {
                if *negate_acc {
                    negates += 1;
                    assert!(operands.is_empty(), "negate-acc Mul must be zero-arity");
                }
                assert!(
                    !(operands.len() == 1
                        && matches!(
                            operands[0],
                            OperandLine::Ldc { sub: LdcSub::Special, idx }
                                if idx == Special::NegOne as u16
                        )),
                    "unary Mul Special(NegOne) idiom must not be emitted"
                );
            }
        }
        assert_eq!(negates, 1, "the (-1)*x root must negate exactly once via Mul{{negate_acc}}");
    }
}

// ── StepPlan decoupling (former sub-project-2 Task 1 regression) ──────────────────
//
// DELETED (Task 4, schema v2): this module pinned that the legacy recompute path
// (now `decisions: None`) ignores the
// v1 schema's per-step `StepPlan.resident_*` sets. Schema v2 has no persisted
// per-step residency at all (`LayerSchedule` = `order` + `sites`), so the property
// this test guarded no longer has anything to regress against.

#[test]
fn compile_circuit_loads_validates_and_compiles_all_layers() {
    let name = "add_sub_lui_auipc_mop_layout_gkr.json";
    let artifact = common::load_fixture(name);
    let dag = cs::gkr_compiler::dag_ir::lower_dag(&artifact).unwrap();
    cs::gkr_compiler::dag_ir::validate(&dag).unwrap();
    let sched: cs::gkr_compiler::dag_ir::CircuitSchedule = serde_json::from_reader(
        std::fs::File::open(schedule_path("add_sub_lui_auipc_mop")).unwrap(),
    )
    .unwrap();
    cs::gkr_compiler::dag_ir::validate_circuit_schedule(&dag, &sched).unwrap();
    let compiled = compile_circuit(&dag, &sched, &artifact).unwrap();
    assert_eq!(compiled.layers.len(), dag.layers.len());
    assert_eq!(compiled.budget, 16);
}

// Cone-value gate (spec §6.1), Task 8: re-pointed from `compile_circuit`
// (then uncached recompute) to the `Decisions` compile the committed schedules were
// actually produced under — every root's interpreted value == the eval.rs oracle.
#[test]
fn schedule_driven_compile_matches_eval_oracle_add_sub() {
    let name = "add_sub_lui_auipc_mop_layout_gkr.json";
    let (dag, sched, artifact) = load_dag_sched(name);
    let compiled = compile_circuit(&dag, &sched, &artifact)
        .unwrap_or_else(|e| panic!("[{name}] compile_circuit: {e:?}"));
    let sr = SyntheticResolvers; // unit struct
    let n = dag.globals.trace_len;
    let mut checks = 0usize;
    for (li, layer) in dag.layers.iter().enumerate() {
        if !layer_needs_compile(sched.layers[li].units.is_empty(), layer) {
            continue;
        }
        let cl = &compiled.layers[li];
        for &row in &sample_rows(n) {
            let outs = interpret_layer_row(cl, layer, &resolvers(&sr), row).unwrap();
            for (rid, _) in &cl.root_outputs {
                let got = outs.by_root[rid];
                let want =
                    cs::gkr_compiler::dag_ir::eval_layer_root(layer, *rid, row, &resolvers(&sr));
                assert_eq!(got, want, "{name} L{li} root {rid:?} row {row}");
                checks += 1;
            }
        }
    }
    assert!(checks > 0, "vacuous");
}

/// Load + validate one committed schedule for a fixture (shared by GATE-V/D/F).
fn load_committed(
    name: &str,
    stem: &str,
) -> (cs::gkr_compiler::dag_ir::DagCircuit, CircuitSchedule, GKRCircuitArtifact<BabyBearField>) {
    let artifact = common::load_fixture(name);
    let dag = cs::gkr_compiler::dag_ir::lower_dag(&artifact)
        .unwrap_or_else(|e| panic!("[{name}] lower_dag: {e}"));
    cs::gkr_compiler::dag_ir::validate(&dag).unwrap_or_else(|e| panic!("[{name}] validate: {e}"));
    let sched = gkr_eval_isa::fwd::compile::load_committed_schedule(&schedule_path(stem))
        .unwrap_or_else(|e| panic!("[{name}] load_committed_schedule {stem}: {e:?}"));
    cs::gkr_compiler::dag_ir::validate_circuit_schedule(&dag, &sched)
        .unwrap_or_else(|e| panic!("[{name}] validate_circuit_schedule: {e}"));
    (dag, sched, artifact)
}

// GATE-V (Task 8, re-pointed from `compile_circuit`'s uncached recompute to the
// `Decisions` compile the schedules were produced under): corpus-wide value parity
// over all 11 committed b16 schedules. Each fixture: lower → validate → load+validate
// committed schedule → per-layer Decisions compile (stored `sites`, cap re-derived
// from stored `order`) → every exposed root's interp value == eval oracle at sampled
// rows.
#[test]
fn all_committed_schedules_compile_and_match_oracle() {
    let sr = SyntheticResolvers;
    let mut passed = 0usize;
    let mut total_checks = 0usize;
    for (name, stem) in COMMITTED_CORPUS {
        let (dag, sched, artifact) = load_committed(name, stem);
        let compiled = compile_circuit(&dag, &sched, &artifact)
            .unwrap_or_else(|e| panic!("[{name}] compile_circuit: {e:?}"));
        assert_eq!(compiled.layers.len(), dag.layers.len(), "{name} layer count");

        let n = dag.globals.trace_len;
        for (li, layer) in dag.layers.iter().enumerate() {
            if !layer_needs_compile(sched.layers[li].units.is_empty(), layer) {
                continue;
            }
            let cl = &compiled.layers[li];
            for &row in &sample_rows(n) {
                let outs = interpret_layer_row(cl, layer, &resolvers(&sr), row)
                    .unwrap_or_else(|e| panic!("[{name}] L{li} row {row} interp: {e:?}"));
                for (rid, _) in &cl.root_outputs {
                    let got = outs.by_root[rid];
                    let want =
                        cs::gkr_compiler::dag_ir::eval_layer_root(layer, *rid, row, &resolvers(&sr));
                    assert_eq!(got, want, "{name} L{li} root {rid:?} row {row}");
                    total_checks += 1;
                }
            }
        }
        passed += 1;
        eprintln!("[stage3-parity] {name}: OK ({} layers)", compiled.layers.len());
    }
    assert_eq!(passed, COMMITTED_CORPUS.len(), "all committed schedules must compile + match");
    assert!(total_checks > 0, "vacuous");
    eprintln!(
        "[stage3-parity] {passed}/{} fixtures, {total_checks} root checks",
        COMMITTED_CORPUS.len()
    );
}

// GATE-D + GATE-F (Task 8): recompiling every committed schedule's stored
// `(order, sites)` under `Decisions` (cap re-derived from the stored order — the
// producer's own deterministic derivation) reproduces the persisted
// `predicted_traffic` EXACTLY per layer. A failure means the artifact is stale or
// the emitter drifted since the regen — regenerate or fix the drift, NEVER weaken
// this to a tolerance. GATE-F rides the same compile: the persisted action-aware
// floor must bound the achieved dram_traffic from below on every compiled layer.
#[test]
fn all_committed_schedules_recompile_to_predicted_traffic() {
    for (name, stem) in COMMITTED_CORPUS {
        let (dag, sched, artifact) = load_committed(name, stem);
        let compiled = compile_circuit(&dag, &sched, &artifact)
            .unwrap_or_else(|e| panic!("[{name}] compile_circuit: {e:?}"));
        for (li, (cl, ls)) in compiled.layers.iter().zip(&sched.layers).enumerate() {
            if !layer_needs_compile(ls.units.is_empty(), &dag.layers[li]) {
                assert_eq!(
                    ls.predicted_traffic, 0,
                    "{name} L{li}: skipped layer must persist predicted_traffic=0"
                );
                continue;
            }
            // GATE-D: emitter drift vs stored provenance.
            assert_eq!(
                cl.stats.dram_traffic, ls.predicted_traffic,
                "{name} L{li}: recompile != stored predicted_traffic (emitter drift vs artifact)"
            );
            // GATE-F: floor <= achieved traffic.
            assert!(
                ls.floor <= cl.stats.dram_traffic,
                "{name} L{li}: floor {} above achieved dram_traffic {}",
                ls.floor,
                cl.stats.dram_traffic
            );
        }
        eprintln!("[gate-d] {name}: OK");
    }
}
