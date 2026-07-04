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
    build_cross_layer_field_map, compile_circuit, compile_layer_with_policy, MaterializePolicy,
};
use gkr_eval_isa::fwd::context::CompiledLayer;
use gkr_eval_isa::fwd::interp::interpret_layer_row;
use gkr_eval_isa::schedule_search::scorer::resident_cap_for_order;

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

/// Compile every scheduled layer of a committed schedule under
/// `MaterializePolicy::Decisions` built from the stored `sites`, with the resident
/// admission cap re-derived from the stored `order` via
/// `scorer::resident_cap_for_order` — the SAME deterministic `(layer, order, budget)`
/// derivation `scorer::score` applied when the producer created the artifact, so
/// this reproduces the producer's compile exactly (GATE-D's premise). Returns
/// `None` for layers the producer skipped (empty `order` — mirrors
/// `compile_circuit`'s own `layer_needs_compile` skip; the producer shares that
/// predicate, so empty-`order` schedules exist only for genuinely skippable layers).
fn compile_committed_decisions(
    dag: &cs::gkr_compiler::dag_ir::DagCircuit,
    sched: &CircuitSchedule,
    artifact: &GKRCircuitArtifact<BabyBearField>,
    name: &str,
) -> Vec<Option<CompiledLayer>> {
    assert_eq!(sched.layers.len(), dag.layers.len(), "{name}: schedule/dag layer count");
    let cross = build_cross_layer_field_map(dag);
    dag.layers
        .iter()
        .zip(&sched.layers)
        .enumerate()
        .map(|(li, (layer, ls))| {
            if ls.order.is_empty() {
                return None;
            }
            let cap = resident_cap_for_order(
                layer,
                &artifact.layers[li],
                &artifact.scratch_space_mapping,
                &cross,
                &ls.order,
                sched.budget,
            );
            let decisions = SiteDecisions::new(ls.sites.iter().copied());
            Some(
                compile_layer_with_policy(
                    layer,
                    &artifact.layers[li],
                    &artifact.scratch_space_mapping,
                    &cross,
                    ls,
                    sched.budget,
                    MaterializePolicy::Decisions { decisions, budget: cap },
                )
                .unwrap_or_else(|e| panic!("[{name}] L{li}: Decisions compile: {e:?}")),
            )
        })
        .collect()
}

// ── Task 1 (event-local `MaterializePolicy::Materialize` cache-produce-vs-fuse) ──
//
// DELETED (Task 4, schema v2): this module hand-built `StepPlan`/`ReplayEvent`/
// `DemandKind` schedules and drove `MaterializePolicy::Materialize`, both deleted
// along with the v1 event-replay schema (`.superpowers/sdd/task-4-brief.md`).
// `MaterializePolicy` is now `{ LegacyRecompute, Decisions }` only.

// ── Task 8: emitter coverage for preserved nested same-op shapes ───────────────────
//
// The DAG simplify pipeline now PRESERVES fan-out>=2 same-op nested nodes (an
// `Add` directly inside an `Add`, a `Mul` directly inside a `Mul`) instead of
// unconditionally flattening them — a shape the emitter's `LegacyRecompute`
// lowering (`compile_add_virtual`/`compile_mul_virtual`, `lower.rs:431-465`)
// never saw under the old flatten. These tests hand-build a synthetic layer with
// each shape (shared nested node consumed by two roots — one same-op, one
// cross-op) and pin that `compile_layer_with_policy` under `LegacyRecompute`
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

    use gkr_eval_isa::fwd::compile::{compile_layer_with_policy, MaterializePolicy};
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
    /// per-step residency at all) — only `order` drives root-compile order under
    /// `LegacyRecompute`, which lazily recomputes from the DAG shape.
    fn trivial_schedule(order: Vec<RootId>) -> LayerSchedule {
        LayerSchedule { order, sites: vec![], predicted_traffic: 0, floor: 0 }
    }

    /// Compile `layer` under `LegacyRecompute` and assert every exposed root's
    /// interpreted value matches `eval_layer_root` on every row in `rows`.
    fn assert_compiles_and_matches_oracle(layer: &DagLayer, sched: &LayerSchedule, rows: &[usize]) {
        let art = compute_artifact_layer();
        let cross: HashMap<ReadPlace, FieldKind> = HashMap::new();
        let compiled = compile_layer_with_policy(
            layer,
            &art,
            &BTreeMap::new(),
            &cross,
            sched,
            16,
            MaterializePolicy::LegacyRecompute,
        )
        .expect("compile_layer_with_policy");
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
}

// ── StepPlan decoupling (former sub-project-2 Task 1 regression) ──────────────────
//
// DELETED (Task 4, schema v2): this module pinned that `LegacyRecompute` ignores the
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
// (`LegacyRecompute`) to the `Decisions` compile the committed schedules were
// actually produced under — every root's interpreted value == the eval.rs oracle.
#[test]
fn schedule_driven_compile_matches_eval_oracle_add_sub() {
    let name = "add_sub_lui_auipc_mop_layout_gkr.json";
    let (dag, sched, artifact) = load_dag_sched(name);
    let compiled = compile_committed_decisions(&dag, &sched, &artifact, name);
    let sr = SyntheticResolvers; // unit struct
    let n = dag.globals.trace_len;
    let mut checks = 0usize;
    for (li, layer) in dag.layers.iter().enumerate() {
        let Some(cl) = &compiled[li] else { continue };
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
    let sched: CircuitSchedule = serde_json::from_reader(
        std::fs::File::open(schedule_path(stem))
            .unwrap_or_else(|e| panic!("[{name}] open schedule {stem}: {e}")),
    )
    .unwrap_or_else(|e| panic!("[{name}] parse schedule {stem}: {e}"));
    cs::gkr_compiler::dag_ir::validate_circuit_schedule(&dag, &sched)
        .unwrap_or_else(|e| panic!("[{name}] validate_circuit_schedule: {e}"));
    (dag, sched, artifact)
}

// GATE-V (Task 8, re-pointed from `compile_circuit`/`LegacyRecompute` to the
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
        let compiled = compile_committed_decisions(&dag, &sched, &artifact, name);
        assert_eq!(compiled.len(), dag.layers.len(), "{name} layer count");

        let n = dag.globals.trace_len;
        for (li, layer) in dag.layers.iter().enumerate() {
            let Some(cl) = &compiled[li] else { continue };
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
        eprintln!("[stage3-parity] {name}: OK ({} layers)", compiled.len());
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
        let compiled = compile_committed_decisions(&dag, &sched, &artifact, name);
        for (li, (cl, ls)) in compiled.iter().zip(&sched.layers).enumerate() {
            let Some(cl) = cl else {
                assert_eq!(
                    ls.predicted_traffic, 0,
                    "{name} L{li}: skipped layer must persist predicted_traffic=0"
                );
                continue;
            };
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
