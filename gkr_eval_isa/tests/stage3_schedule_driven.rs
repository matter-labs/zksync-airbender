//! Stage-3 target tests (plan Task 3, Step 1): the schedule-driven
//! `compile_circuit` loads + validates a committed schedule and produces a
//! value-correct forward program for every layer (spec §6.1 cone-value gate).
//!
//! Tests/ binary: lib items via `gkr_eval_isa::`, shared fixture helpers via
//! `mod common`.

mod common;
use common::{load_dag_sched, resolvers, sample_rows, schedule_path, SyntheticResolvers};

use gkr_eval_isa::fwd::compile::compile_circuit;
use gkr_eval_isa::fwd::interp::interpret_layer_row;

// ── Task 1: event-local cache-produce vs fuse for fusable `Mul`-in-`Add` ───────────
//
// These tests hand-construct SYNTHETIC feasible mini-schedules and drive the emitter
// under `MaterializePolicy::Materialize`. Committed schedules keep the default
// `LegacyRecompute` policy (see `all_committed_schedules_compile_and_match_oracle`).
mod task1 {
    use std::collections::{BTreeMap, HashMap};

    use cs::gkr_compiler::dag_ir::{
        eval_layer_root, BatchingOrder, ChallengeKey, ChallengePower, ChallengeRef, ClaimInfo,
        DagLayer, DemandKind, Expr, ExprId, FieldKind, LayerSchedule, ReadPlace, ReplayEvent, Root,
        RootGroup, RootId, RootOrigin, RootSlot, SinkInfo, SinkKind, SourceId, SourceInfo,
        SourceKind, StepPlan,
    };
    use cs::gkr_compiler::{
        GKRLayerDescription, GateArtifacts, NoFieldGKRRelation, NoFieldMaxQuadraticGKRRelation,
        NoFieldStructuredExpression,
    };

    use gkr_eval_isa::fwd::compile::{
        compile_layer_with_policy, lower_layer_stream, LoweredInstr, LoweredKind, MaterializePolicy,
    };
    use gkr_eval_isa::fwd::interp::interpret_layer_row;

    use crate::common::{resolvers, SyntheticResolvers};

    /// BabyBear −1 (= P−1); the canonical additive-inverse-of-1 constant.
    const NEG_ONE: u32 = 0x78000001 - 1;

    // ── synthetic circuit/schedule builders ────────────────────────────────────

    fn witness(col: usize) -> SourceInfo {
        SourceInfo { kind: SourceKind::Read { place: ReadPlace::BaseLayerWitness { column: col } } }
    }

    fn constant(value: u32) -> SourceInfo {
        SourceInfo { kind: SourceKind::Constant { value } }
    }

    /// An Ext-field challenge source (so a product with this factor resolves to `Ext`).
    fn challenge() -> SourceInfo {
        SourceInfo {
            kind: SourceKind::Challenge {
                reference: ChallengeRef {
                    key: ChallengeKey::ConstraintAggregation,
                    power: ChallengePower::One,
                },
            },
        }
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

    /// A cache (materialize-only, no claim) root over `expr`.
    fn cache_root(expr: ExprId) -> Root {
        Root {
            expr,
            materialize: Some(SinkInfo {
                kind: SinkKind::Cache { layer: 0, offset: 0 },
                field: FieldKind::Base,
            }),
            claim: None,
        }
    }

    /// An artifact layer whose single gate classifies to `ForwardAction::Compute` (an
    /// `EnforceSingleMaxQuadraticConstraint`, matched by `classify_relation`'s `_` arm).
    /// Every atom root here uses `relation_index = 0`, so one gate serves all of them.
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

    fn demand(consumer: ExprId, value: ExprId, kind: DemandKind) -> ReplayEvent {
        ReplayEvent::Demand { consumer, input_index: 0, value, kind }
    }

    fn step(before: &[ExprId], events: Vec<ReplayEvent>, after: &[ExprId]) -> StepPlan {
        StepPlan {
            resident_before: before.to_vec(),
            events,
            resident_after: after.to_vec(),
        }
    }

    fn schedule(order: Vec<RootId>, steps: Vec<StepPlan>) -> LayerSchedule {
        LayerSchedule { order, steps, predicted_traffic: 0, floor: 0 }
    }

    fn lower(layer: &DagLayer, sched: &LayerSchedule) -> Vec<LoweredInstr> {
        let art = compute_artifact_layer();
        let scratch = BTreeMap::new();
        let cross: HashMap<ReadPlace, FieldKind> = HashMap::new();
        lower_layer_stream(layer, &art, &scratch, &cross, sched, MaterializePolicy::Materialize)
            .expect("lower_layer_stream")
    }

    // ── per-step stream predicates ─────────────────────────────────────────────

    fn step_has_kind(stream: &[LoweredInstr], step: usize, kind: LoweredKind) -> bool {
        stream.iter().any(|i| i.step == step && i.kind == kind)
    }

    fn step_defines(stream: &[LoweredInstr], step: usize, v: ExprId) -> bool {
        stream.iter().any(|i| i.step == step && i.defines == Some(v))
    }

    fn any_defines(stream: &[LoweredInstr], v: ExprId) -> bool {
        stream.iter().any(|i| i.defines == Some(v))
    }

    fn step_reads_value(stream: &[LoweredInstr], step: usize, v: ExprId) -> bool {
        stream.iter().any(|i| i.step == step && i.value_reads.contains(&v))
    }

    // ── Step 2: a cache-produce demand emits a real Mul→cell; a Resident consumer
    //    reads the cell (no re-fuse). ──────────────────────────────────────────
    #[test]
    fn cached_product_materialized() {
        // exprs: x, y, a, b, p=Mul(x,y), add0=p+a, add1=p+b.
        let layer = DagLayer {
            sources: vec![witness(0), witness(1), witness(2), witness(3)],
            exprs: vec![
                Expr::Source(SourceId(0)), // 0 = x
                Expr::Source(SourceId(1)), // 1 = y
                Expr::Source(SourceId(2)), // 2 = a
                Expr::Source(SourceId(3)), // 3 = b
                Expr::Mul(vec![ExprId(0), ExprId(1)]), // 4 = p
                Expr::Add(vec![ExprId(4), ExprId(2)]), // 5 = add0
                Expr::Add(vec![ExprId(4), ExprId(3)]), // 6 = add1
            ],
            roots: vec![atom_root(ExprId(5), 0), atom_root(ExprId(6), 1)],
            batching: BatchingOrder { roots: vec![RootId(0), RootId(1)] },
            resolutions: BTreeMap::new(),
        };
        let p = ExprId(4);
        let sched = schedule(
            vec![RootId(0), RootId(1)],
            vec![
                // Add0: Recompute p AND Admit p in the same step -> cache-produce.
                step(
                    &[],
                    vec![demand(ExprId(5), p, DemandKind::Recompute), ReplayEvent::Admit { value: p }],
                    &[p],
                ),
                // Add1: p demanded Resident -> read the cell.
                step(&[p], vec![demand(ExprId(6), p, DemandKind::Resident)], &[]),
            ],
        );
        let stream = lower(&layer, &sched);

        // Add0 (step 0): a real Mul computes p, p is written to a cell (`defines`), and it
        // is NOT fused; p is not read back (it is already the acc seed).
        assert!(step_has_kind(&stream, 0, LoweredKind::Mul), "step0 must contain a Mul (cache-produce compute)");
        assert!(step_defines(&stream, 0, p), "step0 must write p to a cell (defines = p)");
        assert!(!step_has_kind(&stream, 0, LoweredKind::Fma), "step0 must NOT fuse the cached product");
        assert!(!step_reads_value(&stream, 0, p), "step0 must NOT re-read Value(p) (it seeds the acc)");

        // Add1 (step 1): reads the cell, no FMA over (x,y).
        assert!(step_reads_value(&stream, 1, p), "step1 must read Value(p) (the cell)");
        assert!(!step_has_kind(&stream, 1, LoweredKind::Fma), "step1 must NOT re-fuse (x,y)");
    }

    // ── Step 3: a bare Recompute (no same-step Admit) fuses even though the SAME
    //    product is admitted at another occurrence (event-local, not per-layer). ──
    #[test]
    fn bare_recompute_fuses_even_if_later_admitted() {
        // p=Mul(x,y); add1=p+a1, add2=p+a2, add3=p+a3.
        let layer = DagLayer {
            sources: vec![witness(0), witness(1), witness(2), witness(3), witness(4)],
            exprs: vec![
                Expr::Source(SourceId(0)), // 0 = x
                Expr::Source(SourceId(1)), // 1 = y
                Expr::Source(SourceId(2)), // 2 = a1
                Expr::Source(SourceId(3)), // 3 = a2
                Expr::Source(SourceId(4)), // 4 = a3
                Expr::Mul(vec![ExprId(0), ExprId(1)]), // 5 = p
                Expr::Add(vec![ExprId(5), ExprId(2)]), // 6 = add1
                Expr::Add(vec![ExprId(5), ExprId(3)]), // 7 = add2
                Expr::Add(vec![ExprId(5), ExprId(4)]), // 8 = add3
            ],
            roots: vec![atom_root(ExprId(6), 0), atom_root(ExprId(7), 1), atom_root(ExprId(8), 2)],
            batching: BatchingOrder { roots: vec![RootId(0), RootId(1), RootId(2)] },
            resolutions: BTreeMap::new(),
        };
        let p = ExprId(5);
        let sched = schedule(
            vec![RootId(0), RootId(1), RootId(2)],
            vec![
                // Add1: Recompute, NO Admit -> fuse.
                step(&[], vec![demand(ExprId(6), p, DemandKind::Recompute)], &[]),
                // Add2: Recompute + Admit -> cache-produce.
                step(
                    &[],
                    vec![demand(ExprId(7), p, DemandKind::Recompute), ReplayEvent::Admit { value: p }],
                    &[p],
                ),
                // Add3: Resident -> read the cell.
                step(&[p], vec![demand(ExprId(8), p, DemandKind::Resident)], &[]),
            ],
        );
        let stream = lower(&layer, &sched);

        // Add1 (step 0): FUSED (a per-layer "admitted-ever" rule would wrongly cache here).
        assert!(step_has_kind(&stream, 0, LoweredKind::Fma), "step0 (bare Recompute) must fuse");
        assert!(!step_defines(&stream, 0, p), "step0 must NOT cache-produce p");

        // Add2 (step 1): cache-produced.
        assert!(step_has_kind(&stream, 1, LoweredKind::Mul), "step1 must contain the cache-produce Mul");
        assert!(step_defines(&stream, 1, p), "step1 must write p to a cell (defines = p)");
        assert!(!step_has_kind(&stream, 1, LoweredKind::Fma), "step1 must NOT fuse (cache-produced)");

        // Add3 (step 2): reads the cell.
        assert!(step_reads_value(&stream, 2, p), "step2 must read Value(p)");
        assert!(!step_has_kind(&stream, 2, LoweredKind::Fma), "step2 must NOT re-fuse (x,y)");
    }

    // ── Step 4: a cache-root Mul is NOT fusable — even with a same-step Recompute +
    //    Admit it is NOT cache-produced by this path; it flows through the existing
    //    materialize/fuse path (regression guard for the cache-root exclusion). ──
    #[test]
    fn cache_root_mul_uses_existing_path() {
        // p=Mul(x,y) is BOTH a child of add0 AND a cache root; add0 = p + w.
        let layer = DagLayer {
            sources: vec![witness(0), witness(1), witness(2)],
            exprs: vec![
                Expr::Source(SourceId(0)), // 0 = x
                Expr::Source(SourceId(1)), // 1 = y
                Expr::Source(SourceId(2)), // 2 = w
                Expr::Mul(vec![ExprId(0), ExprId(1)]), // 3 = p (cache root)
                Expr::Add(vec![ExprId(3), ExprId(2)]), // 4 = add0
            ],
            // RootId(0) = atom add0; RootId(1) = cache root over p.
            roots: vec![atom_root(ExprId(4), 0), cache_root(ExprId(3))],
            batching: BatchingOrder { roots: vec![RootId(0)] },
            resolutions: BTreeMap::new(),
        };
        let p = ExprId(3);
        // Same-step Recompute + Admit for p — would cache-produce IF p were fusable.
        let sched = schedule(
            vec![RootId(0)],
            vec![step(
                &[],
                vec![demand(ExprId(4), p, DemandKind::Recompute), ReplayEvent::Admit { value: p }],
                &[],
            )],
        );
        let stream = lower(&layer, &sched);

        // The fusion/cache-produce partition MUST exclude the cache root: no instruction
        // cache-produces p, and add0 fuses its factors via the existing path.
        assert!(!any_defines(&stream, p), "a cache-root Mul must NOT be cache-produced (defines = p)");
        assert!(step_has_kind(&stream, 0, LoweredKind::Fma), "the cache-root product goes through the existing fuse path");

        // And value-correct: interp == oracle for every root the compile exposed as a
        // `root_output` (the atom root over add0; the materialize-only cache root is exposed
        // by the final sweep, so it is covered too when present).
        let art = compute_artifact_layer();
        let cross: HashMap<ReadPlace, FieldKind> = HashMap::new();
        let compiled = compile_layer_with_policy(
            &layer,
            &art,
            &BTreeMap::new(),
            &cross,
            &sched,
            16,
            MaterializePolicy::Materialize,
        )
        .expect("compile_layer_with_policy");
        let sr = SyntheticResolvers;
        let mut checks = 0usize;
        for row in [0usize, 1, 2, 5] {
            let outs = interpret_layer_row(&compiled, &layer, &resolvers(&sr), row).unwrap();
            for (rid, _) in &compiled.root_outputs {
                let got = outs.by_root[rid];
                let want = eval_layer_root(&layer, *rid, row, &resolvers(&sr));
                assert_eq!(got, want, "cache-root layer {rid:?} row {row}");
                checks += 1;
            }
        }
        assert!(checks > 0, "vacuous");
    }

    // ── Step 5: a negated cached product's cell holds its TRUE signed value; a second
    //    Resident consumer reading Value(p) yields p's DAG value (assert CELL semantics
    //    by evaluating the compiled layer vs the oracle). ────────────────────────
    #[test]
    fn cached_product_sign_applied_once() {
        // p = Mul(-1, x, y) = -x*y; add0 = p + a; add1 = p + b (Resident read of p).
        let layer = DagLayer {
            sources: vec![witness(0), witness(1), witness(2), witness(3), constant(NEG_ONE)],
            exprs: vec![
                Expr::Source(SourceId(0)), // 0 = x
                Expr::Source(SourceId(1)), // 1 = y
                Expr::Source(SourceId(2)), // 2 = a
                Expr::Source(SourceId(3)), // 3 = b
                Expr::Source(SourceId(4)), // 4 = -1
                Expr::Mul(vec![ExprId(4), ExprId(0), ExprId(1)]), // 5 = p = -x*y
                Expr::Add(vec![ExprId(5), ExprId(2)]),            // 6 = add0
                Expr::Add(vec![ExprId(5), ExprId(3)]),            // 7 = add1
            ],
            roots: vec![atom_root(ExprId(6), 0), atom_root(ExprId(7), 1)],
            batching: BatchingOrder { roots: vec![RootId(0), RootId(1)] },
            resolutions: BTreeMap::new(),
        };
        let p = ExprId(5);
        let sched = schedule(
            vec![RootId(0), RootId(1)],
            vec![
                step(
                    &[],
                    vec![demand(ExprId(6), p, DemandKind::Recompute), ReplayEvent::Admit { value: p }],
                    &[p],
                ),
                step(&[p], vec![demand(ExprId(7), p, DemandKind::Resident)], &[]),
            ],
        );

        // Structural: step0 cache-produces p; step1 reads the cell (so the sign assertion
        // below binds to the CELL, not the producing Add's local fold).
        let stream = lower(&layer, &sched);
        assert!(step_defines(&stream, 0, p), "step0 must cache-produce p");
        assert!(step_reads_value(&stream, 1, p), "step1 must read the cell Value(p)");

        // Value: the cell must hold -x*y, so BOTH roots match the oracle.
        let art = compute_artifact_layer();
        let cross: HashMap<ReadPlace, FieldKind> = HashMap::new();
        let compiled = compile_layer_with_policy(
            &layer,
            &art,
            &BTreeMap::new(),
            &cross,
            &sched,
            16,
            MaterializePolicy::Materialize,
        )
        .expect("compile_layer_with_policy");
        let sr = SyntheticResolvers;
        let mut checks = 0usize;
        for row in [0usize, 1, 2, 3, 7] {
            let outs = interpret_layer_row(&compiled, &layer, &resolvers(&sr), row).unwrap();
            for (rid, _) in &compiled.root_outputs {
                let got = outs.by_root[rid];
                let want = eval_layer_root(&layer, *rid, row, &resolvers(&sr));
                assert_eq!(got, want, "signed-cell {rid:?} row {row}");
                checks += 1;
            }
        }
        assert!(checks > 0, "vacuous");
    }

    // ── Two cache-produce products in ONE Add whose factors have DIFFERENT fields
    //    (base×base and base×Ext), both Recompute+same-step-Admit, then consumed
    //    Resident by a second Add. Exercises the multi-cache-produce offload/fold-back
    //    path (Constraint 4): the offloaded partial must be evicted AND folded back at
    //    ITS OWN accumulator field, not the second product's field. ────────────────
    #[test]
    fn multi_cache_produce_mixed_fields() {
        // p1 = Mul(x, y) [Base]; p2 = Mul(z, w) with z an Ext challenge [Ext].
        // add0 = p1 + p2 + a; add1 = p1 + p2 + b (both products demanded Resident).
        let layer = DagLayer {
            sources: vec![
                witness(0),   // 0 = x  (Base)
                witness(1),   // 1 = y  (Base)
                witness(2),   // 2 = w  (Base)
                witness(3),   // 3 = a  (Base)
                witness(4),   // 4 = b  (Base)
                challenge(),  // 5 = z  (Ext)
            ],
            exprs: vec![
                Expr::Source(SourceId(0)), // 0 = x
                Expr::Source(SourceId(1)), // 1 = y
                Expr::Source(SourceId(2)), // 2 = w
                Expr::Source(SourceId(3)), // 3 = a
                Expr::Source(SourceId(4)), // 4 = b
                Expr::Source(SourceId(5)), // 5 = z (Ext)
                Expr::Mul(vec![ExprId(0), ExprId(1)]), // 6 = p1 = x*y     (Base)
                Expr::Mul(vec![ExprId(5), ExprId(2)]), // 7 = p2 = z*w     (Ext)
                Expr::Add(vec![ExprId(6), ExprId(7), ExprId(3)]), // 8 = add0
                Expr::Add(vec![ExprId(6), ExprId(7), ExprId(4)]), // 9 = add1
            ],
            roots: vec![atom_root(ExprId(8), 0), atom_root(ExprId(9), 1)],
            batching: BatchingOrder { roots: vec![RootId(0), RootId(1)] },
            resolutions: BTreeMap::new(),
        };
        let p1 = ExprId(6);
        let p2 = ExprId(7);
        let sched = schedule(
            vec![RootId(0), RootId(1)],
            vec![
                // Add0: BOTH products Recompute + same-step Admit -> two cache-produces.
                step(
                    &[],
                    vec![
                        demand(ExprId(8), p1, DemandKind::Recompute),
                        demand(ExprId(8), p2, DemandKind::Recompute),
                        ReplayEvent::Admit { value: p1 },
                        ReplayEvent::Admit { value: p2 },
                    ],
                    &[p1, p2],
                ),
                // Add1: both products demanded Resident -> read the cells.
                step(
                    &[p1, p2],
                    vec![
                        demand(ExprId(9), p1, DemandKind::Resident),
                        demand(ExprId(9), p2, DemandKind::Resident),
                    ],
                    &[],
                ),
            ],
        );

        // Structural: step0 cache-produces BOTH products (exercising the offload/fold-back
        // branch) with no fuse; step1 reads BOTH cells.
        let stream = lower(&layer, &sched);
        assert!(step_defines(&stream, 0, p1), "step0 must cache-produce p1 (Base)");
        assert!(step_defines(&stream, 0, p2), "step0 must cache-produce p2 (Ext)");
        assert!(step_has_kind(&stream, 0, LoweredKind::Mul), "step0 must contain cache-produce Muls");
        assert!(!step_has_kind(&stream, 0, LoweredKind::Fma), "step0 must NOT fuse either product");
        assert!(step_reads_value(&stream, 1, p1), "step1 must read Value(p1)");
        assert!(step_reads_value(&stream, 1, p2), "step1 must read Value(p2)");

        // Value-correct: interp == oracle for both roots (add0 = add1 modulo their addends).
        let art = compute_artifact_layer();
        let cross: HashMap<ReadPlace, FieldKind> = HashMap::new();
        let compiled = compile_layer_with_policy(
            &layer,
            &art,
            &BTreeMap::new(),
            &cross,
            &sched,
            16,
            MaterializePolicy::Materialize,
        )
        .expect("compile_layer_with_policy");
        let sr = SyntheticResolvers;
        let mut checks = 0usize;
        for row in [0usize, 1, 2, 3, 7] {
            let outs = interpret_layer_row(&compiled, &layer, &resolvers(&sr), row).unwrap();
            for (rid, _) in &compiled.root_outputs {
                let got = outs.by_root[rid];
                let want = eval_layer_root(&layer, *rid, row, &resolvers(&sr));
                assert_eq!(got, want, "mixed-field multi cache-produce {rid:?} row {row}");
                checks += 1;
            }
        }
        assert!(checks > 0, "vacuous");
    }
}

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
        SinkKind, SourceId, SourceInfo, SourceKind, StepPlan,
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

    /// An artifact layer whose single gate classifies to `ForwardAction::Compute`
    /// (mirrors `task1::compute_artifact_layer`); every atom root here uses
    /// `relation_index = 0`, so one gate serves both roots.
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

    /// A trivial no-op schedule: no resident sets, no replay events (irrelevant
    /// under `LegacyRecompute`, which lazily recomputes from the DAG shape and
    /// ignores the event stream) — only `order` drives root-compile order.
    fn trivial_schedule(order: Vec<RootId>) -> LayerSchedule {
        let steps = order
            .iter()
            .map(|_| StepPlan { resident_before: vec![], events: vec![], resident_after: vec![] })
            .collect();
        LayerSchedule { order, steps, predicted_traffic: 0, floor: 0 }
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

#[test]
#[ignore = "committed schedules stale under DAG simplification; regenerated by the sub-project-2 compile-in-loop scorer (spec .agents/specs/2026-07-04-gkr-dag-simplify-design.md §6)"]
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

// Cone-value gate (spec §6.1): every root's interpreted value == the eval.rs oracle.
#[test]
#[ignore = "committed schedules stale under DAG simplification; regenerated by the sub-project-2 compile-in-loop scorer (spec .agents/specs/2026-07-04-gkr-dag-simplify-design.md §6)"]
fn schedule_driven_compile_matches_eval_oracle_add_sub() {
    let name = "add_sub_lui_auipc_mop_layout_gkr.json";
    let (dag, sched, artifact) = load_dag_sched(name);
    let compiled = compile_circuit(&dag, &sched, &artifact).unwrap();
    let sr = SyntheticResolvers; // unit struct
    let n = dag.globals.trace_len;
    let mut checks = 0usize;
    for (li, layer) in dag.layers.iter().enumerate() {
        for &row in &sample_rows(n) {
            let outs =
                interpret_layer_row(&compiled.layers[li], layer, &resolvers(&sr), row).unwrap();
            for (rid, _) in &compiled.layers[li].root_outputs {
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

// Corpus-wide value parity over all 11 committed b16 schedules (report evidence). The
// schedule stem differs from the fixture stem only for `inits_and_teardowns`
// (fixture: `..._preprocessed_layout_gkr.json`, schedule: `inits_and_teardowns`), so we
// map explicitly. Each fixture: lower → validate → load+validate committed schedule →
// compile_circuit → every exposed root's interp value == eval oracle at sampled rows.
#[test]
#[ignore = "committed schedules stale under DAG simplification; regenerated by the sub-project-2 compile-in-loop scorer (spec .agents/specs/2026-07-04-gkr-dag-simplify-design.md §6)"]
fn all_committed_schedules_compile_and_match_oracle() {
    // (fixture file, committed schedule stem)
    let corpus: &[(&str, &str)] = &[
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

    let sr = SyntheticResolvers;
    let mut passed = 0usize;
    let mut total_checks = 0usize;
    for (name, stem) in corpus {
        let artifact = common::load_fixture(name);
        let dag = cs::gkr_compiler::dag_ir::lower_dag(&artifact)
            .unwrap_or_else(|e| panic!("[{name}] lower_dag: {e}"));
        cs::gkr_compiler::dag_ir::validate(&dag)
            .unwrap_or_else(|e| panic!("[{name}] validate: {e}"));
        let sched: cs::gkr_compiler::dag_ir::CircuitSchedule = serde_json::from_reader(
            std::fs::File::open(schedule_path(stem))
                .unwrap_or_else(|e| panic!("[{name}] open schedule {stem}: {e}")),
        )
        .unwrap_or_else(|e| panic!("[{name}] parse schedule {stem}: {e}"));
        cs::gkr_compiler::dag_ir::validate_circuit_schedule(&dag, &sched)
            .unwrap_or_else(|e| panic!("[{name}] validate_circuit_schedule: {e}"));

        let compiled = compile_circuit(&dag, &sched, &artifact)
            .unwrap_or_else(|e| panic!("[{name}] compile_circuit: {e:?}"));
        assert_eq!(compiled.layers.len(), dag.layers.len(), "{name} layer count");

        let n = dag.globals.trace_len;
        for (li, layer) in dag.layers.iter().enumerate() {
            for &row in &sample_rows(n) {
                let outs = interpret_layer_row(&compiled.layers[li], layer, &resolvers(&sr), row)
                    .unwrap_or_else(|e| panic!("[{name}] L{li} row {row} interp: {e:?}"));
                for (rid, _) in &compiled.layers[li].root_outputs {
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
    assert_eq!(passed, corpus.len(), "all committed schedules must compile + match");
    assert!(total_checks > 0, "vacuous");
    eprintln!("[stage3-parity] {passed}/{} fixtures, {total_checks} root checks", corpus.len());
}
