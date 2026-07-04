//! Task 3 target tests: `MaterializePolicy::Decisions` — emitter-owned residency,
//! capacity, and eviction, driven by Task 2's `SiteDecisions`/`OccurrenceStreams`.
//! See `.superpowers/sdd/task-3-brief.md` for the exact semantics these tests pin.
//!
//! Layer/schedule builders follow `tests/stage3_schedule_driven.rs`'s `task1`/`task8`
//! synthetic patterns (single-gate `Compute`-classified artifact layer, `atom_root`
//! Export sinks, a trivial schedule with an empty `sites` genome — schema v2
//! (Task 4) has no persisted per-step residency at all, and `Decisions`, like
//! `LegacyRecompute`, drives root-compile order purely from `order`).

mod common;
use common::{resolvers, SyntheticResolvers};

use std::collections::{BTreeMap, HashMap};

use cs::gkr_compiler::dag_ir::{
    eval_layer_root, BatchingOrder, ChallengeKey, ChallengePower, ChallengeRef, ClaimInfo,
    DagLayer, Expr, ExprId, FieldKind, LayerSchedule, ReadPlace, Root, RootGroup, RootId,
    RootOrigin, RootSlot, SinkInfo, SinkKind, SourceId, SourceInfo, SourceKind,
};
use cs::gkr_compiler::{
    GKRLayerDescription, GateArtifacts, NoFieldGKRRelation, NoFieldMaxQuadraticGKRRelation,
    NoFieldStructuredExpression,
};

use gkr_eval_isa::fwd::compile::decisions::{SiteConsumer, SiteDecisions, SiteKey};
use gkr_eval_isa::fwd::compile::{compile_layer_with_policy, MaterializePolicy};
use gkr_eval_isa::fwd::interp::interpret_layer_row;

// ── shared synthetic-layer scaffolding (mirrors task1/task8 in stage3_schedule_driven) ──

fn witness(col: usize) -> SourceInfo {
    SourceInfo { kind: SourceKind::Read { place: ReadPlace::BaseLayerWitness { column: col } } }
}

fn challenge() -> SourceInfo {
    SourceInfo {
        kind: SourceKind::Challenge {
            reference: ChallengeRef { key: ChallengeKey::ConstraintAggregation, power: ChallengePower::One },
        },
    }
}

/// An atom (Output+claim) root over `expr`, materialized to `Export { slot }` at `field`.
fn atom_root_field(expr: ExprId, slot: usize, field: FieldKind) -> Root {
    Root {
        expr,
        materialize: Some(SinkInfo { kind: SinkKind::Export { slot }, field }),
        claim: Some(ClaimInfo {
            origin: RootOrigin { group: RootGroup::Gates, relation_index: 0, slot: RootSlot::Output(slot) },
        }),
    }
}

fn atom_root(expr: ExprId, slot: usize) -> Root {
    atom_root_field(expr, slot, FieldKind::Base)
}

/// An artifact layer whose single gate classifies to `ForwardAction::Compute` (an
/// `EnforceSingleMaxQuadraticConstraint`, matched by `classify_relation`'s `_` arm).
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

/// A trivial no-op schedule: `Decisions`, like `LegacyRecompute`, only reads `order` —
/// schema v2 has no persisted per-step residency for either policy to consult.
fn trivial_schedule(order: Vec<RootId>) -> LayerSchedule {
    LayerSchedule { order, sites: vec![], predicted_traffic: 0, floor: 0 }
}

fn root_output(root: RootId, value: ExprId) -> SiteKey {
    SiteKey { root, consumer: SiteConsumer::RootOutput, value }
}

fn site(root: RootId, consumer_expr: ExprId, input_index: u32, value: ExprId) -> SiteKey {
    SiteKey { root, consumer: SiteConsumer::Expr { expr: consumer_expr, input_index }, value }
}

fn compile(
    layer: &DagLayer,
    sched: &LayerSchedule,
    budget: usize,
    policy: MaterializePolicy,
) -> gkr_eval_isa::fwd::context::CompiledLayer {
    let art = compute_artifact_layer();
    let cross: HashMap<ReadPlace, FieldKind> = HashMap::new();
    compile_layer_with_policy(layer, &art, &BTreeMap::new(), &cross, sched, budget, policy)
        .expect("compile_layer_with_policy")
}

// ── Test 1: cache hit beats LegacyRecompute on instr count ─────────────────────────

/// High-priority reused value is served from residency (1 compute, no recompute):
/// instr count strictly below the LegacyRecompute compile of the same layer.
#[test]
fn decisions_cache_hit_beats_legacy_recompute() {
    // s = Add(x,y) [compound, Base]; R0 = Mul(s, x2) demands s once, R1 = Mul(s, x3)
    // demands it a second time — a genuine `lower_operand_virtual` demand site (Mul
    // children are lowered individually, unlike an Add-child product).
    let layer = DagLayer {
        sources: vec![witness(0), witness(1), witness(2), witness(3)],
        exprs: vec![
            Expr::Source(SourceId(0)), // 0 = x
            Expr::Source(SourceId(1)), // 1 = y
            Expr::Source(SourceId(2)), // 2 = x2
            Expr::Source(SourceId(3)), // 3 = x3
            Expr::Add(vec![ExprId(0), ExprId(1)]), // 4 = s = x + y (shared)
            Expr::Mul(vec![ExprId(4), ExprId(2)]), // 5 = R0 = s * x2
            Expr::Mul(vec![ExprId(4), ExprId(3)]), // 6 = R1 = s * x3
        ],
        roots: vec![atom_root(ExprId(5), 0), atom_root(ExprId(6), 1)],
        batching: BatchingOrder { roots: vec![RootId(0), RootId(1)] },
        resolutions: BTreeMap::new(),
    };
    let (x, y, s) = (ExprId(0), ExprId(1), ExprId(4));
    let order = vec![RootId(0), RootId(1)];
    let sched = trivial_schedule(order);

    // Budget=1 (a single Base slot): s's HIGH remaining-occurrence priority must win the
    // slot over x/y's LOW ones, so x/y's transient (structurally-inevitable, since
    // `demand_expand` recurses into s's children on EVERY occurrence of s) admission
    // attempts get evicted again rather than compounding the instr count — isolating the
    // property under test (s served from residency, not recomputed) from that overhead.
    let decisions = SiteDecisions::new([
        // s's 2nd occurrence: consumer = Mul(6) at input_index 0 (s is R1's first factor).
        (site(RootId(1), ExprId(6), 0, s), 100.0),
        // x/y's 2nd occurrence: consumer = s's own Add(4) at input_index 0/1, under R1.
        (site(RootId(1), ExprId(4), 0, x), -100.0),
        (site(RootId(1), ExprId(4), 1, y), -100.0),
    ]);
    let decisions_compiled = compile(
        &layer,
        &sched,
        16,
        MaterializePolicy::Decisions { decisions, budget: 1 },
    );
    let legacy_compiled = compile(&layer, &sched, 16, MaterializePolicy::LegacyRecompute);

    assert!(
        decisions_compiled.program.instrs.len() < legacy_compiled.program.instrs.len(),
        "Decisions ({}) must emit strictly fewer instrs than LegacyRecompute ({}) once s is cached",
        decisions_compiled.program.instrs.len(),
        legacy_compiled.program.instrs.len()
    );

    // Sanity: s really is resident after R0 (else the test would be vacuous).
    assert!(
        decisions_compiled.resident_realized[0].1.contains(&s),
        "s must be admitted to residency after R0"
    );
}

// ── Test 2: capacity + priority-gated eviction ──────────────────────────────────────

/// Zero-capacity pressure: admitting an Ext (width 4) at budget 4 with a Base
/// resident evicts the Base iff its priority is lower; skips admission iff higher.
#[test]
fn eviction_respects_priority_and_width() {
    // B (Base leaf) and E (Ext/challenge leaf), each demanded twice: once as a bare
    // producer root, once wrapped in a distinct `Add([leaf])` "probe" root (a genuine
    // 2nd `lower_operand_virtual` demand site — two DIFFERENT roots sharing the SAME
    // bare leaf as `root.expr` would instead collapse into one `materialize_if_root`
    // event, an existing shared-ExprId root dedup unrelated to Task 3). Order:
    // [R0=B_produce, R1=E_produce (contends for B's slot), R2=B_probe, R3=E_probe].
    fn build_layer() -> (DagLayer, ExprId, ExprId) {
        let layer = DagLayer {
            sources: vec![witness(0), challenge()],
            exprs: vec![
                Expr::Source(SourceId(0)),    // 0 = B (Base)
                Expr::Source(SourceId(1)),    // 1 = E (Ext)
                Expr::Add(vec![ExprId(0)]),   // 2 = B-probe wrapper
                Expr::Add(vec![ExprId(1)]),   // 3 = E-probe wrapper
            ],
            roots: vec![
                atom_root_field(ExprId(0), 0, FieldKind::Base), // R0: B produce
                atom_root_field(ExprId(1), 1, FieldKind::Ext),  // R1: E produce (contends)
                atom_root_field(ExprId(2), 2, FieldKind::Base), // R2: B probe
                atom_root_field(ExprId(3), 3, FieldKind::Ext),  // R3: E probe
            ],
            batching: BatchingOrder { roots: vec![RootId(0), RootId(1), RootId(2), RootId(3)] },
            resolutions: BTreeMap::new(),
        };
        (layer, ExprId(0), ExprId(1))
    }

    let run = |b_priority: f64, e_priority: f64| -> gkr_eval_isa::fwd::context::CompiledLayer {
        let (layer, b, e) = build_layer();
        let order = vec![RootId(0), RootId(1), RootId(2), RootId(3)];
        let sched = trivial_schedule(order);
        let decisions = SiteDecisions::new([
            (site(RootId(2), ExprId(2), 0, b), b_priority),
            (site(RootId(3), ExprId(3), 0, e), e_priority),
        ]);
        compile(&layer, &sched, 4, MaterializePolicy::Decisions { decisions, budget: 4 })
    };

    // (a) B's priority LOWER than E's admitting priority: B is evicted, E admitted.
    let (_, b, e) = build_layer();
    let lower = run(1.0, 100.0);
    let after_r1_lower = &lower.resident_realized[1].1;
    assert!(!after_r1_lower.contains(&b), "lower-priority B must be evicted to admit E");
    assert!(after_r1_lower.contains(&e), "E must be admitted once it evicts B");

    // (b) B's priority HIGHER: E's admission is skipped, B stays resident.
    let higher = run(100.0, 1.0);
    let after_r1_higher = &higher.resident_realized[1].1;
    assert!(after_r1_higher.contains(&b), "higher-priority B must survive E's admission attempt");
    assert!(!after_r1_higher.contains(&e), "E must NOT be admitted over a higher-priority B");
}

// ── Test 3: dead residents evict before any live one ───────────────────────────────

/// Dead value (occurrences exhausted) is evicted before any live resident.
#[test]
fn dead_values_evict_first() {
    // A: produced (R0), then demanded again via a probe wrapper (R1) -> exhausted
    //    (dead) but still resident (a HIT never triggers eviction on its own).
    // D: produced (R2), with a LIVE remaining occurrence (its probe R4 is scheduled
    //    AFTER the eviction battle, so `effective_priority(D)` is still `Some` then).
    // C: produced (R3) with admitting priority 1.0 — lower than D's 5.0, so the ONLY
    //    way C fits (budget=2, all width 1) is by evicting the DEAD A, never D.
    // Probes wrap their leaf in a distinct `Add([leaf])` expr (see
    // `eviction_respects_priority_and_width`'s doc for why: two roots sharing the SAME
    // bare leaf as `root.expr` would collapse into one `materialize_if_root` event).
    let layer = DagLayer {
        sources: vec![witness(0), witness(1), witness(2)],
        exprs: vec![
            Expr::Source(SourceId(0)), // 0 = A
            Expr::Source(SourceId(1)), // 1 = D
            Expr::Source(SourceId(2)), // 2 = C
            Expr::Add(vec![ExprId(0)]), // 3 = A-probe wrapper
            Expr::Add(vec![ExprId(1)]), // 4 = D-probe wrapper
            Expr::Add(vec![ExprId(2)]), // 5 = C-probe wrapper
        ],
        roots: vec![
            atom_root(ExprId(0), 0), // R0: A produce
            atom_root(ExprId(3), 1), // R1: A probe (drains A to dead)
            atom_root(ExprId(1), 2), // R2: D produce
            atom_root(ExprId(2), 3), // R3: C produce (triggers eviction)
            atom_root(ExprId(4), 4), // R4: D probe (D must still be resident after R3)
            atom_root(ExprId(5), 5), // R5: C probe (C must be resident after R3)
        ],
        batching: BatchingOrder {
            roots: vec![RootId(0), RootId(1), RootId(2), RootId(3), RootId(4), RootId(5)],
        },
        resolutions: BTreeMap::new(),
    };
    let (a, d, c) = (ExprId(0), ExprId(1), ExprId(2));
    let order = vec![RootId(0), RootId(1), RootId(2), RootId(3), RootId(4), RootId(5)];
    let sched = trivial_schedule(order);

    let decisions = SiteDecisions::new([
        (site(RootId(4), ExprId(4), 0, d), 5.0), // D's remaining-occurrence priority (read at R4)
        (site(RootId(5), ExprId(5), 0, c), 1.0), // C's remaining-occurrence priority (read at R5)
    ]);
    let compiled = compile(&layer, &sched, 2, MaterializePolicy::Decisions { decisions, budget: 2 });

    // After R3 (index 3): A is gone (evicted, dead), D and C both survive.
    let after_r3 = &compiled.resident_realized[3].1;
    assert!(!after_r3.contains(&a), "dead A must be evicted first, not live D");
    assert!(after_r3.contains(&d), "live D must survive C's admission");
    assert!(after_r3.contains(&c), "C must be admitted (only A needed evicting)");
}

// ── Test 4: leaf caching removes the second DRAM read ──────────────────────────────

/// Miss on a DRAM Read leaf resolves via source_to_vop and counts traffic;
/// caching it (high priority site) removes the second read.
#[test]
fn read_leaf_cacheable() {
    // R1 wraps W in a distinct `Add([W])` expr rather than reusing W as its OWN
    // `root.expr` directly — two roots sharing the same bare leaf `root.expr` collapse
    // into a single `materialize_if_root` event (existing shared-ExprId root dedup,
    // unrelated to Task 3), which would make this test vacuous (only ever 1 read).
    let layer = DagLayer {
        sources: vec![witness(0)],
        exprs: vec![
            Expr::Source(SourceId(0)),  // 0 = W
            Expr::Add(vec![ExprId(0)]), // 1 = W-probe wrapper
        ],
        roots: vec![atom_root(ExprId(0), 0), atom_root(ExprId(1), 1)],
        batching: BatchingOrder { roots: vec![RootId(0), RootId(1)] },
        resolutions: BTreeMap::new(),
    };
    let w = ExprId(0);
    let order = vec![RootId(0), RootId(1)];
    let sched = trivial_schedule(order);

    let decisions = SiteDecisions::new([(site(RootId(1), ExprId(1), 0, w), 1.0)]);
    let decisions_compiled =
        compile(&layer, &sched, 16, MaterializePolicy::Decisions { decisions, budget: 16 });
    let legacy_compiled = compile(&layer, &sched, 16, MaterializePolicy::LegacyRecompute);

    assert_eq!(legacy_compiled.stats.dram_reads, 2, "LegacyRecompute reads W twice");
    assert_eq!(
        decisions_compiled.stats.dram_reads, 1,
        "Decisions must cache W after its first read, removing the second DRAM read"
    );
}

// ── Test 5: determinism ─────────────────────────────────────────────────────────────

/// DETERMINISM: two compiles of identical inputs emit identical instruction
/// streams (Vec<Instr> equality).
#[test]
fn decisions_compile_is_deterministic() {
    // Three Base leaves (X, Y, Z) tied at equal priority for a single contested slot
    // (budget=1) — a tie-break-heavy scenario that would expose any HashMap-driven
    // nondeterminism in eviction-candidate ordering.
    let layer = DagLayer {
        sources: vec![witness(0), witness(1), witness(2)],
        exprs: vec![
            Expr::Source(SourceId(0)), // 0 = X
            Expr::Source(SourceId(1)), // 1 = Y
            Expr::Source(SourceId(2)), // 2 = Z
        ],
        roots: vec![
            atom_root(ExprId(0), 0),
            atom_root(ExprId(1), 1),
            atom_root(ExprId(2), 2),
            atom_root(ExprId(0), 3),
            atom_root(ExprId(1), 4),
            atom_root(ExprId(2), 5),
        ],
        batching: BatchingOrder {
            roots: vec![RootId(0), RootId(1), RootId(2), RootId(3), RootId(4), RootId(5)],
        },
        resolutions: BTreeMap::new(),
    };
    let (x, y, z) = (ExprId(0), ExprId(1), ExprId(2));
    let order = vec![RootId(0), RootId(1), RootId(2), RootId(3), RootId(4), RootId(5)];
    let sched = trivial_schedule(order);

    let build_decisions = || {
        SiteDecisions::new([
            (root_output(RootId(3), x), 7.0),
            (root_output(RootId(4), y), 7.0),
            (root_output(RootId(5), z), 7.0),
        ])
    };

    let c1 = compile(
        &layer,
        &sched,
        1,
        MaterializePolicy::Decisions { decisions: build_decisions(), budget: 1 },
    );
    let c2 = compile(
        &layer,
        &sched,
        1,
        MaterializePolicy::Decisions { decisions: build_decisions(), budget: 1 },
    );

    assert_eq!(c1.program, c2.program, "identical Decisions inputs must emit identical programs");
    assert_eq!(c1.resident_realized, c2.resident_realized, "residency snapshots must also match");
}

// ── Test 6: value parity under adversarial priorities ───────────────────────────────

/// Value parity: every root's interpreted value == eval_layer_root under
/// arbitrary (adversarial low/high) priorities.
#[test]
fn decisions_value_parity_any_priorities() {
    // s = Add(x,y) [shared, Base]; R0 = Mul(s,s), R1 = Mul(s,z) — the
    // `stepplan_decoupling` fixture shape, reused here under `Decisions` with a very
    // tight budget so admission/eviction genuinely fires on every row.
    let layer = DagLayer {
        sources: vec![witness(0), witness(1), witness(2)],
        exprs: vec![
            Expr::Source(SourceId(0)),             // 0 = x
            Expr::Source(SourceId(1)),             // 1 = y
            Expr::Source(SourceId(2)),             // 2 = z
            Expr::Add(vec![ExprId(0), ExprId(1)]), // 3 = s = x + y (shared)
            Expr::Mul(vec![ExprId(3), ExprId(3)]), // 4 = R0 = s * s
            Expr::Mul(vec![ExprId(3), ExprId(2)]), // 5 = R1 = s * z
        ],
        roots: vec![atom_root(ExprId(4), 0), atom_root(ExprId(5), 1)],
        batching: BatchingOrder { roots: vec![RootId(0), RootId(1)] },
        resolutions: BTreeMap::new(),
    };
    let order = vec![RootId(0), RootId(1)];
    let sched = trivial_schedule(order);

    let (x, y, z, s) = (ExprId(0), ExprId(1), ExprId(2), ExprId(3));
    let r0 = ExprId(4);
    let r1 = ExprId(5);

    // Two adversarial, mutually-swapped priority configurations, both extreme, over a
    // best-effort enumeration of this tiny layer's demand sites (a missing/duplicate
    // key just falls back to 0.0 per `SiteDecisions`/`OccurrenceStreams::build`'s doc —
    // harmless for this value-correctness check).
    let configs: [[f64; 2]; 2] = [[1.0e9, -1.0e9], [-1.0e9, 1.0e9]];
    let sr = SyntheticResolvers;
    let mut checks = 0usize;

    for [hi, lo] in configs {
        let decisions = SiteDecisions::new([
            (site(RootId(0), r0, 0, s), hi),
            (site(RootId(0), r0, 1, s), hi),
            (site(RootId(1), r1, 0, s), hi),
            (site(RootId(1), r1, 1, z), lo),
            (site(RootId(0), s, 0, x), lo),
            (site(RootId(0), s, 1, y), lo),
            (site(RootId(1), s, 0, x), lo),
            (site(RootId(1), s, 1, y), lo),
            (root_output(RootId(0), r0), hi),
            (root_output(RootId(1), r1), lo),
        ]);
        let compiled = compile(&layer, &sched, 16, MaterializePolicy::Decisions { decisions, budget: 1 });

        for row in [0usize, 1, 2, 5] {
            let outs = interpret_layer_row(&compiled, &layer, &resolvers(&sr), row).unwrap();
            for (rid, _) in &compiled.root_outputs {
                let got = outs.by_root[rid];
                let want = eval_layer_root(&layer, *rid, row, &resolvers(&sr));
                assert_eq!(got, want, "row {row} root {rid:?} mismatch under config hi={hi} lo={lo}");
                checks += 1;
            }
        }
    }
    assert!(checks > 0, "vacuous");
}

// ── Extra (not one of the 6, but required by the Task-3 brief): serve-order alignment
//    lock for a materialized-mixed Add (addends + a fusable product). ────────────────

/// Regression guard for the CRITICAL constraint: `Decisions` must lower `Add` through
/// the SAME virtual/FMA-partition path `OccurrenceStreams::build` mirrors (addends
/// before product operands), never `compile_add_materialize`'s original-encounter-order
/// path. This test locks the OBSERVABLE consequence: for `Add[addend_a, Mul(l,r),
/// addend_b]` at a materialized root, with all four leaves' 2nd-occurrence priorities
/// EQUAL (so ties resolve to "first two admitted, in visitation order, win the only two
/// slots"), the surviving pair must be the FMA-partition-order pair (addend_a, addend_b)
/// — NOT the original-encounter-order pair (addend_a, l) that `compile_add_materialize`
/// would visit first (`lower.rs:484-521`: children iterated in original order, so `l`
/// and `r` — the product's own operands — are visited before `addend_b`).
#[test]
fn decisions_add_order_matches_virtual_fma_partition_not_materialize_shape() {
    let layer = DagLayer {
        sources: vec![witness(0), witness(1), witness(2), witness(3)],
        exprs: vec![
            Expr::Source(SourceId(0)), // 0 = addend_a
            Expr::Source(SourceId(1)), // 1 = addend_b
            Expr::Source(SourceId(2)), // 2 = l
            Expr::Source(SourceId(3)), // 3 = r
            Expr::Mul(vec![ExprId(2), ExprId(3)]), // 4 = Mul(l, r)
            // Deliberately interleaved: addend, product, addend.
            Expr::Add(vec![ExprId(0), ExprId(4), ExprId(1)]), // 5 = Add root
        ],
        roots: vec![
            atom_root(ExprId(5), 0), // R0: the mixed Add (produces all 4 leaves)
            atom_root(ExprId(0), 1), // R1: addend_a probe
            atom_root(ExprId(1), 2), // R2: addend_b probe
            atom_root(ExprId(2), 3), // R3: l probe
            atom_root(ExprId(3), 4), // R4: r probe
        ],
        batching: BatchingOrder {
            roots: vec![RootId(0), RootId(1), RootId(2), RootId(3), RootId(4)],
        },
        resolutions: BTreeMap::new(),
    };
    let (addend_a, addend_b, l, r) = (ExprId(0), ExprId(1), ExprId(2), ExprId(3));
    let order = vec![RootId(0), RootId(1), RootId(2), RootId(3), RootId(4)];
    let sched = trivial_schedule(order);

    // Equal 2nd-occurrence priority for all 4 leaves: with budget=2 (width 1 each), the
    // first two ADMITTED without needing eviction stay resident forever (a same-priority
    // newcomer can never evict an incumbent — `try_admit`'s `>=` skip rule) — so the
    // final resident pair reveals exactly which two were visited FIRST.
    let decisions = SiteDecisions::new([
        (root_output(RootId(1), addend_a), 100.0),
        (root_output(RootId(2), addend_b), 100.0),
        (root_output(RootId(3), l), 100.0),
        (root_output(RootId(4), r), 100.0),
    ]);
    let compiled = compile(&layer, &sched, 2, MaterializePolicy::Decisions { decisions, budget: 2 });

    let after_r0 = &compiled.resident_realized[0].1;
    assert!(after_r0.contains(&addend_a), "addend_a is visited first under both orderings");
    assert!(
        after_r0.contains(&addend_b),
        "FMA-partition order (addends before products) must admit addend_b 2nd, not l — \
         got resident {after_r0:?} (a materialize-shaped original-encounter-order lowering \
         would instead admit `l` here)"
    );
    assert!(!after_r0.contains(&l), "l must lose the 2-slot budget to addend_b under FMA-partition order");
    assert!(!after_r0.contains(&r), "r must lose the 2-slot budget to addend_b under FMA-partition order");
}
