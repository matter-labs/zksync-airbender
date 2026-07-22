//! Task 3 target tests: `compile_layer`'s `decisions: Some(&SiteDecisions)` path — emitter-owned residency,
//! capacity, and eviction, driven by Task 2's `SiteDecisions`/`OccurrenceStreams`.
//! See `.superpowers/sdd/task-3-brief.md` for the exact semantics these tests pin.
//!
//! Layer/schedule builders follow `tests/stage3_schedule_driven.rs`'s `task1`/`task8`
//! synthetic patterns (single-gate `Compute`-classified artifact layer, `atom_root`
//! Export sinks, a trivial schedule with an empty `sites` genome — schema v2
//! (Task 4) has no persisted per-step residency at all, and `Some`-decisions, like
//! `decisions: None`, drives root-compile order purely from `order`).

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
use gkr_eval_isa::fwd::compile::compile_layer;
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

fn constant(value: u32) -> SourceInfo {
    SourceInfo { kind: SourceKind::Constant { value } }
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

/// A trivial no-op schedule: `Some`-decisions, like `decisions: None`, only reads
/// the atom order — schema v2 has no persisted per-step residency for either mode
/// to consult. Phase 1: the flat `order` is carried as one `RelationUnit`'s
/// `atom_roots` (every root here is `(Gates, 0)`, matching the canonical
/// single-unit decomposition), so `atom_order()` reproduces `order` exactly.
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

fn root_output(root: RootId, value: ExprId) -> SiteKey {
    SiteKey { root, consumer: SiteConsumer::RootOutput, value }
}

fn site(root: RootId, consumer_expr: ExprId, input_index: u32, value: ExprId) -> SiteKey {
    SiteKey { root, consumer: SiteConsumer::Expr { expr: consumer_expr, input_index }, value }
}

/// A cross-layer Ext DRAM read leaf: `SourceKind::Read` (so it reaches DRAM and is
/// admissible) whose field the cross map resolves to `Ext` (width 4). This is the only
/// way to build an Ext value that is a genuine cache candidate — a bare `challenge()`
/// leaf recomputes for free and is (correctly) refused by the reaches-DRAM admission gate.
fn ext_dram_read(offset: usize) -> (SourceInfo, ReadPlace) {
    let place = ReadPlace::CacheOutput { layer: 0, offset };
    (SourceInfo { kind: SourceKind::Read { place: place.clone() } }, place)
}

fn compile(
    layer: &DagLayer,
    sched: &LayerSchedule,
    budget: usize,
    decisions: Option<&SiteDecisions>,
) -> gkr_eval_isa::fwd::context::CompiledLayer {
    compile_with_cross(layer, sched, budget, decisions, &HashMap::new())
}

fn compile_with_cross(
    layer: &DagLayer,
    sched: &LayerSchedule,
    budget: usize,
    decisions: Option<&SiteDecisions>,
    cross: &HashMap<ReadPlace, FieldKind>,
) -> gkr_eval_isa::fwd::context::CompiledLayer {
    let art = compute_artifact_layer();
    compile_layer(layer, &art, &BTreeMap::new(), cross, sched, budget, decisions)
        .expect("compile_layer")
}

// ── Test 1: cache hit beats the uncached (`decisions: None`) compile on the caching metric ──

/// High-priority reused value is served from residency (1 compute, no recompute): the cached
/// compile reads strictly less DRAM traffic than the uncached compile of the same layer, and
/// computes the shared expression `s` exactly once rather than twice.
#[test]
fn decisions_cache_hit_beats_uncached() {
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
    let decisions_compiled = compile(&layer, &sched, 1, Some(&decisions));
    let uncached_compiled = compile(&layer, &sched, 16, None);

    // The caching benefit here is a DRAM-traffic / recompute win, NOT an instruction-count
    // win. On this trivial synthetic (`s` is a single Add of two leaves), caching `s` costs
    // a store + reload (2 MOVs) that exactly TIES recomputing `s` (load + add, 2 ops) on
    // instruction count — so both programs are 8 instrs after the codegen-quality pass.
    // History: the RR site-gate fix shrank the old transient x/y admit+evict overhead
    // (11→9 decisions); the F5 dead-admission rule then peeled the last transient x/y
    // admission that reached a cell but was never read back out of BOTH paths (uncached
    // 12→8, decisions 9→8), which is why raw instr count no longer separates them. What
    // caching actually buys is measured by `dram_traffic` (the S3 primary objective) and the
    // recompute count below.
    assert_eq!(decisions_compiled.program.instrs.len(), 8, "decisions instr-count pin (tied post-F5)");
    assert_eq!(uncached_compiled.program.instrs.len(), 8, "uncached instr-count pin (tied post-F5)");

    // "1 compute, no recompute": `s` is the layer's only Add, computed ONCE when cached and
    // TWICE when uncached (recomputed for R1).
    assert_eq!(
        decisions_compiled.stats.op_counts[gkr_eval_isa::fwd::stats::OP_ADD], 1,
        "cached: s (the only Add) computed exactly once",
    );
    assert_eq!(
        uncached_compiled.stats.op_counts[gkr_eval_isa::fwd::stats::OP_ADD], 2,
        "uncached: s recomputed for R1 → the Add appears twice",
    );

    // The caching win: strictly less DRAM traffic. Cached reads x,y,x2,x3 once each (=4);
    // uncached re-reads x,y to recompute s (=6). This is the property the test exists to pin.
    assert_eq!(decisions_compiled.stats.dram_traffic, 4, "cached DRAM-traffic pin");
    assert_eq!(uncached_compiled.stats.dram_traffic, 6, "uncached DRAM-traffic pin");
    assert!(
        decisions_compiled.stats.dram_traffic < uncached_compiled.stats.dram_traffic,
        "Decisions ({}) must read strictly less DRAM traffic than uncached ({}) once s is cached",
        decisions_compiled.stats.dram_traffic,
        uncached_compiled.stats.dram_traffic,
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
    fn build_layer() -> (DagLayer, ExprId, ExprId, HashMap<ReadPlace, FieldKind>) {
        let (e_src, e_place) = ext_dram_read(0);
        let layer = DagLayer {
            sources: vec![witness(0), e_src],
            exprs: vec![
                Expr::Source(SourceId(0)),    // 0 = B (Base DRAM leaf)
                Expr::Source(SourceId(1)),    // 1 = E (Ext DRAM leaf, via cross map)
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
        let cross: HashMap<ReadPlace, FieldKind> = [(e_place, FieldKind::Ext)].into();
        (layer, ExprId(0), ExprId(1), cross)
    }

    let run = |b_priority: f64, e_priority: f64| -> gkr_eval_isa::fwd::context::CompiledLayer {
        let (layer, b, e, cross) = build_layer();
        let order = vec![RootId(0), RootId(1), RootId(2), RootId(3)];
        let sched = trivial_schedule(order);
        let decisions = SiteDecisions::new([
            (site(RootId(2), ExprId(2), 0, b), b_priority),
            (site(RootId(3), ExprId(3), 0, e), e_priority),
        ]);
        compile_with_cross(&layer, &sched, 4, Some(&decisions), &cross)
    };

    // (a) B's priority LOWER than E's admitting priority: B is evicted, E admitted.
    let (_, b, e, _) = build_layer();
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

// ── Test 2b: non-domain leaves (interior challenge/const) are never admitted ─────────

/// RR-invariant (site-gate fix): the emitter must NEVER admit a non-domain value into
/// residency. A challenge or constant used as an INTERIOR operand (not itself a root's
/// materialized expr) carries zero DRAM traffic — it is an `Ldc` read, not a backing
/// read — so caching it cannot save a read; it only squats a residency slot. Even with
/// spare budget AND a genome that explicitly assigns those interior sites a huge
/// priority, `try_admit`'s `is_admittable` gate (cs `enumerate_site_domain`: cacheable ∧
/// fan-out ≥ 2) refuses them. A genuinely cacheable reused DRAM leaf in the same layer is
/// still admitted, so the gate is discriminating, not blanket-refusing. Pre-fix, the
/// neutral/spare-budget path opportunistically cached these — the `derivedA(...)`/`#2`-in-
/// smem disassembly that motivated this fix.
#[test]
fn interior_challenge_and_constant_are_never_admitted_even_with_high_priority_genes() {
    // e0/e1 = w0/w1 (DRAM Read leaves); e2 = c (challenge); e3 = k (constant). c is a Mul
    // factor in R0 and R1 (fan-out 2); k is an Add addend in R2 and R3 (fan-out 2); w0 is
    // reused in R0 and R2 (fan-out 2). None of c/k/w0 is any root's expr, so c/k stay
    // non-cacheable (interior challenge/const) while w0 is a legit cacheable∧fan-out≥2
    // DRAM leaf. (A challenge that IS a root's own expr is a materialized backing and thus
    // legitimately cacheable — see `eviction_respects_priority_and_width`; this test
    // isolates the INTERIOR-operand case the disasm exposed.)
    let (w0, c, k) = (ExprId(0), ExprId(2), ExprId(3));
    let layer = DagLayer {
        sources: vec![witness(0), witness(1), challenge(), constant(7)],
        exprs: vec![
            Expr::Source(SourceId(0)),             // 0 = w0 (DRAM, reused)
            Expr::Source(SourceId(1)),             // 1 = w1 (DRAM)
            Expr::Source(SourceId(2)),             // 2 = c  (challenge, interior)
            Expr::Source(SourceId(3)),             // 3 = k  (constant, interior)
            Expr::Mul(vec![ExprId(0), ExprId(2)]), // 4 = R0 = w0 * c
            Expr::Mul(vec![ExprId(1), ExprId(2)]), // 5 = R1 = w1 * c
            Expr::Add(vec![ExprId(0), ExprId(3)]), // 6 = R2 = w0 + k
            Expr::Add(vec![ExprId(1), ExprId(3)]), // 7 = R3 = w1 + k
        ],
        roots: vec![
            atom_root(ExprId(4), 0),
            atom_root(ExprId(5), 1),
            atom_root(ExprId(6), 2),
            atom_root(ExprId(7), 3),
        ],
        batching: BatchingOrder { roots: vec![RootId(0), RootId(1), RootId(2), RootId(3)] },
        resolutions: BTreeMap::new(),
    };
    let order = vec![RootId(0), RootId(1), RootId(2), RootId(3)];
    let sched = trivial_schedule(order);
    // Adversarial genome: MAX priority on c's and k's interior 2nd-occurrence demand
    // sites. Pre-fix (or with the gate removed) this forced their admission; post-fix
    // `is_admittable` refuses them regardless of gene value.
    let decisions = SiteDecisions::new([
        (site(RootId(1), ExprId(5), 1, c), 1000.0),
        (site(RootId(3), ExprId(7), 1, k), 1000.0),
    ]);
    let compiled = compile(&layer, &sched, 16, Some(&decisions));

    for (step, (_, after)) in compiled.resident_realized.iter().enumerate() {
        assert!(
            !after.contains(&c),
            "interior challenge {c:?} must NEVER be resident (non-domain), but was after step {step}: {after:?}"
        );
        assert!(
            !after.contains(&k),
            "interior constant {k:?} must NEVER be resident (non-domain), but was after step {step}: {after:?}"
        );
    }
    // Non-vacuous: the genuinely cacheable reused DRAM leaf w0 IS admitted at some step
    // (spare budget), so the gate discriminates rather than refusing everything.
    assert!(
        compiled.resident_realized.iter().any(|(_, after)| after.contains(&w0)),
        "reused DRAM leaf {w0:?} (cacheable ∧ fan-out≥2) must still be admitted; snapshots: {:?}",
        compiled.resident_realized.iter().map(|(_, a)| a).collect::<Vec<_>>()
    );
}

// ── Test 3: a dead value's cell is REUSED (fill+placement), not force-evicted ───────

/// Under fill-then-trim the whole cache set is admitted with eviction disabled, and
/// `plan_placement` (lifetime-aware) reuses a value's cell the instant its live range
/// ends. So a value A whose last use precedes a later value C's birth shares A's cell
/// with C automatically — all of A/D/C cache in a 2-cell budget with NO eviction and NO
/// re-read, where the old greedy would have had to force-evict dead A to fit C. This
/// pins the improvement: dead-slot reuse replaces dead-value eviction.
#[test]
fn dead_value_slot_reused_without_eviction() {
    // A: produced (R0), probed once (R1) — last use R1, then dead.
    // D: produced (R2), probed (R4). C: produced (R3), probed (R5). D and C overlap
    // (both live across [R3, R4]), but A is already dead by R2, so peak live = 2 = budget.
    // Probes wrap their leaf in a distinct `Add([leaf])` expr (see
    // `eviction_respects_priority_and_width`'s doc: two roots sharing the SAME bare leaf
    // as `root.expr` would collapse into one `materialize_if_root` event).
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
            atom_root(ExprId(3), 1), // R1: A probe (A's last use — dead after)
            atom_root(ExprId(1), 2), // R2: D produce
            atom_root(ExprId(2), 3), // R3: C produce (C is born after A died)
            atom_root(ExprId(4), 4), // R4: D probe
            atom_root(ExprId(5), 5), // R5: C probe
        ],
        batching: BatchingOrder {
            roots: vec![RootId(0), RootId(1), RootId(2), RootId(3), RootId(4), RootId(5)],
        },
        resolutions: BTreeMap::new(),
    };
    let order = vec![RootId(0), RootId(1), RootId(2), RootId(3), RootId(4), RootId(5)];
    let sched = trivial_schedule(order);
    let (a, d, c) = (ExprId(0), ExprId(1), ExprId(2));

    // Cache all three (each is a witness DRAM leaf with fan-out 2 → admittable ∧ reaches
    // DRAM). Under fill, priorities are irrelevant (nothing is evicted), so any genome
    // works; give each probe occurrence a positive gene for clarity.
    let decisions = SiteDecisions::new([
        (site(RootId(3), ExprId(3), 0, a), 1.0),
        (site(RootId(4), ExprId(4), 0, d), 1.0),
        (site(RootId(5), ExprId(5), 0, c), 1.0),
    ]);
    let cached = compile(&layer, &sched, 2, Some(&decisions));
    let uncached = compile(&layer, &sched, 2, None);

    // Uncached re-reads every occurrence: A(R0,R1) + D(R2,R4) + C(R3,R5) = 6 DRAM reads.
    assert_eq!(uncached.stats.dram_reads, 6, "uncached re-reads each of A/D/C twice");
    // Cached fits all three in a 2-cell budget with zero re-reads — dead A's cell is
    // REUSED by placement for C, no eviction required. 3 = one read per distinct leaf.
    assert_eq!(
        cached.stats.dram_reads, 3,
        "fill caches A/D/C in budget 2 via dead-slot reuse (no eviction, no re-read)"
    );
    assert!(cached.stats.max_live_cells <= 2, "peak live must fit the 2-cell budget");
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
    let decisions_compiled = compile(&layer, &sched, 16, Some(&decisions));
    let uncached_compiled = compile(&layer, &sched, 16, None);

    assert_eq!(uncached_compiled.stats.dram_reads, 2, "uncached (decisions: None) reads W twice");
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

    let d1 = build_decisions();
    let d2 = build_decisions();
    let c1 = compile(&layer, &sched, 1, Some(&d1));
    let c2 = compile(&layer, &sched, 1, Some(&d2));

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
        // Task 8b: `Decisions.budget` is now the SAME single budget that bounds
        // placement (demand-driven eviction — no separate resident-admission cap;
        // see `lower.rs`'s `DecisionsState`), so both arguments must agree. `2` is
        // the tightest budget this Mul(s,s)/Mul(s,z) shape can compile at (two
        // concurrent Base operands for a product's lhs/rhs) while still forcing
        // admission/eviction to fire under the extreme adversarial priorities.
        let compiled = compile(&layer, &sched, 2, Some(&decisions));

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
    let compiled = compile(&layer, &sched, 2, Some(&decisions));

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

// ── Task 8c: generation-identity readmission ────────────────────────────────────────

/// Adversarial layer engineered to hit ADMIT -> EVICT -> RE-ADMIT -> SERVE for the
/// same real `ExprId` (B) within one layer compile, at budget=1 (a single Base cell —
/// B and C can never coexist). Sequence (bare-leaf roots produce, `Add([leaf])`
/// wrapper roots probe, per this file's established pattern):
///
///   R0: B produce (admits B, budget has free capacity).
///   R1: C produce — evicts B (C's 2nd-occurrence priority HIGH beats B's 2nd-occurrence
///       priority LOW) — `evicted_ever` now contains B.
///   R2: C probe — drains C's last occurrence (C goes dead, still resident).
///   R3: B probe #2 — B is no longer `defined`, so this demand re-triggers `try_admit`;
///       B's 3rd-occurrence priority is a plain positive finite value, which trivially
///       beats dead C (`NEG_INFINITY`), so B is RE-ADMITTED under a FRESH generation id
///       (Task 8c: `evicted_ever` no longer blocks this — it now only decides whether
///       the readmission needs a fresh identity).
///   R4: B probe #3 — served from B's cell (the fresh generation, not the real ExprId's
///       original — now-stale — cell).
///
/// Pre-fix (`never_readmit`) RED: R3's `try_admit(B, ..)` would hit
/// `ds.never_readmit.contains(&v)` and return `false` unconditionally (B was evicted at
/// R1) — R3/R4 would both recompute B from its source instead of caching it, i.e.
/// `resident_realized[3].1` would NOT contain B. This is asserted directly below by a
/// literal revert of the fix (see the test's trailing comment for the exact command).
///
/// Post-fix GREEN (this test, against the current emitter): the compile succeeds,
/// `plan_placement`'s peak (`stats.max_live_cells`) never exceeds the budget, B IS
/// resident again after R3, and every root's interpreted value matches the
/// `eval_layer_root` oracle across several rows — i.e. the two disjoint generations
/// never get collapsed into one over-wide `plan_placement` liveness interval, and
/// nothing about the fresh generation identity leaks into the observable value.
#[test]
fn readmission_after_eviction_gets_fresh_generation_and_stays_placement_feasible() {
    let layer = DagLayer {
        sources: vec![witness(0), witness(1)],
        exprs: vec![
            Expr::Source(SourceId(0)), // 0 = B
            Expr::Source(SourceId(1)), // 1 = C
            Expr::Add(vec![ExprId(1)]), // 2 = C-probe wrapper
            Expr::Add(vec![ExprId(0)]), // 3 = B-probe #2 wrapper (triggers re-admission)
            Expr::Add(vec![ExprId(0)]), // 4 = B-probe #3 wrapper (served from new generation)
        ],
        roots: vec![
            atom_root_field(ExprId(0), 0, FieldKind::Base), // R0: B produce
            atom_root_field(ExprId(1), 1, FieldKind::Base), // R1: C produce (evicts B)
            atom_root(ExprId(2), 2),                        // R2: C probe (drains C)
            atom_root(ExprId(3), 3),                        // R3: B probe #2 (re-admits B)
            atom_root(ExprId(4), 4),                        // R4: B probe #3 (served)
        ],
        batching: BatchingOrder {
            roots: vec![RootId(0), RootId(1), RootId(2), RootId(3), RootId(4)],
        },
        resolutions: BTreeMap::new(),
    };
    let b = ExprId(0);
    let order = vec![RootId(0), RootId(1), RootId(2), RootId(3), RootId(4)];
    let sched = trivial_schedule(order);

    let decisions = SiteDecisions::new([
        (site(RootId(3), ExprId(3), 0, b), -100.0), // B's occ#2: LOW (loses to C at R1)
        (site(RootId(2), ExprId(2), 0, ExprId(1)), 100.0), // C's occ#2: HIGH (evicts B at R1)
        (site(RootId(4), ExprId(4), 0, b), 1.0),    // B's occ#3: beats dead C at R3
    ]);
    let compiled = compile(&layer, &sched, 1, Some(&decisions));

    // Eviction fired as engineered: B is gone after R1, back after R3.
    assert!(!compiled.resident_realized[1].1.contains(&b), "C's admission must evict B at R1");
    assert!(
        compiled.resident_realized[3].1.contains(&b),
        "B must be RE-ADMITTED at R3 now that `never_readmit` no longer blocks it \
         (resident set after R3: {:?})",
        compiled.resident_realized[3].1
    );

    // Placement agreement: the tracker's admission decisions must still be realizable
    // by `plan_placement` within the SAME budget (compile_layer already
    // chains emit -> plan_placement; `compile()` unwraps `Ok`, so reaching here at all
    // is half the proof — this pins the numeric peak too).
    assert!(
        compiled.stats.max_live_cells <= 1,
        "placement peak {} must not exceed budget 1",
        compiled.stats.max_live_cells
    );

    // Value parity vs the pure oracle, across several rows.
    let sr = SyntheticResolvers;
    let mut checks = 0usize;
    for row in [0usize, 1, 2, 5] {
        let outs = interpret_layer_row(&compiled, &layer, &resolvers(&sr), row).unwrap();
        for (rid, _) in &compiled.root_outputs {
            let got = outs.by_root[rid];
            let want = eval_layer_root(&layer, *rid, row, &resolvers(&sr));
            assert_eq!(got, want, "row {row} root {rid:?} mismatch under readmission");
            checks += 1;
        }
    }
    assert!(checks > 0, "vacuous");
}
