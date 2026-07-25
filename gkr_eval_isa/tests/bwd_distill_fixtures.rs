//! Task-4 smoke test: distill every layer of the 12 pinned fixtures in both
//! backward regimes (spec §2.2).
//!
//! Per layer × regime this checks (i) `distill` completes without panicking,
//! (ii) the distilled root is VALUE-identical to the alpha-combined canonical
//! claim roots under a rewrite-aware reference evaluation (`LookupValue` leaf
//! ↦ its query expr — the backward semantics), and (iii) the pinned
//! `skipped_decoder` set, asserted exactly so coverage changes are loud.
//!
//! # The cache fence
//!
//! Post Task-2, the distilled `d.layer` replaces each same-layer cache cone
//! with a `Read(ReadPlace::CacheOutput{..})` fold leaf; the oracle here still
//! recomputes the ORIGINAL cone. The two agree only if the read side used to
//! evaluate the distilled root is WITNESS-CONSISTENT for those fenced places
//! (`common::CacheConsistentResolvers` — see its module doc and
//! `bwd_value_parity.rs`), so `got` is evaluated with the cache-consistent
//! resolver bundle while `expected` (the plain rewritten-cone oracle) stays on
//! the plain synthetic resolvers, matching the sibling G1 gate.

mod common;

use std::collections::{BTreeMap, BTreeSet, HashMap};

use common::{
    CacheConsistentResolvers, SyntheticResolvers, cache_consistent_resolvers, load_fixture,
    resolvers,
};
use cs::gkr_compiler::dag_ir::{
    ArenaBuilder, BatchingOrder, BwdRegime, ChallengeKey, ChallengePower, ChallengeRef, ClaimInfo,
    DagLayer, Expr, ExprId, Ext, ReadPlace, Resolvers, Root, RootGroup, RootId, RootOrigin,
    RootSlot, SourceKind, bwd_relation_units, bwd_roots, eval_layer_expr, eval_layer_root,
    lower_dag, validate,
};
use field::Field;
use gkr_eval_isa::bwd::compile::{BwdCompiledLayer, compile_distilled, spine_terms};
use gkr_eval_isa::bwd::distill::{DistilledLayer, StableBwdExprKey, distill};
use gkr_eval_isa::bwd::source::BwdSpecial;
use gkr_eval_isa::fwd::compile::build_cross_layer_field_map;
use gkr_eval_isa::fwd::isa::{DstLine, Instr, MovDir, OperandLine, Program};

/// Count VS-origin `FoldSource` operand USES in a compiled bwd program. These
/// use the O(k) multilinear closed form (Task 7): compute-only, zero DRAM, so
/// they add `fold_uses` but no `fold_traffic`. Read-origin folds gather 4
/// cells/use as before.
fn count_vs_fold_uses(c: &BwdCompiledLayer) -> usize {
    let mut n = 0usize;
    let mut visit = |op: &OperandLine| {
        if let OperandLine::Special { desc } = op {
            if let Some(BwdSpecial::FoldSource { origin }) = c.specials.get(*desc) {
                if origin.is_vs() {
                    n += 1;
                }
            }
        }
    };
    for instr in &c.program.instrs {
        match instr {
            Instr::Mov { src: Some(op), .. } => visit(op),
            Instr::Mov { src: None, .. } => {}
            Instr::Add { operands, .. } | Instr::Mul { operands, .. } => {
                operands.iter().for_each(&mut visit)
            }
            Instr::Fma { pairs, .. } => {
                for (l, r) in pairs {
                    visit(l);
                    visit(r);
                }
            }
        }
    }
    n
}

/// The 12 pinned Global Constraints fixtures: the 11 classic with-caches
/// layouts (same list as `fwd_vm_desc_census.rs`) + the unified machine.
const FIXTURES: &[&str] = &[
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

/// The pinned decoder-bearing set: `"{fixture_stem}[L{layer}]"` for every layer
/// whose claim cone reaches a `PeekDecoder` resolution key (skipped in BOTH
/// regimes). Update deliberately when decoder coverage changes.
/// EMPTY since the backward cache fence (commits 165ec73f..7fdc644e): every
/// corpus `PeekDecoder` cone is reachable only through a same-layer cache, so
/// `claim_cone_has_decoder` now stops descent at the cache root and every
/// former decoder-skipped `[L0]` layer is distillable (its fenced floor shows
/// up in `PINNED_B16_INFEASIBLE` instead) — identical to `bwd_value_parity.rs`.
const PINNED_SKIPPED_DECODER: &[&str] = &[];

/// Rewrite-aware reference evaluation of a canonical expr: identical to
/// `eval_layer_expr` except a `LookupValue` leaf evaluates to its QUERY expr
/// (the distillation rewrite), not the lookup resolver. Memoized per row.
fn eval_rewritten(
    layer: &DagLayer,
    e: ExprId,
    row: usize,
    r: &Resolvers<'_>,
    memo: &mut HashMap<ExprId, Ext>,
) -> Ext {
    if let Some(&v) = memo.get(&e) {
        return v;
    }
    let v = match &layer.exprs[e.0 as usize] {
        Expr::Source(sid) => match &layer.sources[sid.0 as usize].kind {
            SourceKind::LookupValue { query, .. } => eval_rewritten(layer, *query, row, r, memo),
            SourceKind::Constant { .. }
            | SourceKind::Challenge { .. }
            | SourceKind::Read { .. }
            | SourceKind::VirtualSetup { .. } => {
                // Delegate single-leaf evaluation to the authoritative evaluator
                // (a leaf expr has no LookupValue beneath it to rewrite).
                cs::gkr_compiler::dag_ir::eval_layer_expr(layer, e, row, r)
            }
        },
        Expr::Add(children) => {
            let mut acc = Ext::ZERO;
            for &c in children {
                let t = eval_rewritten(layer, c, row, r, memo);
                acc.add_assign(&t);
            }
            acc
        }
        Expr::Mul(children) => {
            let mut acc = Ext::ONE;
            for &c in children {
                let t = eval_rewritten(layer, c, row, r, memo);
                acc.mul_assign(&t);
            }
            acc
        }
    };
    memo.insert(e, v);
    v
}

/// beta^i challenge value as the distilled spine resolves it (i >= 1).
fn beta_i(r: &Resolvers<'_>, i: usize) -> Ext {
    let power = if i == 1 {
        ChallengePower::One
    } else {
        ChallengePower::Static(i as u32)
    };
    r.challenge.challenge(&ChallengeRef {
        key: ChallengeKey::ClaimBatching,
        power,
    })
}

#[test]
fn distill_all_fixtures_both_regimes() {
    let syn = SyntheticResolvers;
    let r = resolvers(&syn);
    let mut skipped: BTreeSet<String> = BTreeSet::new();
    let mut add_sub_nonempty_domain = false;

    for name in FIXTURES {
        let stem = common::schedule_stem(name);
        let artifact = load_fixture(name);
        let dag = lower_dag(&artifact).unwrap_or_else(|e| panic!("[{name}] lower_dag: {e}"));
        validate(&dag).unwrap_or_else(|e| panic!("[{name}] validate: {e}"));

        let cross = build_cross_layer_field_map(&dag);
        for (li, layer) in dag.layers.iter().enumerate() {
            // Witness-consistent read side for the DISTILLED root: a fenced
            // `CacheOutput` fold leaf reads as the per-row value of its
            // defining cone (see the module doc / `bwd_value_parity.rs`).
            let cc = CacheConsistentResolvers::new(layer);
            let cc_r = cache_consistent_resolvers(&cc);
            for regime in [BwdRegime::R0, BwdRegime::Ext] {
                let d = gkr_eval_isa::bwd::distill::distill(layer, regime, &cross, None);
                if d.skipped_decoder {
                    skipped.insert(format!("{stem}[L{li}]"));
                }

                // Canonical root provenance (Plan-6 Task 1): the same gate the
                // synthetic permutation test applies, over the whole corpus.
                assert_root_terms_canonical(layer, &d, &format!("{stem} L{li} {regime:?}"));

                // Value parity: distilled root == alpha-combined rewritten
                // canonical roots (holds regardless of skipped_decoder — the
                // rebuild itself is always well-defined).
                for row in [0usize, 1] {
                    let mut memo: HashMap<ExprId, Ext> = HashMap::new();
                    let mut expected = Ext::ZERO;
                    for (i, &rid) in bwd_roots(layer).iter().enumerate() {
                        let mut t = eval_rewritten(
                            layer,
                            layer.roots[rid.0 as usize].expr,
                            row,
                            &r,
                            &mut memo,
                        );
                        if i >= 1 {
                            t.mul_assign(&beta_i(&r, i));
                        }
                        expected.add_assign(&t);
                    }
                    let got = eval_layer_root(&d.layer, d.root, row, &cc_r);
                    assert_eq!(
                        got, expected,
                        "[{stem} L{li} {regime:?}] distilled root value mismatch at row {row}"
                    );
                }

                // The site domain over the REBUILT layer is non-empty for the
                // constraint-bearing add_sub layers (checked below).
                if *name == FIXTURES[0]
                    && regime == BwdRegime::R0
                    && !gkr_eval_isa::bwd::distill::distilled_site_domain(&d).is_empty()
                {
                    add_sub_nonempty_domain = true;
                }
            }
        }
    }

    println!("skipped_decoder set ({}):", skipped.len());
    for s in &skipped {
        println!("  {s}");
    }
    let pinned: BTreeSet<String> = PINNED_SKIPPED_DECODER
        .iter()
        .map(|s| s.to_string())
        .collect();
    assert_eq!(
        skipped, pinned,
        "skipped_decoder set drifted from the pinned expectation — update deliberately"
    );

    assert!(
        add_sub_nonempty_domain,
        "at least one add_sub distilled layer must expose a non-empty backward site domain"
    );
}

// ── Plan-6 Task 1: canonical root provenance (`DistilledLayer::root_terms`) ───

/// A synthetic canonical layer with three claim-only backward roots in three
/// distinct relation units (`relation_index` 0/1/2, so `bwd_relation_units`
/// yields three permutable units) whose BATCHING order is deliberately NOT the
/// root-index order: `batching.roots = [R2, R0, R1]`. "Root zero" (the unbatched
/// claim, beta exponent 0) is therefore `RootId(2)`, so an implementation that
/// keyed the unbatched slot off `RootId(0)` instead of `bwd_roots(layer)[0]`
/// fails the gates below. The three cones are structurally distinct (no two roots
/// intern to one rebuilt expression) but share read leaves, so cone re-interning
/// is still exercised.
fn synthetic_three_unit_layer() -> DagLayer {
    fn read_leaf(a: &mut ArenaBuilder, column: usize) -> ExprId {
        let s = a.intern_source(SourceKind::Read {
            place: ReadPlace::BaseLayerWitness { column },
        });
        a.source_expr(s)
    }
    fn claim_only_root(expr: ExprId, relation_index: usize) -> Root {
        Root {
            expr,
            materialize: None,
            claim: Some(ClaimInfo {
                origin: RootOrigin {
                    group: RootGroup::Gates,
                    relation_index,
                    slot: RootSlot::Constraint(0),
                },
            }),
        }
    }

    let mut a = ArenaBuilder::new();
    let x0 = read_leaf(&mut a, 0);
    let x1 = read_leaf(&mut a, 1);
    let x2 = read_leaf(&mut a, 2);
    let cone_a = a.add(vec![x0, x1]);
    let cone_b = a.mul(vec![x1, x2]);
    let cone_c = a.mul(vec![cone_a, x2]);

    DagLayer {
        sources: a.sources().to_vec(),
        exprs: a.exprs().to_vec(),
        roots: vec![
            claim_only_root(cone_a, 0),
            claim_only_root(cone_b, 1),
            claim_only_root(cone_c, 2),
        ],
        batching: BatchingOrder {
            roots: vec![RootId(2), RootId(0), RootId(1)],
        },
        resolutions: BTreeMap::new(),
    }
}

/// The `ChallengeRef` of a distilled `Challenge` leaf — what a batching factor
/// MUST be (a `ClaimBatching` power); anything else is a provenance bug.
fn challenge_ref_of(layer: &DagLayer, e: ExprId) -> ChallengeRef {
    match &layer.exprs[e.0 as usize] {
        Expr::Source(sid) => match &layer.sources[sid.0 as usize].kind {
            SourceKind::Challenge { reference } => reference.clone(),
            other => panic!("batching factor must be a Challenge leaf, got {other:?}"),
        },
        other => panic!("batching factor must be a leaf, got {other:?}"),
    }
}

/// Order-independent projection of one `DistilledRootTerm`. Distilled `ExprId`s
/// are relation-unit-ORDER dependent, so the value/batched exprs are compared
/// through their `StableBwdExprKey` provenance and the batching factor through
/// its (structurally stable) `ChallengeRef`.
#[derive(Clone, Debug, PartialEq, Eq)]
struct StableRootTerm {
    canonical_root: RootId,
    value: Option<StableBwdExprKey>,
    factor: Option<ChallengeRef>,
    batched: Option<StableBwdExprKey>,
}

fn stable_root_terms(d: &DistilledLayer) -> Vec<StableRootTerm> {
    d.root_terms
        .iter()
        .map(|t| StableRootTerm {
            canonical_root: t.canonical_root,
            value: d.stable_key(t.value_expr),
            factor: t.batching_factor.map(|f| challenge_ref_of(&d.layer, f)),
            batched: d.stable_key(t.batched_expr),
        })
        .collect()
}

/// Multiset (count map) of a slice — the order-independent comparison, identical
/// to `bwd_fragment_invariance.rs`.
fn multiset<T: std::hash::Hash + Eq + Clone>(v: &[T]) -> HashMap<T, usize> {
    let mut m: HashMap<T, usize> = HashMap::new();
    for x in v {
        *m.entry(x.clone()).or_insert(0) += 1;
    }
    m
}

/// The Task-1 provenance gate shared by the synthetic permutation test and the
/// corpus smoke above: `root_terms` is exactly `bwd_roots(canonical)` IN ORDER,
/// root zero (the first entry of that order) is UNSCALED, and every later entry
/// names the exact `ClaimBatching` power of its canonical batching position.
fn assert_root_terms_canonical(canonical: &DagLayer, d: &DistilledLayer, ctx: &str) {
    let order = bwd_roots(canonical);
    let got: Vec<RootId> = d.root_terms.iter().map(|t| t.canonical_root).collect();
    assert_eq!(
        got,
        order.to_vec(),
        "[{ctx}] root_terms must follow canonical bwd_roots order"
    );
    for (i, t) in d.root_terms.iter().enumerate() {
        match (i, t.batching_factor) {
            (0, None) => assert_eq!(
                t.batched_expr, t.value_expr,
                "[{ctx}] root zero is UNSCALED, so its batched term IS its value"
            ),
            (0, Some(_)) => panic!("[{ctx}] root zero must have no batching factor"),
            (_, None) => panic!("[{ctx}] batched root at position {i} lost its batching factor"),
            (_, Some(f)) => {
                let expected = ChallengeRef {
                    key: ChallengeKey::ClaimBatching,
                    power: if i == 1 {
                        ChallengePower::One
                    } else {
                        ChallengePower::Static(i as u32)
                    },
                };
                assert_eq!(
                    challenge_ref_of(&d.layer, f),
                    expected,
                    "[{ctx}] root at batching position {i} must name beta^{i}"
                );
                assert_ne!(
                    t.batched_expr, t.value_expr,
                    "[{ctx}] a batched root's term must differ from its unscaled value"
                );
            }
        }
    }
}

/// `root_terms` is a CANONICAL table: a relation-unit permutation changes the
/// construction order (and hence the distilled `ExprId` numbering) but must not
/// change the table's order, its root identities, or which entry is unbatched.
/// Also re-asserts (regression) that `FragmentTable`'s stable view stays
/// permutation-invariant on the same layer — `root_terms` is added ALONGSIDE the
/// fragment decomposition, not in place of it.
#[test]
fn distilled_root_terms_preserve_canonical_relation_order_and_batching() {
    let layer = synthetic_three_unit_layer();
    let cross = HashMap::new();
    assert_eq!(
        bwd_relation_units(&layer).len(),
        3,
        "the synthetic layer must expose three permutable relation units"
    );
    // Canonical batching order is NOT root-index order: root zero is RootId(2).
    assert_eq!(bwd_roots(&layer), &[RootId(2), RootId(0), RootId(1)]);

    let perms: [Option<Vec<usize>>; 3] = [None, Some(vec![2, 1, 0]), Some(vec![1, 2, 0])];
    for regime in [BwdRegime::R0, BwdRegime::Ext] {
        let mut baseline: Option<(Vec<StableRootTerm>, _, _)> = None;
        // Non-vacuity: a permutation must actually RENUMBER the distilled exprs,
        // otherwise the invariance assertions below would hold trivially.
        let mut raw: BTreeSet<Vec<ExprId>> = BTreeSet::new();
        for p in &perms {
            let d = distill(&layer, regime, &cross, p.as_deref());
            let ctx = format!("{regime:?} perm {p:?}");
            assert_root_terms_canonical(&layer, &d, &ctx);
            assert_eq!(
                d.root_terms[0].canonical_root,
                RootId(2),
                "[{ctx}] root zero is bwd_roots[0] (RootId(2)), not RootId(0)"
            );
            assert_eq!(
                d.root_terms[1].canonical_root,
                RootId(0),
                "[{ctx}] RootId(0) sits at batching position 1 here, so it IS batched"
            );

            raw.insert(d.root_terms.iter().map(|t| t.batched_expr).collect());
            let stable = stable_root_terms(&d);
            let frag = multiset(&d.fragments.stable_view(&d));
            let cinit = multiset(&d.fragments.stable_c_init(&d));
            match &baseline {
                None => baseline = Some((stable, frag, cinit)),
                Some((b_stable, b_frag, b_cinit)) => {
                    assert_eq!(
                        &stable, b_stable,
                        "[{ctx}] root_terms drifted under a relation-unit permutation"
                    );
                    assert_eq!(
                        &frag, b_frag,
                        "[{ctx}] FragmentTable::stable_view drifted under a relation-unit permutation"
                    );
                    assert_eq!(
                        &cinit, b_cinit,
                        "[{ctx}] FragmentTable::stable_c_init drifted under a relation-unit permutation"
                    );
                }
            }
        }
        assert!(
            raw.len() >= 2,
            "[{regime:?}] the permutations never renumbered a batched term — \
             the invariance assertions would be vacuous"
        );
        println!(
            "{regime:?}: root_terms invariant over {} permutations ({} distinct raw ExprId tuples)",
            perms.len(),
            raw.len()
        );
    }
}

/// Each entry keeps BOTH representations: the rebuilt UNSCALED root cone
/// (`value_expr`, value-equal to the canonical cone under the backward rewrite)
/// and its batched spine term (`batched_expr == beta^i · value_expr`, with
/// `batching_factor` naming beta^i). A table that stored only one of the two
/// would fail here — that is exactly what R0 `acc_c0` lowering needs to keep
/// apart (design §5.2).
#[test]
fn distilled_root_terms_distinguish_value_from_batched_term() {
    let syn = SyntheticResolvers;
    let r = resolvers(&syn);
    let layer = synthetic_three_unit_layer();
    let cross = HashMap::new();
    let d = distill(&layer, BwdRegime::R0, &cross, None);
    assert_eq!(d.root_terms.len(), bwd_roots(&layer).len());

    // Non-vacuity: three structurally distinct cones stay three distinct values.
    let mut values: Vec<ExprId> = d.root_terms.iter().map(|t| t.value_expr).collect();
    let n_values = values.len();
    values.sort_unstable();
    values.dedup();
    assert_eq!(
        values.len(),
        n_values,
        "distinct canonical cones must not collapse into one rebuilt value_expr"
    );

    for (i, t) in d.root_terms.iter().enumerate() {
        let canonical_expr = layer.roots[t.canonical_root.0 as usize].expr;
        assert_eq!(
            d.stable_key(t.value_expr),
            Some(StableBwdExprKey::Canonical(canonical_expr)),
            "position {i}: value_expr must be the rebuilt canonical cone of {:?}",
            t.canonical_root
        );

        // Value side: value_expr == the unscaled cone, batched_expr == beta^i · cone.
        for row in [0usize, 1] {
            let mut memo: HashMap<ExprId, Ext> = HashMap::new();
            let unscaled = eval_rewritten(&layer, canonical_expr, row, &r, &mut memo);
            assert_eq!(
                eval_layer_expr(&d.layer, t.value_expr, row, &r),
                unscaled,
                "position {i}: value_expr must evaluate to the UNSCALED canonical cone (row {row})"
            );
            let mut want = unscaled;
            if i >= 1 {
                want.mul_assign(&beta_i(&r, i));
            }
            assert_eq!(
                eval_layer_expr(&d.layer, t.batched_expr, row, &r),
                want,
                "position {i}: batched_expr must evaluate to beta^{i} · value (row {row})"
            );
        }

        // Structure side: the batched term is literally `Mul(beta^i, value_expr)`.
        match t.batching_factor {
            None => {
                assert_eq!(i, 0, "only root zero may be unbatched");
                assert_eq!(t.batched_expr, t.value_expr);
            }
            Some(f) => {
                assert_ne!(f, t.value_expr, "position {i}: factor must not BE the value");
                let children = match &d.layer.exprs[t.batched_expr.0 as usize] {
                    Expr::Mul(children) => children.clone(),
                    other => panic!("position {i}: batched_expr must be a Mul, got {other:?}"),
                };
                let mut got = children;
                got.sort_unstable();
                let mut want = vec![f, t.value_expr];
                want.sort_unstable();
                assert_eq!(
                    got, want,
                    "position {i}: batched_expr must be exactly beta^{i} · value_expr"
                );
                assert_eq!(
                    d.stable_key(t.batched_expr),
                    Some(StableBwdExprKey::BatchingTerm(t.canonical_root)),
                    "position {i}: the batched term's stable provenance is its canonical root"
                );
            }
        }
    }
}

// ── Task 5: compile smoke over every distillable layer, b16, both regimes ─────

/// Spec §3 terminal convention: no `GlobalMaterialize` anywhere; the last
/// instruction leaves the root value in acc (arith fold or `Mov AccFromSrc`).
fn assert_result_in_acc(p: &Program, ctx: &str) {
    assert!(!p.instrs.is_empty(), "[{ctx}] empty bwd program");
    for i in &p.instrs {
        if let Instr::Mov {
            dst: Some(DstLine::GlobalMaterialize { .. }),
            ..
        } = i
        {
            panic!("[{ctx}] bwd program must never emit GlobalMaterialize: {i:?}");
        }
    }
    match p.instrs.last().unwrap() {
        Instr::Add { .. } | Instr::Mul { .. } | Instr::Fma { .. } => {}
        Instr::Mov {
            dir: MovDir::AccFromSrc,
            ..
        } => {}
        other => panic!("[{ctx}] terminal instruction must leave the value in acc: {other:?}"),
    }
}

/// Distilled layer x regime instances whose placement FLOOR exceeds b16 —
/// `"{stem}[L{layer}][{regime}] floor={floor}"`, pinned exactly so drift is
/// loud. These WERE the wide delegation-circuit cones: the backward rebuild
/// INLINES every `LookupValue` query cone (fwd fences them behind terminal
/// resolution Specials), so `compile_reduction_virtual`/FMA pre-materialization
/// needed far more concurrent temps than the same layer's forward atoms.
///
/// SP1 (Task 5): EMPTY. These 12 overflow through the FMA path
/// (`try_compile_fma_virtual`), NOT the pure `compile_reduction_virtual` path;
/// `compile_distilled`'s legacy-first-fallback-to-streamed retry (Task 2's
/// one-Ext-cell streamed lowering under `stream_reductions = true`, which streams
/// BOTH reduction and FMA — these product-heavy cones collapse via the streamed
/// FMA sibling) brings every one of the former 12 wide `[L0]`/`[L1]` cones under
/// the b16 placement floor, so the measured residual collapsed to empty — identical set
/// to `bwd_value_parity.rs`. Kept as a pinned (rather than deleted) constant +
/// the floor-retry branch below stays live — a future circuit could reintroduce
/// a residual.
const PINNED_B16_INFEASIBLE: &[&str] = &[];

/// Task-5 smoke: `compile_distilled` at the committed b16 budget over EVERY
/// distillable (non-decoder) fixture layer, BOTH regimes, uncached (no bwd
/// genome exists yet — `decisions: None`). Cross-layer field map: WHOLE-CIRCUIT
/// (`build_cross_layer_field_map`), the same superset choice as the Task-4
/// smoke above — an upto-layer map would be a strict subset with no behavioral
/// difference for the layers it covers, so the simple superset is used
/// consistently for both bwd fixture harnesses.
#[test]
fn compile_distilled_all_fixtures_b16() {
    const BUDGET: usize = 16;
    let mut compiled = 0usize;
    let mut fold_layers = 0usize;
    let mut infeasible: BTreeSet<String> = BTreeSet::new();

    for name in FIXTURES {
        let stem = common::schedule_stem(name);
        let artifact = load_fixture(name);
        let dag = lower_dag(&artifact).unwrap_or_else(|e| panic!("[{name}] lower_dag: {e}"));
        validate(&dag).unwrap_or_else(|e| panic!("[{name}] validate: {e}"));
        let cross = build_cross_layer_field_map(&dag);

        for (li, layer) in dag.layers.iter().enumerate() {
            if bwd_roots(layer).is_empty() {
                continue; // nothing to prove backward
            }
            for regime in [BwdRegime::R0, BwdRegime::Ext] {
                let d = gkr_eval_isa::bwd::distill::distill(layer, regime, &cross, None);
                if d.skipped_decoder {
                    continue; // OUT of v1 in both regimes
                }
                let ctx = format!("{stem} L{li} {regime:?}");
                let c = match compile_distilled(&d, BUDGET, None) {
                    Ok(c) => c,
                    // A placement floor above b16 is the pinned known limitation
                    // (see PINNED_B16_INFEASIBLE); anything else is a hard failure.
                    Err(gkr_eval_isa::fwd::error::CompileError::BudgetBelowFloor {
                        floor, ..
                    }) => {
                        infeasible.insert(format!("{stem}[L{li}][{regime:?}] floor={floor}"));
                        continue;
                    }
                    Err(e) => panic!("[{ctx}] compile_distilled: {e:?}"),
                };
                compiled += 1;

                assert_result_in_acc(&c.program, &ctx);
                assert!(c.stats.program_lanes > 0, "[{ctx}] stats not populated");
                assert_eq!(
                    c.stats.op_counts.iter().sum::<usize>(),
                    c.stats.program_lanes,
                    "[{ctx}] op_counts must partition program_lanes"
                );
                assert!(
                    c.stats.max_live_cells <= BUDGET,
                    "[{ctx}] max_live_cells {} > budget {BUDGET}",
                    c.stats.max_live_cells
                );
                // A multi-term spine spills at least one partial → live cells.
                if spine_terms(&d).len() >= 2 {
                    assert!(
                        c.stats.max_live_cells > 0,
                        "[{ctx}] compound layer used no cells"
                    );
                }
                // Traffic-tally consistency (search-facing extension): every
                // Read-origin FoldSource use tallies 4 cells; VS-origin folds use
                // the O(k) closed form (Task 7) — 0 DRAM, so they add fold_uses
                // but NOT fold_traffic.
                let vs_fold_uses = count_vs_fold_uses(&c);
                assert_eq!(
                    c.stats_ext.fold_traffic,
                    4 * (c.stats_ext.fold_uses - vs_fold_uses),
                    "[{ctx}] Read-origin fold traffic is 4 cells/use ({vs_fold_uses} VS closed-form uses excluded)"
                );
                assert_eq!(
                    c.stats_ext.global, c.stats.dram_traffic,
                    "[{ctx}] stats_ext.global mirrors width-weighted Global traffic"
                );
                match regime {
                    // R0: Reads stay Global backings; only VirtualSetup descs exist,
                    // which are NOT FoldSources.
                    BwdRegime::R0 => assert_eq!(
                        c.stats_ext.fold_uses, 0,
                        "[{ctx}] R0 has no FoldSource descs"
                    ),
                    // Ext: every origin Read/VirtualSetup is a FoldSource — a layer
                    // whose program still reads Global would be a hook bypass.
                    BwdRegime::Ext => {
                        if c.stats_ext.fold_uses > 0 {
                            fold_layers += 1;
                        }
                        let mut global_ops = 0usize;
                        for instr in &c.program.instrs {
                            let mut f = |op: &OperandLine| {
                                if matches!(op, OperandLine::Source { .. }) {
                                    global_ops += 1;
                                }
                            };
                            match instr {
                                Instr::Add { operands, .. } | Instr::Mul { operands, .. } => {
                                    operands.iter().for_each(&mut f)
                                }
                                Instr::Fma { pairs, .. } => pairs.iter().for_each(|(l, r)| {
                                    f(l);
                                    f(r);
                                }),
                                Instr::Mov { src: Some(op), .. } => f(op),
                                Instr::Mov { src: None, .. } => {}
                            }
                        }
                        assert_eq!(
                            global_ops, 0,
                            "[{ctx}] Ext regime must lower every origin leaf via its \
                             FoldSource desc, never a Global backing"
                        );
                    }
                }
            }
        }
    }
    println!(
        "compiled {compiled} distilled layer x regime instances; {fold_layers} Ext instances with fold uses"
    );
    println!("b16-infeasible ({}):", infeasible.len());
    for s in &infeasible {
        println!("  {s}");
    }
    assert!(
        compiled > 0,
        "smoke must compile at least one distillable layer"
    );
    assert!(
        fold_layers > 0,
        "at least one Ext layer must exercise FoldSource operands"
    );
    let pinned: BTreeSet<String> = PINNED_B16_INFEASIBLE
        .iter()
        .map(|s| s.to_string())
        .collect();
    assert_eq!(
        infeasible, pinned,
        "b16-infeasible set drifted from the pinned expectation — update deliberately"
    );
}
