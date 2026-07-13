//! Task 8: smoke test for the backward schedule-search ADAPTER
//! (`gkr_eval_isa::bwd::search::search_bwd_layer`).
//!
//! Two decoder-free picks per REV2 (add_sub/shift L0 are decoder-skipped):
//!   * bigint L0, regime R0, budget 96 (>= the pinned floor 83 — feasible),
//!   * blake2_with_extended_control L0, regime Ext, budget 16 (feasible — NOT in
//!     `PINNED_B16_INFEASIBLE`), the Ext-fold pick so the search sees FoldSource
//!     traffic via `stats_ext.fold_traffic`.
//!
//! Per pick this asserts:
//!   (i)   the outcome decisions compile FEASIBLY at the pick's budget;
//!   (ii)  outcome traffic (global + fold_traffic) <= the no-decisions compile at
//!         the same budget (non-regression);
//!   (iii) `unit_permutation` round-trips through re-distillation with identical
//!         G1-style row values on 8 sampled rows (the permutation is value-
//!         identical by Add-commutativity — the shared role/fold transform
//!         `role_combine`/`sumcheck_fold_point` is applied at the leaves, mirroring
//!         `tests/bwd_value_parity.rs`'s oracle).

mod common;

use std::collections::HashMap;

use common::{lift, load_fixture, resolvers, SyntheticResolvers};
use cs::gkr_compiler::dag_ir::{
    bwd_roots, eval_layer_expr, lower_dag, validate, BwdRegime, ChallengeKey, ChallengePower,
    ChallengeRef, DagLayer, Expr, ExprId, Ext, Resolvers, SourceKind,
};
use field::{Field, PrimeField};
use gkr_eval_isa::bwd::compile::compile_distilled;
use gkr_eval_isa::bwd::distill::distill;
use gkr_eval_isa::bwd::interp::{role_combine, sumcheck_fold_point, Role};
use gkr_eval_isa::bwd::search::{
    search_bwd_layer, BwdOrderMutation, BwdSearchConfig, BwdSeedStrategy,
};
use gkr_eval_isa::fwd::compile::build_cross_layer_field_map;
use gkr_eval_isa::fwd::error::CompileError;

// ── G1-style oracle (scoped copy of tests/bwd_value_parity.rs, two layers) ────

/// beta^i as the distilled spine resolves it (i >= 1).
fn beta_i(r: &Resolvers<'_>, i: usize) -> Ext {
    let power = if i == 1 { ChallengePower::One } else { ChallengePower::Static(i as u32) };
    r.challenge.challenge(&ChallengeRef { key: ChallengeKey::ClaimBatching, power })
}

/// Evaluate canonical (or distilled) expr `e` at (`regime`, `role`, `row`,
/// `round`), applying the SHARED role+fold transform at every `Read`/
/// `VirtualSetup` leaf — identical to `bwd_value_parity::eval_oracle`.
#[allow(clippy::too_many_arguments)]
fn eval_oracle(
    layer: &DagLayer,
    e: ExprId,
    regime: BwdRegime,
    role: Role,
    row: usize,
    round: u8,
    ch: &[Ext],
    orig: &SyntheticResolvers,
    plain: &Resolvers<'_>,
    memo: &mut HashMap<ExprId, Ext>,
) -> Ext {
    if let Some(&v) = memo.get(&e) {
        return v;
    }
    let v = match &layer.exprs[e.0 as usize] {
        Expr::Source(sid) => match &layer.sources[sid.0 as usize].kind {
            SourceKind::LookupValue { query, .. } => {
                eval_oracle(layer, *query, regime, role, row, round, ch, orig, plain, memo)
            }
            SourceKind::Read { place } => {
                let depth = if regime == BwdRegime::Ext { round } else { 0 };
                let base = |z: usize| {
                    use cs::gkr_compiler::dag_ir::ReadResolver;
                    orig.read(place, z)
                };
                let a = sumcheck_fold_point(&base, 2 * row, depth, ch).unwrap();
                let b = sumcheck_fold_point(&base, 2 * row + 1, depth, ch).unwrap();
                role_combine(role, a, b)
            }
            SourceKind::VirtualSetup { kind } => {
                let base = |z: usize| {
                    use cs::gkr_compiler::dag_ir::VirtualSetupResolver;
                    lift(orig.virtual_setup(kind, z))
                };
                let a = sumcheck_fold_point(&base, 2 * row, round, ch).unwrap();
                let b = sumcheck_fold_point(&base, 2 * row + 1, round, ch).unwrap();
                role_combine(role, a, b)
            }
            SourceKind::Constant { .. } | SourceKind::Challenge { .. } => {
                eval_layer_expr(layer, e, row, plain)
            }
        },
        Expr::Add(children) => {
            let ch_ids = children.clone();
            let mut acc = Ext::ZERO;
            for c in ch_ids {
                acc.add_assign(&eval_oracle(layer, c, regime, role, row, round, ch, orig, plain, memo));
            }
            acc
        }
        Expr::Mul(children) => {
            let ch_ids = children.clone();
            let mut acc = Ext::ONE;
            for c in ch_ids {
                acc.mul_assign(&eval_oracle(layer, c, regime, role, row, round, ch, orig, plain, memo));
            }
            acc
        }
    };
    memo.insert(e, v);
    v
}

/// `Σ_i beta^i · eval(root_i)` (root 0 unscaled) over the canonical `bwd_roots`
/// batching order — the ground-truth value the permuted distilled root must match.
#[allow(clippy::too_many_arguments)]
fn oracle_root(
    layer: &DagLayer,
    regime: BwdRegime,
    role: Role,
    row: usize,
    round: u8,
    ch: &[Ext],
    orig: &SyntheticResolvers,
    plain: &Resolvers<'_>,
) -> Ext {
    let mut memo: HashMap<ExprId, Ext> = HashMap::new();
    let mut acc = Ext::ZERO;
    for (i, &rid) in bwd_roots(layer).iter().enumerate() {
        let expr = layer.roots[rid.0 as usize].expr;
        let mut t = eval_oracle(layer, expr, regime, role, row, round, ch, orig, plain, &mut memo);
        if i >= 1 {
            t.mul_assign(&beta_i(plain, i));
        }
        acc.add_assign(&t);
    }
    acc
}

// ── The smoke ─────────────────────────────────────────────────────────────────

/// One pick: (fixture file, layer index, regime, budget).
struct Pick {
    name: &'static str,
    layer: usize,
    regime: BwdRegime,
    budget: usize,
}

#[test]
fn search_bwd_layer_smoke() {
    // Base-subfield round challenges (fold depth 1 exercises the fold transform).
    let round_challenges: Vec<Ext> = [3u32, 5, 7]
        .into_iter()
        .map(|k| lift(cs::gkr_compiler::dag_ir::Bf::from_u32_with_reduction(k)))
        .collect();
    let round: u8 = 1;
    let role = Role::T0;

    let syn = SyntheticResolvers;
    let plain = resolvers(&syn);

    let picks = [
        Pick {
            name: "bigint_with_extended_control_layout_gkr.json",
            layer: 0,
            regime: BwdRegime::R0,
            budget: 96,
        },
        Pick {
            name: "blake2_with_extended_control_layout_gkr.json",
            layer: 0,
            regime: BwdRegime::Ext,
            budget: 16,
        },
    ];

    for pick in &picks {
        let artifact = load_fixture(pick.name);
        let dag = lower_dag(&artifact).unwrap_or_else(|e| panic!("[{}] lower_dag: {e}", pick.name));
        validate(&dag).unwrap_or_else(|e| panic!("[{}] validate: {e}", pick.name));
        let cross = build_cross_layer_field_map(&dag);
        let layer = &dag.layers[pick.layer];

        // Baseline: no-decisions compile at the pick's budget.
        let d0 = distill(layer, pick.regime, &cross, None);
        assert!(!d0.skipped_decoder, "[{}] pick must be decoder-free", pick.name);
        let baseline = compile_distilled(&d0, pick.budget, None)
            .unwrap_or_else(|e| panic!("[{}] baseline compile: {e:?}", pick.name));
        let baseline_traffic = baseline.stats_ext.global + baseline.stats_ext.fold_traffic;

        // Run the search (tiny smoke config).
        let cfg = BwdSearchConfig {
            pop: 4,
            evals: 40,
            seed: 0,
            mutation_sigma: 0.2,
            seed_strategy: BwdSeedStrategy::StructureAware,
            order_mutation: BwdOrderMutation::ReuseEdgeRelocate,
        };
        let outcome = search_bwd_layer(layer, pick.regime, &cross, pick.budget, &cfg);
        let out_traffic = outcome.stats.global + outcome.stats.fold_traffic;

        // Both picks have caching headroom at their budgets: the GA finds a
        // strictly-better candidate, so the outcome carries real decisions (the
        // fallback branch is covered by the floor-budget test below).
        assert!(
            outcome.decisions.is_some(),
            "[{}] expected a strictly-improving Some(decisions) outcome",
            pick.name
        );

        // (i) outcome decisions compile feasibly at the pick's budget. The
        // decisions are keyed to the WINNING permutation's distilled ExprIds, so
        // they must be replayed against a distill of that same permutation (the
        // intended consumer contract — decisions + unit_permutation used
        // together; `decisions: None` = the no-decisions baseline outcome).
        let d_perm = distill(layer, pick.regime, &cross, Some(&outcome.unit_permutation));
        let recompiled = match compile_distilled(&d_perm, pick.budget, outcome.decisions.as_ref())
        {
            Ok(c) => c,
            Err(CompileError::BudgetBelowFloor { floor, .. }) => panic!(
                "[{}] outcome decisions infeasible at budget {} (floor {floor})",
                pick.name, pick.budget
            ),
            Err(e) => panic!("[{}] outcome decisions compile: {e:?}", pick.name),
        };
        // The re-compile under the outcome decisions reproduces the reported stats.
        let recompiled_traffic = recompiled.stats_ext.global + recompiled.stats_ext.fold_traffic;
        assert_eq!(
            recompiled_traffic, out_traffic,
            "[{}] re-compiled traffic must reproduce outcome.stats",
            pick.name
        );

        // (ii) non-regression: outcome traffic <= no-decisions baseline. This
        // now holds BY CONSTRUCTION — `search_bwd_layer` evaluates the
        // `None`-decisions baseline itself and returns it whenever the GA's best
        // is infeasible or not strictly better; asserted anyway as the gate.
        assert!(
            out_traffic <= baseline_traffic,
            "[{}] regression: outcome traffic {out_traffic} > baseline {baseline_traffic}",
            pick.name
        );

        // (iii) unit_permutation round-trips through re-distillation with identical
        //       G1-style row values on 8 sampled rows (reusing `d_perm` above).
        let d_perm_root_expr = d_perm.layer.roots[d_perm.root.0 as usize].expr;
        for row in 0..8usize {
            let mut memo: HashMap<ExprId, Ext> = HashMap::new();
            let got = eval_oracle(
                &d_perm.layer, d_perm_root_expr, pick.regime, role, row, round, &round_challenges,
                &syn, &plain, &mut memo,
            );
            let expected =
                oracle_root(layer, pick.regime, role, row, round, &round_challenges, &syn, &plain);
            assert_eq!(
                got, expected,
                "[{}] permuted distilled root value mismatch at row {row}",
                pick.name
            );
        }

        println!(
            "[{}] L{} {:?} b{}: baseline_traffic={baseline_traffic} outcome_traffic={out_traffic} \
             (global={} fold_traffic={}) perm={:?}",
            pick.name, pick.layer, pick.regime, pick.budget, outcome.stats.global,
            outcome.stats.fold_traffic, outcome.unit_permutation,
        );
    }
}

/// The baseline-fallback path: at a budget equal to the `None`-decisions
/// placement FLOOR (probed at runtime — `compile_distilled` at budget 1 reports
/// it), bigint L0 R0's decision-candidates all land infeasible or no better
/// than the baseline (caching at the floor has no headroom), so the search must
/// return the baseline outcome: `decisions: None`, identity `unit_permutation`,
/// and stats identical to the no-decisions compile. Deterministic (fixed seed)
/// and fast (the tight budget makes every candidate compile cheap). The picks
/// above prove the OTHER branch (a strictly-better `Some` outcome); together
/// they cover both sides of the by-construction non-regression floor.
#[test]
fn search_bwd_layer_falls_back_to_none_baseline_at_floor_budget() {
    let name = "bigint_with_extended_control_layout_gkr.json";
    let regime = BwdRegime::R0;

    let artifact = load_fixture(name);
    let dag = lower_dag(&artifact).unwrap_or_else(|e| panic!("[{name}] lower_dag: {e}"));
    validate(&dag).unwrap_or_else(|e| panic!("[{name}] validate: {e}"));
    let cross = build_cross_layer_field_map(&dag);
    let layer = &dag.layers[0];

    // Probe the None-decisions floor (budget 1 is always below it for a
    // compound layer), then compile the baseline exactly at that floor.
    let d0 = distill(layer, regime, &cross, None);
    let floor = match compile_distilled(&d0, 1, None) {
        Err(CompileError::BudgetBelowFloor { floor, .. }) => floor,
        Ok(_) => 1,
        Err(e) => panic!("[{name}] floor probe: {e:?}"),
    };
    let baseline = compile_distilled(&d0, floor, None)
        .unwrap_or_else(|e| panic!("[{name}] baseline compile at floor {floor}: {e:?}"));

    let cfg = BwdSearchConfig {
        pop: 4,
        evals: 12,
        seed: 0,
        mutation_sigma: 0.2,
        seed_strategy: BwdSeedStrategy::StructureAware,
        order_mutation: BwdOrderMutation::ReuseEdgeRelocate,
    };
    let outcome = search_bwd_layer(layer, regime, &cross, floor, &cfg);

    assert!(
        outcome.decisions.is_none(),
        "[{name}] at the None floor budget {floor} the search must fall back to the \
         no-decisions baseline"
    );
    assert_eq!(
        outcome.unit_permutation,
        (0..d0.unit_order.len()).collect::<Vec<_>>(),
        "[{name}] baseline fallback must report the canonical identity permutation"
    );
    assert_eq!(
        outcome.stats, baseline.stats_ext,
        "[{name}] baseline fallback stats must equal the no-decisions compile's"
    );
    println!(
        "[{name}] fallback exercised at floor budget {floor}: traffic={}",
        outcome.stats.global + outcome.stats.fold_traffic
    );
}

/// Task 2.5: candidate scoring inside `search_bwd_layer` now runs on rayon
/// `par_iter` (seed cohort + each bred cohort). This proves the parallelization
/// introduced no thread-order nondeterminism: two runs of the SAME seed on the
/// SAME (layer, regime, budget, cfg) must agree on every observable field.
/// `mem_word_only` L0 is the smallest fast fixture that still has caching
/// headroom at b16 (feasible — `PINNED_B16_INFEASIBLE` is empty corpus-wide),
/// so the GA actually explores distinct `Some(decisions)` candidates rather
/// than degenerating to the trivial baseline-fallback path exercised above.
/// `BwdSearchOutcome`/`SiteDecisions` have no `PartialEq`, so the determinism
/// contract is checked on the three fields that fully characterize the search
/// result: `unit_permutation`, `stats` (`BwdTrafficStats: PartialEq`), and
/// `decisions.is_some()`. Byte-identical-to-SEQUENTIAL is a separate, by
/// construction argument (RNG draws stay sequential; `score_candidate` is pure;
/// `collect()` preserves index order) — this test only rules out cross-run
/// (thread-schedule-dependent) nondeterminism.
#[test]
fn search_bwd_layer_is_deterministic() {
    let name = "mem_word_only_layout_gkr.json";
    let regime = BwdRegime::Ext;
    let budget = 16;

    let artifact = load_fixture(name);
    let dag = lower_dag(&artifact).unwrap_or_else(|e| panic!("[{name}] lower_dag: {e}"));
    validate(&dag).unwrap_or_else(|e| panic!("[{name}] validate: {e}"));
    let cross = build_cross_layer_field_map(&dag);
    let layer = &dag.layers[0];

    let d0 = distill(layer, regime, &cross, None);
    assert!(!d0.skipped_decoder, "[{name}] pick must be decoder-free");

    let cfg = BwdSearchConfig {
        pop: 4,
        evals: 12,
        seed: 0,
        mutation_sigma: 0.2,
        seed_strategy: BwdSeedStrategy::StructureAware,
        order_mutation: BwdOrderMutation::ReuseEdgeRelocate,
    };
    let outcome1 = search_bwd_layer(layer, regime, &cross, budget, &cfg);
    let outcome2 = search_bwd_layer(layer, regime, &cross, budget, &cfg);

    assert_eq!(
        outcome1.unit_permutation, outcome2.unit_permutation,
        "[{name}] parallel scoring must not change unit_permutation across runs"
    );
    assert_eq!(
        outcome1.stats, outcome2.stats,
        "[{name}] parallel scoring must not change outcome.stats across runs"
    );
    assert_eq!(
        outcome1.decisions.is_some(),
        outcome2.decisions.is_some(),
        "[{name}] parallel scoring must not change whether decisions were found"
    );
    assert!(
        outcome1.decisions.is_some(),
        "[{name}] pick must exercise a real (non-fallback) Some(decisions) outcome \
         so scoring runs across a genuinely diverse cohort"
    );

    println!(
        "[{name}] deterministic across 2 runs: traffic={} perm={:?}",
        outcome1.stats.global + outcome1.stats.fold_traffic, outcome1.unit_permutation,
    );
}

/// Fast equal-compile-budget probe before spending evaluations on bigint or
/// keccak. Both modes retain identical selection/crossover/mutation; with
/// `evals == pop`, this isolates their four initial genomes exactly.
#[test]
fn structure_aware_seed_equal_eval_probe() {
    let name = "mem_word_only_layout_gkr.json";
    let regime = BwdRegime::Ext;
    let budget = 16;
    let artifact = load_fixture(name);
    let dag = lower_dag(&artifact).unwrap_or_else(|e| panic!("[{name}] lower_dag: {e}"));
    validate(&dag).unwrap_or_else(|e| panic!("[{name}] validate: {e}"));
    let cross = build_cross_layer_field_map(&dag);
    let layer = &dag.layers[0];

    let d0 = distill(layer, regime, &cross, None);
    let baseline = compile_distilled(&d0, budget, None)
        .unwrap_or_else(|e| panic!("[{name}] baseline compile: {e:?}"));
    let baseline_traffic = baseline.stats_ext.global + baseline.stats_ext.fold_traffic;

    let config = |seed_strategy| BwdSearchConfig {
        pop: 4,
        evals: 4,
        seed: 0,
        mutation_sigma: 0.2,
        seed_strategy,
        order_mutation: BwdOrderMutation::PerKey,
    };
    let legacy = search_bwd_layer(
        layer,
        regime,
        &cross,
        budget,
        &config(BwdSeedStrategy::Legacy),
    );
    let structured = search_bwd_layer(
        layer,
        regime,
        &cross,
        budget,
        &config(BwdSeedStrategy::StructureAware),
    );
    let legacy_traffic = legacy.stats.global + legacy.stats.fold_traffic;
    let structured_traffic = structured.stats.global + structured.stats.fold_traffic;

    assert!(legacy_traffic <= baseline_traffic);
    assert!(structured_traffic <= baseline_traffic);
    assert!(
        structured_traffic <= legacy_traffic,
        "structure-aware seeds must not lose the equal-evaluation probe: \
         structured={structured_traffic}, legacy={legacy_traffic}"
    );
    println!(
        "[{name}] equal 4-eval seed probe: baseline={baseline_traffic} legacy={legacy_traffic} \
         structured={structured_traffic}"
    );
}
