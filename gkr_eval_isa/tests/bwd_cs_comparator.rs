//! Task 10 (CS-M0): the G-M0 comparator harness — constructive engine
//! ([`cs_schedule_bwd_layer`], Task 9) vs the GA-at-strength reference
//! ([`search_bwd_layer`], Task 8) on the four G-M0 gated fixtures, Ext regime,
//! layer index 0, budget 16 (b16).
//!
//! Two test fns:
//!   * [`comparator_smoke`] — NOT ignored; add_sub L0 at a tiny GA config
//!     (`pop: 4, evals: 40`), exercising the full comparison path (CS run, GA
//!     run, winner recompile + its determinism cross-check, verdict
//!     computation) so the harness code stays compiled + exercised in normal
//!     CI. NOT a G-M0 pass/fail (add_sub is not one of the four gated
//!     fixtures).
//!   * [`g_m0_comparator`] — `#[ignore]`; the real gate, run explicitly at
//!     Task 11 (see its doc header for the exact invocation).

mod common;

use std::time::Instant;

use common::{load_layer, CrossFields};
use cs::gkr_compiler::dag_ir::{bwd_roots, BwdRegime, DagLayer};
use gkr_eval_isa::bwd::compile::compile_distilled;
use gkr_eval_isa::bwd::distill::distill;
use gkr_eval_isa::bwd::engine::{cs_schedule_bwd_layer, cs_schedule_bwd_layer_research};
use gkr_eval_isa::bwd::price::RECLAIM_N;
use gkr_eval_isa::bwd::search::{
    search_bwd_layer, BwdOrderMutation, BwdSearchConfig, BwdSeedStrategy,
};

/// The b16 budget both engines schedule at (G-M0 pin).
const BUDGET: usize = 16;

/// The four G-M0 gated fixtures (Ext regime, layer index 0).
const G_M0_FIXTURES: &[&str] = &[
    "bigint_with_extended_control_layout_gkr.json",
    "keccak_special5_layout_gkr.json",
    "blake2_with_extended_control_layout_gkr.json",
    "unified_reduced_machine_layout_gkr.json",
];

/// GA-at-strength reference config (spec-pinned): population, eval budget, and
/// the 3 fixed deterministic seeds best-of-3'd per circuit.
const GA_POP: usize = 64;
const GA_EVALS: usize = 2000;
const GA_SEEDS: [u64; 3] = [0, 1, 2];

/// A run measured longer than this is a harness DNF *marker* only — it is
/// EXCLUDED from the best-of ranking, never an in-search abort or timeout. The
/// search itself never consults wall-clock time (determinism), so this cap is
/// applied strictly post-hoc, after `search_bwd_layer` has already run to
/// completion.
const DNF_SECS: f64 = 600.0;

// ── GA seed runner (shared by both tests) ──────────────────────────────────────

/// One `search_bwd_layer` run at `(pop, evals, seed)`; every other
/// `BwdSearchConfig` field is pinned to the G-M0 reference (`mutation_sigma:
/// 0.2, seed_strategy: StructureAware, order_mutation: ReuseEdgeRelocate`).
struct GaSeedResult {
    seed: u64,
    /// Wall time exceeded [`DNF_SECS`] — excluded from [`best_of`]'s ranking.
    dnf: bool,
    secs: f64,
    /// `search_bwd_layer` never returns an actually-infeasible outcome (it
    /// falls back to the feasible `None`-decisions baseline, panicking only if
    /// even that baseline is infeasible) — always `false` here, kept so the
    /// best-of sort key has the same shape as `cs_schedule_bwd_layer`'s
    /// `(infeasible, traffic, instrs)` non-regression key.
    infeasible: bool,
    traffic: usize,
    instrs: usize,
}

/// Run `search_bwd_layer(layer, regime, cross, budget, cfg)` at `seed`, timing
/// it with [`Instant`]. `BwdSearchOutcome` exposes only `stats` (traffic),
/// never an instruction count, so the winner is recompiled deterministically —
/// `distill(.., Some(&outcome.unit_permutation))` ->
/// `compile_distilled(.., outcome.decisions.as_ref())` — to read
/// `stats.program_lanes`. That recompile doubles as a free determinism
/// cross-check: its `stats_ext` MUST equal `outcome.stats` bit-for-bit
/// (asserted here).
fn run_ga_seed(
    layer: &DagLayer,
    regime: BwdRegime,
    cross: &CrossFields,
    budget: usize,
    seed: u64,
    pop: usize,
    evals: usize,
) -> GaSeedResult {
    let cfg = BwdSearchConfig {
        pop,
        evals,
        seed,
        mutation_sigma: 0.2,
        seed_strategy: BwdSeedStrategy::StructureAware,
        order_mutation: BwdOrderMutation::ReuseEdgeRelocate,
    };
    let start = Instant::now();
    let outcome = search_bwd_layer(layer, regime, cross, budget, &cfg);
    let secs = start.elapsed().as_secs_f64();

    let d = distill(layer, regime, cross, Some(&outcome.unit_permutation));
    let recompiled = compile_distilled(&d, budget, outcome.decisions.as_ref()).unwrap_or_else(|e| {
        panic!("seed {seed}: GA winner recompile must be feasible at budget {budget}: {e:?}")
    });
    assert_eq!(
        recompiled.stats_ext, outcome.stats,
        "seed {seed}: recompiled stats_ext must reproduce outcome.stats (determinism cross-check)"
    );

    GaSeedResult {
        seed,
        dnf: secs > DNF_SECS,
        secs,
        infeasible: false,
        traffic: outcome.stats.global + outcome.stats.fold_traffic,
        instrs: recompiled.stats.program_lanes,
    }
}

/// Best-of-N by `(infeasible, traffic, instrs)`, excluding any seed measured
/// `dnf` (a DNF is excluded from ranking, never treated as an automatic winner
/// or loser).
fn best_of(results: &[GaSeedResult]) -> Option<&GaSeedResult> {
    results.iter().filter(|r| !r.dnf).min_by_key(|r| (r.infeasible, r.traffic, r.instrs))
}

// ── comparator_smoke (Task 10, NOT ignored) ─────────────────────────────────────

/// Wiring smoke: add_sub L0 (Ext, b16), tiny GA config (`pop: 4, evals: 40`,
/// seed 0). Exercises the FULL comparison path — `cs_schedule_bwd_layer`,
/// `search_bwd_layer` at the tiny config, the winner recompile (+ its
/// determinism cross-check), and the verdict computation — so the harness
/// code stays compiled and exercised in normal CI runs. NOT a G-M0 pass/fail:
/// add_sub is not one of the four gated fixtures, so a `FAIL` verdict here is
/// printed but not asserted (only the *mechanics* — feasibility + the
/// recompile cross-check — are asserted).
#[test]
fn comparator_smoke() {
    const NAME: &str = "add_sub_lui_auipc_mop_layout_gkr.json";
    const SMOKE_POP: usize = 4;
    const SMOKE_EVALS: usize = 40;

    let (layer, cross) = load_layer(NAME, 0);
    assert!(!bwd_roots(&layer).is_empty(), "{NAME}: layer 0 must have bwd roots");

    // Constructive engine.
    let cs = cs_schedule_bwd_layer(&layer, BwdRegime::Ext, &cross, BUDGET);
    let cs_traffic = cs.stats.global + cs.stats.fold_traffic;
    let cs_cert_ok = cs.certificate.counted_traffic == cs.certificate.reported_traffic;
    assert!(cs_cert_ok, "{NAME}: CS certificate must be Ok (counted == reported)");
    assert!(cs.instrs > 0, "{NAME}: CS shipped program must be non-empty");

    // GA at the tiny smoke config, seed 0 — the recompile + its determinism
    // cross-check run inside `run_ga_seed`.
    let ga = run_ga_seed(&layer, BwdRegime::Ext, &cross, BUDGET, 0, SMOKE_POP, SMOKE_EVALS);
    assert!(!ga.dnf, "{NAME}: tiny smoke config must not DNF ({} secs)", ga.secs);
    assert!(ga.instrs > 0, "{NAME}: GA winner recompile must be non-empty");

    // Full verdict computation (same rule `g_m0_comparator` uses), printed but
    // not asserted as pass/fail — add_sub is not a gated circuit.
    let pass = cs_cert_ok
        && (cs_traffic < ga.traffic || (cs_traffic == ga.traffic && cs.instrs <= ga.instrs));
    println!(
        "comparator_smoke ({NAME}, Ext L0, b{BUDGET}): cs_traffic={cs_traffic} cs_instrs={} | \
         ga_traffic={} ga_instrs={} secs={:.3} | verdict(non-gating)={}",
        cs.instrs,
        ga.traffic,
        ga.instrs,
        ga.secs,
        if pass { "PASS" } else { "FAIL" }
    );
}

// ── g_m0_comparator (Task 10, #[ignore] — the heavy gate, runs at Task 11) ─────

/// Per-fixture ledger row (printed unconditionally before any assertion fires).
struct LayerRow {
    name: &'static str,
    baseline_traffic: usize,
    ga_results: Vec<GaSeedResult>,
    cs_traffic: usize,
    cs_instrs: usize,
    cs_rounds: usize,
    cs_pins: usize,
    cs_cert_ok: bool,
    pass: bool,
}

fn print_ledger(rows: &[LayerRow]) {
    println!(
        "\nG-M0 comparator ledger (constructive CS vs GA-at-strength, Ext L0, b{BUDGET}):"
    );
    println!(
        "  {:<48} | {:>10} | {:>34} | {:>24} | verdict",
        "circuit",
        "baseline",
        "GA best (traffic/instrs/seed/secs)",
        "CS (traffic/instrs/rounds/pins)"
    );
    for r in rows {
        let dnf_seeds: Vec<u64> = r.ga_results.iter().filter(|g| g.dnf).map(|g| g.seed).collect();
        let ga_str = match best_of(&r.ga_results) {
            Some(g) => format!("{}/{}/seed{}/{:.1}s", g.traffic, g.instrs, g.seed, g.secs),
            None => "ALL-DNF".to_string(),
        };
        let ga_str = if dnf_seeds.is_empty() {
            ga_str
        } else {
            format!("{ga_str} (dnf seeds={dnf_seeds:?})")
        };
        println!(
            "  {:<48} | {:>10} | {:>34} | {:>24} | {}{}",
            r.name,
            r.baseline_traffic,
            ga_str,
            format!("{}/{}/{}/{}", r.cs_traffic, r.cs_instrs, r.cs_rounds, r.cs_pins),
            if r.pass { "PASS" } else { "FAIL" },
            if r.cs_cert_ok { "" } else { " (certificate NOT ok)" },
        );
    }
    println!();
}

/// THE G-M0 gate (heavy): loops the 4 gated fixtures x {constructive CS
/// engine, 3 GA-at-strength seeds}, best-of-3's the GA reference, and asserts
/// CS never loses. Run explicitly (NOT part of normal CI, ~2h):
///
/// ```text
/// RUST_MIN_STACK=1073741824 RUSTFLAGS=-Awarnings cargo test -p gkr_eval_isa \
///   --test bwd_cs_comparator g_m0_comparator -- --ignored --nocapture
/// ```
///
/// Per circuit: `cs_schedule_bwd_layer(&layer, Ext, &cross, 16)` vs
/// `search_bwd_layer` at `BwdSearchConfig { pop: 64, evals: 2000, seed,
/// mutation_sigma: 0.2, seed_strategy: StructureAware, order_mutation:
/// ReuseEdgeRelocate }` for `seed in [0, 1, 2]`, best-of-3 by `(infeasible,
/// traffic, instrs)` (excluding any seed measured DNF at > 600s — a harness
/// marker only, never an in-search abort). Pass per layer: `cs.traffic <=
/// best_ga.traffic` (tie-break `cs.instrs <= best_ga.instrs`) AND
/// `cs.certificate` is Ok (`counted_traffic == reported_traffic`). Prints the
/// full ledger table UNCONDITIONALLY (even on failure) before asserting — this
/// table is the G-M0 evidence RR adjudicates.
#[test]
#[ignore = "G-M0 heavy gate: 4 circuits x 3 GA seeds at pop=64/evals=2000 real \
            compiles each (~2h) — run explicitly at Task 11, see doc header"]
fn g_m0_comparator() {
    let mut rows = Vec::new();

    for &name in G_M0_FIXTURES {
        let (layer, cross) = load_layer(name, 0);
        assert!(!bwd_roots(&layer).is_empty(), "{name}: layer 0 must have bwd roots");

        // Canonical baseline traffic (the non-regression floor both engines share).
        let bl_d = distill(&layer, BwdRegime::Ext, &cross, None);
        let bl_c = compile_distilled(&bl_d, BUDGET, None)
            .unwrap_or_else(|e| panic!("{name}: canonical baseline compile @ b16 failed: {e:?}"));
        let baseline_traffic = bl_c.stats_ext.global + bl_c.stats_ext.fold_traffic;

        // Constructive engine.
        let cs = cs_schedule_bwd_layer(&layer, BwdRegime::Ext, &cross, BUDGET);
        let cs_traffic = cs.stats.global + cs.stats.fold_traffic;
        let cs_cert_ok = cs.certificate.counted_traffic == cs.certificate.reported_traffic;

        // GA-at-strength, 3 fixed seeds.
        let ga_results: Vec<GaSeedResult> = GA_SEEDS
            .iter()
            .map(|&seed| {
                run_ga_seed(&layer, BwdRegime::Ext, &cross, BUDGET, seed, GA_POP, GA_EVALS)
            })
            .collect();

        let pass = match best_of(&ga_results) {
            Some(g) => {
                cs_cert_ok
                    && (cs_traffic < g.traffic || (cs_traffic == g.traffic && cs.instrs <= g.instrs))
            }
            // No valid GA baseline (all 3 seeds DNF) — cannot certify a pass either way.
            None => false,
        };

        rows.push(LayerRow {
            name,
            baseline_traffic,
            ga_results,
            cs_traffic,
            cs_instrs: cs.instrs,
            cs_rounds: cs.rounds,
            cs_pins: cs.pins.len(),
            cs_cert_ok,
            pass,
        });
    }

    // The evidence prints FIRST, unconditionally — even if the assertion below fails.
    print_ledger(&rows);

    let failures: Vec<String> = rows
        .iter()
        .filter(|r| !r.pass)
        .map(|r| {
            format!(
                "{}: cs_traffic={} cs_instrs={} cert_ok={} best_ga={:?}",
                r.name,
                r.cs_traffic,
                r.cs_instrs,
                r.cs_cert_ok,
                best_of(&r.ga_results).map(|g| (g.traffic, g.instrs, g.seed))
            )
        })
        .collect();
    assert!(failures.is_empty(), "G-M0 comparator FAILURES:\n{}", failures.join("\n"));
}

// ── g_m0_comparator_sweep (CS-M4 Task 6, #[ignore] — in-process 1x/2x sweep) ─────

/// One CS run at a given leaf-reclaim `multiplier` (production `gap_cap=RECLAIM_N`,
/// `enforce_budget=true`), plus the Tier-2 verdict vs the SHARED GA reference. The
/// verdict rule is IDENTICAL to `g_m0_comparator`'s pass rule (certificate Ok AND CS
/// never loses: strict traffic drop, or a tie broken by `instrs`) — but here it is only
/// RECORDED, never asserted, so the sweep can measure (and report) a Partial.
struct CsSweepRun {
    multiplier: usize,
    traffic: usize,
    /// Per-run leaf-search `compile_distilled_planned` count (`CsOutcome::leaf_calls`).
    leaf_calls: usize,
    instrs: usize,
    reaches_tier2: bool,
}

/// Run `cs_schedule_bwd_layer_research(.., multiplier, RECLAIM_N, true)` once and score
/// it against the already-computed GA reference. Asserts ONLY the per-run sanity gate
/// (certificate exact-equality `counted_traffic == reported_traffic`); never a tier/GA
/// gate.
fn run_cs_sweep(
    layer: &DagLayer,
    cross: &CrossFields,
    multiplier: usize,
    ga_traffic: usize,
    ga_instrs: usize,
) -> CsSweepRun {
    let out =
        cs_schedule_bwd_layer_research(layer, BwdRegime::Ext, cross, BUDGET, multiplier, RECLAIM_N, true);
    let traffic = out.stats.global + out.stats.fold_traffic;
    let cert_ok = out.certificate.counted_traffic == out.certificate.reported_traffic;
    // Sanity only — the shipped plan must certify exactly (counted == reported). This is
    // the sole assertion in the sweep; there is NO cs <= ga / tier gate here.
    assert!(
        cert_ok,
        "CS@{multiplier} certificate must be Ok (counted == reported): counted={} reported={}",
        out.certificate.counted_traffic, out.certificate.reported_traffic
    );
    // Same rule as g_m0_comparator: CS reaches Tier 2 on this fixture iff it never loses
    // to the GA reference (strict traffic drop, or tie broken by instrs).
    let reaches_tier2 =
        traffic < ga_traffic || (traffic == ga_traffic && out.instrs <= ga_instrs);
    CsSweepRun { multiplier, traffic, leaf_calls: out.leaf_calls, instrs: out.instrs, reaches_tier2 }
}

/// THE G-M0 multiplier sweep (heavy, in-process): for each of the four gated fixtures it
/// computes the GA-at-strength reference ONCE (identical config to [`g_m0_comparator`] —
/// `pop=64, evals=2000, seeds [0,1,2]`, best-of-3), then runs CS at `multiplier=1` and,
/// ONLY when multiplier 1 misses Tier 2 on that fixture, again at `multiplier=2`. It
/// prints a per-fixture ledger (GA, CS@1, conditional CS@2 — traffic + leaf-search calls
/// + tier verdict each, plus the smallest sufficient multiplier ∈ {1, 2, none}) so the
/// controller can adjudicate the smallest sufficient multiplier per fixture. NO hard
/// `cs <= ga` assert — the sweep MEASURES (only per-run certificate sanity is asserted,
/// inside [`run_cs_sweep`]). Run explicitly (NOT part of normal CI, ~GA-bound heavy):
///
/// ```text
/// RUST_MIN_STACK=1073741824 RUSTFLAGS=-Awarnings cargo test -p gkr_eval_isa --release \
///   --test bwd_cs_comparator g_m0_comparator_sweep -- --ignored --nocapture
/// ```
#[test]
#[ignore = "G-M0 heavy sweep: 4 circuits x 3 GA seeds at pop=64/evals=2000 (GA-bound) + \
            CS at multiplier 1 (and conditionally 2) — run explicitly, see doc header"]
fn g_m0_comparator_sweep() {
    for &name in G_M0_FIXTURES {
        let (layer, cross) = load_layer(name, 0);
        assert!(!bwd_roots(&layer).is_empty(), "{name}: layer 0 must have bwd roots");

        // ── GA-at-strength reference, computed ONCE per fixture (the expensive part) —
        //    identical config to g_m0_comparator: GA_POP/GA_EVALS over GA_SEEDS,
        //    best-of-3 by (infeasible, traffic, instrs), DNF-excluded. NEVER re-run per
        //    multiplier. ──────────────────────────────────────────────────────────────
        let ga_results: Vec<GaSeedResult> = GA_SEEDS
            .iter()
            .map(|&seed| run_ga_seed(&layer, BwdRegime::Ext, &cross, BUDGET, seed, GA_POP, GA_EVALS))
            .collect();
        let (ga_traffic, ga_instrs, ga_seed) = match best_of(&ga_results) {
            Some(g) => (g.traffic, g.instrs, g.seed),
            // No valid GA baseline (all 3 seeds DNF) — cannot form a reference. Report
            // and move on; the sweep is measurement-only, never a hard fail here.
            None => {
                eprintln!(
                    "g_m0_sweep {name} (Ext L0, b{BUDGET}): GA=ALL-DNF (no reference) — SKIP"
                );
                continue;
            }
        };

        // ── CS @ multiplier 1 (production controls). ──────────────────────────────────
        let cs1 = run_cs_sweep(&layer, &cross, 1, ga_traffic, ga_instrs);

        // ── CS @ multiplier 2 ONLY if multiplier 1 misses Tier 2 on this fixture. ─────
        let cs2 = if cs1.reaches_tier2 {
            None
        } else {
            Some(run_cs_sweep(&layer, &cross, 2, ga_traffic, ga_instrs))
        };

        // Smallest sufficient multiplier ∈ {1, 2, none} that reaches Tier 2.
        let smallest = if cs1.reaches_tier2 {
            "1"
        } else if cs2.as_ref().is_some_and(|c| c.reaches_tier2) {
            "2"
        } else {
            "none"
        };

        let verdict = |r: &CsSweepRun| if r.reaches_tier2 { "PASS" } else { "MISS" };
        let cs2_str = match &cs2 {
            Some(c) => format!(
                " | CS@2 traffic={} leaf_calls={} instrs={} tier2={}",
                c.traffic,
                c.leaf_calls,
                c.instrs,
                verdict(c)
            ),
            None => " | CS@2 not-run (CS@1 already Tier 2)".to_string(),
        };

        // Per-fixture ledger line (unconditional; NO tier/GA assert).
        eprintln!(
            "g_m0_sweep {name} (Ext L0, b{BUDGET}): GA={ga_traffic} (instrs={ga_instrs}, seed{ga_seed}) \
             | CS@1 traffic={} leaf_calls={} instrs={} tier2={}{cs2_str} \
             | smallest_sufficient_multiplier={smallest}",
            cs1.traffic,
            cs1.leaf_calls,
            cs1.instrs,
            verdict(&cs1),
        );
    }
}
