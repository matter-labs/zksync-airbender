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
use gkr_eval_isa::bwd::engine::cs_schedule_bwd_layer;
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
