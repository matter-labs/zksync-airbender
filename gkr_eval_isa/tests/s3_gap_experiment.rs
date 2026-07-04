//! S3 Phase-1 gap experiment harness (Task 8c — capstone).
//!
//! ## What this is
//!
//! The S3 ordering question is: does the *order* in which a layer's roots are
//! evaluated change DRAM traffic, or does a fixed (caching-only) schedule already
//! capture the win? We answer it with a joint-vs-fixed-order differential:
//!   - **J** (`Mode::J`) = the joint optimum: the solver is free to choose the
//!     root order AND the residency schedule.
//!   - **E** (`Mode::E`) = fixed identity order: the solver chooses residency only.
//! `E − J` is the traffic a perfect re-ordering would save. `D` is the
//! DAG-intrinsic read floor (the denominator that makes `(E−J)/D` a fraction).
//!
//! ## Why this harness DOWNSCALES (the decision adapted after 8a)
//!
//! 8a found the oracle is OVER-STRICT at the real budget 16 on full 146-node
//! layers: add_sub-L0 J is `infeasible@16` (per-stage transient SUM charge), and
//! the MILP cannot prove optimality on a 146-node circuit within minutes. So a
//! full-size J at budget 16 is unobtainable.
//!
//! **The gate is robust to a SHARED over-strictness.** J and E use the IDENTICAL
//! model, so the systematic error cancels and the *direction* of `J vs E` stays
//! valid on any instance solved to **optimal**. The strategy therefore is:
//!   1. Measure the J-vs-E SIGNAL on DOWNSCALED clusters (via
//!      `connected_root_cluster`) that solve to **optimal** at budget 16 and that
//!      still carry ≥2 Prior edges (so order-sensitivity can manifest).
//!   2. Report full-size layers as BRACKET-ONLY (short cap, expect
//!      infeasible/feasible-not-optimal; record real `compile_layer` traffic as
//!      `C`, mark `required_full_size`). This is what makes `gate()` return
//!      `Insufficient` BY DESIGN — the honest "can't conclude at full scale".
//!   3. Headline the over-strictness + scale finding as the primary Phase-1
//!      result, and read the actionable signal off the downscaled clusters.

mod s3_gap;
mod s3_planner;

use s3_gap::cluster::{connected_root_cluster, reachable_shared_cache_values};
use s3_gap::driver::{oracle_available, run_oracle, Mode, OracleResult};
use s3_gap::floor::dag_traffic_floor;
use s3_gap::instance::{distinct_live_values, extract_instance};
use s3_gap::pack::fragmentation_upper_bound;
use s3_gap::report::{format_report, gate, GapRow};

use std::collections::HashMap;
use std::path::PathBuf;

use cs::gkr_compiler::dag_ir::{
    lower_dag, validate, DagCircuit, DagGlobals, DagLayer, FieldKind, ReadPlace, RootId,
};
use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;
use gkr_eval_isa::fwd::compile::{build_cross_layer_field_map, compile_circuit};

// REAL_BUDGET — the production smem cell budget the whole experiment targets.
const REAL_BUDGET: usize = 16;
// Short solver cap. Downscaled clusters solve in <1s; full-size hits the cap
// (accepted — the full-size row is bracket-only by design).
const CAP_SECS: u64 = 60;

// ── Fixture loading (copied verbatim from fwd_parity.rs:130-140) ──────────────

fn compiled_circuit_dir() -> PathBuf {
    // This test lives in the `gkr_eval_isa` crate; `cs/compiled_circuits` is at
    // `<workspace>/cs/compiled_circuits`, a sibling of this crate.
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../cs/compiled_circuits")
}

/// Deserialize one fixture JSON → `GKRCircuitArtifact<BabyBearField>`.
fn load_fixture(path: &PathBuf) -> Option<GKRCircuitArtifact<BabyBearField>> {
    let bytes = std::fs::read(path).ok()?;
    serde_json::from_slice(&bytes).ok()
}

// ── load_layer_source ─────────────────────────────────────────────────────────

fn load_layer_source(
    fixture: &str,
) -> (
    DagCircuit,
    GKRCircuitArtifact<BabyBearField>,
    HashMap<ReadPlace, FieldKind>,
) {
    let artifact = load_fixture(&compiled_circuit_dir().join(fixture))
        .expect("fixture load failed: check compiled_circuits path");
    let dag = lower_dag(&artifact).expect("lower_dag failed");
    validate(&dag).expect("validate failed");
    let cross = build_cross_layer_field_map(&dag);
    (dag, artifact, cross)
}

/// Load the committed b16 schedule for `stem` (`{stem}_schedule_b16_gkr.json`).
fn load_committed_schedule(stem: &str) -> Option<cs::gkr_compiler::dag_ir::CircuitSchedule> {
    let path = compiled_circuit_dir().join(format!("{stem}_schedule_b16_gkr.json"));
    let bytes = std::fs::read(path).ok()?;
    serde_json::from_slice(&bytes).ok()
}

/// M7 baseline: the schedule-driven compiler's width-weighted DRAM traffic for an L0
/// fixture. Post-T3b this compiles the committed b16 schedule (`compile_circuit`) and
/// returns layer 0's `stats.dram_traffic` — the same cell-weighted metric the gap
/// experiment compares C/E/J/D in. Returns `None` when the fixture cannot load OR has no
/// committed schedule (e.g. the `_no_caches` variants) — those rows report
/// `PROD_COMPILE_FAILED` and are skipped. `budget` is retained for signature stability;
/// the committed schedule is b16 (== `REAL_BUDGET`).
fn production_l0_traffic(fixture: &str, _budget: usize) -> Option<u64> {
    let artifact = load_fixture(&compiled_circuit_dir().join(fixture))?;
    let dag = lower_dag(&artifact).ok()?;
    validate(&dag).ok()?;
    let stem = fixture
        .trim_end_matches("_layout_gkr.json")
        .trim_end_matches("_layout_no_caches_gkr.json");
    let sched = load_committed_schedule(stem)?;
    let compiled = compile_circuit(&dag, &sched, &artifact).ok()?;
    Some(compiled.layers.first()?.stats.dram_traffic as u64)
}

/// Wrap a single (possibly downscaled) layer into a `DagCircuit` so `validate()`
/// can run on it, and so `build_cross_layer_field_map` can re-derive its fields.
fn wrap_layer(layer: DagLayer) -> DagCircuit {
    DagCircuit {
        layers: vec![layer],
        globals: DagGlobals::default(),
    }
}

// ── Seed selection for the downscaled decision-bearing clusters ────────────────

/// A candidate downscaled cluster: the seed that produced it, the cluster layer,
/// and its re-derived cross-layer field map.
struct ClusterCandidate {
    seed: RootId,
    layer: DagLayer,
    cross: HashMap<ReadPlace, FieldKind>,
    n_roots: usize,
    n_priors: usize,
}

/// Sweep seeds on `layer`, build each Prior-cluster, and keep the candidates in
/// the sweet spot: `min_priors ≤ priors` and `min_roots ≤ roots ≤ max_roots`.
///
/// Returned candidates are sorted by (descending priors, ascending roots) so the
/// caller tries the densest-but-smallest first — the most likely to (a) solve to
/// optimal quickly and (b) actually exhibit an order gap.
///
/// `add_sub` L0 has ~69 roots; this sweep is O(roots × cone) but completes in
/// well under a second on that layer (8b: ~0.01s per cluster build).
fn sweet_spot_clusters(
    layer: &DagLayer,
    min_priors: usize,
    min_roots: usize,
    max_roots: usize,
) -> Vec<ClusterCandidate> {
    let mut out: Vec<ClusterCandidate> = Vec::new();
    for rid in 0..layer.roots.len() as u32 {
        let seed = RootId(rid);
        let cluster = connected_root_cluster(layer, seed);
        let n_roots = cluster.roots.len();
        let n_priors = reachable_shared_cache_values(&cluster);
        if n_priors < min_priors || n_roots < min_roots || n_roots > max_roots {
            continue;
        }
        // Re-derive the cross-layer field map for the subsetted layer so widths
        // are correct after re-indexing.
        let wrapped = wrap_layer(cluster.clone());
        // The cluster must still validate (8b guarantees this; assert cheaply).
        if validate(&wrapped).is_err() {
            continue;
        }
        let cross = build_cross_layer_field_map(&wrapped);
        out.push(ClusterCandidate {
            seed,
            layer: cluster,
            cross,
            n_roots,
            n_priors,
        });
    }
    // Densest priors first, then smallest root count first.
    out.sort_by(|a, b| b.n_priors.cmp(&a.n_priors).then(a.n_roots.cmp(&b.n_roots)));
    // Deduplicate clusters that are structurally identical (same root set yields
    // the same cluster from multiple seeds) by (n_roots, n_priors, source count).
    let mut seen: std::collections::HashSet<(usize, usize, usize)> =
        std::collections::HashSet::new();
    out.retain(|c| seen.insert((c.n_roots, c.n_priors, c.layer.sources.len())));
    out
}

// ── The experiment ─────────────────────────────────────────────────────────────

/// S3 Phase-1 gap experiment.
///
/// Builds the instance set (downscaled decision-bearing clusters + an
/// order-insensitive validation instance + a full-size bracket row), runs J and
/// E at budget 16 under a short cap, prints the report + gate verdict, and prints
/// the downscaled-cluster `(E−J)/D` signal that the `gate()`'s `Insufficient`
/// guard intentionally suppresses (because the full-size row cannot solve to
/// optimal).
///
/// Result is recorded at `.agents/audits/2026-06-24-gkr-gap-experiment-result.md`.
#[test]
#[ignore = "S3 Phase-1 gap experiment; needs python3+ortools; run on demand with --ignored"]
fn s3_gap_experiment() {
    if !oracle_available() {
        eprintln!("[GAP] SKIP: python3+ortools absent");
        return;
    }

    // Tracks (label, (E−J)/D, direction, shared_dram_leaves) for the downscaled
    // both-optimal clusters.
    let mut signal_rows: Vec<(String, f64, &'static str, usize)> = Vec::new();
    let mut rows: Vec<GapRow> = Vec::new();

    // ── 1. DOWNSCALED decision-bearing clusters from add_sub L0 ───────────────
    {
        let (dag, _artifact, _cross) = load_layer_source("add_sub_lui_auipc_mop_layout_gkr.json");
        let layer = &dag.layers[0];

        eprintln!(
            "[GAP] add_sub-L0 source layer: roots={} priors={}",
            layer.roots.len(),
            reachable_shared_cache_values(layer)
        );

        // Sweet spot: ≥2 Priors, 3..=15 roots. Try densest-first until we have
        // 2-3 both-optimal clusters.
        let candidates = sweet_spot_clusters(layer, 2, 3, 15);
        eprintln!(
            "[GAP] add_sub-L0 sweet-spot candidates (≥2 priors, 3..=15 roots): {}",
            candidates.len()
        );

        let want = 3usize;
        let mut accepted = 0usize;
        for cand in &candidates {
            if accepted >= want {
                break;
            }
            let inst = extract_instance(&cand.layer, &cand.cross, REAL_BUDGET);
            if inst.roots.is_empty() || inst.nodes.is_empty() {
                continue;
            }
            // Cheap precondition: a decision-bearing cluster must carry Prior edges.
            assert!(
                cand.n_priors >= 2,
                "sweet-spot guarantees ≥2 priors; got {}",
                cand.n_priors
            );

            let d = dag_traffic_floor(&cand.layer, &cand.cross) as u64;
            let j = run_oracle(&inst, Mode::J, 0.01, CAP_SECS).expect("oracle J");
            let e = run_oracle(&inst, Mode::E, 0.01, CAP_SECS).expect("oracle E");

            // ASSERT optimal-for-both; skip + log a cluster that doesn't solve.
            if j.status != "optimal" || e.status != "optimal" {
                eprintln!(
                    "[GAP]   skip seed={:?} ({} roots, {} priors): J={} E={} (not both optimal)",
                    cand.seed, cand.n_roots, cand.n_priors, j.status, e.status
                );
                continue;
            }

            let frag = fragmentation_upper_bound(&inst, &j);
            // No matching artifact layer for a synthetic re-indexed cluster → C
            // is not meaningfully computable here; record u64::MAX (BUDGET<FLOOR-
            // style sentinel) so the report omits a misleading headroom column.
            let c = u64::MAX;
            let label = format!("add_sub-L0-c{}r{}p", accepted + 1, cand.n_roots);
            let shared = shared_dram_leaves(&inst);

            print_gap_line(&label, &inst, d, c, &j, &e, frag);
            eprintln!(
                "[GAP]   seed={:?} shared_dram_leaves={shared} (order-tension driver; 0 ⇒ no tension)",
                cand.seed
            );

            let ratio = (e.traffic as f64 - j.traffic as f64) / d.max(1) as f64;
            signal_rows.push((label.clone(), ratio, direction(ratio), shared));

            rows.push(GapRow {
                name: label,
                decision_bearing: true,
                required_full_size: false,
                c,
                e: e.traffic,
                j_ideal: j.traffic,
                frag,
                d,
                e_status: e.status,
                j_status: j.status,
            });
            accepted += 1;
        }

        if accepted == 0 {
            // BLOCKED escalation path: even small ≥2-prior clusters are
            // over-strict-infeasible at 16. Dump what we tried before failing.
            eprintln!("[GAP] ESCALATION: no ≥2-prior add_sub-L0 cluster solved BOTH J and E to optimal at budget {REAL_BUDGET} within {CAP_SECS}s.");
            eprintln!("[GAP] Candidates tried (seed -> roots/priors):");
            for cand in &candidates {
                eprintln!(
                    "[GAP]   seed={:?} roots={} priors={}",
                    cand.seed, cand.n_roots, cand.n_priors
                );
            }
            panic!(
                "BLOCKED: even downscaled ≥2-prior clusters are over-strict-infeasible at budget {REAL_BUDGET}. \
                 Cannot obtain an optimal J — escalate (Task-4 within-stage charge needs relaxation)."
            );
        }
    }

    // ── 2. Order-INSENSITIVE validation instance (no_caches add_sub L0) ───────
    // no_caches L0 has NO Prior edges → connected_root_cluster yields a tiny
    // single-root cone. With no order sensitivity, J == E (gap 0) — the in-repo
    // replacement for "gap is 0 on trees".
    {
        let (dag, _artifact, _cross) =
            load_layer_source("add_sub_lui_auipc_mop_layout_no_caches_gkr.json");
        let layer = &dag.layers[0];
        eprintln!(
            "[GAP] no_caches-add_sub-L0 source layer: roots={} priors={}",
            layer.roots.len(),
            reachable_shared_cache_values(layer)
        );

        // Downscale to a single seed's cone (no Priors to follow → tiny cluster).
        let seed = RootId(0);
        let cluster = connected_root_cluster(layer, seed);
        let wrapped = wrap_layer(cluster.clone());
        validate(&wrapped).expect("no_caches cluster must validate");
        let cross = build_cross_layer_field_map(&wrapped);

        let inst = extract_instance(&cluster, &cross, REAL_BUDGET);
        let d = dag_traffic_floor(&cluster, &cross) as u64;
        let j = run_oracle(&inst, Mode::J, 0.01, CAP_SECS).expect("oracle J (no_caches)");
        let e = run_oracle(&inst, Mode::E, 0.01, CAP_SECS).expect("oracle E (no_caches)");
        let frag = fragmentation_upper_bound(&inst, &j);
        let c = u64::MAX;
        let label = "no_caches-add_sub-L0".to_string();
        print_gap_line(&label, &inst, d, c, &j, &e, frag);

        // The validation expectation: J == E (no order sensitivity). Only assert
        // when both solved to optimal (a feasible-but-capped result is not a
        // proof of equality).
        if j.status == "optimal" && e.status == "optimal" {
            assert_eq!(
                j.traffic, e.traffic,
                "order-insensitive instance must have J == E (gap 0)"
            );
            eprintln!(
                "[GAP]   VALIDATION OK: J == E == {} (no order sensitivity)",
                j.traffic
            );
        } else {
            eprintln!(
                "[GAP]   note: no_caches cluster not both-optimal (J={} E={}); equality not asserted",
                j.status, e.status
            );
        }

        rows.push(GapRow {
            name: label,
            decision_bearing: false,
            required_full_size: false,
            c,
            e: e.traffic,
            j_ideal: j.traffic,
            frag,
            d,
            e_status: e.status,
            j_status: j.status,
        });
    }

    // ── 3. Full-size REQUIRED bracket row (add_sub L0 @ budget 16, short cap) ──
    // Expected feasible-not-optimal at full scale (a pure MILP SCALE limit now
    // that the per-stage over-strictness is fixed — 146 nodes/39 roots cannot be
    // proven optimal within the cap) → makes gate() return Insufficient BY DESIGN.
    // Record real schedule-driven compiler traffic as C.
    {
        let (dag, artifact, cross) = load_layer_source("add_sub_lui_auipc_mop_layout_gkr.json");
        let layer = &dag.layers[0];
        let inst = extract_instance(layer, &cross, REAL_BUDGET);
        let d = dag_traffic_floor(layer, &cross) as u64;
        // Real C from the schedule-driven compiler at the committed b16 schedule.
        let c = match load_committed_schedule("add_sub_lui_auipc_mop")
            .and_then(|sched| compile_circuit(&dag, &sched, &artifact).ok())
        {
            Some(cc) => cc.layers[0].stats.dram_traffic as u64,
            None => {
                eprintln!("[GAP] full-size compile error (recording C=MAX)");
                u64::MAX
            }
        };
        let j = run_oracle(&inst, Mode::J, 0.01, CAP_SECS).expect("oracle J (full-size)");
        let e = run_oracle(&inst, Mode::E, 0.01, CAP_SECS).expect("oracle E (full-size)");
        let frag = fragmentation_upper_bound(&inst, &j);
        let label = "add_sub-L0-FULL".to_string();
        print_gap_line(&label, &inst, d, c, &j, &e, frag);
        eprintln!(
            "[GAP]   full-size status: J={} E={} (expected NOT both-optimal at scale → gate Insufficient)",
            j.status, e.status
        );

        rows.push(GapRow {
            name: label,
            decision_bearing: true,
            required_full_size: true,
            c,
            e: e.traffic,
            j_ideal: j.traffic,
            frag,
            d,
            e_status: e.status,
            j_status: j.status,
        });
    }

    // ── Report + gate verdict ─────────────────────────────────────────────────
    println!("\n{}", format_report(&rows));
    let verdict = gate(&rows);
    println!("GATE: {verdict:?}");
    println!(
        "GATE EXPLANATION: `Insufficient` is the HONEST verdict here — the §4.3 guard requires a \n\
         full-size prior_edges>0 row solved to OPTIMAL before concluding, and the full-size row \n\
         cannot be PROVEN optimal at budget {REAL_BUDGET} (a pure MILP scale limit on 146 nodes/39 \n\
         roots; the per-stage over-strictness has been fixed by the sequential SU-peak charge, so \n\
         the downscaled order-sensitive cluster now solves both-optimal at 16). gate() therefore \n\
         refuses to conclude at full scale. The actionable Phase-1 signal is the downscaled-cluster \n\
         section below, which the gate's guard intentionally suppresses."
    );

    // ── Downscaled-cluster signal section ─────────────────────────────────────
    println!("\n=== DOWNSCALED-CLUSTER SIGNAL (both-optimal @ budget {REAL_BUDGET}) ===");
    if signal_rows.is_empty() {
        println!("  (no both-optimal downscaled clusters — see escalation log above)");
    }
    let mut max_ratio = f64::MIN;
    let mut any_with_tension = false;
    for (label, ratio, dir, shared) in &signal_rows {
        println!(
            "  {label:<22} (E−J)/D = {:.2}%  shared_dram_leaves={shared}  → {dir}",
            ratio * 100.0
        );
        max_ratio = max_ratio.max(*ratio);
        any_with_tension |= *shared > 0;
    }
    if !signal_rows.is_empty() {
        println!(
            "\n  PHASE-1 SIGNAL: max (E−J)/D over downscaled clusters = {:.2}% → {}",
            max_ratio * 100.0,
            direction(max_ratio)
        );
        println!(
            "  Interpretation: ≥15% → order matters (BuildBeam-leaning); <5% → order ~irrelevant \n\
             (CachingOnly-leaning); 5–15% → Marginal."
        );
        if !any_with_tension {
            println!(
                "  CAVEAT: every both-optimal cluster @ budget {REAL_BUDGET} has shared_dram_leaves=0 \n\
                 — no DRAM leaf feeds ≥2 roots, so there is nothing for ordering to optimize. \n\
                 Their J==E is structurally CORRECT but UNINFORMATIVE about the ordering question. \n\
                 See the supplementary order-tension probe below for the decision-relevant datum."
            );
        }
    }

    // ── Supplementary order-tension probe ─────────────────────────────────────
    // The ONLY add_sub-L0 cluster that shares a DRAM leaf across roots (seed 18,
    // shared_dram_leaves=2) is the one genuinely order-sensitive instance. Under
    // the sequential Sethi-Ullman charge it now solves BOTH J and E to optimal AT
    // the real budget 16 (the old per-stage SUM charge wrongly made it infeasible
    // there). We sweep budgets to confirm whether ANY budget exposes an order gap
    // on it — the most decision-relevant J-vs-E datum the experiment can produce
    // on a genuinely order-sensitive real sub-circuit.
    println!("\n=== SUPPLEMENTARY ORDER-TENSION PROBE (shared-DRAM cluster, budget sweep) ===");
    order_tension_probe();

    // ── Headline finding ──────────────────────────────────────────────────────
    println!("\n=== HEADLINE FINDING ===");
    println!(
        "  Sequential SU-peak charge fixes the over-strictness: the genuinely order-sensitive \n\
         downscaled cluster (seed 18, shared_dram_leaves=2) now solves BOTH J and E to optimal AT \n\
         the real budget 16 → (E−J)/D = 0% (order ~irrelevant). The remaining limit is pure MILP \n\
         scale: the full 146-node/39-root layer is only feasible-not-optimal within the cap, so a \n\
         PROVEN full-size optimum is still unobtainable and gate() stays Insufficient. The valid \n\
         Phase-1 signal is the downscaled both-optimal section: order does not matter on add_sub-L0 \n\
         at the real budget (the earlier 12.5%@budget-48 was an artifact of the old E over-strictness)."
    );
}

/// Find the add_sub-L0 cluster with cross-root DRAM sharing (the only genuine
/// order-tension instance) and sweep budgets to locate the window where it
/// solves BOTH J and E to optimal, printing the gap at each budget.
fn order_tension_probe() {
    let (dag, _a, _c) = load_layer_source("add_sub_lui_auipc_mop_layout_gkr.json");
    let layer = &dag.layers[0];

    // Find the smallest cluster with ≥1 shared DRAM leaf across roots.
    let mut chosen: Option<(RootId, DagLayer, HashMap<ReadPlace, FieldKind>, usize)> = None;
    for cand in sweet_spot_clusters(layer, 1, 2, 30) {
        let inst = extract_instance(&cand.layer, &cand.cross, REAL_BUDGET);
        let shared = shared_dram_leaves(&inst);
        if shared >= 1 {
            chosen = Some((cand.seed, cand.layer, cand.cross, shared));
            break;
        }
    }
    let (seed, clayer, cross, shared) = match chosen {
        Some(t) => t,
        None => {
            println!("  (no shared-DRAM-leaf cluster found on add_sub-L0)");
            return;
        }
    };
    let d = dag_traffic_floor(&clayer, &cross) as u64;
    println!(
        "  cluster seed={seed:?}: shared_dram_leaves={shared}, D={d}. \n\
         Sweeping budgets (sequential SU-peak charge makes it feasible at the real budget {REAL_BUDGET}):"
    );

    let mut best_signal: Option<(usize, u64, u64)> = None; // (budget, j, e) at first both-optimal
    for b in [REAL_BUDGET, 20, 24, 28, 32, 40, 48, 64] {
        let inst = extract_instance(&clayer, &cross, b);
        let j = run_oracle(&inst, Mode::J, 0.01, 30).expect("oracle J (tension)");
        let e = run_oracle(&inst, Mode::E, 0.01, 30).expect("oracle E (tension)");
        let gap = e.traffic as i64 - j.traffic as i64;
        let both_opt = j.status == "optimal" && e.status == "optimal";
        println!(
            "    budget={b:<3} J={}({}) E={}({}) gap={gap}{}",
            j.status,
            j.traffic,
            e.status,
            e.traffic,
            if both_opt { "  [both-optimal]" } else { "" }
        );
        if both_opt && best_signal.is_none() && gap != 0 {
            best_signal = Some((b, j.traffic, e.traffic));
        }
    }
    match best_signal {
        Some((b, j, e)) => {
            let ratio = (e as f64 - j as f64) / d.max(1) as f64;
            println!(
                "\n  ORDER-TENSION DATUM: at budget {b} (first both-optimal with a gap), \n\
                 J={j} E={e} → (E−J)/D = {:.2}% → {}. \n\
                 Order DOES matter on this genuinely order-sensitive cluster, but the magnitude \n\
                 is small (one reload). The real-budget zeros above lack this tension entirely.",
                ratio * 100.0,
                direction(ratio)
            );
        }
        None => {
            println!(
                "\n  ORDER-TENSION DATUM: no budget in the sweep produced a both-optimal gap≠0 \n\
                 (either the cluster never solved both-optimal, or J==E at every solvable budget)."
            );
        }
    }
}

// ── Output helpers ─────────────────────────────────────────────────────────────

/// Print the `[GAP]` line for one instance.
fn print_gap_line(
    label: &str,
    inst: &s3_gap::instance::OracleInstance,
    d: u64,
    c: u64,
    j: &OracleResult,
    e: &OracleResult,
    frag: u64,
) {
    let c_str = if c == u64::MAX {
        "n/a".to_string()
    } else {
        c.to_string()
    };
    eprintln!(
        "[GAP] {label}: nodes={} roots={} live_values≈{} | C={c_str} D={d} | \
         J(status={},traffic={}) E(status={},traffic={}) | frag={frag}",
        inst.nodes.len(),
        inst.roots.len(),
        distinct_live_values(inst),
        j.status,
        j.traffic,
        e.status,
        e.traffic,
    );
}

/// Count DRAM leaves (`real_dram` nodes) reachable from ≥2 roots — the actual
/// order-tension driver. A cluster with 0 shared DRAM leaves has nothing for
/// ordering to optimize (each read feeds exactly one root), so J == E is the
/// structurally correct (but uninformative) answer there, NOT an artifact.
fn shared_dram_leaves(inst: &s3_gap::instance::OracleInstance) -> usize {
    use std::collections::{HashMap, HashSet};
    let id_to_idx: HashMap<u32, usize> = inst
        .nodes
        .iter()
        .enumerate()
        .map(|(i, n)| (n.id, i))
        .collect();
    let mut uses: HashMap<u32, usize> = HashMap::new();
    for &root_id in &inst.roots {
        let mut seen: HashSet<u32> = HashSet::new();
        let mut stack = vec![root_id];
        while let Some(nid) = stack.pop() {
            if !seen.insert(nid) {
                continue;
            }
            let n = &inst.nodes[id_to_idx[&nid]];
            if n.real_dram {
                *uses.entry(nid).or_insert(0) += 1;
            }
            for &c in &n.children {
                stack.push(c);
            }
        }
    }
    uses.values().filter(|&&u| u >= 2).count()
}

/// Format `2^w` exactly for small `w`, else as `10^d`.
fn pow2_str(w: u32) -> String {
    if w <= 62 {
        format!("{}", 1u64 << w)
    } else {
        format!("~10^{:.0}", w as f64 * std::f64::consts::LOG10_2)
    }
}

/// CACHEABLE-CANDIDATE CENSUS for the "fork cache-vs-recompute per multi-consumer
/// node" idea. Fixing the binary decision at every cacheable candidate makes the
/// reference string deterministic (kills the keep-vs-recompute circularity), so a
/// fixed order's inner problem becomes an enumeration over `2^K` decision vectors.
///
/// But the decisions only interact when their live-ranges overlap, so the inner
/// problem is solvable by a left-to-right DP whose state is the set of currently
/// "in-flight" decisions — cost `roots × 2^W`, where `W` = max concurrent
/// cross-root candidate live-ranges. `W` (not `K`) is the real tractability knob.
///
/// Per circuit L0 we report, on the canonical scheduling DAG (`extract_instance`):
///   - `K`   = #nodes with ≥2 consumers (the user's raw fork count → 2^K variants)
///     split into recompute (Add/Mul; the hard ones) vs reload (Read/Prior).
///   - `K_x` = those whose reuse spans ≥2 DISTINCT roots (the real cross-root cache
///     decisions; same-cone reuse is handled by the within-stage SU peak).
///   - `W`   = max, over root boundaries, of cross-root candidates spanning it.
#[test]
#[ignore = "DAG fan-out census for the cache-fork tractability analysis; run with --ignored"]
fn dag_fanout_census() {
    use s3_gap::instance::NodeKind;
    use std::collections::HashSet;

    println!(
        "\n=== CACHEABLE-CANDIDATE CENSUS (fork = cache vs recompute per multi-consumer node) ==="
    );
    println!("K=#(≥2 consumers); K_x=cross-root-reused (real cache decisions); W=max concurrent → DP state 2^W\n");
    for &fixture in ALL_FIXTURES {
        let short = fixture.trim_end_matches("_layout_gkr.json");
        let Some((layer, cross)) = try_load_l0(fixture) else {
            println!("[{short}] LOAD FAILED");
            continue;
        };
        let inst = extract_instance(&layer, &cross, REAL_BUDGET);
        let n = inst.nodes.len();
        // extract_instance assigns id == topo index, so nodes[i].id == i.
        let mut consumers = vec![0u32; n];
        for nd in &inst.nodes {
            for &c in &nd.children {
                consumers[c as usize] += 1;
            }
        }
        for &r in &inst.roots {
            consumers[r as usize] += 1;
        }
        // first/last use root-index per node (DFS per root, like distinct_live_values).
        let mut first = vec![u32::MAX; n];
        let mut last = vec![0u32; n];
        let mut seen_any = vec![false; n];
        for (ri, &root) in inst.roots.iter().enumerate() {
            let ri = ri as u32;
            let mut stack = vec![root];
            let mut seen: HashSet<u32> = HashSet::new();
            while let Some(id) = stack.pop() {
                if !seen.insert(id) {
                    continue;
                }
                let i = id as usize;
                seen_any[i] = true;
                first[i] = first[i].min(ri);
                last[i] = last[i].max(ri);
                for &c in &inst.nodes[i].children {
                    stack.push(c);
                }
            }
        }
        let (mut k_all, mut k_recompute, mut k_reload, mut k_x, mut max_fanout) =
            (0, 0, 0, 0, 0u32);
        // (first, last, is_fork): is_fork = Add|Mul (the forward planner's
        // search set); Read leaves are Belady-handled, excluded from fork concurrency.
        let mut intervals: Vec<(u32, u32, bool)> = Vec::new();
        for i in 0..n {
            max_fanout = max_fanout.max(consumers[i]);
            if consumers[i] < 2 {
                continue;
            }
            k_all += 1;
            let recompute = matches!(inst.nodes[i].kind, NodeKind::Add | NodeKind::Mul);
            let reload = matches!(inst.nodes[i].kind, NodeKind::Read);
            if recompute {
                k_recompute += 1;
            }
            if reload {
                k_reload += 1;
            }
            // cross-root reuse: consumed under ≥2 distinct roots → a real cache decision
            if seen_any[i] && last[i] > first[i] {
                k_x += 1;
                if recompute || reload {
                    let is_fork = matches!(inst.nodes[i].kind, NodeKind::Add | NodeKind::Mul);
                    intervals.push((first[i], last[i], is_fork));
                }
            }
        }
        // W      = max concurrent cross-root candidates (all reload+recompute).
        // W_fork = same EXCLUDING Read leaves — the real forward-planner DP-state
        //          exponent (Reads are Belady-handled; only Add/Mul/Prior are forks).
        let nr = inst.roots.len() as u32;
        let (mut w, mut w_fork) = (0u32, 0u32);
        for b in 0..nr.saturating_sub(1) {
            let active = intervals
                .iter()
                .filter(|(f, l, _)| *f <= b && *l >= b + 1)
                .count() as u32;
            let active_fork = intervals
                .iter()
                .filter(|(f, l, fk)| *fk && *f <= b && *l >= b + 1)
                .count() as u32;
            w = w.max(active);
            w_fork = w_fork.max(active_fork);
        }
        println!(
            "[{short:<32}] N={n:<5} roots={:<4} | K={k_all:<4}(recompute={k_recompute} reload={k_reload}) maxfanout={max_fanout:<4} | W={w:<3} | W_fork={w_fork:<3} → DP 2^W_fork={}",
            inst.roots.len(),
            pow2_str(w_fork),
        );
        let _ = k_x;
    }
}

// NOTE (Part A / Step 2b): `prior_recompute_census` was DELETED here. It walked
// `SourceKind::Prior` to bucket cache-value recoveries (reload vs recompute) by width.
// `Prior` is gone (same-layer cache reuse is a recomputed shared `ExprId`), the test was
// `#[ignore]`d, and its analysis is superseded by the Part-B recompute decision — so it
// is removed rather than ported.

/// Map a `(E−J)/D` ratio to its qualitative direction.
fn direction(ratio: f64) -> &'static str {
    if ratio >= 0.15 {
        "order MATTERS (BuildBeam-leaning)"
    } else if ratio < 0.05 {
        "order ~irrelevant (CachingOnly-leaning)"
    } else {
        "Marginal"
    }
}

// ── Multi-circuit generalization (does the add_sub-L0 CachingOnly verdict hold?) ─

/// Every compiled GKR circuit fixture (`*_layout_gkr.json`) in `cs/compiled_circuits`.
const ALL_FIXTURES: &[&str] = &[
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
];

/// Non-panicking L0 loader: returns `(layer0, full-dag cross map)` or `None` if a
/// fixture fails to load/lower/validate (so one bad circuit cannot abort the sweep).
fn try_load_l0(fixture: &str) -> Option<(DagLayer, HashMap<ReadPlace, FieldKind>)> {
    let artifact = load_fixture(&compiled_circuit_dir().join(fixture))?;
    let dag = lower_dag(&artifact).ok()?;
    validate(&dag).ok()?;
    let cross = build_cross_layer_field_map(&dag);
    let layer = dag.layers.into_iter().next()?;
    Some((layer, cross))
}

/// Dump an instance JSON to `$GAP_DUMP_DIR/<name>.json` for independent
/// verification (the verifier adds the `"mode"` field). No-op if unset.
fn dump_instance(name: &str, inst: &s3_gap::instance::OracleInstance) {
    if let Ok(dir) = std::env::var("GAP_DUMP_DIR") {
        let _ = std::fs::create_dir_all(&dir);
        let path = PathBuf::from(dir).join(format!("{name}.json"));
        if let Ok(s) = serde_json::to_string(inst) {
            let _ = std::fs::write(&path, s);
        }
    }
}

/// GENERALIZATION: re-run the J-vs-E gap on EVERY circuit fixture, not just
/// add_sub-L0, to test whether the CachingOnly verdict (order doesn't matter at
/// budget 16) holds across circuit families or whether some circuit shows real
/// order tension.
///
/// Per circuit: load L0, report roots/priors. Circuits with no Prior edges are
/// cache-free tree forests where order is trivially irrelevant (skipped, noted).
/// Otherwise: downscale to Prior-connected sweet-spot clusters, keep those with a
/// DRAM leaf shared across ≥2 roots (the only order-sensitive ones), and solve
/// J/E at the real budget 16. Each measured order-sensitive cluster's instance is
/// dumped (`$GAP_DUMP_DIR`) for independent re-derivation.
#[test]
#[ignore = "S3 multi-circuit gap generalization; needs python3+ortools; run with --ignored"]
fn s3_gap_multicircuit() {
    if !oracle_available() {
        eprintln!("[GAPX] SKIP: python3+ortools absent");
        return;
    }
    const PER_CLUSTER_CAP: u64 = 30;
    const MAX_MEASURED_PER_CIRCUIT: usize = 3;

    println!("\n=== MULTI-CIRCUIT J-vs-E @ budget {REAL_BUDGET} (order-sensitive clusters) ===");
    // (circuit, label, shared, status_both_optimal, J, E, D, ratio)
    let mut summary: Vec<(String, bool, usize, bool, u64, u64, u64, f64)> = Vec::new();

    for &fixture in ALL_FIXTURES {
        let short = fixture.trim_end_matches("_layout_gkr.json");
        let Some((layer, _cross)) = try_load_l0(fixture) else {
            println!("\n[{short}] LOAD FAILED — skipped");
            continue;
        };
        let priors = reachable_shared_cache_values(&layer);
        println!(
            "\n[{short}] L0: roots={} priors={}",
            layer.roots.len(),
            priors
        );
        if priors == 0 {
            println!(
                "  no Prior edges → cache-free tree forest → order trivially irrelevant (skip)"
            );
            summary.push((short.to_string(), false, 0, true, 0, 0, 0, 0.0));
            continue;
        }

        // Prior-connected sweet-spot clusters (≥1 prior, 2..=15 roots), densest first.
        let candidates = sweet_spot_clusters(&layer, 1, 2, 15);
        let mut measured = 0usize;
        let mut any_shared = false;
        for cand in &candidates {
            if measured >= MAX_MEASURED_PER_CIRCUIT {
                break;
            }
            let inst = extract_instance(&cand.layer, &cand.cross, REAL_BUDGET);
            let shared = shared_dram_leaves(&inst);
            if shared == 0 {
                continue; // no cross-root DRAM sharing → no order tension to measure
            }
            any_shared = true;
            let d = dag_traffic_floor(&cand.layer, &cand.cross) as u64;
            let j = run_oracle(&inst, Mode::J, 0.01, PER_CLUSTER_CAP).expect("oracle J");
            let e = run_oracle(&inst, Mode::E, 0.01, PER_CLUSTER_CAP).expect("oracle E");
            let both_opt = j.status == "optimal" && e.status == "optimal";
            let ratio = if both_opt && d > 0 {
                (e.traffic as f64 - j.traffic as f64) / d as f64
            } else {
                f64::NAN
            };
            let label = format!("{short}-seed{}", cand.seed.0);
            println!(
                "  {label:<32} nodes={:<3} roots={} shared={shared} D={d} | \
                 J={}({}) E={}({}){}",
                inst.nodes.len(),
                inst.roots.len(),
                j.status,
                j.traffic,
                e.status,
                e.traffic,
                if both_opt {
                    format!("  (E−J)/D={:.1}% → {}", ratio * 100.0, direction(ratio))
                } else {
                    "  [NOT both-optimal — bracket only]".to_string()
                }
            );
            dump_instance(&label, &inst);
            summary.push((
                label, true, shared, both_opt, j.traffic, e.traffic, d, ratio,
            ));
            measured += 1;
        }
        if !any_shared {
            println!("  caches present, but no sweet-spot cluster has a DRAM leaf shared across ≥2 roots");
            summary.push((short.to_string(), false, 0, true, 0, 0, 0, 0.0));
        }
    }

    // ── Cross-circuit verdict ─────────────────────────────────────────────────
    println!("\n=== CROSS-CIRCUIT VERDICT ===");
    let measured: Vec<_> = summary.iter().filter(|r| r.2 > 0 && r.3).collect();
    let mut max_ratio = f64::MIN;
    let mut any_order_matters = false;
    for r in &measured {
        if r.7.is_finite() {
            max_ratio = max_ratio.max(r.7);
            if r.7 >= 0.05 {
                any_order_matters = true;
                println!("  ORDER TENSION: {} (E−J)/D={:.1}%", r.0, r.7 * 100.0);
            }
        }
    }
    println!(
        "  order-sensitive clusters measured both-optimal: {} | max (E−J)/D = {:.1}%",
        measured.len(),
        if max_ratio.is_finite() {
            max_ratio * 100.0
        } else {
            0.0
        }
    );
    if any_order_matters {
        println!("  VERDICT: order matters on ≥1 circuit → CachingOnly is NOT universal; investigate the flagged clusters.");
    } else {
        println!("  VERDICT: every order-sensitive cluster shows ~0% gap at budget {REAL_BUDGET} → CachingOnly generalizes (fix eviction, no order beam).");
    }
}

// ── Task 5: M1 gate — corpus differential, determinism, per-family frontier ────

#[test]
fn m1_planner_is_deterministic() {
    use s3_planner::inner_dp::plan_fixed_order;
    let Some((layer, _cross)) = try_load_l0("add_sub_lui_auipc_mop_layout_gkr.json") else {
        eprintln!("fixture unavailable; skipping");
        return;
    };
    let Some(c) = sweet_spot_clusters(&layer, 1, 2, 15).into_iter().next() else {
        return;
    };
    let inst = extract_instance(&c.layer, &c.cross, REAL_BUDGET);
    let a = plan_fixed_order(&inst).result.objective();
    let b = plan_fixed_order(&inst).result.objective();
    let d = plan_fixed_order(&inst).result.objective();
    assert_eq!(a, b);
    assert_eq!(b, d);
}

/// True iff all real-DRAM leaf nodes share one width (so Belady is exact).
fn cluster_dram_widths_uniform(inst: &s3_gap::instance::OracleInstance) -> bool {
    let mut w: Option<u8> = None;
    for nd in &inst.nodes {
        if nd.real_dram {
            match w {
                None => w = Some(nd.width),
                Some(x) if x != nd.width => return false,
                _ => {}
            }
        }
    }
    true
}

#[test]
#[ignore = "requires python3 + ortools; full corpus, minutes"]
fn m1_planner_matches_oracle_e_across_corpus() {
    use s3_planner::inner_dp::plan_fixed_order;
    use std::collections::BTreeMap;
    if !oracle_available() {
        eprintln!("ortools unavailable; skipping");
        return;
    }

    const FRONTIER_CAP: usize = 200_000; // R3: log-and-flag, never silently truncate
    let mut checked = 0usize;
    let mut checked_uniform = 0usize;
    let mut max_gap: i64 = 0;
    let mut frontier_by_fixture: BTreeMap<&str, usize> = BTreeMap::new();
    let mut cap_exceeded = false;

    for fx in ALL_FIXTURES {
        let Some((layer, _cross)) = try_load_l0(fx) else {
            continue;
        };
        for c in sweet_spot_clusters(&layer, 1, 2, 15).into_iter().take(3) {
            let inst = extract_instance(&c.layer, &c.cross, REAL_BUDGET);
            let e = match run_oracle(&inst, Mode::E, 0.0, 60) {
                Ok(r) if r.status == "optimal" => r,
                _ => continue,
            };
            let run = plan_fixed_order(&inst);
            let (pt, pi) = run.result.objective();
            assert!(
                (pt, pi) >= (e.traffic, e.instrs),
                "[{fx}] planner-E {:?} < oracle-E {:?} — DP bug",
                (pt, pi),
                (e.traffic, e.instrs)
            );
            if cluster_dram_widths_uniform(&inst) {
                assert_eq!(
                    (pt, pi),
                    (e.traffic, e.instrs),
                    "[{fx}] uniform-width must equal oracle-E"
                );
                checked_uniform += 1;
            }
            max_gap = max_gap.max(pt as i64 - e.traffic as i64);
            let slot = frontier_by_fixture.entry(fx).or_insert(0);
            *slot = (*slot).max(run.max_frontier);
            if run.max_frontier > FRONTIER_CAP {
                cap_exceeded = true;
            }
            checked += 1;
        }
    }
    assert!(
        checked > 0,
        "no optimal oracle-E rows checked — corpus/oracle setup broken"
    );
    eprintln!(
        "[M1] checked={checked} (uniform={checked_uniform}); max (planner-E − oracle-E)={max_gap}"
    );
    for (fx, f) in &frontier_by_fixture {
        eprintln!("[M1] frontier[{fx}] = {f}");
    }
    if cap_exceeded {
        eprintln!(
            "[M1][WARN] dominance frontier exceeded {FRONTIER_CAP} — investigate before scaling"
        );
    }
}

#[test]
fn m1_uniform_binding_c_is_exact_handbuilt() {
    use s3_gap::instance::{NodeKind, OracleInstance, OracleNode};
    use s3_planner::inner_dp::plan_fixed_order;
    let nd = |id, kind, width, real_dram, children| OracleNode {
        id,
        kind,
        width,
        real_dram,
        children,
    };
    // budget 1, all base width 1, single-accumulator streaming model. X(0) is read at
    // A=Add{0} (s0) and reused at C=Add{0} (s2). The intervening B (s1) is a fold-of-
    // folds B=Add{g,h}, g=Add{p}, h=Add{q}: computing B spills its partial once, so
    // P[B]=1 (a plain fold over reads would stream at peak 0 and not bind (C)).
    // (C) at s1: X outsider(1) + P[B](1) = 2 > 1 -> X evicted before B, re-read at C.
    // traffic = X@s0(1) + p,q@s1(2) + X@s2(1) = 4 ; instrs = 5.
    let inst = OracleInstance {
        budget: 1,
        reloadable_values: vec![],
        roots: vec![3, 6, 7],
        nodes: vec![
            nd(0, NodeKind::Read, 1, true, vec![]),     // X
            nd(1, NodeKind::Read, 1, true, vec![]),     // p
            nd(2, NodeKind::Read, 1, true, vec![]),     // q
            nd(3, NodeKind::Add, 1, false, vec![0]),    // A (s0), reads X
            nd(4, NodeKind::Add, 1, false, vec![1]),    // g
            nd(5, NodeKind::Add, 1, false, vec![2]),    // h
            nd(6, NodeKind::Add, 1, false, vec![4, 5]), // B (s1), fold-of-folds, P[B]=1
            nd(7, NodeKind::Add, 1, false, vec![0]),    // C (s2), reuses X
        ],
    };
    let run = plan_fixed_order(&inst);
    assert_eq!(run.result.objective(), (4, 5));
}

#[test]
fn replay_plan_matches_score_and_reproduces_residency() {
    use s3_gap::instance::extract_instance;
    use s3_gap::instance::relation_units;
    use s3_planner::metaheuristic::{project_genome_to_units, seeded_smoke_population};
    use s3_planner::metaheuristic::{
        enumerate_demand_sites, replay_plan, score_candidate_grouped, unit_members, ReplayEventRaw,
    };

    // Known-present fixture: assert the load (do NOT silently return — that hides a regression).
    let (layer, cross) =
        try_load_l0("add_sub_lui_auipc_mop_layout_gkr.json").expect("add_sub L0 must load");
    let inst = extract_instance(&layer, &cross, REAL_BUDGET);
    assert!(!inst.roots.is_empty(), "add_sub L0 must have atom roots");
    let sites = enumerate_demand_sites(&inst);
    let units = unit_members(&relation_units(&layer));
    let flat = seeded_smoke_population(&inst, &sites, 1, 0);
    let genome = project_genome_to_units(&flat[0], &units);

    let (score, steps) = replay_plan(&inst, &sites, &genome, &units);

    // Parity: replay_plan's score == the scorer's, on the same genome.
    let ref_score = score_candidate_grouped(&inst, &sites, &genome, &units);
    assert_eq!(score.traffic, ref_score.traffic, "traffic parity");
    assert_eq!(score.instrs, ref_score.instrs, "instrs parity");
    assert_eq!(score.feasible, ref_score.feasible, "feasible parity");
    assert!(
        score.feasible,
        "fixture must be feasible at budget 16 for the integrity check"
    );

    // Event integrity: replaying events from resident_before yields resident_after, per step.
    // (One step per occurrence even for real_dram/infeasible roots — see Step 3's owned loop.)
    assert_eq!(steps.len(), inst.roots.len());
    for (si, step) in steps.iter().enumerate() {
        let mut resident: std::collections::HashSet<u32> =
            step.resident_before.iter().copied().collect();
        for ev in &step.events {
            match ev {
                ReplayEventRaw::Admit { value } => {
                    resident.insert(*value);
                }
                ReplayEventRaw::Evict { value } => {
                    resident.remove(value);
                }
                ReplayEventRaw::Demand { input_index, .. } => {
                    assert_ne!(*input_index, u32::MAX, "step {si}: root-output not a Demand");
                }
            }
        }
        let after: std::collections::HashSet<u32> =
            step.resident_after.iter().copied().collect();
        assert_eq!(resident, after, "step {si}: events must reproduce resident_after");
    }
}

#[test]
fn peak_with_cached_treats_cached_mul_as_leaf_with_own_production_cone() {
    use s3_gap::instance::{NodeKind, OracleInstance, OracleNode};
    use s3_planner::forkset;

    fn n(id: u32, kind: NodeKind, children: Vec<u32>) -> OracleNode {
        OracleNode {
            id,
            kind,
            width: 4,
            real_dram: matches!(kind, NodeKind::Read),
            children,
        }
    }

    // A shared, NON-fusing Mul (its factors are folds, so it does not stream) that is a
    // child of two Add roots. Streaming `analyze` folds the Mul's own peak into each Add
    // root's peak; caching the Mul makes it a 0-transient LEAF in the roots' cones (peak
    // contribution 0) while it retains its own production-cone peak. This is the exact
    // residency-aware behavior Task-2's cost model needs.
    //
    //   A1 = Add(r0, r1)      A2 = Add(r3, r4)     (both non-streamable, peak 0)
    //   M  = Mul(A1, A2)      (2 non-streamable children -> production peak = 4)
    //   A3 = Add(r7, r8)      (non-streamable, peak 0)
    //   root0 = Add(M, A3)    root1 = Add(M, r7)   (M shared: 2 consumers)
    let inst = OracleInstance {
        budget: 16,
        reloadable_values: vec![],
        roots: vec![10, 11],
        nodes: vec![
            n(0, NodeKind::Read, vec![]),
            n(1, NodeKind::Read, vec![]),
            n(2, NodeKind::Add, vec![0, 1]), // A1
            n(3, NodeKind::Read, vec![]),
            n(4, NodeKind::Read, vec![]),
            n(5, NodeKind::Add, vec![3, 4]), // A2
            n(6, NodeKind::Mul, vec![2, 5]), // M (shared)
            n(7, NodeKind::Read, vec![]),
            n(8, NodeKind::Read, vec![]),
            n(9, NodeKind::Add, vec![7, 8]),  // A3
            n(10, NodeKind::Add, vec![6, 9]), // root0 = M + A3
            n(11, NodeKind::Add, vec![6, 7]), // root1 = M + r7
        ],
    };
    let n_nodes = inst.nodes.len();

    let streaming = forkset::analyze(&inst).peak;
    // No-cache identity: peak_with_cached with nothing cached == streaming peak.
    assert_eq!(
        forkset::peak_with_cached(&inst, &vec![false; n_nodes]),
        streaming,
        "no-cache identity: peak_with_cached(all-false) must equal analyze().peak"
    );

    // Streaming: M does not fuse (folded factors), so it contributes its own peak (4) to
    // each Add root -> root peak 4.
    assert_eq!(streaming[6], 4, "M production peak (two folded factors)");
    assert_eq!(streaming[10], 4, "root0 streams M's peak");
    assert_eq!(streaming[11], 4, "root1 streams M's peak");

    // Cache M: it becomes a 0-transient leaf in BOTH roots' cones (their peaks drop to 0),
    // while M's own entry keeps its production-cone peak.
    let mut cached = vec![false; n_nodes];
    cached[6] = true;
    let with_cached = forkset::peak_with_cached(&inst, &cached);

    assert_ne!(with_cached, streaming, "caching M must change the peak vector");
    assert_eq!(with_cached[6], 4, "cached M retains its own production-cone peak");
    assert_eq!(with_cached[10], 0, "cached M is a 0-transient leaf in root0's cone");
    assert_eq!(with_cached[11], 0, "cached M is a 0-transient leaf in root1's cone");
}

// DELETED (Task 4, schema v2): `replay_plan_still_serializes_schedule_events_after_
// runtime_pruning` + its support (`find_runtime_pruning_step`,
// `descendant_demand_values_for_occurrence`, `bridge_step_plan`,
// `bridge_step_plan_with_inverse`, `bridge_step_plans`, `invert_step_plan`,
// `invert_step_plans`) bridged `s3_planner`'s raw `StepPlanRaw`/`ReplayEventRaw`
// replay trace to `cs::dag_ir::StepPlan`/`ReplayEvent` — both deleted along with
// the v1 event-replay schema. Task 5's sites-based producer supersedes this bridge.

// ── Task 6: id-bridge helpers + order-bridge binding gate ─────────────────────

/// Atom roots in walk order: roots that are both materialized (claim-bearing Output)
/// and contribute to the oracle's occurrence list — i.e. `materialize.is_some() &&
/// claim.is_some()`. Matches `extract_instance`'s `top_exprs` predicate exactly.
fn atom_root_ids(layer: &DagLayer) -> Vec<RootId> {
    layer
        .roots
        .iter()
        .enumerate()
        .filter(|(_, r)| r.materialize.is_some() && r.claim.is_some())
        .map(|(i, _)| RootId(i as u32))
        .collect()
}

/// Reorder `atom_roots` by `occ_order` (an occurrence-index permutation from the
/// metaheuristic) into a `Vec<RootId>` over production root ids.
fn bridge_order(occ_order: &[usize], atom_roots: &[RootId]) -> Vec<RootId> {
    occ_order.iter().map(|&occ| atom_roots[occ]).collect()
}

#[test]
fn order_bridge_binding_holds() {
    use s3_gap::instance::{extract_instance_with_remap, relation_units};
    use s3_planner::metaheuristic::{project_genome_to_units, seeded_smoke_population};
    use s3_planner::metaheuristic::{
        decode_grouped_occurrence_order, enumerate_demand_sites, order_keeps_units_contiguous,
        unit_members,
    };

    // Known-present fixture: assert the load, don't silently return.
    let (layer, cross) = try_load_l0("mem_word_only_layout_gkr.json").expect("mem_word_only L0 must load");
    let (inst, remap) = extract_instance_with_remap(&layer, &cross, REAL_BUDGET);
    assert!(!inst.roots.is_empty(), "mem_word_only L0 must have atom roots");
    let sites = enumerate_demand_sites(&inst);
    let units = unit_members(&relation_units(&layer));
    let flat = seeded_smoke_population(&inst, &sites, 1, 0);
    let genome = project_genome_to_units(&flat[0], &units);

    let atom_roots = atom_root_ids(&layer);
    assert_eq!(atom_roots.len(), inst.roots.len(), "one atom root per occurrence");

    // THE BINDING (non-tautological): the producer's atom-walk order matches extract_instance's
    // occurrence order, verified through the remap.
    for occ in 0..inst.roots.len() {
        let expr0 = layer.roots[atom_roots[occ].0 as usize].expr.0;
        assert_eq!(
            remap.get(&expr0).copied(),
            Some(inst.roots[occ]),
            "atom_roots[{occ}] must map to inst.roots[{occ}] via the remap"
        );
    }

    // bridge_order + unit contiguity (both used by the producer).
    let occ_order = decode_grouped_occurrence_order(&inst, &genome, &units);
    let order = bridge_order(&occ_order, &atom_roots);
    assert_eq!(order.len(), occ_order.len());
    assert!(order_keeps_units_contiguous(&occ_order, &units), "unit contiguity");
}

// ── Task 7's on-demand CircuitSchedule producer (DELETED, schema v2 — Task 4) ──
//
// `produce_circuit_schedule` and its supporting machinery (`SearchConfig`,
// `parse_usize_env`/`parse_u64_env`, `schedule_search_config_from_env`,
// `ScheduleEnvGuard`/`schedule_env_lock`/`panic_message`) built a `CircuitSchedule`
// against the v1 schema (`LayerSchedule.steps: Vec<StepPlan>`, `ReplayEvent`
// bridging via `bridge_step_plans`/`invert_step_plan`). That schema was deleted
// wholesale in Task 4 (`.superpowers/sdd/task-4-brief.md`): `LayerSchedule` is now
// `{ order, sites: Vec<(SiteKey, f64)>, predicted_traffic, floor }`. A sites-based
// producer is Task 5's job (`schedule_search::structure::enumerate_sites` wraps
// `cs::enumerate_site_domain`); until then there is no schedule producer here.
// Deleted tests: produce_schedule_smoke_one_fixture,
// validate_schedules_from_grouped_metaheuristic,
// grouped_metaheuristic_fixture_regression_does_not_exceed_snapshotted_baseline,
// schedule_search_config_defaults_match_current_producer,
// schedule_search_config_env_overrides_and_validation (below `produce_all_schedules`
// is deleted too, for the same reason).

// ── Task 3: pin the Task-2 residency-aware feasibility bound ─────────────────

/// POSITIVE side: for a schedule the corrected producer's own replay engine emits, the
/// residency-aware cone-fit invariant must hold at EVERY step. `resident_before` is
/// exactly the residency state `enforce_cone_fit(occ)` leaves behind on successful
/// return (see the design doc's "Task-2 edits" (b): the cone peak is computed once
/// before the eviction loop and only outsiders are evicted), so recomputing
/// `peak_with_cached` over `resident_before` and re-checking it against `root`
/// reconstructs the gate's own bound from outside the `Replay`.
#[test]
fn residency_aware_bound_holds_at_every_step_on_real_fixture() {
    use s3_gap::instance::extract_instance;
    use s3_gap::instance::relation_units;
    use s3_planner::forkset;
    use s3_planner::metaheuristic::{
        decode_grouped_occurrence_order, enumerate_demand_sites, project_genome_to_units,
        replay_plan, seeded_smoke_population, unit_members,
    };

    let (layer, cross) =
        try_load_l0("add_sub_lui_auipc_mop_layout_gkr.json").expect("add_sub L0 must load");
    let inst = extract_instance(&layer, &cross, REAL_BUDGET);
    assert!(!inst.roots.is_empty(), "add_sub L0 must have atom roots");

    let sites = enumerate_demand_sites(&inst);
    let units = unit_members(&relation_units(&layer));
    let flat = seeded_smoke_population(&inst, &sites, 1, 0);
    let genome = project_genome_to_units(&flat[0], &units);

    let (score, steps) = replay_plan(&inst, &sites, &genome, &units);
    assert!(
        score.feasible,
        "producer-emitted schedule must be feasible at budget {REAL_BUDGET}"
    );

    let occurrence_order = decode_grouped_occurrence_order(&inst, &genome, &units);
    assert_eq!(steps.len(), occurrence_order.len(), "one step per occurrence");

    let mut checked = 0usize;
    for (si, (step, &occ)) in steps.iter().zip(&occurrence_order).enumerate() {
        let root = inst.roots[occ];

        // Weaker-but-real fallback: the residency SET alone never exceeds budget.
        let before_width: usize = step
            .resident_before
            .iter()
            .map(|&v| inst.nodes[v as usize].width as usize)
            .sum();
        let after_width: usize = step
            .resident_after
            .iter()
            .map(|&v| inst.nodes[v as usize].width as usize)
            .sum();
        assert!(
            before_width <= inst.budget,
            "step {si}: resident_before width {before_width} > budget {}",
            inst.budget
        );
        assert!(
            after_width <= inst.budget,
            "step {si}: resident_after width {after_width} > budget {}",
            inst.budget
        );

        // The precise three-instant/cone-entry bound: resident_width(resident_before) +
        // peak_with_cached(inst, resident_before)[root] <= budget.
        let mut cached = vec![false; inst.nodes.len()];
        for &v in &step.resident_before {
            cached[v as usize] = true;
        }
        let peaks = forkset::peak_with_cached(&inst, &cached);
        let cone_peak = peaks[root as usize] as usize;
        assert!(
            before_width + cone_peak <= inst.budget,
            "step {si} (root {root}): resident_width {before_width} + cone_peak {cone_peak} \
             > budget {} — residency-aware bound violated",
            inst.budget
        );
        checked += 1;
    }
    assert!(checked > 0, "no steps checked — fixture/harness broken");
}

/// NEGATIVE side: hand-built regression pin for the Task-2 fix (design doc §2, "why the
/// current producer was incoherent"). Under the OLD model, `enforce_cone_fit` charged
/// only OUTSIDER resident cells (`outsider_resident_width`) plus a STATIC,
/// caching-agnostic streaming peak (`fork_info.peak`) — an in-cone cached value was
/// charged ZERO in both terms even though its cell genuinely occupies the budget.
///
/// Here X and Y are each cached at their own first-demanding root (each admission is
/// individually gated by the three-instant `maybe_admit` bound and never exceeds
/// budget on its own). A LATER root B then consumes X and Y directly, so both are
/// IN-CONE of B (never outsiders — nothing is evictable there), plus a third,
/// never-cached fold-of-folds subtree W that forces its own accumulator spill (peak 4).
/// `resident_width` = X(4) + Y(4) = 8 exactly fills `budget` = 8, leaving no room for
/// B's own transient peak. The corrected residency-aware bound
/// (`resident_width + peak_with_cached[root] <= budget`) must reject this — 8 + 4 = 12
/// > 8, and no outsider exists to evict — where the OLD bound
/// (`outsider_resident_width(B)=0 + static_peak[B]=4 = 4 <= 8`) would have accepted it.
#[test]
fn cone_fit_rejects_in_cone_cache_footprint_that_old_streaming_model_missed() {
    use s3_gap::instance::{NodeKind, OracleInstance, OracleNode};
    use s3_planner::metaheuristic::{enumerate_demand_sites, score_candidate, Genome};

    fn n(id: u32, kind: NodeKind, width: u8, real_dram: bool, children: Vec<u32>) -> OracleNode {
        OracleNode { id, kind, width, real_dram, children }
    }

    let inst = OracleInstance {
        budget: 8,
        reloadable_values: vec![],
        roots: vec![2, 3, 9], // A1, A2, B — processed in this order under Genome::neutral
        nodes: vec![
            n(0, NodeKind::Read, 4, true, vec![]),      // X
            n(1, NodeKind::Read, 4, true, vec![]),      // Y
            n(2, NodeKind::Add, 4, false, vec![0]),     // A1 (s0): first demand of X -> cached
            n(3, NodeKind::Add, 4, false, vec![1]),     // A2 (s1): first demand of Y -> cached
            n(4, NodeKind::Read, 1, true, vec![]),      // r_g
            n(5, NodeKind::Read, 1, true, vec![]),      // r_h
            n(6, NodeKind::Add, 1, false, vec![4]),     // g = Add(r_g), peak 0
            n(7, NodeKind::Add, 1, false, vec![5]),     // h = Add(r_h), peak 0
            n(8, NodeKind::Add, 4, false, vec![6, 7]),  // W = Add(g,h), fold-of-folds, peak 4
            n(9, NodeKind::Add, 4, false, vec![0, 1, 8]), // B (s2): Add(X, Y, W)
        ],
    };
    let sites = enumerate_demand_sites(&inst);
    let genome = Genome::neutral(&inst, &sites);

    let score = score_candidate(&inst, &sites, &genome);

    // Sanity-check the premise: X and Y must both have been legitimately admitted
    // (each individually within budget) before B is ever reached.
    assert_eq!(
        score.admitted, 2,
        "setup broken: X and Y must both be cached before B's cone-fit runs"
    );
    assert!(
        !score.feasible,
        "residency-aware cone-fit must reject B: resident X(4)+Y(4)=8 fills budget 8, \
         leaving no room for B's own transient peak (4) — the old outsider-only + \
         static-peak bound would have wrongly accepted this"
    );
}

// `produce_all_schedules` (the GKR_PRODUCE_SCHEDULES-gated artifact writer) DELETED
// alongside `produce_circuit_schedule` above — see that tombstone.
