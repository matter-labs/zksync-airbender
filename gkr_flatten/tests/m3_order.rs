//! M3 Phase-0 gate: a dead-aware re-baseline of the M2 budget-sweep harness
//! (spec .agents/specs/2026-07-16-gkr-flattener-m2-search-design.md §7, run
//! under M3's counted walker). It mirrors `tests/m2_search.rs`'s
//! `run_cell`/`assert_parity`/`SweepRow` structure exactly, with one change:
//! every score/greedy/GA call threads the per-value use countdown
//! (`counts = table.use_counts(n_exprs)`, one per instance) through the
//! `search::*_ctx` variants, so the dead-aware residency (`Residency::mark_dead`)
//! engages. Each calibration row is tagged `phase0` so the M2 and M3 audit
//! tables diff line-by-line.
//!
//! Run (fast smoke, non-ignored — CI-safe):
//!   `cargo test -p gkr_flatten --test m3_order smoke`
//! Run (full sweep, release-only):
//!   `RUSTFLAGS="-Awarnings" cargo test -p gkr_flatten --release --test m3_order -- --ignored --nocapture`

use cs::gkr_compiler::dag_ir::eval::eval_layer_root;
use cs::gkr_compiler::dag_ir::{ExprId, RootId};
use gkr_flatten::analysis::size_layer;
use gkr_flatten::dag::LayerView;
use gkr_flatten::fixtures::{bwd_instance, fwd_instance, Instance};
use gkr_flatten::genome::{decode, Genome};
use gkr_flatten::ir::interpret;
use gkr_flatten::oracle::{SiteTable, UseCounts};
use gkr_flatten::resolvers::HashResolvers;
use gkr_flatten::search::{
    ga_ctx, greedy_ctx, naive_fill_genome, neutral_genome, score_ctx, EvalCtx, GaParams, Score,
};
use gkr_flatten::walk::flatten_counted;

const HEAVY_QUARTET: [&str; 4] = [
    "bigint_with_extended_control_layout_gkr.json",
    "keccak_special5_layout_gkr.json",
    "blake2_with_extended_control_layout_gkr.json",
    "unified_reduced_machine_layout_gkr.json",
];

struct SweepRow {
    budget: Option<u32>,
    ceiling: u64,
    floor: u64,
    neutral: Score,
    naive: Score,
    greedy: Score,
    ga_best: Score,
}

/// Runs baselines + greedy + GA on one instance at one budget, ALL through the
/// counted (`*_ctx` + `counts`) search variants; asserts the per-budget hard
/// gates; returns the calibration row and the best genome. Deltas from M2's
/// `run_cell`: `counts = table.use_counts(n_exprs)` per instance and every
/// score/greedy/GA call routes through the `_ctx` variant with that context.
fn run_cell(inst: &Instance, budget: Option<u32>, params: &GaParams) -> (SweepRow, Genome) {
    let view = LayerView::new(&inst.layer, &inst.cross, inst.overrides.as_ref());
    let roots: Vec<ExprId> = inst.layer.roots.iter().map(|r| r.expr).collect();
    let report = size_layer(&view, &roots);
    // Gate 3: peak assert precondition.
    if let Some(b) = budget {
        assert!(b >= report.peak, "{}: budget {b} < neutral peak {}", inst.label, report.peak);
    }
    let table = SiteTable::enumerate(&view);
    // M3 delta: the per-value use countdown for the dead-aware walk.
    let counts = table.use_counts(inst.layer.exprs.len());
    let ctx = EvalCtx { counts: Some(&counts), ..EvalCtx::default() };
    let n = inst.layer.roots.len();

    let s_neutral = score_ctx(&view, &table, &neutral_genome(&table, n), budget, &ctx);
    let s_naive = score_ctx(&view, &table, &naive_fill_genome(&table, n), budget, &ctx);
    let g_greedy = greedy_ctx(&view, &table, n, budget, &ctx);
    let s_greedy = score_ctx(&view, &table, &g_greedy, budget, &ctx);
    let seeds = vec![neutral_genome(&table, n), naive_fill_genome(&table, n), g_greedy.clone()];
    let (g_best, s_ga) = ga_ctx(&view, &table, n, budget, params, seeds, &ctx);

    // Gate 2: determinism (same seed -> same best).
    let seeds2 = vec![neutral_genome(&table, n), naive_fill_genome(&table, n), g_greedy.clone()];
    let (g_best2, s_ga2) = ga_ctx(&view, &table, n, budget, params, seeds2, &ctx);
    assert_eq!(g_best, g_best2, "{}: GA nondeterministic", inst.label);
    assert_eq!(s_ga, s_ga2);

    // Gate 1: bracket, on every headline score.
    let ceiling = s_neutral.traffic;
    for s in [s_neutral, s_naive, s_greedy, s_ga] {
        assert!(s.traffic >= report.floor && s.traffic <= ceiling,
            "{}: bracket violation {s:?} not in [{}, {ceiling}]", inst.label, report.floor);
    }
    // Gate 5 (sanity half): GA ties-or-beats greedy (elitist seeding).
    assert!(s_ga <= s_greedy, "{}: GA lost to its own greedy seed", inst.label);
    // Gate 5 (endpoint): unbounded budget reaches the floor.
    if budget.is_none() {
        assert_eq!(s_ga.traffic, report.floor, "{}: unbounded best must equal floor", inst.label);
    }
    (SweepRow { budget, ceiling, floor: report.floor,
                neutral: s_neutral, naive: s_naive, greedy: s_greedy, ga_best: s_ga },
     if s_ga <= s_greedy { g_best } else { g_greedy })
}

/// Gate 4: the best genome's program still interprets bit-exact vs
/// `eval_layer_root` (rows 0, 1, 17; shared HashResolvers seed 7). M3 delta:
/// the program is re-flattened through the SAME counted walk (`counts` passed
/// to `flatten_counted`) that scored it, so parity validates the dead-aware
/// program actually selected — not a counts-free stand-in.
fn assert_parity(inst: &Instance, table: &SiteTable, best: &Genome, budget: Option<u32>, counts: &UseCounts) {
    let view = LayerView::new(&inst.layer, &inst.cross, inst.overrides.as_ref());
    let out = flatten_counted(&view, &decode(best, table), budget, Some(counts));
    let r = HashResolvers { seed: 7 }.bundle();
    for row in [0usize, 1, 17] {
        let got = interpret(&out.program, &inst.layer, row, &r);
        for (i, _) in inst.layer.roots.iter().enumerate() {
            let want = eval_layer_root(&inst.layer, RootId(i as u32), row, &r);
            assert_eq!(got[&RootId(i as u32)], want,
                "{} root {i} row {row}: searched-genome parity broke", inst.label);
        }
    }
}

/// Fast, non-ignored smoke: add_sub fwd L0, one tight budget, tiny GA — counted.
#[test]
fn smoke_add_sub_counted_tight_budget() {
    let inst = fwd_instance("add_sub_lui_auipc_mop_layout_gkr.json");
    let view = LayerView::new(&inst.layer, &inst.cross, None);
    let roots: Vec<ExprId> = inst.layer.roots.iter().map(|r| r.expr).collect();
    let report = size_layer(&view, &roots);
    let params = GaParams { pop: 8, max_evals: 120, elites: 2, descent_flips: 4, seed: 0, ..GaParams::default() };
    let (row, best) = run_cell(&inst, Some(report.peak + 2), &params);
    assert!(row.ga_best <= row.neutral);
    let table = SiteTable::enumerate(&view);
    let counts = table.use_counts(inst.layer.exprs.len());
    assert_parity(&inst, &table, &best, Some(report.peak + 2), &counts);
}

/// The M3 Phase-0 re-baseline sweep: the full M2 grid (8 instances × 6 budgets
/// × best-of-seeds {0,1,2}) re-run under the counted walker, with every M2 hard
/// gate re-asserted per cell. Release-only. GA strength per spec §6: pop 64 /
/// evals 2000 / seeds {0, 1, 2} — the win gate takes best-of-seeds.
#[test]
#[ignore = "release-only full sweep (phase-0 re-baseline)"]
fn phase0_rebaseline() {
    let mut calibration: Vec<(String, Vec<SweepRow>)> = Vec::new();

    for name in HEAVY_QUARTET {
        for inst in [fwd_instance(name), bwd_instance(name)] {
            let view = LayerView::new(&inst.layer, &inst.cross, inst.overrides.as_ref());
            let roots: Vec<ExprId> = inst.layer.roots.iter().map(|r| r.expr).collect();
            let report = size_layer(&view, &roots);
            let table = SiteTable::enumerate(&view);
            let counts = table.use_counts(inst.layer.exprs.len());
            assert!((report.floor as u128) < report.ceiling, "no reuse to search");
            let tight = [Some(report.peak), Some(report.peak + 2)];
            let budgets = [Some(report.peak), Some(report.peak + 2),
                           Some(12), Some(16), Some(24), None];
            let mut rows = Vec::new();
            for budget in budgets {
                let budget = budget.map(|b| b.max(report.peak)); // 12/16/24 clamped to feasibility
                // Best-of-seeds {0,1,2}; run_cell's internal double-run
                // covers per-seed determinism.
                let (row, best) = [0u64, 1, 2]
                    .into_iter()
                    .map(|seed| run_cell(&inst, budget, &GaParams { seed, ..GaParams::default() }))
                    .min_by_key(|(row, _)| row.ga_best)
                    .unwrap();
                // Gate 5 (win): strict beat over both no-intelligence
                // baselines at each tight budget.
                if tight.contains(&budget) {
                    assert!(row.ga_best < row.neutral,
                        "{} @ {budget:?}: search failed to beat neutral", inst.label);
                    assert!(row.ga_best < row.naive,
                        "{} @ {budget:?}: search failed to beat naive-fill", inst.label);
                    // Gate 4 on tight budgets only (parity of searched IR).
                    assert_parity(&inst, &table, &best, budget, &counts);
                }
                rows.push(row);
            }
            calibration.push((inst.label.clone(), rows));
        }
    }

    // Calibration readout (non-gating): FB2 band ~8-20%, E4c curve shape. Each
    // row is `phase0`-tagged; everything after the tag is byte-format-identical
    // to M2's readout so the two audit tables diff line-by-line.
    println!("\n== phase0 calibration ==");
    for (label, rows) in &calibration {
        for r in rows {
            let win = 100.0 * (r.neutral.traffic - r.ga_best.traffic) as f64
                / r.neutral.traffic.max(1) as f64;
            println!(
                "phase0 {label} @ {:?}: ceiling {} floor {} | neutral {} naive {} greedy {} ga {} | win {win:.1}%",
                r.budget, r.ceiling, r.floor, r.neutral.traffic, r.naive.traffic,
                r.greedy.traffic, r.ga_best.traffic
            );
        }
    }
}
