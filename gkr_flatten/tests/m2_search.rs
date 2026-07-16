//! M2 exit gate: budget-sweep search harness (spec
//! .agents/specs/2026-07-16-gkr-flattener-m2-search-design.md §7).
//!
//! Run (fast smoke, non-ignored — CI-safe):
//!   `cargo test -p gkr_flatten --test m2_search smoke`
//! Run (full sweep, release-only):
//!   `RUSTFLAGS="-Awarnings" cargo test -p gkr_flatten --release --test m2_search -- --ignored --nocapture`

use std::collections::{BTreeMap, HashMap};

use cs::gkr_compiler::dag_ir::eval::eval_layer_root;
use cs::gkr_compiler::dag_ir::{BwdRegime, DagLayer, ExprId, FieldKind, ReadPlace, RootId};
use gkr_eval_isa::bwd::distill::distill;
use gkr_flatten::analysis::size_layer;
use gkr_flatten::dag::LayerView;
use gkr_flatten::fixtures::load_circuit;
use gkr_flatten::genome::{decode, Genome};
use gkr_flatten::ir::interpret;
use gkr_flatten::oracle::SiteTable;
use gkr_flatten::resolvers::HashResolvers;
use gkr_flatten::search::{ga, greedy, naive_fill_genome, neutral_genome, score, GaParams, Score};
use gkr_flatten::walk::flatten_budgeted;

const HEAVY_QUARTET: [&str; 4] = [
    "bigint_with_extended_control_layout_gkr.json",
    "keccak_special5_layout_gkr.json",
    "blake2_with_extended_control_layout_gkr.json",
    "unified_reduced_machine_layout_gkr.json",
];

/// One searchable layer instance: a fwd L0 or a bwd Ext-distilled L0, with
/// whatever the LayerView needs kept alive.
struct Instance {
    label: String,
    layer: DagLayer,
    cross: HashMap<ReadPlace, FieldKind>,
    // The bwd distill's per-expr field overrides. `distill(..).field_overrides`
    // and `LayerView::new`'s third parameter are both `BTreeMap<ExprId,
    // FieldKind>` in the landed code (the brief's skeleton showed a `HashMap`
    // placeholder — the landed type wins). `None` for fwd layers.
    overrides: Option<BTreeMap<ExprId, FieldKind>>,
}

// bwd instances hard-fail here (no silent_catch): M1 measured 0 construct
// skips, so a new panic is a regression to surface, not to skip.

/// Forward L0: load the circuit, own a clone of layer 0 and its cross-layer
/// field map. No field overrides on the forward path.
fn fwd_instance(name: &str) -> Instance {
    let (dag, cross) = load_circuit(name);
    Instance { label: format!("{name} [fwd L0]"), layer: dag.layers[0].clone(), cross, overrides: None }
}

/// Backward Ext-distilled L0: distill layer 0 in the `Ext` regime and own the
/// rebuilt layer, its merged cross-layer field map, and the per-expr field
/// overrides — mirrors `tests/m1_parity.rs::probe_fixture`. The distilled
/// layer owns all three, so they move straight into the `Instance`.
fn bwd_instance(name: &str) -> Instance {
    let (dag, cross) = load_circuit(name);
    let distilled = distill(&dag.layers[0], BwdRegime::Ext, &cross, None);
    Instance {
        label: format!("{name} [bwd Ext L0]"),
        layer: distilled.layer,
        cross: distilled.cross_fields,
        overrides: Some(distilled.field_overrides),
    }
}

struct SweepRow {
    budget: Option<u32>,
    ceiling: u64,
    floor: u64,
    neutral: Score,
    naive: Score,
    greedy: Score,
    ga_best: Score,
}

/// Runs baselines + greedy + GA on one instance at one budget; asserts the
/// per-budget hard gates; returns the calibration row and the best genome.
fn run_cell(inst: &Instance, budget: Option<u32>, params: &GaParams) -> (SweepRow, Genome) {
    let view = LayerView::new(&inst.layer, &inst.cross, inst.overrides.as_ref());
    let roots: Vec<ExprId> = inst.layer.roots.iter().map(|r| r.expr).collect();
    let report = size_layer(&view, &roots);
    // Gate 3: peak assert precondition.
    if let Some(b) = budget {
        assert!(b >= report.peak, "{}: budget {b} < neutral peak {}", inst.label, report.peak);
    }
    let table = SiteTable::enumerate(&view);
    let n = inst.layer.roots.len();

    let s_neutral = score(&view, &table, &neutral_genome(&table, n), budget);
    let s_naive = score(&view, &table, &naive_fill_genome(&table, n), budget);
    let g_greedy = greedy(&view, &table, n, budget);
    let s_greedy = score(&view, &table, &g_greedy, budget);
    let seeds = vec![neutral_genome(&table, n), naive_fill_genome(&table, n), g_greedy.clone()];
    let (g_best, s_ga) = ga(&view, &table, n, budget, params, seeds);

    // Gate 2: determinism (same seed -> same best).
    let seeds2 = vec![neutral_genome(&table, n), naive_fill_genome(&table, n), g_greedy.clone()];
    let (g_best2, s_ga2) = ga(&view, &table, n, budget, params, seeds2);
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
/// `eval_layer_root` (rows 0, 1, 17; shared HashResolvers seed 7).
fn assert_parity(inst: &Instance, table: &SiteTable, best: &Genome, budget: Option<u32>) {
    let view = LayerView::new(&inst.layer, &inst.cross, inst.overrides.as_ref());
    let out = flatten_budgeted(&view, &decode(best, table), budget);
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

/// Fast, non-ignored smoke: add_sub fwd L0, one tight budget, tiny GA.
#[test]
fn smoke_add_sub_tight_budget() {
    let inst = fwd_instance("add_sub_lui_auipc_mop_layout_gkr.json");
    let view = LayerView::new(&inst.layer, &inst.cross, None);
    let roots: Vec<ExprId> = inst.layer.roots.iter().map(|r| r.expr).collect();
    let report = size_layer(&view, &roots);
    let params = GaParams { pop: 8, max_evals: 120, elites: 2, descent_flips: 4, seed: 0 };
    let (row, best) = run_cell(&inst, Some(report.peak + 2), &params);
    assert!(row.ga_best <= row.neutral);
    let table = SiteTable::enumerate(&view);
    assert_parity(&inst, &table, &best, Some(report.peak + 2));
}

/// The M2 exit sweep (spec §7). Release-only. GA strength per spec §6:
/// pop 64 / evals 2000 / seeds {0, 1, 2} — the win gate takes best-of-seeds.
#[test]
#[ignore = "release-only full sweep"]
fn m2_sweep() {
    let mut calibration: Vec<(String, Vec<SweepRow>)> = Vec::new();

    for name in HEAVY_QUARTET {
        for inst in [fwd_instance(name), bwd_instance(name)] {
            let view = LayerView::new(&inst.layer, &inst.cross, inst.overrides.as_ref());
            let roots: Vec<ExprId> = inst.layer.roots.iter().map(|r| r.expr).collect();
            let report = size_layer(&view, &roots);
            let table = SiteTable::enumerate(&view);
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
                    assert_parity(&inst, &table, &best, budget);
                }
                rows.push(row);
            }
            calibration.push((inst.label.clone(), rows));
        }
    }

    // Calibration readout (non-gating): FB2 band ~8-20%, E4c curve shape.
    println!("\n== M2 calibration ==");
    for (label, rows) in &calibration {
        for r in rows {
            let win = 100.0 * (r.neutral.traffic - r.ga_best.traffic) as f64
                / r.neutral.traffic.max(1) as f64;
            println!(
                "{label} @ {:?}: ceiling {} floor {} | neutral {} naive {} greedy {} ga {} | win {win:.1}%",
                r.budget, r.ceiling, r.floor, r.neutral.traffic, r.naive.traffic,
                r.greedy.traffic, r.ga_best.traffic
            );
        }
    }
}
