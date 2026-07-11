//! Task 12: the backward-VM CENSUS. Emits (to stdout, `#[ignore]`d) the markdown
//! tables answering the direction doc's §7 questions: per (circuit, layer) ×
//! regime × budget × policy × round, what budget/traffic does the backward pass
//! demand?
//!
//! Run: `cargo test -p gkr_eval_isa --release bwd_census -- --ignored --nocapture`.
//!
//! Three tables:
//!   * **A. Structural** — per (circuit, layer, regime, budget): feasibility
//!     (INFEASIBLE(floor=N) below floor), max_live_cells (Ext: bucket demand =
//!     cells/4), n_instr + encoded lanes, floor, realized÷floor, cell spill,
//!     skipped-decoder mark. The budget knee lives here.
//!   * **B. Traffic** — per (circuit, layer, regime, policy) at a representative
//!     feasible budget (no-decisions traffic is budget-invariant — asserted):
//!     per-round r1..r4 read bytes (T0+T2) + fold-store + geometric total. The
//!     round/policy/depth tradeoff lives here.
//!   * **C. L0 search** — per (circuit, L0, regime): floor, search budget,
//!     baseline vs searched traffic, delta. Search runs ONLY for L0 layers.

mod common;

use std::collections::HashMap;

use common::{load_fixture, schedule_stem};
use cs::gkr_compiler::dag_ir::{bwd_roots, bwd_traffic_floor, lower_dag, validate, BwdRegime};
use gkr_eval_isa::bwd::compile::{compile_distilled, BwdCompiledLayer};
use gkr_eval_isa::bwd::cost::{geometric_total, round_cost};
use gkr_eval_isa::bwd::distill::{distill, DistilledLayer};
use gkr_eval_isa::bwd::search::{search_bwd_layer, BwdSearchConfig};
use gkr_eval_isa::bwd::source::MaterializationPolicy;
use gkr_eval_isa::fwd::compile::build_cross_layer_field_map;
use gkr_eval_isa::fwd::encode::encode;
use gkr_eval_isa::fwd::error::CompileError;

/// The 12 pinned Global-Constraints fixtures (same list as
/// `bwd_distill_fixtures.rs` / `fwd_vm_desc_census.rs`).
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

const BUDGETS: &[usize] = &[16, 24, 32, 48, 64];
const MAX_ROUND: u8 = 4;

const POLICIES: &[(&str, MaterializationPolicy)] = &[
    ("AlwaysMat", MaterializationPolicy::AlwaysMaterialize),
    ("Lazy≤2", MaterializationPolicy::LazyUpTo(2)),
    ("Lazy≤4", MaterializationPolicy::LazyUpTo(4)),
];

/// Try to compile `d` at `budget` (no decisions). `Ok(Some(_))` feasible;
/// `Ok(None)` = below floor; the error carries the floor.
fn try_compile(d: &DistilledLayer, budget: usize) -> Result<BwdCompiledLayer, usize> {
    match compile_distilled(d, budget, None) {
        Ok(c) => Ok(c),
        Err(CompileError::BudgetBelowFloor { floor, .. }) => Err(floor),
        Err(e) => panic!("unexpected compile error: {e:?}"),
    }
}

/// The smallest census budget that is feasible for `d`, else the layer's floor
/// (always feasible). Returns `(budget, compiled)`.
fn smallest_feasible(d: &DistilledLayer) -> (usize, BwdCompiledLayer) {
    let mut floor = 0usize;
    for &b in BUDGETS {
        match try_compile(d, b) {
            Ok(c) => return (b, c),
            Err(f) => floor = f,
        }
    }
    // None of the census budgets fit — compile at the floor (feasible by def).
    let c = compile_distilled(d, floor, None).expect("compile at floor must be feasible");
    (floor, c)
}

#[test]
#[ignore = "census: run explicitly with --ignored --nocapture"]
fn bwd_census() {
    let t_start = std::time::Instant::now();

    // Layers to search (L0 of every fixture, both regimes) collected for Table C.
    let mut structural: Vec<String> = Vec::new();
    let mut traffic: Vec<String> = Vec::new();
    let mut search_rows: Vec<String> = Vec::new();

    // §7 aggregates.
    let mut bucket_hist: HashMap<usize, usize> = HashMap::new(); // min feasible budget → count (Ext)
    let mut ext_floor_over_64: Vec<(String, usize)> = Vec::new();

    for name in FIXTURES {
        let stem = schedule_stem(name);
        let artifact = load_fixture(name);
        let dag = lower_dag(&artifact).unwrap_or_else(|e| panic!("[{name}] lower_dag: {e}"));
        validate(&dag).unwrap_or_else(|e| panic!("[{name}] validate: {e}"));
        let cross = build_cross_layer_field_map(&dag);

        for (li, layer) in dag.layers.iter().enumerate() {
            if bwd_roots(layer).is_empty() {
                continue; // nothing to prove backward
            }
            for regime in [BwdRegime::R0, BwdRegime::Ext] {
                let d = distill(layer, regime, &cross, None);
                let skip_mark = if d.skipped_decoder { " [SKIPPED-DECODER]" } else { "" };
                // Traffic floor (role-neutral DRAM cells: distinct Read leaves,
                // Ext=4/leaf). Distinct from the PLACEMENT floor (smem lanes)
                // that `BudgetBelowFloor` reports.
                let tfloor = bwd_traffic_floor(layer, regime, &cross);
                let rk = format!("{stem} L{li} {regime:?}");

                // ── Table A: structural, per budget ──────────────────────────
                let mut representative: Option<(usize, BwdCompiledLayer)> = None;
                for &budget in BUDGETS {
                    match try_compile(&d, budget) {
                        Ok(c) => {
                            let enc = encode(&c.program).map(|v| v.len()).unwrap_or(0);
                            let mlc = c.stats.max_live_cells;
                            let buckets = if regime == BwdRegime::Ext {
                                format!("{} (b{})", mlc, mlc / 4)
                            } else {
                                format!("{mlc}")
                            };
                            // Realized role-neutral DRAM traffic (cells) vs floor:
                            // the uncached re-read multiplicity (fwd-comparable).
                            let realized = c.stats_ext.global + c.stats_ext.fold_traffic;
                            let ratio = if tfloor > 0 {
                                format!("{:.1}", realized as f64 / tfloor as f64)
                            } else {
                                "-".to_string()
                            };
                            let spill = c.stats.cell_stores;
                            structural.push(format!(
                                "| {rk} | b{budget} | {buckets} | {} | {} | {realized} | {tfloor} | {ratio} | {} |{skip_mark}",
                                c.stats.program_lanes, enc, spill,
                            ));
                            if representative.is_none() {
                                representative = Some((budget, c));
                            }
                        }
                        Err(f) => {
                            structural.push(format!(
                                "| {rk} | b{budget} | INFEASIBLE(place-floor={f} lanes) | - | - | - | {tfloor} | - | - |{skip_mark}"
                            ));
                        }
                    }
                }

                // Representative feasible compile for traffic (fall back to floor).
                let (rep_budget, rep) = match representative {
                    Some(rc) => rc,
                    None => smallest_feasible(&d),
                };

                // Ext bucket-demand histogram (smallest smem budget that fits =
                // the placement floor when above all census budgets).
                if regime == BwdRegime::Ext {
                    *bucket_hist.entry(rep_budget).or_insert(0) += 1;
                    if rep_budget > 64 {
                        ext_floor_over_64.push((rk.clone(), rep_budget));
                    }
                }

                // Budget-invariance guard: no-decisions traffic must not depend
                // on budget. Compare the representative's round-1 AlwaysMat cost
                // against the largest feasible budget's.
                if let Ok(hi) = try_compile(&d, *BUDGETS.last().unwrap()) {
                    let a = round_cost(&rep, MaterializationPolicy::AlwaysMaterialize, 1, &d.cross_fields);
                    let b = round_cost(&hi, MaterializationPolicy::AlwaysMaterialize, 1, &d.cross_fields);
                    assert_eq!(
                        a, b,
                        "[{rk}] no-decisions traffic must be budget-invariant (b{rep_budget} vs b{})",
                        BUDGETS.last().unwrap()
                    );
                }

                // ── Table B: traffic, per policy (at rep budget) ─────────────
                for (pname, policy) in POLICIES {
                    let mut per_round = String::new();
                    let mut store_round = String::new();
                    for r in 1..=MAX_ROUND {
                        let rc = round_cost(&rep, *policy, r, &d.cross_fields);
                        per_round.push_str(&format!(" {} |", rc.read_bytes()));
                        store_round.push_str(&format!("{}/", rc.fold_store_bytes));
                    }
                    let g = geometric_total(&rep, *policy, MAX_ROUND, &d.cross_fields);
                    traffic.push(format!(
                        "| {rk} @b{rep_budget} | {pname} |{per_round} {} | {:.1} |{skip_mark}",
                        store_round.trim_end_matches('/'),
                        g.total_bytes(),
                    ));
                }

                // ── Table C: L0 search (at the smallest PLACEMENT-feasible
                // budget — search_bwd_layer requires the None baseline feasible).
                if li == 0 && !d.skipped_decoder {
                    let cfg = BwdSearchConfig::default(); // smoke scale: pop 4, evals 40
                    let sb = rep_budget; // = smallest feasible smem budget (lanes)
                    let base_traffic = rep.stats_ext.global + rep.stats_ext.fold_traffic;
                    let out = search_bwd_layer(layer, regime, &cross, sb, &cfg);
                    let searched = out.stats.global + out.stats.fold_traffic;
                    let used = out.decisions.is_some();
                    let delta = base_traffic as i64 - searched as i64;
                    search_rows.push(format!(
                        "| {rk} | b{sb} | {tfloor} | {base_traffic} | {searched} | {delta} | {} |",
                        if used { "decisions" } else { "baseline" },
                    ));
                }
            }
        }
    }

    // ── Emit ──────────────────────────────────────────────────────────────────
    println!("# Backward-VM Census\n");
    println!("Budgets: {BUDGETS:?} (bf lanes; Ext buckets = lanes/4). Rounds 1..={MAX_ROUND} + geometric total over rounds 0..={MAX_ROUND} (weight 2^-r).\n");

    println!("## Table A — Structural (per circuit × layer × regime × budget)\n");
    println!("`max_live` is smem occupancy in lanes (Ext buckets = lanes/4); INFEASIBLE rows give the PLACEMENT floor (min feasible lanes). `realized` / `traffic_floor` are role-neutral DRAM cells (uncached, budget-invariant); `real÷floor` is the uncached per-leaf re-read multiplicity.\n");
    println!("| layer | budget | max_live (Ext: buckets) | n_instr | enc_lanes | realized | traffic_floor | real÷floor | cell_stores |");
    println!("|---|---|---|---|---|---|---|---|---|");
    for r in &structural {
        println!("{r}");
    }

    println!("\n## Table B — Traffic (per circuit × layer × regime × policy; read bytes T0+T2 per row)\n");
    println!("no-decisions traffic is budget-invariant (guarded); tallied at the smallest feasible budget shown.\n");
    println!("| layer @budget | policy | r1 | r2 | r3 | r4 | fold-store r1/r2/r3/r4 | geo-total B |");
    println!("|---|---|---|---|---|---|---|---|");
    for r in &traffic {
        println!("{r}");
    }

    println!("\n## Table C — L0 search on/off (search runs for L0 layers only)\n");
    println!("Search budget = smallest placement-feasible smem budget (lanes). Traffic is role-neutral DRAM cells (global + fold).\n");
    println!("| L0 layer | search budget | traffic_floor | baseline traffic | searched traffic | Δ (base−search) | winner |");
    println!("|---|---|---|---|---|---|---|");
    for r in &search_rows {
        println!("{r}");
    }

    // ── §7 aggregates ──────────────────────────────────────────────────────────
    println!("\n## Ext bucket-demand distribution (smallest budget that fits, per Ext layer)\n");
    let mut budgets: Vec<usize> = bucket_hist.keys().copied().collect();
    budgets.sort_unstable();
    for b in budgets {
        println!("- b{b}: {} Ext layers", bucket_hist[&b]);
    }
    if !ext_floor_over_64.is_empty() {
        println!("\nExt placement floors above b64 (need >16 buckets — sequential-accumulation follow-up):");
        for (rk, lanes) in &ext_floor_over_64 {
            println!("- {rk}: placement floor {lanes} lanes ({} buckets)", lanes / 4);
        }
    }

    println!("\ncensus runtime: {:.1?}", t_start.elapsed());
}
