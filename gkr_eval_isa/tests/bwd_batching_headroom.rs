//! DIAGNOSTIC (not a gate): budget-adaptive batching headroom + distance-to-floor prize.
//!
//! SP1 proved every wide backward L0 *fits* `b16`. That is a feasibility bit; it says
//! nothing about (a) how far the realized traffic sits above the DRAM read floor at that
//! budget, or (b) what the streamed lowering spent — and it never asks whether the
//! commutativity of add/mul/fma can be used to split the fold to reclaim either. This
//! census sizes both prizes with exact numbers so a follow-up chunker design is grounded.
//!
//! Two tables, per wide backward L0 (every fixture, both regimes):
//!
//!   * **Table 1 — the K=1 tax & the idle resource.** The current streamed lowering folds
//!     one operand at a time (K=1): it stashes the running partial around every compound
//!     child and never spends a spare lane. This table PROVES that: `peak`, `n_instr`, and
//!     `cell_stores` are asserted budget-INVARIANT (b16 == b64), so `idle = budget - peak`
//!     grows with the budget while the lowering reclaims none of it. `cell_stores` is the
//!     smem-write traffic a budget-adaptive chunker could attack (upper bound on the
//!     program-size prize).
//!
//!   * **Table 2 — the distance-to-floor prize.** `real÷floor` and `reread_waste`
//!     (= realized − floor) are the DRAM cells caching could reclaim if the freed budget
//!     were spent on residency (the dominant lever — the heavy circuits run 10–15× above
//!     floor). The `FoldSource` reuse concentration (distinct origins / max reuse /
//!     reuse-excess, from `foldsource_use_histogram`) says whether that reuse is
//!     concentrated in a few hot sources (cheap to cache) or spread out.
//!
//! Uncached (`decisions: None`) traffic is budget-invariant, so Table 2 is measured once at
//! b16. Run:
//!   `cargo test -p gkr_eval_isa --release bwd_batching_headroom -- --ignored --nocapture`
//! (bigint needs `RUST_MIN_STACK=1073741824`).

mod common;

use std::collections::{BTreeMap, BTreeSet};

use cs::gkr_compiler::dag_ir::{bwd_traffic_floor, BwdRegime};
use gkr_eval_isa::bwd::compile::{
    compile_distilled_legacy_only, compile_distilled_streamed, BwdCompiledLayer,
};
use gkr_eval_isa::bwd::distill::{distill, DistilledLayer};
use gkr_eval_isa::bwd::source::BwdSpecial;
use gkr_eval_isa::fwd::isa::{DstLine, Instr, OperandField, OperandLine, Program};

/// Budgets swept for the idle-resource / invariance columns (bf lanes; Ext buckets = /4).
const BUDGETS: &[usize] = &[16, 24, 32, 48, 64];

/// The 12 pinned Global-Constraints fixtures (same list as `bwd_census.rs`).
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

/// Streamed compile at `budget` (the SP1 fallback lowering, unconditionally engaged).
fn streamed(d: &DistilledLayer, budget: usize) -> BwdCompiledLayer {
    compile_distilled_streamed(d, budget, None, true).expect("streamed feasible")
}

/// Does the legacy pre-materialize lowering already fit b16? (`false` ⟹ streaming is what
/// `compile_distilled` selects — the wide L0s this diagnostic is about.)
fn legacy_fits_b16(d: &DistilledLayer) -> bool {
    compile_distilled_legacy_only(d, 16, None).is_ok()
}

/// Reuse concentration of a compiled layer's `FoldSource` operands: (distinct origins,
/// total uses, max reuse, #origins reused ≥2×, Σ(use−1) reuse-excess).
fn fold_reuse(c: &BwdCompiledLayer) -> (usize, usize, usize, usize, usize) {
    let hist = common::foldsource_use_histogram(c);
    let distinct = hist.len();
    let total: usize = hist.values().sum();
    let max = hist.values().copied().max().unwrap_or(0);
    let reused = hist.values().filter(|&&v| v >= 2).count();
    let excess = total.saturating_sub(distinct); // Σ(v−1)
    (distinct, total, max, reused, excess)
}

#[test]
#[ignore = "diagnostic: run explicitly with --ignored --nocapture"]
fn bwd_batching_headroom() {
    let mut t1: Vec<String> = Vec::new(); // Table 1 rows
    let mut t2: Vec<String> = Vec::new(); // Table 2 rows

    // Aggregates over the STREAMING-SELECTED L0s (the ones this diagnostic targets).
    let mut sum_reread_waste = 0usize;
    let mut sum_idle_b16 = 0usize;
    let mut streamed_count = 0usize;
    let mut invariance_ok = true;

    for name in FIXTURES {
        let stem = name.trim_end_matches("_layout_gkr.json");
        // L0 is the widest layer — the one streaming was built for.
        let (layer, cross) = common::load_layer(name, 0);
        for regime in [BwdRegime::R0, BwdRegime::Ext] {
            let d = distill(&layer, regime, &cross, None);
            if d.skipped_decoder {
                continue;
            }
            let sel = if legacy_fits_b16(&d) { "legacy" } else { "STREAM" };
            let is_stream = sel == "STREAM";

            // ── budget invariance (K=1 proof): b16 vs b64 identical peak/prog/stores ──
            let c16 = streamed(&d, 16);
            let c64 = streamed(&d, 64);
            let peak = c16.stats.max_live_cells;
            let n_instr = c16.stats.program_lanes;
            let stores = c16.stats.cell_stores;
            let budget_blind = peak == c64.stats.max_live_cells
                && n_instr == c64.stats.program_lanes
                && stores == c64.stats.cell_stores;
            invariance_ok &= budget_blind;

            // ── Table 1: the idle resource across budgets (peak is invariant) ──
            let idle: Vec<String> = BUDGETS
                .iter()
                .map(|&b| format!("{}", b.saturating_sub(peak)))
                .collect();
            let mark = if budget_blind { "" } else { " ⚠BUDGET-SENSITIVE" };
            t1.push(format!(
                "| {stem} L0 {regime:?} | {sel} | {peak} | {n_instr} | {stores} | {} |{mark}",
                idle.join(" | "),
            ));

            // ── Table 2: distance-to-floor prize (uncached ⟹ budget-invariant) ──
            let floor = bwd_traffic_floor(&layer, regime, &cross);
            let global = c16.stats_ext.global;
            let fold_traffic = c16.stats_ext.fold_traffic;
            let realized = global + fold_traffic;
            let waste = realized.saturating_sub(floor);
            let ratio = if floor > 0 {
                format!("{:.1}", realized as f64 / floor as f64)
            } else {
                "-".into()
            };
            let (distinct, uses, max_reuse, reused, excess) = fold_reuse(&c16);
            t2.push(format!(
                "| {stem} L0 {regime:?} | {sel} | {floor} | {realized} | {ratio} | {waste} | {global} | {fold_traffic} | {distinct} | {uses} | {max_reuse} | {reused} | {excess} |",
            ));

            if is_stream {
                streamed_count += 1;
                sum_reread_waste += waste;
                sum_idle_b16 += 16usize.saturating_sub(peak);
            }
        }
    }

    // The K=1 tax proof is a real invariant of the current lowering; fail loudly if a
    // future change makes the streamed program budget-adaptive (that would be the chunker
    // landing — update this diagnostic deliberately when it does).
    assert!(
        invariance_ok,
        "expected the current streamed lowering to be budget-BLIND (K=1); a row is \
         budget-sensitive — the batching chunker may have landed. Update this diagnostic."
    );

    println!("# Backward batching-headroom diagnostic\n");
    println!(
        "Budgets {BUDGETS:?} (bf lanes; Ext buckets = /4). `sel` = STREAM when legacy \
         overflows b16 (⟹ `compile_distilled` picks the streamed fallback), else legacy.\n"
    );

    println!("## Table 1 — the K=1 tax & the idle resource\n");
    println!(
        "`peak` / `n_instr` / `cell_stores` are ASSERTED budget-invariant (b16 == b64): the \
         streamed lowering is K=1 (folds one operand at a time, stashes the partial around \
         every compound child, spends no spare lane). `idle@B = B − peak` therefore grows \
         with the budget while the lowering reclaims NONE of it. `cell_stores` = smem-write \
         traffic a budget-adaptive chunker could attack.\n"
    );
    println!("| L0 layer | sel | peak | n_instr | cell_stores | idle@16 | idle@24 | idle@32 | idle@48 | idle@64 |");
    println!("|---|---|---|---|---|---|---|---|---|---|");
    for r in &t1 {
        println!("{r}");
    }

    println!("\n## Table 2 — the distance-to-floor prize\n");
    println!(
        "`floor` = distinct DRAM read leaves (Ext=4 cells/leaf); `realized` = global + \
         fold_traffic; `real÷floor` = per-leaf re-read multiplicity; `reread_waste` = \
         realized − floor = DRAM cells caching could reclaim given residency room. \
         `FoldSource` reuse: `distinct` origins, total `uses`, `max_reuse`, `#reused` \
         (≥2×), `excess` = Σ(use−1) = fold gathers a perfect cache would erase.\n"
    );
    println!("| L0 layer | sel | floor | realized | real÷floor | reread_waste | global | fold_traffic | distinct | uses | max_reuse | #reused | excess |");
    println!("|---|---|---|---|---|---|---|---|---|---|---|---|---|");
    for r in &t2 {
        println!("{r}");
    }

    println!("\n## Prize summary (STREAMING-SELECTED L0s only)\n");
    println!("- streaming-selected L0 instances: {streamed_count}");
    println!(
        "- Σ reread_waste = **{sum_reread_waste} DRAM cells** above floor (the residency/caching prize)"
    );
    println!(
        "- Σ idle@b16 = **{sum_idle_b16} lanes** sitting unused at b16 (the resource the K=1 lowering leaves on the table)"
    );
    println!("- budget-invariance (K=1) held on every row: {invariance_ok}");
}

// ── Lifetime-aware prize sizing ────────────────────────────────────────────────
//
// The Table-2 `excess` is a static UPPER bound: it assumes a perfect cache holding every
// reused source at once. Realizing it needs each cached source resident across its LIFETIME
// (first→last use), so the binding limit is the PEAK CONCURRENT live-cache set, not the
// count. This analysis extracts per-origin use positions from the compiled program and
// brackets the prize with three tiers of decreasing optimism:
//
//   (1) `excess` (Table 2)            — perfect cache, no lifetimes. OVERSTATES.
//   (2) lifetime-aware, CURRENT ORDER — `WS_peak` = cells to reclaim 100% on this schedule;
//       `greedy%@B` = feasible prize under a cache of B extra lanes (respects capacity at
//       every instruction). A rigorous static bracket — but the fold ORDER is fixed.
//   (3) realizable joint (order+cache) — commutativity lets us REORDER to shorten lifetimes
//       (shrinking `WS_peak`), so tier (3) ≥ tier (2). That number needs the actual
//       order+residency OPTIMIZER (the bwd search / SP3) — it is NOT statically derivable.
//
// So: greedy%@B (current order) ≤ realizable@B ≤ excess. This test reports the tier-(2)
// bracket and the lifetime distribution that says how much reordering headroom tier (3) has.

/// Per read-origin (`!is_vs`) `FoldSource`, the sorted instruction indices at which it is
/// used. Keyed by origin (merges descs sharing an origin — caching the value serves all).
/// VS-origin folds are compute-only (zero DRAM gather) and excluded from the DRAM prize.
fn read_origin_positions(c: &BwdCompiledLayer) -> Vec<Vec<usize>> {
    let mut map: BTreeMap<String, (Vec<usize>, bool)> = BTreeMap::new();
    for (idx, instr) in c.program.instrs.iter().enumerate() {
        let ops: Vec<&OperandLine> = match instr {
            Instr::Add { operands, .. } | Instr::Mul { operands, .. } => operands.iter().collect(),
            Instr::Fma { pairs, .. } => pairs.iter().flat_map(|(l, r)| [l, r]).collect(),
            Instr::Mov { src: Some(op), .. } => vec![op],
            Instr::Mov { src: None, .. } => vec![],
        };
        for op in ops {
            if let OperandLine::Special { desc } = op {
                if let Some(BwdSpecial::FoldSource { origin }) = c.specials.get(*desc) {
                    let e = map
                        .entry(format!("{origin:?}"))
                        .or_insert_with(|| (Vec::new(), origin.is_vs()));
                    e.0.push(idx);
                }
            }
        }
    }
    map.into_values().filter(|(_, vs)| !*vs).map(|(p, _)| p).collect()
}

/// Reuse working-set peak (cells): max concurrent 4-cell residency over all reused origins'
/// [first,last] spans — the cache size to reclaim 100% of the current-order excess.
fn ws_peak(reused: &[(usize, usize, usize)]) -> usize {
    let mut ev: Vec<(usize, i64)> = Vec::with_capacity(reused.len() * 2);
    for &(f, l, _) in reused {
        ev.push((f, 4));
        ev.push((l + 1, -4));
    }
    ev.sort_unstable();
    let (mut cur, mut peak) = (0i64, 0i64);
    for (_, d) in ev {
        cur += d;
        peak = peak.max(cur);
    }
    peak as usize
}

/// Feasible caching prize (saved gathers) under a cache of `cap` cells, greedily admitting
/// reused origins by density (saved ÷ span) and enforcing capacity at every instruction.
/// A LOWER bound on the current-order caching optimum (density-greedy is a heuristic).
fn greedy_prize(reused_by_density: &[(usize, usize, usize)], n: usize, cap: usize) -> usize {
    let mut occ = vec![0usize; n];
    let mut prize = 0usize;
    for &(f, l, saved) in reused_by_density {
        if (f..=l).all(|t| occ[t] + 4 <= cap) {
            for t in f..=l {
                occ[t] += 4;
            }
            prize += saved;
        }
    }
    prize
}

#[test]
#[ignore = "diagnostic: run explicitly with --ignored --nocapture"]
fn bwd_reuse_lifetimes() {
    // Extra cache lanes (beyond the fold working set) the curve is sampled at (buckets ×4).
    const EXTRA: &[usize] = &[4, 8, 16, 32, 52]; // 1,2,4,8,13 Ext buckets
    let mut rows: Vec<String> = Vec::new();

    for name in FIXTURES {
        let stem = name.trim_end_matches("_layout_gkr.json");
        let (layer, cross) = common::load_layer(name, 0);
        let d = distill(&layer, BwdRegime::Ext, &cross, None);
        if d.skipped_decoder {
            continue;
        }
        let c = streamed(&d, 16);
        let n = c.program.instrs.len();
        let peak = c.stats.max_live_cells;
        let reread_waste = (c.stats_ext.global + c.stats_ext.fold_traffic)
            .saturating_sub(bwd_traffic_floor(&layer, BwdRegime::Ext, &cross));

        // Per read-origin lifetimes; keep the reused ones (count ≥ 2).
        let mut reused: Vec<(usize, usize, usize)> = Vec::new(); // (first, last, saved)
        for pos in read_origin_positions(&c) {
            if pos.len() >= 2 {
                let (f, l) = (pos[0], *pos.last().unwrap());
                reused.push((f, l, pos.len() - 1));
            }
        }
        let total_saved: usize = reused.iter().map(|&(_, _, s)| s).sum();
        if total_saved == 0 {
            rows.push(format!("| {stem} L0 Ext | {reread_waste} | {n} | 0 | — | — | — | — | (no fold reuse) |"));
            continue;
        }

        // Lifetime distribution (span as % of program).
        let mut spans: Vec<usize> = reused.iter().map(|&(f, l, _)| l - f).collect();
        spans.sort_unstable();
        let med_span = spans[spans.len() / 2];
        let max_span = *spans.last().unwrap();
        let long_lived = spans.iter().filter(|&&s| s * 2 > n).count();
        let med_pct = 100 * med_span / n.max(1);
        let max_pct = 100 * max_span / n.max(1);

        let wsp = ws_peak(&reused); // cells for 100% on current order

        // Greedy prize curve (density-sorted), reported as % of total reclaimable.
        let mut by_density = reused.clone();
        by_density.sort_by(|a, b| {
            let da = a.2 as f64 / ((a.1 - a.0 + 1) as f64);
            let db = b.2 as f64 / ((b.1 - b.0 + 1) as f64);
            db.partial_cmp(&da).unwrap()
        });
        let curve: Vec<String> = EXTRA
            .iter()
            .map(|&cap| format!("{}", 100 * greedy_prize(&by_density, n, cap) / total_saved))
            .collect();

        // Budget to reclaim 100% on the current order ≈ fold working set + full cache demand.
        let full_prize_budget = peak + wsp;

        rows.push(format!(
            "| {stem} L0 Ext | {reread_waste} | {n} | {} | {wsp} | {med_pct}% | {max_pct}% ({long_lived} >½) | {full_prize_budget} | {} |",
            reused.len(),
            curve.join(" / "),
        ));
    }

    println!("# Backward fold-reuse LIFETIME analysis (Ext L0)\n");
    println!(
        "Tiers of prize optimism: (1) Table-2 `excess` = perfect cache, no lifetimes \
         (overstates); (2) THIS = lifetime-aware on the CURRENT fold order — `WS_peak` cells \
         reclaim 100%, `greedy%@+B` reclaims under a +B-lane cache (feasible, capacity-checked \
         every instruction); (3) realizable joint order+cache ≥ (2) because commutative \
         REORDER shrinks lifetimes — and needs the actual optimizer (SP3), not a static read.\n"
    );
    println!(
        "`WS_peak` = cells to hold every reused source across its [first,last] span at once. \
         `full-prize budget` ≈ fold-peak + WS_peak (lanes to reclaim 100% WITHOUT reordering). \
         `greedy%` at +B ∈ {{4,8,16,32,52}} lanes (1,2,4,8,13 Ext buckets) = % of the \
         reread-waste a +B-lane cache reclaims on the current order.\n"
    );
    println!("| L0 layer | reread_waste | n_instr | reused_src | WS_peak | median span | max span | full-prize budget | greedy% @+4/+8/+16/+32/+52 |");
    println!("|---|---|---|---|---|---|---|---|---|");
    for r in &rows {
        println!("{r}");
    }
    println!(
        "\nReading: a large `WS_peak` (≫ any realistic budget) with LONG spans means the \
         current-order caching-alone prize saturates slowly (`greedy%` low at feasible +B) — \
         so the realizable win depends on REORDERING to shorten lifetimes, which only the \
         joint order+cache optimizer can size. Short spans / fast-saturating `greedy%` mean \
         caching-alone already captures most of it at a modest budget."
    );
}

// ── FC0: exact fixed-order ceiling (per-site envelope FiF) ────────────────────

/// A retention candidate: hold `origin`'s value from its use at instruction `start`
/// to its next use at `end`. Occupancy is `(start, end]` — the cell is stored AFTER
/// the start use's miss is serviced (lower.rs:791-804) and stays live THROUGH the
/// closing read (placement is inclusive [def, last_use], place.rs:138-154). Chained
/// gaps of one origin tile without double-count: [u1+1,u2], [u2+1,u3]. A ZERO-LENGTH
/// gap (same-instruction double use, e.g. x*x) occupies just its own instant
/// [end, end] — the cell is borrowed within the instruction; FC2 must verify the
/// machinery realizes that instant-borrow (FC0 ceiling impact is tiny either way).
#[derive(Clone, Copy, Debug)]
struct Gap {
    origin: usize,
    start: usize,
    end: usize,
}

/// Occupied instants of a retained gap (closed `(first, last)`; see `Gap`). The
/// SINGLE shared phase definition — solver and oracle both use it, so the fuzz
/// actually exercises the real phase model (codex H5b: revision 1's oracle copied
/// the solver's wrong phase, making the fuzz blind to it).
fn occ_range(g: &Gap) -> (usize, usize) {
    if g.start == g.end {
        (g.end, g.end)
    } else {
        (g.start + 1, g.end)
    }
}

/// Per-instruction occupied smem lanes of a placed program: a lane is occupied from
/// the instruction that writes it (`Mov` with `dst = Smem`) through its last read
/// before the lane's next write (write-segmented lifetimes, lane granularity). A
/// read of a never-written lane counts as occupied from t=0 (pre-initialized).
fn live_profile(p: &Program) -> Vec<usize> {
    #[derive(Clone, Copy)]
    enum Ev {
        Write,
        Read,
    }
    let n = p.instrs.len();
    // WIRE DECODE (v2, `smem_lane` src/fwd/interp.rs:132-142): a Base `Smem` index is
    // a LANE; an Ext `Smem` index is a BUCKET whose lanes are cell*4 .. cell*4+4.
    // (codex H5a: revision 1 treated Ext cells as lane-addressed and corrupted the
    // profile.)
    let span = |cell: u16, f: OperandField| match f {
        OperandField::Base => (cell as u32, 1u32),
        OperandField::Ext => (cell as u32 * 4, 4u32),
    };
    let mut lanes: BTreeMap<u32, Vec<(usize, Ev)>> = BTreeMap::new();
    let mut push = |lanes: &mut BTreeMap<u32, Vec<(usize, Ev)>>, cell: u16, f: OperandField, t, ev| {
        let (base, width) = span(cell, f);
        for l in base..base + width {
            lanes.entry(l).or_default().push((t, ev));
        }
    };
    for (t, i) in p.instrs.iter().enumerate() {
        match i {
            Instr::Add { field, operands, .. } | Instr::Mul { field, operands, .. } => {
                for op in operands {
                    if let OperandLine::Smem { cell } = op {
                        push(&mut lanes, *cell, *field, t, Ev::Read);
                    }
                }
            }
            Instr::Fma { field_lhs, field_rhs, pairs, .. } => {
                for (l, r) in pairs {
                    if let OperandLine::Smem { cell } = l {
                        push(&mut lanes, *cell, *field_lhs, t, Ev::Read);
                    }
                    if let OperandLine::Smem { cell } = r {
                        push(&mut lanes, *cell, *field_rhs, t, Ev::Read);
                    }
                }
            }
            Instr::Mov { field, dst, src, .. } => {
                if let Some(OperandLine::Smem { cell }) = src {
                    push(&mut lanes, *cell, *field, t, Ev::Read);
                }
                if let Some(DstLine::Smem { cell }) = dst {
                    push(&mut lanes, *cell, *field, t, Ev::Write);
                }
            }
        }
    }
    let mut occ = vec![0usize; n];
    for (_, evs) in lanes {
        let mut i = 0;
        while i < evs.len() {
            let seg_start = match evs[i].1 {
                Ev::Write => evs[i].0,
                Ev::Read => 0,
            };
            let mut seg_end = evs[i].0;
            let mut j = i + 1;
            while j < evs.len() && matches!(evs[j].1, Ev::Read) {
                seg_end = evs[j].0;
                j += 1;
            }
            for t in seg_start..=seg_end {
                occ[t] += 1;
            }
            i = j;
        }
    }
    occ
}

/// Exact fixed-order reclaim under a time-varying free-lane envelope: retain a
/// maximum number of gaps s.t. at every t, `4 · |selected occupying t| <= free[t]`
/// (occupancy per `occ_range`). Sweep: admit each gap at its first occupied
/// instant, drop the farthest-LAST active gap on overflow (offline
/// farthest-in-future with bypass, variable capacity — codex exhaustively
/// validated the abstract sweep on 82,944 small cases). This implementation is
/// still fuzzed against the oracle below (same `occ_range`, so the fuzz exercises
/// the real phase model); if the fuzz ever finds a gap, escalate to min-cost-flow
/// (design doc §4) instead of shipping a wrong ceiling.
fn fif_select(gaps: &[Gap], free: &[usize]) -> Vec<usize> {
    let mut order: Vec<usize> = (0..gaps.len()).collect();
    order.sort_by_key(|&i| occ_range(&gaps[i]));
    let mut active: BTreeSet<(usize, usize)> = BTreeSet::new(); // (occ last, gap idx)
    let mut kept: Vec<usize> = Vec::new();
    let mut gi = 0usize;
    for t in 0..free.len() {
        while let Some(&(last, idx)) = active.iter().next() {
            if last < t {
                active.remove(&(last, idx));
                kept.push(idx); // survived its whole occupied range: a realized saving
            } else {
                break;
            }
        }
        while gi < order.len() && occ_range(&gaps[order[gi]]).0 == t {
            active.insert((occ_range(&gaps[order[gi]]).1, order[gi]));
            gi += 1;
        }
        while 4 * active.len() > free[t] {
            let &(last, idx) = active.iter().next_back().unwrap(); // farthest last: bypass it
            active.remove(&(last, idx));
        }
    }
    kept.extend(active.into_iter().map(|(_, idx)| idx));
    kept.sort_unstable();
    kept
}

/// Brute-force oracle: max retainable gap count over ALL subsets (≤ 12 gaps).
fn oracle_saved(gaps: &[Gap], free: &[usize]) -> usize {
    let mut best = 0usize;
    'outer: for mask in 0u32..(1u32 << gaps.len()) {
        let mut occ = vec![0usize; free.len()];
        for (i, g) in gaps.iter().enumerate() {
            if mask & (1 << i) != 0 {
                let (s, e) = occ_range(g);
                for t in s..=e {
                    occ[t] += 4;
                    if occ[t] > free[t] {
                        continue 'outer;
                    }
                }
            }
        }
        best = best.max(mask.count_ones() as usize);
    }
    best
}

fn lcg(state: &mut u64, m: u64) -> u64 {
    *state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
    (*state >> 33) % m
}

/// FC0 exactness gate (design §4): the sweep must equal the oracle on every random
/// small instance. NOT #[ignore]d — fast, fixture-free, and it is the gate that
/// lets every downstream number claim "exact".
#[test]
fn fc0_fif_solver_matches_oracle() {
    let mut st = 0x243F_6A88_85A3_08D3u64; // deterministic — wall-clock seeding is banned
    for case in 0..300 {
        let n = 10 + lcg(&mut st, 50) as usize;
        let n_origins = 2 + lcg(&mut st, 6) as usize;
        let mut gaps: Vec<Gap> = Vec::new();
        for o in 0..n_origins {
            let uses = 2 + lcg(&mut st, 4) as usize;
            let mut pos: Vec<usize> = (0..uses).map(|_| lcg(&mut st, n as u64) as usize).collect();
            // Duplicates are DELIBERATELY kept and injected: a repeated position is a
            // same-instruction double use (x*x) → a zero-length gap — the class the
            // dedup'd revision-1 fuzz could never generate (fable R3).
            if lcg(&mut st, 3) == 0 {
                let dup = pos[lcg(&mut st, pos.len() as u64) as usize];
                pos.push(dup);
            }
            pos.sort_unstable();
            for w in pos.windows(2) {
                gaps.push(Gap { origin: o, start: w[0], end: w[1] });
            }
        }
        gaps.truncate(12); // oracle is 2^|gaps|
        let free: Vec<usize> = (0..n).map(|_| 4 * lcg(&mut st, 4) as usize).collect();
        assert_eq!(
            fif_select(&gaps, &free).len(),
            oracle_saved(&gaps, &free),
            "case {case}: gaps={gaps:?} free={free:?}"
        );
    }
}

/// Reconciliation pin: the lane-walk live profile's peak must equal the placement
/// stat. A mismatch means the lifetime definition diverges from `plan_placement` —
/// STOP and reconcile (do not fudge); every FC envelope number depends on this.
/// KNOWN LIMITATION (codex H5a): peak-equality is a weak gate — a profile error
/// away from the peak instant passes it. Full-profile reconciliation needs
/// value-lifetime instrumentation and is deferred to the FC2 redesign; until then
/// this pin plus the budget bound (`max(occ) <= budget`) is the available check.
#[test]
#[ignore = "gate: compiles all fixtures; run explicitly (release + RUST_MIN_STACK)"]
fn fc0_live_profile_matches_placement_peak() {
    for name in FIXTURES {
        let (layer, cross) = common::load_layer(name, 0);
        for regime in [BwdRegime::R0, BwdRegime::Ext] {
            let d = distill(&layer, regime, &cross, None);
            if d.skipped_decoder {
                continue;
            }
            let c = streamed(&d, 16);
            let occ = live_profile(&c.program);
            assert_eq!(
                occ.iter().copied().max().unwrap_or(0),
                c.stats.max_live_cells,
                "{name} {regime:?}: live_profile peak != placement max_live_cells"
            );
        }
    }
}
