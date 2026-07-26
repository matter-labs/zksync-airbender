//! Task 8: the exact `c2`-`c16` cost report over the whole in-scope corpus
//! (design §7.2, §15 "static quality").
//!
//! This is the REPORT gate. It compiles every `(circuit, layer, R0|Ext)` chain at
//! every budget through the real placer, binder and encoder — never a size
//! estimate — and pins:
//!
//!   * the read floor, the realized read traffic and the percentage above the
//!     floor, `(realized / floor - 1) * 100`;
//!   * materialization write bytes, SEPARATELY, never in that numerator;
//!   * BF/mixed/E4 arithmetic as three counts, never as "weighted bytes";
//!   * shared-memory loads and stores, moves, u16 words and bytes; and
//!   * the maximum real encoded word count, which
//!     [`in_scope::MAX_REALIZED_PROGRAM_WORDS`] freezes and Task 9's descriptor
//!     ABI is sized from.
//!
//! `c16` stays in the table as §15's diagnostic approach-to-floor point. It is
//! never an automatic production selection: §13's selector picks budgets from
//! measured GPU runtime, which does not exist yet.
//!
//! # Scope
//!
//! `blake2_with_compression` compiles the SAME GKR circuit as the committed
//! `blake2_with_extended_control_layout_gkr.json` (Task 3's census: byte-identical
//! serialized layouts, field-for-field identical rows), so it is not a separate
//! circuit, §3.1's conditional exclusion cannot trigger, and the 12 committed
//! layouts of [`in_scope`] already cover it. There is no conditional family here.

mod common;

use std::collections::BTreeMap;

use common::{FIXTURES, layers_with_bwd_roots};
use cs::gkr_compiler::dag_ir::BwdRegime;
use gkr_eval_isa::bwd::coeff::artifact::{
    ChainProgress, CoordinateReport, budget_totals, compile_coordinate, percent_above_floor_table,
    summarize,
};
use gkr_eval_isa::bwd::coeff::limits::{KERNEL_ARGUMENT_CEILING_BYTES, in_scope};
use gkr_eval_isa::bwd::coeff::schedule::{CellBudget, SeedKind};
use rayon::prelude::*;

/// Compile every in-scope coordinate's whole budget family, in parallel, with one
/// progress line per completed `(circuit, layer, regime)` chain.
fn corpus() -> (Vec<CoordinateReport>, BTreeMap<&'static str, usize>) {
    let mut coordinates: Vec<(String, usize, cs::gkr_compiler::dag_ir::DagLayer, common::CrossFields)> =
        FIXTURES
            .par_iter()
            .flat_map_iter(|name| {
                layers_with_bwd_roots(name)
                    .map(move |(li, layer, cross)| ((*name).to_string(), li, layer, cross))
            })
            .collect();
    coordinates.sort_by(|a, b| (&a.0, a.1).cmp(&(&b.0, b.1)));

    let compiled: Vec<(CoordinateReport, Vec<SeedKind>)> = coordinates
        .par_iter()
        .flat_map_iter(|(name, li, layer, cross)| {
            [BwdRegime::R0, BwdRegime::Ext]
                .into_iter()
                .map(move |regime| (name, *li, layer, cross, regime))
        })
        .map(|(name, li, layer, cross, regime)| {
            let compiled = compile_coordinate(name, li, layer, cross, regime)
                .unwrap_or_else(|e| panic!("[{name} L{li} {regime:?}] chain: {e:?}"));
            println!("{}", ChainProgress::of(&compiled));
            (compiled.report, compiled.winners)
        })
        .collect();

    let mut seeds: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut reports = Vec::with_capacity(compiled.len());
    for (report, winners) in compiled {
        for winner in winners {
            let label = match winner {
                SeedKind::StableNormalized => "StableNormalized",
                SeedKind::BudgetAwareGreedy => "BudgetAwareGreedy",
                SeedKind::PrecedingWinner => "PrecedingWinner",
            };
            *seeds.entry(label).or_default() += 1;
        }
        reports.push(report);
    }
    reports.sort_by(|a, b| a.sort_key().cmp(&b.sort_key()));
    (reports, seeds)
}

#[test]
fn bwd_coeff_budget_sweep_report() {
    let (reports, seeds) = corpus();
    assert_eq!(reports.len(), in_scope::COORDINATES, "one report per in-scope coordinate");
    assert_eq!(
        reports.len() * CellBudget::ALL.len(),
        in_scope::COORDINATES * 15,
        "c2..c16 for every coordinate"
    );

    // ── the §15 table ────────────────────────────────────────────────────
    println!("\npercent above total-read floor, (realized / floor - 1) * 100:");
    print!("{}", percent_above_floor_table(&reports));

    let totals = budget_totals(&reports);
    println!("\ncorpus totals per budget (bytes are bytes; writes are NOT read bytes):");
    println!(
        "{:>5} {:>14} {:>14} {:>14} {:>9} {:>14} {:>12} {:>12} {:>12} {:>12} {:>12} {:>6} {:>10} {:>9}",
        "cells",
        "read_floor_B",
        "realized_B",
        "reread_B",
        "above%",
        "mat_write_B",
        "bf_ops",
        "mixed_ops",
        "e4_ops",
        "smem_loads",
        "smem_stores",
        "moves",
        "u16_words",
        "max_words",
    );
    for total in &totals {
        println!(
            "{:>5} {:>14} {:>14} {:>14} {:>9.3} {:>14} {:>12} {:>12} {:>12} {:>12} {:>12} {:>6} {:>10} {:>9}",
            total.cells,
            total.total_read_floor_bytes,
            total.realized_total_read_bytes,
            total.cacheable_reread_bytes,
            total.percent_above_floor(),
            total.materialization_write_bytes,
            total.bf_ops,
            total.mixed_ops,
            total.e4_ops,
            total.shared_loads,
            total.shared_stores,
            total.moves,
            total.words,
            total.max_words,
        );
    }

    let summary = summarize(&reports);
    println!(
        "\nMAX realized program = {} words / {} bytes at {} c{} (cap {}), corpus moves = {}",
        summary.max_program_words,
        summary.max_program_bytes,
        summary.max_program_at,
        summary.max_program_cells,
        KERNEL_ARGUMENT_CEILING_BYTES,
        summary.total_moves,
    );
    println!("coordinates exactly at the read floor, per budget: {:?}", summary.at_floor_per_budget);
    println!("winning seeds over all 1710 selections: {seeds:?}");

    // ── the floor really is a floor ──────────────────────────────────────
    for report in &reports {
        for program in &report.budgets {
            assert!(
                program.realized_total_read_bytes >= program.total_read_floor_bytes,
                "[{} c{}] realized {} is below the floor {}",
                report.label(),
                program.cells,
                program.realized_total_read_bytes,
                program.total_read_floor_bytes,
            );
            assert_eq!(
                program.cacheable_reread_bytes,
                program.realized_total_read_bytes - program.total_read_floor_bytes,
                "[{} c{}] reread bytes must be exactly the traffic above the floor",
                report.label(),
                program.cells,
            );
            assert_eq!(
                program.compulsory_read_once_bytes, program.total_read_floor_bytes,
                "the floor IS the compulsory read-once total",
            );
        }
    }

    // ── more budget never costs more traffic ─────────────────────────────
    //
    // §7.2 selects each budget's order from a candidate set that always contains
    // the preceding winner, so a larger cell file can never be forced into a worse
    // realized read cost than a smaller one.
    for report in &reports {
        for pair in report.budgets.windows(2) {
            assert!(
                pair[1].realized_total_read_bytes <= pair[0].realized_total_read_bytes,
                "[{}] c{} reads more ({}) than c{} ({})",
                report.label(),
                pair[1].cells,
                pair[1].realized_total_read_bytes,
                pair[0].cells,
                pair[0].realized_total_read_bytes,
            );
        }
    }
    for pair in totals.windows(2) {
        assert!(pair[1].percent_above_floor() <= pair[0].percent_above_floor());
    }

    // ── materialization writes never enter the read numerator ────────────
    //
    // R0 runs at depth 0 and publishes nothing; Ext runs at the published steady
    // state and publishes every DRAM-backed source once. If write bytes had leaked
    // into the read side, the R0 and Ext columns could not both be exact.
    for report in &reports {
        for program in &report.budgets {
            if report.regime.label() == "R0" {
                assert_eq!(
                    program.materialization_write_bytes, 0,
                    "[{}] R0 does not materialize",
                    report.label()
                );
            }
            assert_eq!(
                program.percent_above_floor(),
                if program.total_read_floor_bytes == 0 {
                    0.0
                } else {
                    (program.realized_total_read_bytes as f64
                        / program.total_read_floor_bytes as f64
                        - 1.0)
                        * 100.0
                },
                "the percentage is read bytes only",
            );
        }
    }
    assert!(
        totals.iter().any(|t| t.materialization_write_bytes > 0),
        "the Ext half of the corpus publishes, so the write column must be live"
    );

    // ── the pins Task 9 consumes ─────────────────────────────────────────
    assert_eq!(
        summary.max_program_words,
        in_scope::MAX_REALIZED_PROGRAM_WORDS,
        "the corpus-wide realized maximum program moved; re-pin deliberately"
    );
    assert_eq!(summary.max_program_bytes, in_scope::MAX_REALIZED_PROGRAM_BYTES);
    assert_eq!(summary.max_program_at, in_scope::MAX_REALIZED_PROGRAM_COORDINATE);
    assert_eq!(
        summary.max_program_cells,
        in_scope::MAX_REALIZED_PROGRAM_CELLS,
        "the longest program is not at the largest budget — see the constant's note"
    );
    assert_eq!(summary.total_moves, in_scope::REALIZED_MOVES);
    assert_eq!(summary.programs, in_scope::REALIZED_PLACEMENTS);
    assert!(
        in_scope::MAX_REALIZED_PROGRAM_BYTES <= in_scope::MAX_UPPER_BOUND_PROGRAM_BYTES,
        "Task 3's conservative maximum must bound the real encoder"
    );
    assert!(
        in_scope::DESCRIPTOR_PROGRAM_WORDS >= in_scope::MAX_REALIZED_PROGRAM_WORDS
            && in_scope::DESCRIPTOR_PROGRAM_WORDS - in_scope::MAX_REALIZED_PROGRAM_WORDS < 8,
        "the descriptor array is the measured maximum rounded up to 16-byte alignment, \
         and nothing more"
    );
    assert!(in_scope::DESCRIPTOR_PROGRAM_BYTES < KERNEL_ARGUMENT_CEILING_BYTES);

    // c16 is a diagnostic ceiling, not a selection: it is reported, and the report
    // is expected to show it at or near the floor.
    let c16 = totals.last().expect("c16 is the last budget");
    assert_eq!(c16.cells, 16);
    println!(
        "\nc16 diagnostic: {:.3}% above floor corpus-wide, {} of {} coordinates exactly at it",
        c16.percent_above_floor(),
        summary.at_floor_per_budget.last().copied().unwrap_or(0),
        reports.len(),
    );
}
