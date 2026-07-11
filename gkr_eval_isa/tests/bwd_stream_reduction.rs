//! SP1 Task 1 — the streamed backward reduction (`compile_reduction_virtual`'s
//! one-Ext-cell stash+refold fallback), gated on SYNTHETIC DistilledLayers built
//! directly in the arena so a wide reduction routes through the streamed engine.
//!
//! These are Task 1's green gate. Each fixture is value-checked against the
//! independent expression oracle (`common::assert_synthetic_value_exact`), a real
//! behavioral check — the compiled VM program vs a tree-walk interpreter of the
//! same layer, with the compiler (streaming) as the thing under test.

mod common;

use gkr_eval_isa::bwd::compile::{
    compile_distilled, compile_distilled_legacy_only, compile_distilled_streamed,
};

/// A wide pure-ADD reduction overflows the legacy pre-materialize floor at b16, fits via
/// streaming, and stays value-exact on the uncached path.
#[test]
fn streamed_wide_add_fits_and_is_value_exact() {
    let d = common::synthetic_wide_add_layer(40); // legacy floor ≫ 16
    assert!(
        common::is_budget_below_floor(&compile_distilled_legacy_only(&d, 16, None).unwrap_err()),
        "the fixture must overflow the legacy floor (else streaming is never exercised)"
    );
    let c = compile_distilled(&d, 16, None).expect("streamed fits b16");
    assert!(c.stats.max_live_cells <= 16, "max_live {}", c.stats.max_live_cells);
    common::assert_synthetic_value_exact(&c, &d);
}

/// The MUL sibling: a wide product overflows legacy, fits via streaming, value-exact.
#[test]
fn streamed_wide_mul_fits_and_is_value_exact() {
    let d = common::synthetic_wide_mul_layer(40);
    assert!(
        common::is_budget_below_floor(&compile_distilled_legacy_only(&d, 16, None).unwrap_err()),
        "the fixture must overflow the legacy floor (else streaming is never exercised)"
    );
    let c = compile_distilled(&d, 16, None).expect("streamed fits b16");
    assert!(c.stats.max_live_cells <= 16, "max_live {}", c.stats.max_live_cells);
    common::assert_synthetic_value_exact(&c, &d);
}

/// Mixed-field reductions (Base seed + Ext stash, and Ext seed + Base stash) stay
/// value-exact under FORCED streaming (they fit legacy, so `stream_reductions` is set
/// directly), exercising both cross-field stash directions. Never FMA (Task 2 owns FMA).
#[test]
fn streamed_mixed_field_micro_is_value_exact() {
    for ext_seed in [false, true] {
        let d = common::synthetic_mixed_field_micro_layer(ext_seed);
        let c = compile_distilled_streamed(&d, 16, None, true)
            .unwrap_or_else(|e| panic!("streamed mixed micro (ext_seed={ext_seed}): {e:?}"));
        assert!(!common::program_has_fma(&c.program), "a pure reduction must not emit FMA");
        common::assert_synthetic_value_exact(&c, &d);

        // Read-side traffic invariant (Global Constraint): at a commonly-feasible budget,
        // the streamed variant is bit-identical to legacy on the whole read-side stats
        // vector; only cell/op/lane counts may move.
        let legacy = compile_distilled_legacy_only(&d, 16, None)
            .unwrap_or_else(|e| panic!("legacy mixed micro (ext_seed={ext_seed}): {e:?}"));
        assert_eq!(c.stats.dram_reads, legacy.stats.dram_reads, "dram_reads moved");
        assert_eq!(c.stats.dram_traffic, legacy.stats.dram_traffic, "dram_traffic moved");
        assert_eq!(c.stats.special_reads, legacy.stats.special_reads, "special_reads moved");
        assert_eq!(c.stats.ldc_reads, legacy.stats.ldc_reads, "ldc_reads moved");
        assert_eq!(c.stats_ext, legacy.stats_ext, "BwdTrafficStats moved");
    }
}

/// The searched path: at low budget the wide reduction streams AND a prioritized shared
/// leaf is admitted mid-reduction. Value parity must hold, and the admit branch must
/// non-vacuously have fired (Global Constraint: both paths value-safe at this commit).
#[test]
fn streamed_searched_admission_is_value_exact() {
    let d = common::synthetic_wide_add_layer_with_shared_leaf();

    // Non-vacuity baseline: with NO decisions the streamed reduction gathers the shared
    // leaf TWICE (once per occurrence) — nothing is admitted, and it is still value-exact.
    let c_none = compile_distilled(&d, 16, None).expect("streamed feasible (uncached)");
    common::assert_synthetic_value_exact(&c_none, &d);
    assert_eq!(
        common::shared_leaf_fold_uses(&c_none),
        2,
        "uncached path must gather the shared leaf once per occurrence"
    );

    // Searched path: decisions pin the shared leaf to a dominating priority, so the
    // may-admit arm fires mid-reduction and collapses the two gathers into one + a cell
    // re-read. Value parity must still hold (Global Constraint: both paths value-safe).
    let dec = common::decisions_admitting_a_shared_leaf(&d);
    let c = compile_distilled(&d, 16, Some(&dec)).expect("feasible");
    common::assert_synthetic_value_exact_with_decisions(&c, &d, &dec);
    assert!(
        common::program_admits_shared_leaf(&c),
        "admission branch must have fired (shared-leaf gathers 2 → 1)"
    );
}
