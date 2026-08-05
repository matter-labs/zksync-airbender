//! SP1 Task 1 — the streamed backward reduction (`compile_reduction_virtual`'s
//! one-Ext-cell stash+refold fallback), gated on SYNTHETIC DistilledLayers built
//! directly in the arena so a wide reduction routes through the streamed engine.
//!
//! These are Task 1's green gate. Each fixture is value-checked against the
//! independent expression oracle (`common::assert_synthetic_value_exact`), a real
//! behavioral check — the compiled VM program vs a tree-walk interpreter of the
//! same layer, with the compiler (streaming) as the thing under test.

mod common;

use gkr_eval_isa::BwdRegime;
use gkr_eval_isa::bwd::compile::{
    compile_distilled, compile_distilled_legacy_only, compile_distilled_streamed,
};
use gkr_eval_isa::bwd::distill::distill;

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

/// Task 2 green gate: bigint L0 in the Ext regime overflows the legacy FMA pre-materialize
/// floor (320 lanes / 80 concurrent Ext operand cells) but STREAMS to `max_live <= 16`
/// through `fma_streamed`, stays value-exact on the uncached path, and keeps its leaf
/// products FUSED (`program_has_fma`). This is the fixture where the wide base-layer L0s
/// finally collapse to fit b16 — the pure-reduction streaming of Task 1 did not move it
/// (bigint overflows through the FMA path, not the reduction path).
#[test]
fn streamed_fma_collapses_bigint_l0() {
    let (layer, cross) = common::load_layer("bigint_with_extended_control_layout_gkr.json", 0);
    let d = distill(&layer, BwdRegime::Ext, &cross, None);
    // The legacy pre-materialize FMA path cannot fit b16 (else streaming is never
    // exercised) — the retry-to-streaming fallback is what makes b16 feasible.
    assert!(
        common::is_budget_below_floor(&compile_distilled_legacy_only(&d, 16, None).unwrap_err()),
        "bigint L0 Ext must overflow the legacy FMA floor"
    );
    let c = compile_distilled(&d, 16, None).expect("streamed FMA fits b16");
    assert!(c.stats.max_live_cells <= 16, "max_live {}", c.stats.max_live_cells);
    common::assert_bwd_value_parity(&c, &d, &layer);
    assert!(common::program_has_fma(&c.program), "leaf products must stay fused");
}

/// The compound×compound FMA path (both product operands stash — the nested per-operand
/// `lower_operand_virtual` case bigint does NOT exercise): a wide Add mixing leaf products
/// (fused) with `(read+read)*(read+read)` products overflows the legacy FMA floor, streams
/// to `max_live <= 16`, stays value-exact, keeps leaf products fused, and — the A3 Global
/// Constraint — has read-side traffic BIT-IDENTICAL to legacy (only cell/op/lane counts may
/// move; read-side is budget-invariant on the uncached path).
#[test]
fn streamed_fma_compound_products_is_value_exact() {
    let d = common::synthetic_fma_compound_products_layer(8, 6);
    assert!(
        common::is_budget_below_floor(&compile_distilled_legacy_only(&d, 16, None).unwrap_err()),
        "the compound×compound fixture must overflow the legacy FMA floor"
    );
    let c = compile_distilled(&d, 16, None).expect("streamed FMA fits b16");
    assert!(c.stats.max_live_cells <= 16, "max_live {}", c.stats.max_live_cells);
    assert!(common::program_has_fma(&c.program), "leaf products must stay fused");
    common::assert_synthetic_value_exact(&c, &d);

    // A3 read-side traffic invariant: streamed (b16) vs legacy (at a feasible budget) are
    // bit-identical on the whole read-side stats vector — reordering folds and adding stash
    // Movs/cell-reads must not move any DRAM/fold/special/ldc read (each leaf read once).
    let legacy = compile_distilled_legacy_only(&d, 1 << 12, None).expect("legacy fits at 4096");
    assert_eq!(c.stats.dram_reads, legacy.stats.dram_reads, "dram_reads moved");
    assert_eq!(c.stats.dram_traffic, legacy.stats.dram_traffic, "dram_traffic moved");
    assert_eq!(c.stats.special_reads, legacy.stats.special_reads, "special_reads moved");
    assert_eq!(c.stats.ldc_reads, legacy.stats.ldc_reads, "ldc_reads moved");
    assert_eq!(c.stats_ext, legacy.stats_ext, "BwdTrafficStats moved");
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

/// The adversarial REAL-fixture equivalent of `streamed_searched_admission_is_value_exact`:
/// bigint's wide L0 (Ext regime) under decisions that pin a shared read leaf (column
/// `SHARED_COL` = 0) to a dominating priority, so `try_admit` keeps it resident mid-reduction.
/// Task 1 already proved the searched-admission path value-exact on a SYNTHETIC fixture and
/// landed the classifier fix (`may_attempt_admit` / `is_compound_or_may_admit`) that makes it
/// safe; this is the coverage proof on a real, cache-bearing, wide circuit layer — the
/// admission must both preserve the value (no acc clobber) AND non-vacuously fire.
///
/// The budget is 20, not the synthetic test's 16: pinning classified-direct
/// compounds against eviction (8a518b6e) deliberately raised this fixture's
/// mandatory-residency floor under the admitting decisions to 20 lanes, and a
/// budget below the floor is `BudgetBelowFloor` by design, not a searched path.
#[test]
fn streamed_searched_path_real_fixture_value_exact() {
    let (layer, cross) = common::load_layer("bigint_with_extended_control_layout_gkr.json", 0);
    let d = distill(&layer, BwdRegime::Ext, &cross, None);
    let dec = common::decisions_admitting_a_shared_leaf(&d);
    let c = compile_distilled(&d, 20, Some(&dec)).expect("feasible");
    // Searched-path value parity: the streamed lowering under admitting decisions must match
    // the oracle exactly — the may-admit source leaf takes the stash path, never clobbering acc.
    common::assert_bwd_value_parity(&c, &d, &layer);
    // Non-vacuous: pinning the shared read leaf's priority makes admission cache it to cells,
    // strictly reducing its fold-source gathers vs the no-decisions baseline with resident
    // Smem reads present. The synthetic exact-1 collapse (`program_admits_shared_leaf`)
    // does not apply here: budget pressure keeps only some of the leaf's uses resident.
    // The baseline compiles at the SAME 20-lane budget, so the gather drop below is the
    // decisions' doing and not the budget's.
    let c_none = compile_distilled(&d, 20, None).expect("feasible (baseline)");
    assert!(
        common::program_admits_shared_leaf_vs_baseline(&c, &c_none),
        "searched-path admission must fire non-vacuously on bigint: gathers must drop vs baseline \
         (with-dec={}, no-dec={}) and Smem reads be present",
        common::shared_leaf_fold_uses(&c),
        common::shared_leaf_fold_uses(&c_none),
    );
}
