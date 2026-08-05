//! SP1 Task 4 — A3: the read-side traffic-invariance gate (the "free-fix"
//! certificate of the streamed backward lowering).
//!
//! Tasks 1–3 proved the streamed backward reduction/FMA lowering is VALUE-correct.
//! This gate proves it is also TRAFFIC-NEUTRAL: for EVERY pinned fixture / layer /
//! regime on the UNCACHED path (`decisions: None`), the streamed program's whole
//! read-side statistics vector — and the per-`FoldSource`-descriptor use histogram —
//! is BIT-IDENTICAL to the legacy pre-materialize lowering's, compared at legacy's
//! smallest feasible budget (`common::smallest_legacy_feasible`, scanning
//! `[16, 24, 32, 48, 64, floor]`).
//!
//! If any read-side column or histogram bucket drifts, streaming is NOT free — that
//! is a real bug in the Tasks 1–3 lowering, to be fixed in `src/` (per the field
//! rule), NOT masked by relaxing this gate.
//!
//! # Why only the read side, only uncached
//!
//! The read-side vector is exactly the seven columns the search objective and the
//! device-traffic accounting consume:
//!   `dram_reads, dram_traffic, special_reads, ldc_reads,
//!    stats_ext.{global, fold_uses, fold_traffic}`.
//! Only `{cell_reads, cell_stores, op_counts, program_lanes}` are allowed to move —
//! streaming trades concurrent Ext temps for stash Movs + cell traffic, which is the
//! whole point. The SEARCHED path (`decisions: Some`) is NOT read-side-invariant by
//! design (spec F3: admission moves fold gathers into cells), so this gate stays on
//! the uncached census path only.

mod common;

use gkr_eval_isa::BwdRegime;
use gkr_eval_isa::bwd::compile::{
    compile_distilled, compile_distilled_legacy_only, compile_distilled_streamed, BwdCompiledLayer,
};
use gkr_eval_isa::bwd::distill::distill;

/// The read-side statistics vector that MUST be identical streamed-vs-legacy: real
/// DRAM reads/traffic, fold-side Special reads, Ldc reads, and the search-facing
/// `BwdTrafficStats` (`global` DRAM cells, fold uses, fold traffic). Cell/op/lane
/// counts are deliberately excluded — those are the columns streaming is allowed to
/// move.
fn read_side(c: &BwdCompiledLayer) -> (usize, usize, usize, usize, usize, usize, usize) {
    (
        c.stats.dram_reads,
        c.stats.dram_traffic,
        c.stats.special_reads,
        c.stats.ldc_reads,
        c.stats_ext.global,
        c.stats_ext.fold_uses,
        c.stats_ext.fold_traffic,
    )
}

/// A3, the load-bearing gate: for every fixture / layer / regime on the uncached path,
/// the streamed program's read-side vector AND per-descriptor fold-use histogram are
/// bit-identical to legacy's, at legacy's smallest feasible budget. Decoder layers are
/// INCLUDED (post-fence, none are `skipped_decoder`; the `continue` only drops the
/// truly-unrepresentable distillates, of which the corpus has zero).
#[test]
fn streamed_read_side_equals_legacy_all_layers() {
    let mut compared = 0usize;
    for name in common::FIXTURES {
        for (li, layer, cross) in common::layers_with_bwd_roots(name) {
            for regime in [BwdRegime::R0, BwdRegime::Ext] {
                let d = distill(&layer, regime, &cross, None);
                if d.skipped_decoder {
                    continue; // only the truly-unrepresentable decoder distillates
                }
                // Legacy's smallest feasible budget (scan [16,24,32,48,64,floor]); the
                // streamed variant is compiled at the SAME budget. Streaming's feasibility
                // ⊇ legacy's, so the `expect` below also asserts streamed-floor <= legacy-floor.
                let (b, legacy) = common::smallest_legacy_feasible(&d);
                let streamed = compile_distilled_streamed(&d, b, None, true)
                    .expect("streamed must be feasible wherever legacy is");

                assert_eq!(
                    read_side(&legacy),
                    read_side(&streamed),
                    "read-side vector drifted: {name}[L{li}][{regime:?}]@b{b}"
                );
                assert_eq!(
                    common::foldsource_use_histogram(&legacy),
                    common::foldsource_use_histogram(&streamed),
                    "per-descriptor fold-use histogram drifted: {name}[L{li}][{regime:?}]@b{b}"
                );
                compared += 1;
            }
        }
    }
    // Pin the coverage count (57 R0 + 57 Ext = 114 backward-root layer instances across the
    // fixture corpus) so a silent shrink in `layers_with_bwd_roots` / `claim_roots` fails this
    // certificate loudly rather than passing vacuously on a subset. Update deliberately if the
    // corpus changes (mirrors the repo's other coverage pins).
    assert_eq!(
        compared, 114,
        "A3 coverage drifted: compared {compared} layer instances, expected 114 — \
         enumeration shrank/grew; update deliberately"
    );
    println!("A3: read-side + fold-use histogram parity holds on {compared} layer instances");
}

/// The legacy-first fallback must be a no-op on fitting layers: where legacy already
/// fits, `compile_distilled` (legacy-first) selects the legacy program VERBATIM — the
/// streamed fallback only ever engages on `BudgetBelowFloor`, so a fitting layer's
/// selected program is byte-identical to `compile_distilled_legacy_only`'s.
#[test]
fn legacy_first_keeps_exact_legacy_program_on_fitting_layers() {
    // Small, legacy-feasible at b16 (the wide L0s are NOT — those overflow legacy's floor).
    for (name, li) in [("add_sub_lui_auipc_mop_layout_gkr.json", 3), ("blake2_g_function_layout_gkr.json", 2)] {
        let (layer, cross) = common::load_layer(name, li);
        let d = distill(&layer, BwdRegime::Ext, &cross, None);
        let sel = compile_distilled(&d, 16, None).expect("legacy-first selects legacy (fitting)");
        let leg = compile_distilled_legacy_only(&d, 16, None).expect("legacy fits at b16");
        assert_eq!(
            common::encode(&sel.program),
            common::encode(&leg.program),
            "{name}[L{li}] legacy program not preserved by the legacy-first fallback"
        );
    }
}
