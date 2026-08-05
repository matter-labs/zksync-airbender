//! Task 7: G1 — the backward value-parity corpus gate (spec §2, the value gate
//! of the backward-VM CPU instrument).
//!
//! For the 12 pinned Global-Constraints fixtures, per distillable layer × regime
//! {R0, Ext} × role {T0, T2} × policy {AlwaysMaterialize, LazyUpTo(1),
//! LazyUpTo(2)} × round × sampled row, this asserts the backward interpreter
//! (`interpret_bwd_row`) equals the authoritative expression oracle
//!   `Σ_i beta^i · eval(root_i)`  (root 0 unscaled)
//! over the CANONICAL `claim_roots` order, BIT-EXACT.
//!
//! The per-(compiled, distilled, layer) sweep itself — the shared role+fold
//! transform, the rewrite-aware oracle, the materialized-buffer resolver, and the
//! encode/decode + orphan-descriptor structural checks — lives in
//! [`common::assert_bwd_value_parity`] (SP1 Task 1), so this corpus gate and the
//! `bwd_stream_reduction` synthetic gate share ONE implementation. This file owns
//! only the corpus enumeration, the b16 floor-retry bookkeeping, and the pins.
//!
//! # The cache fence (why this stays a SEMANTIC gate)
//!
//! Post Task-2, the distilled instrument replaces each same-layer cache cone with
//! a `Read(ReadPlace::CacheOutput{..})` fold leaf (production folds
//! `GKRAddress::Cached` columns instead of recomputing the defining relation). The
//! oracle inside `assert_bwd_value_parity` still recomputes the ORIGINAL cone (the
//! RAW `layer` passed here) against a witness-consistent read side
//! ([`common::CacheConsistentResolvers`]), so the fenced-column fold equals the
//! defining cone's fold (production's cache relations are LINEAR). `total_fenced >
//! 0` guards that the corpus actually exercises the fence.
//!
//! Because the fence also stops `claim_cone_has_decoder` at cache roots, every
//! former `PeekDecoder` layer is now distillable; `PINNED_SKIPPED_DECODER` is
//! consequently empty. Those former decoder `[L0]` layers land among the wide
//! cones that Task 1-4's streamed backward reduction lowering brought under the
//! b16 placement floor via `compile_distilled`'s legacy-first-fallback-to-
//! streamed retry, so `PINNED_B16_INFEASIBLE` is ALSO empty (SP1 Task 5).

mod common;

use std::collections::BTreeSet;

use common::{CacheConsistentResolvers, load_fixture, schedule_stem};
use gkr_eval_ir::{claim_roots, lower_dag, validate};
use gkr_eval_isa::BwdRegime;
use gkr_eval_isa::bwd::compile::compile_distilled;
use gkr_eval_isa::bwd::distill::distill;
use gkr_eval_isa::fwd::compile::build_cross_layer_field_map;
use gkr_eval_isa::fwd::error::CompileError;

/// The 12 pinned Global-Constraints fixtures — same list as
/// `bwd_distill_fixtures.rs` / `fwd_vm_desc_census.rs`.
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

/// Decoder-bearing layers skipped in BOTH regimes (out of v1). EMPTY since the
/// Task-2 backward cache fence: every corpus `PeekDecoder` cone is reachable only
/// through a same-layer cache, so it is now fenced to a `Read(CacheOutput)` fold
/// leaf and the layer becomes distillable. Pinned so a coverage change is loud.
const PINNED_SKIPPED_DECODER: &[&str] = &[];

/// Distillable layers whose placement floor exceeds b16 — the value gate still
/// covers them by retrying `compile_distilled` at the reported floor. Pinned
/// (empty) so a regression is loud; identical to `bwd_distill_fixtures.rs`.
///
/// SP1 (Task 5): EMPTY. The former 12-entry set overflowed through the FMA path
/// (`try_compile_fma_virtual`), NOT the pure `compile_reduction_virtual`
/// reduction path Task 1 streams; `compile_distilled`'s legacy-first-fallback-
/// to-streamed (Task 2's `stream_reductions = true` retry) turned out to also
/// bring every one of those 12 wide `[L0]` cones under the b16 placement floor,
/// so the residual measured by this gate collapsed to empty. Kept as a pinned
/// (rather than deleted) constant + the floor-retry branch below stays live —
/// a future circuit could reintroduce a residual.
const PINNED_B16_INFEASIBLE: &[&str] = &[];

const BUDGET: usize = 16;

// ── The gate ────────────────────────────────────────────────────────────────

#[test]
fn bwd_value_parity_all_fixtures() {
    let mut skipped: BTreeSet<String> = BTreeSet::new();
    let mut floor_retries: BTreeSet<String> = BTreeSet::new();
    let mut interpreted_r0 = 0usize;
    let mut interpreted_ext = 0usize;
    let mut total_fenced = 0usize;

    for name in FIXTURES {
        let stem = schedule_stem(name);
        let artifact = load_fixture(name);
        let dag = lower_dag(&artifact).unwrap_or_else(|e| panic!("[{name}] lower_dag: {e}"));
        validate(&dag).unwrap_or_else(|e| panic!("[{name}] validate: {e}"));
        let cross = build_cross_layer_field_map(&dag);

        for (li, layer) in dag.layers.iter().enumerate() {
            if claim_roots(layer).is_empty() {
                continue; // nothing to prove backward
            }
            // The corpus MUST exercise fenced cache columns (else the gate silently
            // degrades to the cache-free case); count them so the assert below bites.
            total_fenced += CacheConsistentResolvers::new(layer).n_fences();

            for &regime in &[BwdRegime::R0, BwdRegime::Ext] {
                let d = distill(layer, regime, &cross, None);
                if d.skipped_decoder {
                    // Out of v1 in BOTH regimes; record once (regime-independent).
                    skipped.insert(format!("{stem}[L{li}]"));
                    continue;
                }

                let ctx = format!("{stem} L{li} {regime:?}");
                // Every distillable layer must be interpreted: retry any b16 placement
                // floor at its floor (the value gate cares about semantics, not budget).
                let c = match compile_distilled(&d, BUDGET, None) {
                    Ok(c) => c,
                    Err(CompileError::BudgetBelowFloor { floor, .. }) => {
                        floor_retries.insert(format!("{stem}[L{li}][{regime:?}] floor={floor}"));
                        compile_distilled(&d, floor, None)
                            .unwrap_or_else(|e| panic!("[{ctx}] compile at floor {floor}: {e:?}"))
                    }
                    Err(e) => panic!("[{ctx}] compile_distilled: {e:?}"),
                };
                match regime {
                    BwdRegime::R0 => interpreted_r0 += 1,
                    BwdRegime::Ext => interpreted_ext += 1,
                }

                // The shared sweep: encode/decode roundtrip, no orphan descriptors, and
                // interp(program) == oracle across round × role × row (all policies
                // bit-identical), oracled over the RAW canonical `layer`.
                common::assert_bwd_value_parity(&c, &d, layer);
            }
        }
    }

    println!(
        "bwd G1: interpreted {interpreted_r0} R0 + {interpreted_ext} Ext layer instances; \
         {total_fenced} fenced cache columns"
    );
    println!("floor-retries ({}):", floor_retries.len());
    for s in &floor_retries {
        println!("  {s}");
    }
    println!("skipped_decoder ({}):", skipped.len());
    for s in &skipped {
        println!("  {s}");
    }

    assert!(
        interpreted_r0 > 0 && interpreted_ext > 0,
        "both regimes must be exercised"
    );
    // The whole point of this gate post-fence: the corpus MUST exercise fenced cache
    // columns, otherwise the witness-consistent read side is never engaged.
    assert!(
        total_fenced > 0,
        "no fenced cache columns across the corpus — the fence is not being exercised"
    );

    let pinned_skip: BTreeSet<String> = PINNED_SKIPPED_DECODER
        .iter()
        .map(|s| s.to_string())
        .collect();
    assert_eq!(
        skipped, pinned_skip,
        "skipped_decoder set drifted from the pinned expectation — update deliberately"
    );
    let pinned_floor: BTreeSet<String> = PINNED_B16_INFEASIBLE
        .iter()
        .map(|s| s.to_string())
        .collect();
    assert_eq!(
        floor_retries, pinned_floor,
        "b16-infeasible floor-retry set drifted from the pinned expectation — update deliberately"
    );
}
