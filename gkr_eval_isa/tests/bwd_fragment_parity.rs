//! Task 4 (CS-M5a): the fragment-mode G1 parity gate (red, by design).
//!
//! Mirrors `bwd_value_parity.rs`'s corpus sweep EXACTLY (same 12 pinned
//! Global-Constraints fixtures × every distillable layer × regime {R0, Ext} ×
//! role × round × sampled row × policy, `BUDGET = 16`,
//! `CacheConsistentResolvers`, orphan/roundtrip/value-parity assertions via
//! the shared [`common::assert_bwd_value_parity`]), but compiles each
//! distilled layer through the CS-M5a full-decomposition fragment driver
//! (`compile_distilled_fragments`, Task 5) instead of the spine-accumulation
//! driver (`compile_distilled`). This file and `bwd_value_parity.rs` are
//! separate test binaries and share ONLY `common::` plumbing, so this corpus
//! gate can be extended independently of G1.
//!
//! `compile_distilled_fragments` does not exist yet (Task 5, `bwd/compile.rs`,
//! signature `compile_distilled_fragments(d: &DistilledLayer, budget: usize,
//! order: Option<&[usize]>) -> Result<BwdCompiledLayer, CompileError>`) — this
//! file is the TDD gate Task 5 turns green. Everything else here is intended
//! to compile and pass unmodified once that one function lands.
//!
//! # Order value-neutrality (the second pass)
//!
//! For every distilled layer instance, after the identity-order compile
//! (`order: None`) is asserted against the oracle, the SAME distilled layer is
//! recompiled with its fragment order REVERSED
//! (`order: Some(&(0..n_fragments).rev().collect::<Vec<_>>())`) and
//! re-asserted against the SAME oracle. Fragment accumulation is
//! `acc = c_init + Σ_i recipe_i · value(fragment_i)` over field addition —
//! commutative — so any visitation order of the fragment table must produce a
//! bit-identical accumulator. A divergence here is a real fragment-compiler
//! ordering bug, not a flake.
//!
//! # The cache fence
//!
//! Same as G1: post Task-2, the distilled instrument replaces each same-layer
//! cache cone with a `Read(ReadPlace::CacheOutput{..})` fold leaf, so every
//! former `PeekDecoder` layer is distillable (`PINNED_SKIPPED_DECODER` is
//! empty) and `total_fenced > 0` guards the corpus actually exercises the
//! witness-consistent read side (`CacheConsistentResolvers`).

mod common;

use std::collections::BTreeSet;

use common::{load_fixture, schedule_stem, CacheConsistentResolvers};
use cs::gkr_compiler::dag_ir::{bwd_roots, lower_dag, validate, BwdRegime};
use gkr_eval_isa::bwd::compile::compile_distilled_fragments;
use gkr_eval_isa::bwd::distill::distill;
use gkr_eval_isa::fwd::compile::build_cross_layer_field_map;
use gkr_eval_isa::fwd::error::CompileError;

/// The 12 pinned Global-Constraints fixtures — same list as `bwd_value_parity.rs`
/// / `bwd_distill_fixtures.rs` / `fwd_vm_desc_census.rs`.
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

/// Decoder-bearing layers skipped in BOTH regimes (out of v1). EMPTY — same
/// reasoning as `bwd_value_parity.rs`: distillation (upstream of the fragment
/// compiler) fences every same-layer cache cone before this gate ever sees it,
/// so this pin is regime/compiler-independent. Pinned so a coverage change is
/// loud.
const PINNED_SKIPPED_DECODER: &[&str] = &[];

/// Distillable layers whose placement floor at `BUDGET` exceeds it — the value
/// gate still covers them by retrying `compile_distilled_fragments` at the
/// reported floor. Pinned (empty) so a regression is loud. Mirrors
/// `bwd_value_parity.rs`'s pin; if the fragment driver's placement feasibility
/// profile differs from the spine-accumulation driver's, update deliberately.
const PINNED_B16_INFEASIBLE: &[&str] = &[];

const BUDGET: usize = 16;

// ── The gate ────────────────────────────────────────────────────────────────

#[test]
fn bwd_fragment_parity_all_fixtures() {
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
            if bwd_roots(layer).is_empty() {
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

                // Pass 1: identity fragment order (`order: None`).
                let c = match compile_distilled_fragments(&d, BUDGET, None) {
                    Ok(c) => c,
                    Err(CompileError::BudgetBelowFloor { floor, .. }) => {
                        floor_retries.insert(format!("{stem}[L{li}][{regime:?}] floor={floor}"));
                        compile_distilled_fragments(&d, floor, None).unwrap_or_else(|e| {
                            panic!("[{ctx}] compile (identity order) at floor {floor}: {e:?}")
                        })
                    }
                    Err(e) => panic!("[{ctx}] compile_distilled_fragments (identity order): {e:?}"),
                };
                match regime {
                    BwdRegime::R0 => interpreted_r0 += 1,
                    BwdRegime::Ext => interpreted_ext += 1,
                }

                // The shared sweep: encode/decode roundtrip, no orphan descriptors, and
                // interp(program) == oracle across round × role × row (all policies
                // bit-identical), oracled over the RAW canonical `layer`.
                common::assert_bwd_value_parity(&c, &d, layer);

                // Pass 2: the SAME distilled layer, fragment order REVERSED — order
                // value-neutrality. Fragment accumulation is a field sum, so any
                // visitation order must reproduce the identical accumulator.
                let rev: Vec<usize> = (0..d.fragments.fragments.len()).rev().collect::<Vec<_>>();
                let c_rev = match compile_distilled_fragments(&d, BUDGET, Some(&rev)) {
                    Ok(c) => c,
                    Err(CompileError::BudgetBelowFloor { floor, .. }) => {
                        floor_retries
                            .insert(format!("{stem}[L{li}][{regime:?}][rev] floor={floor}"));
                        compile_distilled_fragments(&d, floor, Some(&rev)).unwrap_or_else(|e| {
                            panic!("[{ctx}] compile (reversed order) at floor {floor}: {e:?}")
                        })
                    }
                    Err(e) => {
                        panic!("[{ctx}] compile_distilled_fragments (reversed order): {e:?}")
                    }
                };
                common::assert_bwd_value_parity(&c_rev, &d, layer);
            }
        }
    }

    println!(
        "bwd fragment G1: interpreted {interpreted_r0} R0 + {interpreted_ext} Ext layer instances \
         (each compiled + value-parity-asserted twice: identity + reversed fragment order); \
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

    assert!(interpreted_r0 > 0 && interpreted_ext > 0, "both regimes must be exercised");
    // The whole point of this gate post-fence: the corpus MUST exercise fenced cache
    // columns, otherwise the witness-consistent read side is never engaged.
    assert!(
        total_fenced > 0,
        "no fenced cache columns across the corpus — the fence is not being exercised"
    );

    let pinned_skip: BTreeSet<String> =
        PINNED_SKIPPED_DECODER.iter().map(|s| s.to_string()).collect();
    assert_eq!(
        skipped, pinned_skip,
        "skipped_decoder set drifted from the pinned expectation — update deliberately"
    );
    let pinned_floor: BTreeSet<String> =
        PINNED_B16_INFEASIBLE.iter().map(|s| s.to_string()).collect();
    assert_eq!(
        floor_retries, pinned_floor,
        "b16-infeasible floor-retry set drifted from the pinned expectation — update deliberately"
    );
}
