//! Task 4 (CS-M5a): the shared fragment-plan parity gate.
//!
//! Mirrors `bwd_value_parity.rs`'s corpus sweep EXACTLY (same 12 pinned
//! Global-Constraints fixtures × every distillable layer × regime {R0, Ext} ×
//! role × round × sampled row × policy, `BUDGET = 16`,
//! `CacheConsistentResolvers`, orphan/roundtrip/value-parity assertions via
//! the shared [`common::assert_bwd_value_parity`]), but compiles each
//! distilled layer through both the incumbent CS-M5a full-decomposition
//! fragment driver and the shared evaluation-plan compiler. This file and
//! `bwd_value_parity.rs` are separate test binaries and share ONLY `common::`
//! plumbing, so this corpus gate can be extended independently of G1.
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
use gkr_eval_isa::bwd::compile::{BwdCompiledLayer, compile_distilled_fragments_traced};
use gkr_eval_isa::bwd::distill::distill;
use gkr_eval_isa::bwd::trace::BwdEvent;
use gkr_eval_isa::eval_plan::compile_backward_fragments_uncached;
use gkr_eval_isa::fwd::compile::build_cross_layer_field_map;
use gkr_eval_isa::fwd::encode::{decode, encode};
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

fn backward_dram(compiled: &BwdCompiledLayer) -> usize {
    compiled.stats_ext.global + compiled.stats_ext.fold_traffic
}

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
                let (old, old_trace) = match compile_distilled_fragments_traced(&d, BUDGET, None) {
                    Ok(c) => c,
                    Err(CompileError::BudgetBelowFloor { floor, .. }) => {
                        floor_retries.insert(format!("{stem}[L{li}][{regime:?}] floor={floor}"));
                        compile_distilled_fragments_traced(&d, floor, None).unwrap_or_else(|e| {
                            panic!("[{ctx}] compile (identity order) at floor {floor}: {e:?}")
                        })
                    }
                    Err(e) => panic!(
                        "[{ctx}] compile_distilled_fragments_traced (identity order): {e:?}"
                    ),
                };
                let new = compile_backward_fragments_uncached(
                    &d,
                    None,
                    4,
                    old_trace.stream_reductions,
                )
                .unwrap_or_else(|e| panic!("[{ctx}] shared compile (identity order): {e:?}"));
                match regime {
                    BwdRegime::R0 => interpreted_r0 += 1,
                    BwdRegime::Ext => interpreted_ext += 1,
                }

                assert_eq!(decode(&new.encoded).unwrap(), new.compiled.program, "{ctx}");
                assert!(
                    backward_dram(&new.compiled) <= backward_dram(&old),
                    "{ctx}: new DRAM traffic regressed"
                );
                assert!(new.trace.events.iter().all(|event| !matches!(
                    event,
                    BwdEvent::Admit { .. } | BwdEvent::Evict { .. } | BwdEvent::Refuse { .. }
                )));
                common::assert_bwd_value_parity(&new.compiled, &d, layer);
                eprintln!(
                    "{ctx}: instructions old={} new={} encoded_lanes old={} new={}",
                    old.program.instrs.len(),
                    new.compiled.program.instrs.len(),
                    encode(&old.program).unwrap().len(),
                    new.encoded.len(),
                );

                // Pass 2: the SAME distilled layer, fragment order REVERSED — order
                // value-neutrality. Fragment accumulation is a field sum, so any
                // visitation order must reproduce the identical accumulator.
                let rev: Vec<usize> = (0..d.fragments.fragments.len()).rev().collect::<Vec<_>>();
                let (old_rev, old_rev_trace) =
                    match compile_distilled_fragments_traced(&d, BUDGET, Some(&rev)) {
                    Ok(c) => c,
                    Err(CompileError::BudgetBelowFloor { floor, .. }) => {
                        floor_retries
                            .insert(format!("{stem}[L{li}][{regime:?}][rev] floor={floor}"));
                        compile_distilled_fragments_traced(&d, floor, Some(&rev))
                            .unwrap_or_else(|e| {
                                panic!("[{ctx}] compile (reversed order) at floor {floor}: {e:?}")
                            })
                    }
                    Err(e) => panic!(
                        "[{ctx}] compile_distilled_fragments_traced (reversed order): {e:?}"
                    ),
                };
                let new_rev = compile_backward_fragments_uncached(
                    &d,
                    Some(&rev),
                    4,
                    old_rev_trace.stream_reductions,
                )
                .unwrap_or_else(|e| panic!("[{ctx}] shared compile (reversed order): {e:?}"));
                assert_eq!(
                    decode(&new_rev.encoded).unwrap(),
                    new_rev.compiled.program,
                    "{ctx} reversed"
                );
                assert!(
                    backward_dram(&new_rev.compiled) <= backward_dram(&old_rev),
                    "{ctx} reversed: new DRAM traffic regressed"
                );
                assert!(new_rev.trace.events.iter().all(|event| !matches!(
                    event,
                    BwdEvent::Admit { .. } | BwdEvent::Evict { .. } | BwdEvent::Refuse { .. }
                )));
                common::assert_bwd_value_parity(&new_rev.compiled, &d, layer);
                eprintln!(
                    "{ctx} reversed: instructions old={} new={} encoded_lanes old={} new={}",
                    old_rev.program.instrs.len(),
                    new_rev.compiled.program.instrs.len(),
                    encode(&old_rev.program).unwrap().len(),
                    new_rev.encoded.len(),
                );
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
