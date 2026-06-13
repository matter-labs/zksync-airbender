//! Per-point correctness harness for the stage-3 GKR eval-ISA bench
//! (spec: .agents/specs/2026-06-12-gkr-eval-isa-stage3-cuda-bench-design.md §6.1
//! step 4). `run_point` runs three correctness gates in order for ONE
//! (circuit, layer, budget, filter) point and returns a structured
//! `PointResult`. 6.C-2 will extend this with the timing phase.
//!
//! Correctness-gate failures are RECORDED as `PointResult::Failed` (not
//! panicked) so the driver/report can show WHICH points failed; only a
//! genuinely infeasible `compile_forward` is `Infeasible`. The three gates:
//!   (a) CPU oracle      — `gkr_eval_isa::test_support::check_layer` (panics on
//!                          violation; wrapped in `catch_unwind`).
//!   (b) structural      — `lower_payloads` (runs `verify_lowered_payloads`
//!                          internally) + pointer-equality checks: every
//!                          embedded dst/setup-table/decoder-pred pointer must
//!                          match the resolver's GKRAddress resolution.
//!   (c) device-compare  — `run_real_fixture_parity_point` (interp dsts/outputs
//!                          vs the flat references resident in storage).
//!
//! Seam: `run_point` REPLAYS the layer's flat launches internally (the spec's
//! "per point" granularity), so the flat references gates (b)/(c) read are
//! freshly resident. The budget/filter grid and `assert_layer_consistency`
//! precheck stay in the driver.

use std::panic::{catch_unwind, AssertUnwindSafe};

use cs::gkr_compiler::codegen_ir::CodegenLayer;
use gkr_design_space::graph::AnalysisGraph;
use gkr_eval_isa::compiler::fwd::{compile_forward, CompiledForward, FwdParams};

use super::fixture::{resolve_decoder_pred, CircuitFixture};
use super::lower::{lower_payloads, lowered_payload_pointers, payload_kind_shape};

/// Outcome of one correctness point. 6.C-2 extends `Verified` with timing.
pub(crate) enum PointResult {
    /// All three gates passed.
    Verified,
    /// A correctness gate found a mismatch (recorded, not panicked).
    Failed { gate: &'static str, reason: String },
    /// `compile_forward` panicked for this (budget, filter) — genuinely
    /// infeasible (mandatory cache-cell operands exceeding the budget).
    Infeasible,
}

/// The point's compiler parameters. 6.C-2 adds residency etc.
pub(crate) struct PointParams {
    pub budget: usize,
    pub exclude_max_quadratic: bool,
}

/// Run the three correctness gates for ONE point, returning on the FIRST
/// failure (no later gate, no timing). Replays the layer's flat launches
/// internally so the flat references are resident before gates (b)/(c).
///
/// `seed` is forwarded verbatim to `check_layer`, which mixes in the layer
/// index itself (`seed ^ (li << 32)`); the caller passes the same per-circuit
/// base seed for every layer.
#[cfg(not(no_cuda))]
pub(crate) fn run_point(
    fixture: &CircuitFixture,
    layer_idx: usize,
    cg_layer: &CodegenLayer,
    graph: &AnalysisGraph,
    params: PointParams,
    seed: u64,
    label: &str,
) -> PointResult {
    let fwd_params = FwdParams {
        budget_cells: params.budget,
        leaf_cache: true,
        exclude_max_quadratic: params.exclude_max_quadratic,
    };

    // ---- compile_forward: a panic here = genuine infeasibility, not a fail.
    let cf = match catch_unwind(AssertUnwindSafe(|| {
        compile_forward(cg_layer, graph, fwd_params)
    })) {
        Ok(cf) => cf,
        Err(_) => return PointResult::Infeasible,
    };

    // ---- Gate (a): CPU oracle. `check_layer` PANICS on any violation; convert
    // a panic into a recorded failure.
    if let Err(panic) = catch_unwind(AssertUnwindSafe(|| {
        gkr_eval_isa::test_support::check_layer(
            label,
            layer_idx,
            cg_layer,
            &cf,
            seed,
            params.exclude_max_quadratic,
        )
    })) {
        return PointResult::Failed {
            gate: "oracle",
            reason: panic_message(panic),
        };
    }

    // ---- Replay the layer's flat launches so storage holds the references the
    // structural + device-compare gates read. (Per-point seam; the driver does
    // not replay.)
    fixture
        .replay_layer(layer_idx)
        .expect("replay_layer for run_point");
    fixture.context().get_exec_stream().synchronize().unwrap();

    // ---- Gate (b): structural lowering check. `lower_payloads` runs the
    // byte-walk `verify_lowered_payloads` internally; this adds the pointer-
    // equality checks (controller ruling #3) by lowering with the SAME
    // GKRAddress resolvers gate (c)'s references use, then re-reading the
    // embedded pointers and asserting they match.
    let structural = catch_unwind(AssertUnwindSafe(|| {
        structural_gate(fixture, layer_idx, &cf, cg_layer)
    }))
    .unwrap_or_else(|panic| {
        Err(format!(
            "structural lowering panicked: {}",
            panic_message(panic)
        ))
    });
    if let Err(reason) = structural {
        return PointResult::Failed {
            gate: "structural",
            reason: format!("{label}: {reason}"),
        };
    }

    // ---- Gate (c): device-compare. The body of `run_real_fixture_parity_point`
    // IS gate (c); it returns Err(reason) on the first row/column mismatch (or a
    // non-zero error_flag, wrong native_fired count, or vacuous compare).
    let layer = &fixture.layers[layer_idx];
    match catch_unwind(AssertUnwindSafe(|| {
        super::tests::run_real_fixture_parity_point(fixture, layer, &cf, cg_layer, label)
    })) {
        Ok(Ok(())) => PointResult::Verified,
        Ok(Err(reason)) => PointResult::Failed {
            gate: "device-compare",
            reason,
        },
        Err(panic) => PointResult::Failed {
            gate: "device-compare",
            reason: format!("{label}: device-compare panicked: {}", panic_message(panic)),
        },
    }
}

/// Gate (b) core: lower the payloads with the addr-resolve-based dst resolver
/// (storage GKRAddress pointers, the SAME resolution gate (c)'s references use),
/// then assert every embedded dst pointer == its resolved GKRAddress pointer,
/// the setup-table pointer == `fixture.setup_table().0`, and the decoder-pred
/// pointer == the fixture's decoder-predicate column. `lower_payloads` runs the
/// structural byte-walk (`verify_lowered_payloads`) on the way in.
#[cfg(not(no_cuda))]
fn structural_gate(
    fixture: &CircuitFixture,
    layer_idx: usize,
    cf: &CompiledForward,
    cg_layer: &CodegenLayer,
) -> Result<(), String> {
    let layer = &fixture.layers[layer_idx];
    let arena = &cg_layer.arena.nodes;
    let ch = fixture.bench_challenges();
    let decoder_pred_addr = fixture.decoder_predicate_address();
    let (setup_ptr, setup_len) = fixture.setup_table();

    // Resolve each dst to its storage GKRAddress pointer (the flat reference);
    // capture them so we can compare against the embedded pointers afterward.
    let lp = lower_payloads(
        cf,
        arena,
        |p, _rec, j| fixture.payload_dst_reference(cf, p, j).1 as *mut u8,
        |_p, _rec| resolve_decoder_pred(layer, &fixture.storage, decoder_pred_addr),
        |_ci| (setup_ptr, setup_len),
        &ch,
    );

    for (p, rec) in cf.payloads.iter().enumerate() {
        let (kind, n_dsts, _) = payload_kind_shape(rec);
        let ptrs = lowered_payload_pointers(&lp, p);
        if ptrs.dsts.len() != n_dsts {
            return Err(format!(
                "payload {p}: embedded dst count {} vs kind dst count {n_dsts}",
                ptrs.dsts.len()
            ));
        }
        for j in 0..n_dsts {
            let want = fixture.payload_dst_reference(cf, p, j).1 as u64;
            if ptrs.dsts[j] != want {
                return Err(format!(
                    "payload {p} dst {j}: embedded ptr {:#x} != resolved GKRAddress ptr {want:#x}",
                    ptrs.dsts[j]
                ));
            }
        }
        // VectorizedLookupSetup table pointer.
        if kind == super::lower::PK_CACHE_LOOKUP_SETUP {
            let got = ptrs
                .setup_table
                .ok_or_else(|| format!("payload {p}: lookup-setup record missing table ptr"))?;
            if got != setup_ptr as u64 {
                return Err(format!(
                    "payload {p}: embedded setup-table ptr {got:#x} != fixture setup_table {:#x}",
                    setup_ptr as u64
                ));
            }
        }
        // Decoder-predicate pointer (decoder-select affine tail).
        if let Some(got) = ptrs.decoder_pred {
            let want = resolve_decoder_pred(layer, &fixture.storage, decoder_pred_addr) as u64;
            if got != want {
                return Err(format!(
                    "payload {p}: embedded decoder-pred ptr {got:#x} != resolved pred ptr {want:#x}"
                ));
            }
        }
    }
    Ok(())
}

/// Render a `catch_unwind` payload as a string.
fn panic_message(payload: Box<dyn std::any::Any + Send>) -> String {
    if let Some(s) = payload.downcast_ref::<&str>() {
        (*s).to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "<non-string panic>".to_string()
    }
}
