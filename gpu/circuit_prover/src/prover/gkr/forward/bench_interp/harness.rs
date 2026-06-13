//! Per-point correctness harness for the stage-3 GKR eval-ISA bench
//! (spec: .agents/specs/2026-06-12-gkr-eval-isa-stage3-cuda-bench-design.md §6.1
//! step 4). `run_point` runs three correctness gates in order for ONE
//! (circuit, layer, budget, filter) point and returns a structured
//! `PointResult`. The timing phase (`time_point` / `time_interp` /
//! `prescan_best_budget`) lives in this file too; residency is a `time_point`
//! argument, never gated by `run_point`.
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

use super::fixture::{resolve_decoder_pred, CircuitFixture, LayerFixture};
use super::lower::{lower_payloads, lowered_payload_pointers, payload_kind_shape};
use super::{
    bench_interp_blocks_per_sm, bench_interp_dynamic_smem_bytes, launch_bench_fwd_interp,
    upload_bench_program_to_constant, BenchThreads, InterpResidency, BENCH_INTERP_DEFAULT_SMEM_CAP,
};

/// Outcome of one correctness point. The `Verified` variant carries no timing
/// (timing is a SEPARATE phase: `run_point` runs only the 3 correctness gates;
/// the verdict test times a point ONLY after it returns `Verified`, spec
/// §6.1.4). `time_point` below is the timing entry point.
pub(crate) enum PointResult {
    /// All three gates passed.
    Verified,
    /// A correctness gate found a mismatch (recorded, not panicked).
    Failed { gate: &'static str, reason: String },
    /// `compile_forward` panicked for this (budget, filter) — genuinely
    /// infeasible (mandatory cache-cell operands exceeding the budget).
    Infeasible,
}

/// The point's compiler parameters (budget + filter). Residency/threads are
/// timing-only knobs (`time_point` args), NOT correctness-gate parameters: the
/// lowered program for a given (budget, filter) is identical across residencies,
/// so a single gate certifies every residency timed at that point.
pub(crate) struct PointParams {
    pub budget: usize,
    pub exclude_max_quadratic: bool,
}

// ===========================================================================
// 6.C-2 — timing phase (spec §6.2). NEVER time a point that is not Verified.
// ===========================================================================

/// N for the full verdict timing (spec §6.2). Median + min over this many iters.
pub(super) const TIMING_ITERS: usize = 50;
/// N for the quick best-feasible budget pre-scan (spec §6.3).
pub(super) const PRESCAN_ITERS: usize = 10;
/// Cross-circuit timing cap (controller ruling): time both sides at
/// `min(trace_len, 1<<20)` so runtime is bounded and the comparison is
/// apples-to-apples. The flat launchers grid on the passed count and tolerate
/// `count <= real buffer length`, so a capped count reads/writes only a prefix.
pub(super) const TIMING_COUNT_CAP: usize = 1 << 20;

/// The Task-7 budget grid (spec §6.3). The pre-scan sweeps `grid ∩ feasible`.
pub(super) const BUDGET_GRID: [usize; 7] = [8, 12, 16, 24, 32, 48, 64];

/// Median + min wall-clock (ms) over `iters` CUDA-event-timed runs of `f`. `f`
/// enqueues the work on `stream`; one start/end event pair brackets each iter,
/// `stream.synchronize()` then reads the elapsed time. Test/bench code only.
pub(super) fn time_iters<F: FnMut()>(
    stream: &era_cudart::stream::CudaStream,
    iters: usize,
    mut f: F,
) -> (f32, f32) {
    use era_cudart::event::{elapsed_time, CudaEvent};
    let start = CudaEvent::create().unwrap();
    let end = CudaEvent::create().unwrap();
    let mut samples = Vec::with_capacity(iters);
    for _ in 0..iters {
        start.record(stream).unwrap();
        f();
        end.record(stream).unwrap();
        stream.synchronize().unwrap();
        samples.push(elapsed_time(&start, &end).unwrap());
    }
    samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let min = samples[0];
    let median = samples[samples.len() / 2];
    (median, min)
}

/// Time the FLAT side of one layer: the full replay launch sequence at `count`,
/// over `iters` iterations. Returns `(median_ms, min_ms, launch_count)`.
pub(super) fn time_flat(
    fixture: &CircuitFixture,
    layer_idx: usize,
    count: usize,
    iters: usize,
) -> (f32, f32, usize) {
    let context = fixture.context();
    let stream = context.get_exec_stream();
    let (median, min) = time_iters(stream, iters, || {
        fixture.replay_layer_count(layer_idx, count).unwrap();
    });
    let launches = fixture.layers[layer_idx].replayable_launch_count();
    (median, min, launches)
}

/// Time the INTERPRETER side of one Verified point: ONE
/// `launch_bench_fwd_interp` per iter at `count`, over `iters` iterations, in
/// the timing-desc form (debug sinks nulled). For LDC, the program upload to
/// `__constant__` happens ONCE before the timed loop (spec §6.2). Returns
/// `Some((median_ms, min_ms))`, or `None` for LDC when the program does not fit
/// the constant array (caller records a skip).
pub(super) fn time_interp(
    fixture: &CircuitFixture,
    setup: &super::tests::InterpDeviceSetup,
    residency: InterpResidency,
    threads: BenchThreads,
    iters: usize,
) -> Option<(f32, f32)> {
    let context = fixture.context();
    let stream = context.get_exec_stream();
    if residency == InterpResidency::Ldc {
        // ONE memcpyToSymbol before the timed loop; bail if the program is too
        // large for the constant array.
        if !upload_bench_program_to_constant(&setup.lanes).unwrap() {
            return None;
        }
        context.get_exec_stream().synchronize().unwrap();
    }
    let desc = setup.timing_desc();
    let (median, min) = time_iters(stream, iters, || {
        launch_bench_fwd_interp(&desc, residency, threads, context).unwrap();
    });
    Some((median, min))
}

/// A pre-scan result: the best-feasible budget (min interpreter median) for a
/// given (residency, threads) config, plus that median (spec §6.3). `None` when
/// no grid budget is both feasible AND timeable (e.g. LDC never fits).
pub(super) struct PreScan {
    pub budget: usize,
    pub median_ms: f32,
}

/// Pre-scan the budget grid `∩ feasible` for one (circuit, layer, filter,
/// residency, threads) config, returning the budget with the minimum
/// interpreter median over `PRESCAN_ITERS` iters (spec §6.3). Feasibility is a
/// non-panicking `compile_forward`; an infeasible or non-fitting budget is
/// skipped. Each candidate is built + timed in isolation (its device buffers
/// drop before the next).
#[allow(clippy::too_many_arguments)]
pub(super) fn prescan_best_budget(
    fixture: &CircuitFixture,
    layer_idx: usize,
    cg_layer: &CodegenLayer,
    graph: &AnalysisGraph,
    exclude_max_quadratic: bool,
    residency: InterpResidency,
    threads: BenchThreads,
    count: usize,
) -> Option<PreScan> {
    let layer = &fixture.layers[layer_idx];
    let mut best: Option<PreScan> = None;
    for &budget in &BUDGET_GRID {
        let fwd_params = FwdParams {
            budget_cells: budget,
            leaf_cache: true,
            exclude_max_quadratic,
        };
        // Feasibility: a panicking compile = infeasible budget; skip.
        let cf = match catch_unwind(AssertUnwindSafe(|| {
            compile_forward(cg_layer, graph, fwd_params)
        })) {
            Ok(cf) => cf,
            Err(_) => continue,
        };
        let setup = super::tests::build_interp_device_setup(fixture, layer, &cf, cg_layer, count);
        let Some((median, _min)) = time_interp(fixture, &setup, residency, threads, PRESCAN_ITERS)
        else {
            continue; // LDC didn't fit at this budget.
        };
        if best.as_ref().map(|b| median < b.median_ms).unwrap_or(true) {
            best = Some(PreScan {
                budget,
                median_ms: median,
            });
        }
    }
    best
}

/// The interpreter-side metrics for one timed point, alongside the device/launch
/// context the report row carries (spec §6.2: smem config, occupancy, program/
/// payload bytes, residency, launch counts, trace_len).
pub(super) struct TimedPoint {
    pub flat_median_ms: f32,
    pub flat_min_ms: f32,
    pub flat_launches: usize,
    pub interp_median_ms: f32,
    pub interp_min_ms: f32,
    pub interp_smem_bytes: usize,
    pub interp_blocks_per_sm: i32,
    pub interp_large_smem_optin: bool,
    pub program_bytes: usize,
    pub payload_bytes: usize,
    pub n_instr: u32,
}

/// Time one Verified point (flat + interpreter) at `count`, for the given
/// residency/threads config. Returns `None` for LDC when the program does not
/// fit the constant array (the caller records a skip). MUST be called only on a
/// `Verified` point (spec §6.1.4): the correctness gates run first via
/// `run_point`; `Failed`/`Infeasible` points carry no timing.
#[allow(clippy::too_many_arguments)]
pub(super) fn time_point(
    fixture: &CircuitFixture,
    layer_idx: usize,
    layer: &LayerFixture,
    cf: &CompiledForward,
    cg_layer: &CodegenLayer,
    residency: InterpResidency,
    threads: BenchThreads,
    count: usize,
) -> Option<TimedPoint> {
    let setup = super::tests::build_interp_device_setup(fixture, layer, cf, cg_layer, count);
    let (interp_median, interp_min) =
        time_interp(fixture, &setup, residency, threads, TIMING_ITERS)?;
    let (flat_median, flat_min, flat_launches) = time_flat(fixture, layer_idx, count, TIMING_ITERS);

    let interp_smem_bytes =
        bench_interp_dynamic_smem_bytes(setup.desc.budget_cells, threads.threads_per_block());
    let interp_blocks_per_sm =
        bench_interp_blocks_per_sm(threads, residency, setup.desc.budget_cells).unwrap_or(0);

    Some(TimedPoint {
        flat_median_ms: flat_median,
        flat_min_ms: flat_min,
        flat_launches,
        interp_median_ms: interp_median,
        interp_min_ms: interp_min,
        interp_smem_bytes,
        interp_blocks_per_sm,
        interp_large_smem_optin: interp_smem_bytes > BENCH_INTERP_DEFAULT_SMEM_CAP,
        program_bytes: setup.program_bytes,
        payload_bytes: setup.payload_bytes,
        n_instr: setup.n_instr,
    })
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
