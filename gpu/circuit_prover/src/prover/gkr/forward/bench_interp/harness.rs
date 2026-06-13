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
    launch_bench_fwd_interp_smem, upload_bench_program_to_constant, BenchThreads, InterpResidency,
    BENCH_INTERP_DEFAULT_SMEM_CAP,
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

/// Time the INTERPRETER side ONLY, at an EXPLICIT dynamic-smem footprint (the
/// `time_interp` body with a padded/natural `smem_bytes` instead of the
/// budget-implied one). Sets B/C/D are interpreter-side sweeps — the flat
/// launch-sum does not vary with the interpreter's budget/smem/residency, so it
/// is NOT re-timed per point here (set A already carries the flat baseline).
/// `smem_bytes` is set B's constant pad or set C's natural size. Returns
/// `Some((median_ms, min_ms))`, or `None` for LDC when the program does not fit.
pub(super) fn time_interp_smem(
    fixture: &CircuitFixture,
    setup: &super::tests::InterpDeviceSetup,
    residency: InterpResidency,
    threads: BenchThreads,
    smem_bytes: usize,
    iters: usize,
) -> Option<(f32, f32)> {
    let context = fixture.context();
    let stream = context.get_exec_stream();
    if residency == InterpResidency::Ldc {
        if !upload_bench_program_to_constant(&setup.lanes).unwrap() {
            return None;
        }
        context.get_exec_stream().synchronize().unwrap();
    }
    let desc = setup.timing_desc();
    let (median, min) = time_iters(stream, iters, || {
        launch_bench_fwd_interp_smem(&desc, residency, threads, smem_bytes, context).unwrap();
    });
    Some((median, min))
}

/// Non-panicking `compile_forward`: returns `None` for a genuinely infeasible
/// (budget, filter) (mandatory cache-cell operands exceeding the budget), so a
/// sweep can record an "infeasible" marker and move on instead of aborting.
/// Shared by the sets B/C feasible-subset sweeps.
pub(super) fn compile_feasible(
    cg_layer: &CodegenLayer,
    graph: &AnalysisGraph,
    budget: usize,
) -> Option<CompiledForward> {
    let fwd_params = FwdParams {
        budget_cells: budget,
        leaf_cache: true,
    };
    catch_unwind(AssertUnwindSafe(|| {
        compile_forward(cg_layer, graph, fwd_params)
    }))
    .ok()
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
        gkr_eval_isa::test_support::check_layer(label, layer_idx, cg_layer, &cf, seed)
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

// ===========================================================================
// Set B secondary readout — host-side ordinary least squares (spec §6.2(B),
// "exploratory correlation"). NO external crate: a plain normal-equations
// solve via Gaussian elimination with partial pivoting. This is a CORRELATION,
// not a causal/validated model: the response is interpreter wall-clock pooled
// across circuits x layers x budgets, the predictors are the per-point
// compiler stats + circuit fixed-effect dummies (controller decision). The
// caller labels it accordingly in the report.
// ===========================================================================

/// A single observation for the pooled regression: response (interp median ms)
/// + the predictor row (already including the leading intercept 1.0 and the
/// circuit fixed-effect dummies — the caller assembles the design row so the
/// solver stays predictor-agnostic).
pub(super) struct RegressionObs {
    pub response: f64,
    /// Design row WITH the leading intercept term (`predictors[0] == 1.0`).
    pub predictors: Vec<f64>,
}

/// OLS fit result: one coefficient per design column (intercept first), R², and
/// residual degrees of freedom (`n_obs - n_coeffs`). `None` columns indicate a
/// rank-deficient / unestimable fit (the solver bailed) — the caller reports
/// that honestly rather than fabricating coefficients.
pub(super) struct RegressionFit {
    pub coefficients: Vec<f64>,
    pub r_squared: f64,
    pub n_obs: usize,
    pub n_coeffs: usize,
    pub residual_dof: isize,
}

/// Fit `response ~ predictors` by ordinary least squares: build the normal
/// equations `XᵀX β = Xᵀy` and solve via Gaussian elimination with partial
/// pivoting. Returns `Err(reason)` when the system is rank-deficient (more
/// coefficients than observations, or a (near-)singular `XᵀX` — e.g. a
/// constant predictor column or a circuit dummy that never varies in the pool),
/// so the caller can report "unestimable" instead of garbage. R² is computed
/// against the response mean.
pub(super) fn fit_ols(obs: &[RegressionObs]) -> Result<RegressionFit, String> {
    let n = obs.len();
    if n == 0 {
        return Err("no observations".into());
    }
    let p = obs[0].predictors.len();
    if obs.iter().any(|o| o.predictors.len() != p) {
        return Err("ragged design matrix (predictor count varies per obs)".into());
    }
    if p > n {
        return Err(format!(
            "rank-deficient: {p} coefficients > {n} observations — reduce predictors"
        ));
    }

    // Normal equations: A = XᵀX (p x p), b = Xᵀy (p).
    let mut a = vec![vec![0.0f64; p]; p];
    let mut b = vec![0.0f64; p];
    for o in obs {
        for i in 0..p {
            b[i] += o.predictors[i] * o.response;
            for j in 0..p {
                a[i][j] += o.predictors[i] * o.predictors[j];
            }
        }
    }

    // Solve A beta = b via Gaussian elimination with partial pivoting.
    let beta = gauss_solve(a, b)?;

    // R²: 1 - SSres/SStot. SStot against the response mean.
    let mean = obs.iter().map(|o| o.response).sum::<f64>() / n as f64;
    let mut ss_res = 0.0f64;
    let mut ss_tot = 0.0f64;
    for o in obs {
        let pred: f64 = o.predictors.iter().zip(&beta).map(|(x, c)| x * c).sum();
        ss_res += (o.response - pred).powi(2);
        ss_tot += (o.response - mean).powi(2);
    }
    let r_squared = if ss_tot > 0.0 {
        1.0 - ss_res / ss_tot
    } else {
        0.0
    };

    Ok(RegressionFit {
        coefficients: beta,
        r_squared,
        n_obs: n,
        n_coeffs: p,
        residual_dof: n as isize - p as isize,
    })
}

/// Solve a dense `n x n` linear system `a x = b` by Gaussian elimination with
/// partial pivoting. `Err` on a (near-)singular matrix.
fn gauss_solve(mut a: Vec<Vec<f64>>, mut b: Vec<f64>) -> Result<Vec<f64>, String> {
    let n = b.len();
    for col in 0..n {
        // Partial pivot: largest |a[row][col]| at or below the diagonal.
        let mut pivot = col;
        let mut best = a[col][col].abs();
        for row in (col + 1)..n {
            let v = a[row][col].abs();
            if v > best {
                best = v;
                pivot = row;
            }
        }
        if best < 1e-12 {
            return Err(format!(
                "singular normal-equations matrix at column {col} (collinear \
                 predictor or a circuit dummy with no within-pool variation)"
            ));
        }
        a.swap(col, pivot);
        b.swap(col, pivot);
        // Eliminate below.
        for row in (col + 1)..n {
            let factor = a[row][col] / a[col][col];
            for k in col..n {
                a[row][k] -= factor * a[col][k];
            }
            b[row] -= factor * b[col];
        }
    }
    // Back-substitution.
    let mut x = vec![0.0f64; n];
    for col in (0..n).rev() {
        let mut s = b[col];
        for k in (col + 1)..n {
            s -= a[col][k] * x[k];
        }
        x[col] = s / a[col][col];
    }
    Ok(x)
}

#[cfg(test)]
mod ols_tests {
    use super::{fit_ols, RegressionObs};

    /// A known-coefficient fit recovers its coefficients and R²≈1 (the OLS
    /// solver is pure host arithmetic — testable without a GPU).
    #[test]
    fn ols_recovers_exact_linear_relation() {
        // y = 2 + 3*x1 - 1*x2, no noise.
        let pts = [(1.0, 1.0), (2.0, 0.0), (0.0, 3.0), (4.0, 2.0), (1.0, 5.0)];
        let obs: Vec<RegressionObs> = pts
            .iter()
            .map(|&(x1, x2)| RegressionObs {
                response: 2.0 + 3.0 * x1 - x2,
                predictors: vec![1.0, x1, x2],
            })
            .collect();
        let fit = fit_ols(&obs).unwrap();
        assert!((fit.coefficients[0] - 2.0).abs() < 1e-6, "intercept");
        assert!((fit.coefficients[1] - 3.0).abs() < 1e-6, "x1 coeff");
        assert!((fit.coefficients[2] + 1.0).abs() < 1e-6, "x2 coeff");
        assert!(fit.r_squared > 1.0 - 1e-9, "R^2 ~ 1");
        assert_eq!(fit.residual_dof, 2);
    }

    /// More coefficients than observations is reported as rank-deficient, not
    /// silently solved.
    #[test]
    fn ols_rank_deficient_is_an_error() {
        let obs = vec![RegressionObs {
            response: 1.0,
            predictors: vec![1.0, 0.0, 0.0],
        }];
        assert!(fit_ols(&obs).is_err());
    }

    /// A collinear predictor (a circuit dummy that never varies) makes the
    /// normal-equations matrix singular — reported, not fabricated.
    #[test]
    fn ols_collinear_predictor_is_an_error() {
        // Second column is identically 1.0 == the intercept => collinear.
        let obs: Vec<RegressionObs> = (0..4)
            .map(|i| RegressionObs {
                response: i as f64,
                predictors: vec![1.0, 1.0, i as f64],
            })
            .collect();
        assert!(fit_ols(&obs).is_err());
    }
}
