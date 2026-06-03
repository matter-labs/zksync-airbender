//! Rust bindings for the DIT engine's on-device twiddle fill kernels
//! (`gpu/ntt/native/dit_twiddle_fill.cu`), plus the Rust-side machinery that
//! drives and owns them: the `CLEAN_CONFIGS`/`COUPLED_CONFIGS` sets (the single
//! source of truth shared with the production launcher), the geometry/count
//! helpers (`log_n1_for`/`log_n2_for`, `clean_triangle_count`/
//! `coupled_triangle_count`), the grid=1 `fill_*` launch dispatchers that bake
//! in the launch contract, and the `DitTriangles` struct that holds the fixed
//! triangle-buffer set built once at `DeviceContext::create`.
//!
//! These kernels do a one-time device fill of the per-config butterfly-triangle
//! and coset d-table buffers, reading red's Rust-initialized `ab_ntt_forward_powers`
//! on-device (`get_forward_twiddle_power`) and writing the exact layouts produced
//! by the parity-proven Rust builders (`build_clean_triangle` /
//! `build_coupled_triangle` / `build_coset_delta_table`, see `tests/dit_engine.rs`).
//!
//! LAUNCH CONTRACT: launch every fill kernel with **grid = 1** (single block).
//! The clean/coupled kernels init-to-`ONE` then overwrite active entries, ordered
//! by `__syncthreads()` which synchronizes within one block only; grid > 1 races.
//!
//! Binding shape: the `era_cudart` multi-arm `cuda_kernel!` form (one shared type
//! + a per-symbol macro) generates module-private types and a non-exported local
//! macro, so it cannot be consumed from another module (e.g. the parity test). We
//! therefore use the single-arm `cuda_kernel!(pub(crate) <Type>, <symbol>(..))`
//! form: it honors the visibility, emitting a crate-visible `<Type>Function`
//! (with `Default` wrapping the symbol) and `<Type>Arguments` per config. Launch
//! via `<Type>Function::default().launch(&config, &args)`.
//!
//! These bindings drive the context-init triangle fill, the runtime d-table
//! fill, and the production launcher, and are also consumed by the parity test
//! in `tests/dit_engine.rs`; the crate-wide `#![allow(dead_code)]` covers the
//! per-config `*Arguments`/`*Function` types the macro generates but that the
//! launcher only constructs for the dispatched config.
#![allow(dead_code)]

use std::collections::HashMap;

use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, Dim3, KernelFunction};
use era_cudart::memory::DeviceAllocation;
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart_sys::{cudaFuncSetAttribute, CudaFuncAttribute};
use gpu_core::primitives::context::DeviceProperties;
use gpu_core::primitives::device_structures::{DeviceMatrixChunkImpl, DeviceMatrixChunkMutImpl};
use gpu_core::primitives::field::BaseField;

type BF = BaseField;

// ---------------------------------------------------------------------------
// CLEAN triangle fill. Deduped (LOG_M, LOG_VPT) set: the 12 single-pass pairs
// (the two-pass pass-2 LOG_N2 set {(4,2),(4,3),(5,2),(5,3),(6,3)} is subsumed).
// ---------------------------------------------------------------------------
cuda_kernel!(pub(crate) AbDitFillClean22, ab_dit_fill_clean_triangle_2_2(dst: *mut BF));
cuda_kernel!(pub(crate) AbDitFillClean32, ab_dit_fill_clean_triangle_3_2(dst: *mut BF));
cuda_kernel!(pub(crate) AbDitFillClean33, ab_dit_fill_clean_triangle_3_3(dst: *mut BF));
cuda_kernel!(pub(crate) AbDitFillClean42, ab_dit_fill_clean_triangle_4_2(dst: *mut BF));
cuda_kernel!(pub(crate) AbDitFillClean43, ab_dit_fill_clean_triangle_4_3(dst: *mut BF));
cuda_kernel!(pub(crate) AbDitFillClean52, ab_dit_fill_clean_triangle_5_2(dst: *mut BF));
cuda_kernel!(pub(crate) AbDitFillClean53, ab_dit_fill_clean_triangle_5_3(dst: *mut BF));
cuda_kernel!(pub(crate) AbDitFillClean62, ab_dit_fill_clean_triangle_6_2(dst: *mut BF));
cuda_kernel!(pub(crate) AbDitFillClean63, ab_dit_fill_clean_triangle_6_3(dst: *mut BF));
cuda_kernel!(pub(crate) AbDitFillClean72, ab_dit_fill_clean_triangle_7_2(dst: *mut BF));
cuda_kernel!(pub(crate) AbDitFillClean73, ab_dit_fill_clean_triangle_7_3(dst: *mut BF));
cuda_kernel!(pub(crate) AbDitFillClean83, ab_dit_fill_clean_triangle_8_3(dst: *mut BF));

// ---------------------------------------------------------------------------
// COUPLED pass-1 triangle fill — every two-pass config (v8 LOG_N 9..13, v4
// LOG_N 8..12); LOG_N1 is derived inside the kernel.
// ---------------------------------------------------------------------------
cuda_kernel!(pub(crate) AbDitFillCoupled93, ab_dit_fill_coupled_triangle_9_3(dst: *mut BF));
cuda_kernel!(pub(crate) AbDitFillCoupled103, ab_dit_fill_coupled_triangle_10_3(dst: *mut BF));
cuda_kernel!(pub(crate) AbDitFillCoupled113, ab_dit_fill_coupled_triangle_11_3(dst: *mut BF));
cuda_kernel!(pub(crate) AbDitFillCoupled123, ab_dit_fill_coupled_triangle_12_3(dst: *mut BF));
cuda_kernel!(pub(crate) AbDitFillCoupled133, ab_dit_fill_coupled_triangle_13_3(dst: *mut BF));
cuda_kernel!(pub(crate) AbDitFillCoupled82, ab_dit_fill_coupled_triangle_8_2(dst: *mut BF));
cuda_kernel!(pub(crate) AbDitFillCoupled92, ab_dit_fill_coupled_triangle_9_2(dst: *mut BF));
cuda_kernel!(pub(crate) AbDitFillCoupled102, ab_dit_fill_coupled_triangle_10_2(dst: *mut BF));
cuda_kernel!(pub(crate) AbDitFillCoupled112, ab_dit_fill_coupled_triangle_11_2(dst: *mut BF));
cuda_kernel!(pub(crate) AbDitFillCoupled122, ab_dit_fill_coupled_triangle_12_2(dst: *mut BF));

// ---------------------------------------------------------------------------
// Coset d-table fill — every two-pass LOG_N (8..13).
// ---------------------------------------------------------------------------
cuda_kernel!(pub(crate) AbDitFillDTable8, ab_dit_fill_d_table_8(dst: *mut BF, step_per_iter: u32));
cuda_kernel!(pub(crate) AbDitFillDTable9, ab_dit_fill_d_table_9(dst: *mut BF, step_per_iter: u32));
cuda_kernel!(pub(crate) AbDitFillDTable10, ab_dit_fill_d_table_10(dst: *mut BF, step_per_iter: u32));
cuda_kernel!(pub(crate) AbDitFillDTable11, ab_dit_fill_d_table_11(dst: *mut BF, step_per_iter: u32));
cuda_kernel!(pub(crate) AbDitFillDTable12, ab_dit_fill_d_table_12(dst: *mut BF, step_per_iter: u32));
cuda_kernel!(pub(crate) AbDitFillDTable13, ab_dit_fill_d_table_13(dst: *mut BF, step_per_iter: u32));

// ---------------------------------------------------------------------------
// Fixed config sets. Defined once here so the context-init triangle fill
// (Task 2) and the production launcher (Task 3) share a single source of truth.
//
// CLEAN `(log_m, log_vpt)` — the deduped 12-pair set: single-pass v4
// (`log_m` 2..7) + v8 (`log_m` 3..8) UNION the two-pass pass-2 `(log_n2, log_vpt)`
// set `{(4,2),(4,3),(5,2),(5,3),(6,3)}` (which is fully subsumed; verifiable by
// applying `log_n2_for` to each two-pass config below).
// ---------------------------------------------------------------------------
pub(crate) const CLEAN_CONFIGS: &[(u8, u8)] = &[
    (2, 2),
    (3, 2),
    (3, 3),
    (4, 2),
    (4, 3),
    (5, 2),
    (5, 3),
    (6, 2),
    (6, 3),
    (7, 2),
    (7, 3),
    (8, 3),
];

// COUPLED `(log_n, log_vpt)` — every two-pass config (v8 `log_n` 9..13,
// v4 `log_n` 8..12). `log_n1` is derived from `log_n1_for`.
pub(crate) const COUPLED_CONFIGS: &[(u8, u8)] = &[
    (9, 3),
    (10, 3),
    (11, 3),
    (12, 3),
    (13, 3),
    (8, 2),
    (9, 2),
    (10, 2),
    (11, 2),
    (12, 2),
];

// ---------------------------------------------------------------------------
// Geometry / sizing helpers (production ports of the parity-proven Rust ports
// in `tests/dit_engine.rs`). Needed by Task 2 (buffer sizes) and Task 3 (d-table
// size + dynamic smem).
// ---------------------------------------------------------------------------

/// `log_n2 = min(log_n / 2, log_vpt + 3)` (matches `TwoPassGeom::new`).
pub(crate) fn log_n2_for(log_n: u32, log_vpt: u32) -> u32 {
    (log_n / 2).min(log_vpt + 3)
}

/// `log_n1 = log_n - log_n2` (matches `TwoPassGeom::new`).
pub(crate) fn log_n1_for(log_n: u32, log_vpt: u32) -> u32 {
    log_n - log_n2_for(log_n, log_vpt)
}

/// `clean_triangle_count(log_m, log_vpt) == 2^log_m - 1`.
pub(crate) fn clean_triangle_count(log_m: u32, log_vpt: u32) -> usize {
    let lanes = 1usize << (log_m - log_vpt);
    (lanes << log_vpt) - 1
}

/// `coupled_triangle_count == THREADS*(VPT-1) + N2*(LANES_P1-1)`, with
/// `log_n1`/`log_n2` derived from `log_n2_for`/`log_n1_for`.
pub(crate) fn coupled_triangle_count(log_n: u32, log_vpt: u32) -> usize {
    let log_n1 = log_n1_for(log_n, log_vpt);
    let vpt = 1usize << log_vpt;
    let threads = 1usize << (log_n - log_vpt);
    let lanes_p1 = 1usize << (log_n1 - log_vpt);
    let n2 = 1usize << (log_n - log_n1);
    threads * (vpt - 1) + n2 * (lanes_p1 - 1)
}

// ---------------------------------------------------------------------------
// Launch-contract-encapsulating dispatch helpers. Each fill config is a distinct
// generated `cuda_kernel!` type; these match (config) -> launch and bake in the
// grid=1 / block=256 contract so callers can't get it wrong. Used by Task 2
// (context init) and Task 3 (runtime d-table fill).
// ---------------------------------------------------------------------------

/// Fixed block size for all fill launches; grid = 1 (single block) per the
/// LAUNCH CONTRACT above. The grid-stride loops inside the kernels cover any
/// count with this block size.
const FILL_BLOCK_THREADS: u32 = 256;

fn fill_launch_config(stream: &CudaStream) -> CudaLaunchConfig<'_> {
    let grid_dim: Dim3 = 1u32.into();
    let block_dim: Dim3 = FILL_BLOCK_THREADS.into();
    CudaLaunchConfig::basic(grid_dim, block_dim, stream)
}

/// Launch the CLEAN-triangle fill kernel for `(log_m, log_vpt)` into `dst`.
pub(crate) fn fill_clean_triangle(
    log_m: u32,
    log_vpt: u32,
    dst: &mut DeviceSlice<BF>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let config = fill_launch_config(stream);
    let dst = dst.as_mut_ptr();
    match (log_m, log_vpt) {
        (2, 2) => AbDitFillClean22Function::default()
            .launch(&config, &AbDitFillClean22Arguments::new(dst)),
        (3, 2) => AbDitFillClean32Function::default()
            .launch(&config, &AbDitFillClean32Arguments::new(dst)),
        (3, 3) => AbDitFillClean33Function::default()
            .launch(&config, &AbDitFillClean33Arguments::new(dst)),
        (4, 2) => AbDitFillClean42Function::default()
            .launch(&config, &AbDitFillClean42Arguments::new(dst)),
        (4, 3) => AbDitFillClean43Function::default()
            .launch(&config, &AbDitFillClean43Arguments::new(dst)),
        (5, 2) => AbDitFillClean52Function::default()
            .launch(&config, &AbDitFillClean52Arguments::new(dst)),
        (5, 3) => AbDitFillClean53Function::default()
            .launch(&config, &AbDitFillClean53Arguments::new(dst)),
        (6, 2) => AbDitFillClean62Function::default()
            .launch(&config, &AbDitFillClean62Arguments::new(dst)),
        (6, 3) => AbDitFillClean63Function::default()
            .launch(&config, &AbDitFillClean63Arguments::new(dst)),
        (7, 2) => AbDitFillClean72Function::default()
            .launch(&config, &AbDitFillClean72Arguments::new(dst)),
        (7, 3) => AbDitFillClean73Function::default()
            .launch(&config, &AbDitFillClean73Arguments::new(dst)),
        (8, 3) => AbDitFillClean83Function::default()
            .launch(&config, &AbDitFillClean83Arguments::new(dst)),
        _ => panic!("unsupported clean fill config (log_m={log_m}, log_vpt={log_vpt})"),
    }
}

/// Launch the COUPLED pass-1 triangle fill kernel for `(log_n, log_vpt)` into `dst`.
pub(crate) fn fill_coupled_triangle(
    log_n: u32,
    log_vpt: u32,
    dst: &mut DeviceSlice<BF>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let config = fill_launch_config(stream);
    let dst = dst.as_mut_ptr();
    match (log_n, log_vpt) {
        (9, 3) => AbDitFillCoupled93Function::default()
            .launch(&config, &AbDitFillCoupled93Arguments::new(dst)),
        (10, 3) => AbDitFillCoupled103Function::default()
            .launch(&config, &AbDitFillCoupled103Arguments::new(dst)),
        (11, 3) => AbDitFillCoupled113Function::default()
            .launch(&config, &AbDitFillCoupled113Arguments::new(dst)),
        (12, 3) => AbDitFillCoupled123Function::default()
            .launch(&config, &AbDitFillCoupled123Arguments::new(dst)),
        (13, 3) => AbDitFillCoupled133Function::default()
            .launch(&config, &AbDitFillCoupled133Arguments::new(dst)),
        (8, 2) => AbDitFillCoupled82Function::default()
            .launch(&config, &AbDitFillCoupled82Arguments::new(dst)),
        (9, 2) => AbDitFillCoupled92Function::default()
            .launch(&config, &AbDitFillCoupled92Arguments::new(dst)),
        (10, 2) => AbDitFillCoupled102Function::default()
            .launch(&config, &AbDitFillCoupled102Arguments::new(dst)),
        (11, 2) => AbDitFillCoupled112Function::default()
            .launch(&config, &AbDitFillCoupled112Arguments::new(dst)),
        (12, 2) => AbDitFillCoupled122Function::default()
            .launch(&config, &AbDitFillCoupled122Arguments::new(dst)),
        _ => panic!("unsupported coupled fill config (log_n={log_n}, log_vpt={log_vpt})"),
    }
}

/// Launch the coset d-table fill kernel for `log_n` into `dst`. Not consumed
/// until Task 3 (runtime per-LDE d-table fill); kept here so all three fill
/// dispatchers share one launch-contract home.
pub(crate) fn fill_d_table(
    log_n: u32,
    dst: &mut DeviceSlice<BF>,
    step_per_iter: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let config = fill_launch_config(stream);
    let dst = dst.as_mut_ptr();
    match log_n {
        8 => AbDitFillDTable8Function::default()
            .launch(&config, &AbDitFillDTable8Arguments::new(dst, step_per_iter)),
        9 => AbDitFillDTable9Function::default()
            .launch(&config, &AbDitFillDTable9Arguments::new(dst, step_per_iter)),
        10 => AbDitFillDTable10Function::default().launch(
            &config,
            &AbDitFillDTable10Arguments::new(dst, step_per_iter),
        ),
        11 => AbDitFillDTable11Function::default().launch(
            &config,
            &AbDitFillDTable11Arguments::new(dst, step_per_iter),
        ),
        12 => AbDitFillDTable12Function::default().launch(
            &config,
            &AbDitFillDTable12Arguments::new(dst, step_per_iter),
        ),
        13 => AbDitFillDTable13Function::default().launch(
            &config,
            &AbDitFillDTable13Arguments::new(dst, step_per_iter),
        ),
        _ => panic!("unsupported d-table fill config (log_n={log_n})"),
    }
}

// ---------------------------------------------------------------------------
// DitTriangles — the fixed, indexed set of butterfly-triangle buffers, built
// ONCE at `DeviceContext::create` and read-only afterward (NO lazy cache, NO
// interior mutability, NO runtime insertion).
// ---------------------------------------------------------------------------
pub(crate) struct DitTriangles {
    clean: HashMap<(u8, u8), DeviceAllocation<BF>>,
    coupled: HashMap<(u8, u8), DeviceAllocation<BF>>,
}

impl DitTriangles {
    /// Build every CLEAN and COUPLED triangle buffer once: `alloc` the buffer,
    /// launch the matching fill kernel (grid=1), insert. The caller MUST
    /// `stream.synchronize()` once after this returns and before reading any
    /// buffer (the launches are async on `stream`).
    pub(crate) fn build(stream: &CudaStream) -> CudaResult<Self> {
        let mut clean = HashMap::with_capacity(CLEAN_CONFIGS.len());
        for &(log_m, log_vpt) in CLEAN_CONFIGS {
            let count = clean_triangle_count(log_m as u32, log_vpt as u32);
            let mut buf = DeviceAllocation::<BF>::alloc(count)?;
            fill_clean_triangle(log_m as u32, log_vpt as u32, &mut buf, stream)?;
            clean.insert((log_m, log_vpt), buf);
        }

        let mut coupled = HashMap::with_capacity(COUPLED_CONFIGS.len());
        for &(log_n, log_vpt) in COUPLED_CONFIGS {
            let count = coupled_triangle_count(log_n as u32, log_vpt as u32);
            let mut buf = DeviceAllocation::<BF>::alloc(count)?;
            fill_coupled_triangle(log_n as u32, log_vpt as u32, &mut buf, stream)?;
            coupled.insert((log_n, log_vpt), buf);
        }

        Ok(Self { clean, coupled })
    }

    /// The CLEAN triangle for `(log_m, log_vpt)`. Panics on a config absent from
    /// the fixed set (programmer error — the set is closed at init).
    pub(crate) fn clean(&self, log_m: u32, log_vpt: u32) -> &DeviceSlice<BF> {
        debug_assert!(
            log_m <= u8::MAX as u32,
            "log_m={log_m} overflows the u8 key"
        );
        debug_assert!(
            log_vpt <= u8::MAX as u32,
            "log_vpt={log_vpt} overflows the u8 key"
        );
        let buf = self
            .clean
            .get(&(log_m as u8, log_vpt as u8))
            .unwrap_or_else(|| {
                panic!("no precomputed clean triangle for (log_m={log_m}, log_vpt={log_vpt})")
            });
        &buf[..]
    }

    /// The COUPLED triangle for `(log_n, log_vpt)`. Panics on a config absent
    /// from the fixed set (programmer error — the set is closed at init).
    pub(crate) fn coupled(&self, log_n: u32, log_vpt: u32) -> &DeviceSlice<BF> {
        debug_assert!(
            log_n <= u8::MAX as u32,
            "log_n={log_n} overflows the u8 key"
        );
        debug_assert!(
            log_vpt <= u8::MAX as u32,
            "log_vpt={log_vpt} overflows the u8 key"
        );
        let buf = self
            .coupled
            .get(&(log_n as u8, log_vpt as u8))
            .unwrap_or_else(|| {
                panic!("no precomputed coupled triangle for (log_n={log_n}, log_vpt={log_vpt})")
            });
        &buf[..]
    }
}

// ===========================================================================
// PHASE-2 Task 3 — production launcher `monomials_to_evals_dit`.
//
// Runs the vendored DIT engine hot kernels (`ntt_single` / `ntt_two_pass`,
// see `gpu/ntt/native/dit_kernels.cuh`, launched via the `ab_dit_single_*` /
// `ab_dit_two_pass_*` wrappers in `dit_kernels_extern.cu`) for the streaming range
// (log_n in [2, 13]). It uses red's coset-major param model: same coset-major
// param model + column loop + strided output, borrowing the precomputed
// `DitTriangles` from the `DeviceContext` and filling the two-pass d-table at
// runtime into a caller-provided pooled scratch buffer.
//
// Wired into strategy/dispatch (Task 4) and the production callers (Task 5):
// `select_forward_strategy` routes log_n in [2, 13] here via
// `NttKernelKind::MonomialsToEvalsDit`.
// ===========================================================================

// ---------------------------------------------------------------------------
// Hot-kernel bindings — the new ABI (trailing `coset_out_stride: u32`). One
// `pub(crate)` single-arm `cuda_kernel!` per symbol so each is crate-visible.
// Single-pass: `(mono, tw_clean, out, cfp_0, coset_step, coset_out_stride)`.
// ---------------------------------------------------------------------------
// Production single-pass = the STREAMING kernel (guarded grid-stride + delta
// walk), unified with two-pass on the streaming/diagonal launch. 7-arg ABI
// (runtime num_cosets, no d-table). The static `ab_dit_single_*` wrappers still
// exist in native for the parity tests, but the launcher no longer uses them.
cuda_kernel!(pub(crate) AbDitSingleStream33, ab_dit_single_stream_3_3(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(pub(crate) AbDitSingleStream43, ab_dit_single_stream_4_3(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(pub(crate) AbDitSingleStream53, ab_dit_single_stream_5_3(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(pub(crate) AbDitSingleStream63, ab_dit_single_stream_6_3(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(pub(crate) AbDitSingleStream73, ab_dit_single_stream_7_3(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(pub(crate) AbDitSingleStream83, ab_dit_single_stream_8_3(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(pub(crate) AbDitSingleStream22, ab_dit_single_stream_2_2(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(pub(crate) AbDitSingleStream32, ab_dit_single_stream_3_2(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(pub(crate) AbDitSingleStream42, ab_dit_single_stream_4_2(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(pub(crate) AbDitSingleStream52, ab_dit_single_stream_5_2(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(pub(crate) AbDitSingleStream62, ab_dit_single_stream_6_2(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(pub(crate) AbDitSingleStream72, ab_dit_single_stream_7_2(mono: *const BF, tw_clean: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));

// Two-pass: `(mono, tw_p1, tw_p2, d_table, out, cfp_0, coset_step, num_cosets, coset_out_stride)`.
cuda_kernel!(pub(crate) AbDitTwoPass93, ab_dit_two_pass_9_3(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(pub(crate) AbDitTwoPass103, ab_dit_two_pass_10_3(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(pub(crate) AbDitTwoPass113, ab_dit_two_pass_11_3(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(pub(crate) AbDitTwoPass123, ab_dit_two_pass_12_3(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(pub(crate) AbDitTwoPass133, ab_dit_two_pass_13_3(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(pub(crate) AbDitTwoPass82, ab_dit_two_pass_8_2(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(pub(crate) AbDitTwoPass92, ab_dit_two_pass_9_2(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(pub(crate) AbDitTwoPass102, ab_dit_two_pass_10_2(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(pub(crate) AbDitTwoPass112, ab_dit_two_pass_11_2(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));
cuda_kernel!(pub(crate) AbDitTwoPass122, ab_dit_two_pass_12_2(mono: *const BF, tw_p1: *const BF, tw_p2: *const BF, d_table: *const BF, out: *mut BF, cfp_0: u32, coset_step: u32, num_cosets: u32, coset_out_stride: u32));

/// Two-pass dynamic-smem size in bytes for `(log_n, log_vpt)`, mirroring
/// `ntt_two_pass_smem<LOG_N, LOG_VPT>()` in `dit_kernels.cuh`:
/// `(coupled_count + P2C_PAD + N + N) * sizeof(BF)`, where
/// `P2C_PAD = (clean_count(LOG_N2, LOG_VPT) + 3) & !3`. Reuses the
/// parity-proven `clean_triangle_count` / `coupled_triangle_count` /
/// `log_n2_for` helpers (do NOT re-derive).
pub(crate) fn ntt_two_pass_smem_bytes(log_n: u32, log_vpt: u32) -> usize {
    let n = 1usize << log_n;
    let log_n2 = log_n2_for(log_n, log_vpt);
    let p1c = coupled_triangle_count(log_n, log_vpt);
    let p2c = clean_triangle_count(log_n2, log_vpt);
    let p2c_pad = (p2c + 3) & !3;
    (p1c + p2c_pad + n + n) * std::mem::size_of::<BF>()
}

/// Production launcher for the DIT NTT engine over the streaming range
/// (`log_n` in `[2, 13]`).
///
/// Maps red's coset-major params to the engine's `(cfp_0, coset_step,
/// num_cosets)` model: `coset_step = 1 << coset_factor_shift` (= `2^(OMEGA_LOG_ORDER -
/// log_n - log_lde_factor)`), `cfp_0 = coset_index_base << coset_factor_shift`.
/// Borrows the precomputed CLEAN / COUPLED triangles from `ctx` and fills the
/// two-pass d-table once at runtime into the caller-provided `d_table_scratch`
/// (len >= N; allocated from the stream-ordered pool so this stays enqueue-only
/// per the GPU scheduling contract — no per-call cudaMalloc/cudaFree). The
/// single-pass path ignores the scratch. Loops over columns, writing each
/// (coset, column) slab at the strided output offset.
#[allow(clippy::too_many_arguments)]
pub(crate) fn monomials_to_evals_dit(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_n: usize,
    log_vpt: usize,
    coset_index_base: usize,
    coset_factor_shift: u32,
    num_cosets: usize,
    num_cols_per_coset: usize,
    transposed_monomials: bool,
    ctx: &crate::ntt_twiddles::DeviceContext,
    d_table_scratch: &mut DeviceSlice<BF>,
    stream: &CudaStream,
    device_props: &DeviceProperties,
) -> CudaResult<()> {
    assert!(
        (2..=13).contains(&log_n),
        "DIT NTT only supports log_n in [2, 13]"
    );
    assert!(
        log_vpt == 2 || log_vpt == 3,
        "log_vpt must be 2 (vec4) or 3 (vec8), got {log_vpt}"
    );
    assert!(
        log_n >= log_vpt,
        "log_n ({log_n}) must be >= log_vpt ({log_vpt})"
    );
    assert!(
        !transposed_monomials,
        "DIT NTT does not support transposed monomials"
    );
    assert!(
        num_cosets.is_power_of_two(),
        "num_cosets must be a power of 2 (got {num_cosets})"
    );
    let n = 1usize << log_n;
    assert_eq!(inputs_matrix.rows(), n);
    assert_eq!(outputs_matrix.rows(), n);
    let num_ntts = inputs_matrix.cols();
    assert!(
        num_cols_per_coset >= num_ntts,
        "num_cols_per_coset ({num_cols_per_coset}) < num_ntts ({num_ntts})",
    );
    let max_col_offset_exclusive = (num_cosets - 1) * num_cols_per_coset + num_ntts;
    assert!(
        outputs_matrix.cols() >= max_col_offset_exclusive,
        "outputs_matrix.cols() = {} < {} (num_cosets={}, stride={}, num_ntts={})",
        outputs_matrix.cols(),
        max_col_offset_exclusive,
        num_cosets,
        num_cols_per_coset,
        num_ntts,
    );

    let cfp_0 = (coset_index_base as u32) << coset_factor_shift;
    let coset_step = 1u32 << coset_factor_shift;
    let two_pass = log_n > log_vpt + 5;

    // Per-coset OUTPUT stride in BF elements. The hot kernels multiply
    // `coset_idx * coset_out_stride`; this matches the streaming kernel's
    // `coset_stride_bf = num_cols_per_coset * output_stride`.
    let coset_out_stride_u64 = (num_cols_per_coset as u64) * (outputs_matrix.stride() as u64);
    assert!(
        coset_out_stride_u64 <= u32::MAX as u64,
        "coset_out_stride ({coset_out_stride_u64}) overflows u32",
    );
    let coset_out_stride = coset_out_stride_u64 as u32;

    let input_stride = inputs_matrix.stride();
    let input_offset = inputs_matrix.offset();
    let output_stride = outputs_matrix.stride();
    let output_offset = outputs_matrix.offset();

    // Engine geometry (NUM_WARPS=4, K_PER_NTT_SLOT=8 baked into the wrappers).
    if two_pass {
        // block_dim = N / VPT (= NttTwoPassGeom::THREADS); free grid choice.
        let block_dim = (n >> log_vpt) as u32;
        let smem = ntt_two_pass_smem_bytes(log_n as u32, log_vpt as u32);
        assert!(
            smem <= device_props.max_dynamic_smem_per_block_optin,
            "two-pass DIT NTT at log_n={log_n} needs {smem} bytes dynamic smem \
             but device cap is {} bytes",
            device_props.max_dynamic_smem_per_block_optin,
        );
        // DIAGONAL launch. One "wave" = sm_count × max-active-blocks-per-SM for
        // THIS kernel (queried at runtime, AFTER opting into the dynamic smem
        // cap). The measured optimum scales inversely with block size: 1 wave at
        // 1024 threads/block, 2 at 512, 4 at 256, 8 at 128, 16 at 64 — i.e.
        // `wave_mult = 1024 / block_threads`. Big blocks are staging-heavy (want
        // the fewest blocks that fill the machine); small blocks are light and
        // want more resident blocks to saturate memory. block = N/VPT, so the
        // rule is identical for both VPT. The guarded grid-stride loop covers any
        // remaining cosets, so `grid` need not divide num_cosets.
        let func = two_pass_func(log_n, log_vpt);
        unsafe {
            cudaFuncSetAttribute(
                func.as_ptr(),
                CudaFuncAttribute::MaxDynamicSharedMemorySize,
                smem as i32,
            )
            .wrap()?;
        }
        let occ = era_cudart::occupancy::max_active_blocks_per_multiprocessor(
            &func,
            block_dim as i32,
            smem,
        )?;
        let one_wave = device_props.sm_count * (occ.max(1) as usize);
        let wave_mult = (1024usize / block_dim as usize).max(1);
        let grid = (one_wave * wave_mult).min(num_cosets).max(1);
        // Per-iteration coset advance = grid * coset_step (see d-table doc).
        let step_per_iter = (grid as u32).wrapping_mul(coset_step);

        // Borrow precomputed triangles; fill the d-table once into scratch.
        let tw_p1_ptr = ctx.coupled_triangle(log_n as u32, log_vpt as u32).as_ptr();
        let log_n2 = log_n2_for(log_n as u32, log_vpt as u32);
        let tw_p2_ptr = ctx.clean_triangle(log_n2, log_vpt as u32).as_ptr();

        // Caller-provided pooled scratch (no per-call cudaMalloc/cudaFree): fill
        // the d-table once into the first N entries.
        assert!(
            d_table_scratch.len() >= n,
            "d_table_scratch len ({}) < N ({n}) for two-pass DIT at log_n={log_n}",
            d_table_scratch.len(),
        );
        let d_table = &mut d_table_scratch[..n];
        fill_d_table(log_n as u32, d_table, step_per_iter, stream)?;
        let d_table_ptr = d_table.as_ptr();

        let inputs_slice = inputs_matrix.slice();
        let outputs_slice_mut = outputs_matrix.slice_mut();
        let grid_dim: Dim3 = (grid as u32).into();
        let block_dim: Dim3 = block_dim.into();
        for col in 0..num_ntts {
            let mono_ptr = unsafe { inputs_slice.as_ptr().add(col * input_stride + input_offset) };
            let out_ptr = unsafe {
                outputs_slice_mut
                    .as_mut_ptr()
                    .add(col * output_stride + output_offset)
            };
            let mut config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
            config.dynamic_smem_bytes = smem;
            let args = AbDitTwoPass93Arguments::new(
                mono_ptr,
                tw_p1_ptr,
                tw_p2_ptr,
                d_table_ptr,
                out_ptr,
                cfp_0,
                coset_step,
                num_cosets as u32,
                coset_out_stride,
            );
            func.launch(&config, &args)?;
        }
        // `d_table_scratch` is owned by the caller and outlives these launches.
    } else {
        // Single-pass: STREAMING kernel + DIAGONAL launch (unified with two-pass).
        // block = NUM_WARPS*32 = 128 threads; smem = clean triangle (< 48 KB, no
        // dynamic-smem opt-in). The guarded grid-stride loop covers any num_cosets,
        // so the grid is free. Diagonal: wave_mult = 1024 / block_threads = 8.
        let block_dim = 4u32 * 32u32; // NUM_WARPS * 32 = 128
        let smem = clean_triangle_count(log_n as u32, log_vpt as u32) * std::mem::size_of::<BF>();
        let tw_clean_ptr = ctx.clean_triangle(log_n as u32, log_vpt as u32).as_ptr();

        let func = single_stream_func(log_n, log_vpt);
        let occ = era_cudart::occupancy::max_active_blocks_per_multiprocessor(
            &func,
            block_dim as i32,
            smem,
        )?;
        let one_wave = device_props.sm_count * (occ.max(1) as usize);
        let wave_mult = (1024usize / block_dim as usize).max(1);
        let grid = (one_wave * wave_mult).min(num_cosets).max(1);

        let inputs_slice = inputs_matrix.slice();
        let outputs_slice_mut = outputs_matrix.slice_mut();
        let grid_dim: Dim3 = (grid as u32).into();
        let block_dim: Dim3 = block_dim.into();
        for col in 0..num_ntts {
            let mono_ptr = unsafe { inputs_slice.as_ptr().add(col * input_stride + input_offset) };
            let out_ptr = unsafe {
                outputs_slice_mut
                    .as_mut_ptr()
                    .add(col * output_stride + output_offset)
            };
            let mut config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
            config.dynamic_smem_bytes = smem;
            let args = AbDitSingleStream33Arguments::new(
                mono_ptr,
                tw_clean_ptr,
                out_ptr,
                cfp_0,
                coset_step,
                num_cosets as u32,
                coset_out_stride,
            );
            func.launch(&config, &args)?;
        }
    }
    Ok(())
}

/// Resolve the single-pass STREAMING hot-kernel function for `(log_n, log_vpt)`.
/// All single-pass-stream symbols share the identical ABI, so they share the
/// `AbDitSingleStream33Arguments` constructor at the call site.
fn single_stream_func(log_n: usize, log_vpt: usize) -> AbDitSingleStream33Function {
    match (log_n, log_vpt) {
        (3, 3) => AbDitSingleStream33Function(ab_dit_single_stream_3_3),
        (4, 3) => AbDitSingleStream33Function(ab_dit_single_stream_4_3),
        (5, 3) => AbDitSingleStream33Function(ab_dit_single_stream_5_3),
        (6, 3) => AbDitSingleStream33Function(ab_dit_single_stream_6_3),
        (7, 3) => AbDitSingleStream33Function(ab_dit_single_stream_7_3),
        (8, 3) => AbDitSingleStream33Function(ab_dit_single_stream_8_3),
        (2, 2) => AbDitSingleStream33Function(ab_dit_single_stream_2_2),
        (3, 2) => AbDitSingleStream33Function(ab_dit_single_stream_3_2),
        (4, 2) => AbDitSingleStream33Function(ab_dit_single_stream_4_2),
        (5, 2) => AbDitSingleStream33Function(ab_dit_single_stream_5_2),
        (6, 2) => AbDitSingleStream33Function(ab_dit_single_stream_6_2),
        (7, 2) => AbDitSingleStream33Function(ab_dit_single_stream_7_2),
        _ => panic!("unsupported single-pass DIT config (log_n={log_n}, log_vpt={log_vpt})"),
    }
}

/// Resolve the two-pass hot-kernel function for `(log_n, log_vpt)`. All
/// two-pass symbols share the identical ABI, so they share the
/// `AbDitTwoPass93Arguments` constructor at the call site.
fn two_pass_func(log_n: usize, log_vpt: usize) -> AbDitTwoPass93Function {
    match (log_n, log_vpt) {
        (9, 3) => AbDitTwoPass93Function(ab_dit_two_pass_9_3),
        (10, 3) => AbDitTwoPass93Function(ab_dit_two_pass_10_3),
        (11, 3) => AbDitTwoPass93Function(ab_dit_two_pass_11_3),
        (12, 3) => AbDitTwoPass93Function(ab_dit_two_pass_12_3),
        (13, 3) => AbDitTwoPass93Function(ab_dit_two_pass_13_3),
        (8, 2) => AbDitTwoPass93Function(ab_dit_two_pass_8_2),
        (9, 2) => AbDitTwoPass93Function(ab_dit_two_pass_9_2),
        (10, 2) => AbDitTwoPass93Function(ab_dit_two_pass_10_2),
        (11, 2) => AbDitTwoPass93Function(ab_dit_two_pass_11_2),
        (12, 2) => AbDitTwoPass93Function(ab_dit_two_pass_12_2),
        _ => panic!("unsupported two-pass DIT config (log_n={log_n}, log_vpt={log_vpt})"),
    }
}
