//! Kernel declarations, `__constant__` symbol uploads and safe launchers.
//!
//! The device tracks a window's backing as `bf *` / `e4 *`; the host tracks it as
//! a `u32` word array (one word per `bf`, four per `e4`), so every pointer that
//! crosses here is a `*mut u32`.

use std::ffi::{c_char, c_void, CStr};

use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
#[cfg(window_diag)]
use era_cudart_sys::cudaMemcpyFromSymbol;
use era_cudart_sys::{
    cudaFuncSetAttribute, cudaMemcpyToSymbol, cuda_struct_and_stub, CudaFuncAttribute,
    CudaMemoryCopyKind,
};

use crate::abi::{
    UniskipCacheDesc, UniskipCompactSlot, UniskipSegDesc, UniskipVmDesc, UniskipWindowDesc,
    UNISKIP_CACHE_UNITS, UNISKIP_CELLS, UNISKIP_COEFF_BANK, UNISKIP_COMPACT_MAX_ROUNDS,
    UNISKIP_EQ_HIGH, UNISKIP_NTT_TABLES, UNISKIP_PAIR_THREADS_128, UNISKIP_SEG_K, UNISKIP_TAPS,
    UNISKIP_THREADS_PER_BLOCK,
};

cuda_struct_and_stub! { static ab_gkr_uniskip_coeff_bank: [[u32; 4]; UNISKIP_COEFF_BANK]; }
cuda_struct_and_stub! { static ab_gkr_uniskip_eq_high: [[u32; 4]; 2 * UNISKIP_EQ_HIGH]; }
cuda_struct_and_stub! { static ab_gkr_uniskip_lde_matrix: [u32; UNISKIP_TAPS * UNISKIP_TAPS]; }
cuda_struct_and_stub! { static ab_gkr_uniskip_fold_weights: [[u32; 4]; UNISKIP_TAPS]; }
cuda_struct_and_stub! { static ab_gkr_uniskip_cache_fill: [u16; UNISKIP_CACHE_UNITS]; }
cuda_struct_and_stub! { static ab_gkr_uniskip_ntt_twiddles: [u32; UNISKIP_NTT_TABLES * UNISKIP_TAPS]; }
cuda_struct_and_stub! { static ab_gkr_uniskip_compact_sched: [UniskipCompactSlot; UNISKIP_COMPACT_MAX_ROUNDS * 32]; }
cuda_struct_and_stub! { static ab_gkr_uniskip_compact_perm: [u32; UNISKIP_TAPS]; }
// Window diagnostics. Both the device symbols and these host references exist only in a
// `GPU_GKR_UNISKIP_BENCH_WINDOW_DIAG=1` build, so a shipped binary carries neither — the
// symbols would otherwise be a permanent (if tiny) footprint on every build.
#[cfg(window_diag)]
cuda_struct_and_stub! { static ab_gkr_uniskip_poison_slots: u32; }
#[cfg(window_diag)]
cuda_struct_and_stub! { static ab_gkr_uniskip_chain_calls: u64; }

/// Blocks a grid-stride launch may use. The kernels loop, so this only bounds the
/// launch; every configuration above it is covered by the stride.
const MAX_BLOCKS: u64 = 1 << 16;

cuda_kernel!(
    InitBf,
    ab_gkr_uniskip_init_bf_kernel(dst: *mut u32, count: u64, seed: u32)
);
cuda_kernel!(
    InitE4,
    ab_gkr_uniskip_init_e4_kernel(dst: *mut u32, count: u64, seed: u32)
);
cuda_kernel!(
    LdeBf,
    ab_gkr_uniskip_lde_bf_kernel(desc: UniskipVmDesc, jobs: *const u16, num_jobs: u32)
);
cuda_kernel!(
    LdeE4,
    ab_gkr_uniskip_lde_e4_kernel(desc: UniskipVmDesc, jobs: *const u16, num_jobs: u32)
);
cuda_kernel!(
    LdeBfRow,
    ab_gkr_uniskip_lde_bf_row_kernel(desc: UniskipVmDesc, jobs: *const u16, num_jobs: u32)
);
cuda_kernel!(
    LdeE4Row,
    ab_gkr_uniskip_lde_e4_row_kernel(desc: UniskipVmDesc, jobs: *const u16, num_jobs: u32)
);
cuda_kernel!(
    FoldBf,
    ab_gkr_uniskip_fold_bf_kernel(
        desc: UniskipVmDesc,
        jobs: *const u16,
        num_jobs: u32,
        folded: *mut u32
    )
);
cuda_kernel!(
    FoldE4,
    ab_gkr_uniskip_fold_e4_kernel(
        desc: UniskipVmDesc,
        jobs: *const u16,
        num_jobs: u32,
        folded: *mut u32
    )
);
cuda_kernel!(Eval, ab_gkr_uniskip_eval_kernel(desc: UniskipVmDesc));
// The fused kernels take the device-side `uniskip_fused_desc`, an empty derived
// class of `uniskip_vm_desc` (same size, same layout, asserted in the header), so
// the wire struct is shared.
cuda_kernel!(EvalFused, ab_gkr_uniskip_eval_fused_kernel(desc: UniskipVmDesc));
cuda_kernel!(
    EvalFusedInterleave,
    ab_gkr_uniskip_eval_fused_interleave_kernel(desc: UniskipVmDesc)
);
// The cached kernels take `uniskip_cached_desc`, the third empty derived class of
// `uniskip_vm_desc` — same wire struct again, and the cache plan travels in the
// records' `cache_slot` byte plus the `ab_gkr_uniskip_cache_fill` symbol.
cuda_kernel!(
    EvalFusedCached,
    ab_gkr_uniskip_eval_fused_cached_kernel(desc: UniskipVmDesc)
);
cuda_kernel!(
    EvalFusedCachedInterleave,
    ab_gkr_uniskip_eval_fused_cached_interleave_kernel(desc: UniskipVmDesc)
);
// The v3 R0 kernel takes `uniskip_lsb_desc`, a fourth empty derived class of
// `uniskip_vm_desc` — same wire struct, LSB-ordered taps, no coset base read.
cuda_kernel!(
    EvalLsbW0,
    ab_gkr_uniskip_eval_lsb_w0_kernel(desc: UniskipVmDesc)
);
// The v3 R1 kernels, one per group count. `uniskip_compact_desc` is a fifth empty
// derived class of `uniskip_vm_desc` - same wire again.
cuda_kernel!(
    EvalLsbCompactG4,
    ab_gkr_uniskip_eval_lsb_compact_g4_kernel(desc: UniskipVmDesc)
);
cuda_kernel!(
    EvalLsbCompactG8,
    ab_gkr_uniskip_eval_lsb_compact_g8_kernel(desc: UniskipVmDesc)
);
// The v3 R2 kernel: pair-resident producer, `uniskip_pair_desc` is the sixth empty
// derived class of `uniskip_vm_desc` — same wire again.
cuda_kernel!(
    EvalLsbPair,
    ab_gkr_uniskip_eval_lsb_pair_kernel(desc: UniskipVmDesc)
);
// The v3 R4 cached kernels: the vm desc plus the prologue table as a SECOND by-value
// parameter, so both no-cache controls keep their launch signature untouched.
cuda_kernel!(
    EvalLsbPairCached,
    ab_gkr_uniskip_eval_lsb_pair_cached_kernel(desc: UniskipVmDesc, plan: UniskipCacheDesc)
);
cuda_kernel!(
    EvalLsbPairCached128,
    ab_gkr_uniskip_eval_lsb_pair_cached_128_kernel(desc: UniskipVmDesc, plan: UniskipCacheDesc)
);
cuda_kernel!(
    EvalLsbPairCached128Lb,
    ab_gkr_uniskip_eval_lsb_pair_cached_128_lb_kernel(desc: UniskipVmDesc, plan: UniskipCacheDesc)
);
// The v3 R4 128-thread no-cache baselines: same wire, same signature, 4 warps. The `_lb`
// sibling is the bounded baseline, so the 128 cache contrast can be taken bound-to-bound.
cuda_kernel!(
    EvalLsbPair128,
    ab_gkr_uniskip_eval_lsb_pair_128_kernel(desc: UniskipVmDesc)
);
cuda_kernel!(
    EvalLsbPair128Lb,
    ab_gkr_uniskip_eval_lsb_pair_128_lb_kernel(desc: UniskipVmDesc)
);
// v3 R3 arms. `pair_lb` is the control body under `__launch_bounds__`; the two window
// entry points take the side descriptor as a SECOND by-value parameter, so the control's
// launch signature is untouched.
cuda_kernel!(
    EvalLsbPairLb,
    ab_gkr_uniskip_eval_lsb_pair_lb_kernel(desc: UniskipVmDesc)
);
cuda_kernel!(
    EvalLsbPairWin,
    ab_gkr_uniskip_eval_lsb_pair_win_kernel(desc: UniskipVmDesc, win: UniskipWindowDesc)
);
cuda_kernel!(
    EvalLsbPairWinLb,
    ab_gkr_uniskip_eval_lsb_pair_win_lb_kernel(desc: UniskipVmDesc, win: UniskipWindowDesc)
);
// v3 R7 segmented kernels. A third by-value parameter carries the per-warp atom lists, so
// every earlier launch signature is untouched. `_cv64` and `_cv100` are one body under two
// symbols: the shared-memory carveout is a sticky per-function attribute, so a rotation
// between two carveout requests needs two functions.
cuda_kernel!(
    EvalLsbSegSCv64,
    ab_gkr_uniskip_eval_lsb_seg_s_cv64_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc,
        seg: UniskipSegDesc
    )
);
cuda_kernel!(
    EvalLsbSegSCv100,
    ab_gkr_uniskip_eval_lsb_seg_s_cv100_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc,
        seg: UniskipSegDesc
    )
);
cuda_kernel!(
    EvalLsbSegSAcc,
    ab_gkr_uniskip_eval_lsb_seg_s_acc_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc,
        seg: UniskipSegDesc
    )
);
cuda_kernel!(
    EvalLsbSegG,
    ab_gkr_uniskip_eval_lsb_seg_g_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc,
        seg: UniskipSegDesc
    )
);
cuda_kernel!(
    EvalLsbSegRecompute,
    ab_gkr_uniskip_eval_lsb_seg_recompute_kernel(desc: UniskipVmDesc, seg: UniskipSegDesc)
);
cuda_kernel!(
    Finalize,
    ab_gkr_uniskip_finalize_kernel(partials: *const u32, blocks: u32, q: *mut u32)
);

fn grid(total: u64) -> u32 {
    total
        .div_ceil(u64::from(UNISKIP_THREADS_PER_BLOCK as u32))
        .clamp(1, MAX_BLOCKS) as u32
}

fn config<'a>(total: u64, stream: &'a CudaStream) -> CudaLaunchConfig<'a> {
    CudaLaunchConfig::basic(grid(total), UNISKIP_THREADS_PER_BLOCK as u32, stream)
}

/// # Safety
///
/// `symbol` must name a `__device__ __constant__` array of exactly `size_of::<T>()`
/// bytes; it is only ever addressed on the host, never dereferenced.
unsafe fn memcpy_to_symbol<T>(symbol: &T, src: &T) -> CudaResult<()> {
    cudaMemcpyToSymbol(
        symbol as *const T as *const c_void,
        src as *const T as *const c_void,
        size_of::<T>(),
        0,
        CudaMemoryCopyKind::HostToDevice,
    )
    .wrap()
}

/// Upload the flattened coset LDE matrix. Entry `[c * UNISKIP_TAPS + t]` is
/// `L_t(gamma * omega^c)`, i.e. row `c` of [`crate::domain::lde_matrix`], which the
/// LDE kernels write into coset plane `c` — the plane [`crate::abi::cell_for_coset_row`]
/// names device cell `UNISKIP_TAPS + c`.
pub fn upload_lde_matrix(matrix: &[u32; UNISKIP_TAPS * UNISKIP_TAPS]) -> CudaResult<()> {
    unsafe { memcpy_to_symbol(&ab_gkr_uniskip_lde_matrix, matrix) }
}

/// Upload both eq high tables. Table 0 occupies `[0, UNISKIP_EQ_HIGH)`, table 1 the
/// remainder — one allocation as far as the init generator is concerned.
pub fn upload_eq_high(tables: &[[u32; 4]; 2 * UNISKIP_EQ_HIGH]) -> CudaResult<()> {
    unsafe { memcpy_to_symbol(&ab_gkr_uniskip_eq_high, tables) }
}

/// Upload the coefficient bank the eval kernel indexes by `term.coeff`.
pub fn upload_coeff_bank(bank: &[[u32; 4]; UNISKIP_COEFF_BANK]) -> CudaResult<()> {
    unsafe { memcpy_to_symbol(&ab_gkr_uniskip_coeff_bank, bank) }
}

/// Upload `[L_t(r)]_t` — [`crate::domain::fold_weights`] at the round challenge, in
/// tap order, which is the order the fold kernels index.
pub fn upload_fold_weights(weights: &[[u32; 4]; UNISKIP_TAPS]) -> CudaResult<()> {
    unsafe { memcpy_to_symbol(&ab_gkr_uniskip_fold_weights, weights) }
}

/// Upload the INVERSE cache plan — [`crate::cache::CachePlan::fill`], unit -> source
/// and limb — which is what the tile fill iterates. Uploaded in every mode so a run
/// never inherits another plan's units; the non-cached kernels never read it.
pub fn upload_cache_fill(fill: &[u16; UNISKIP_CACHE_UNITS]) -> CudaResult<()> {
    unsafe { memcpy_to_symbol(&ab_gkr_uniskip_cache_fill, fill) }
}

/// Upload the LSB producer's lane-indexed twiddles — [`crate::domain::ntt_twiddles`]
/// flattened `[table * UNISKIP_TAPS + lane]`. Uploaded in every mode (they are domain
/// constants, not program state); only the LSB kernel reads them, once per thread into
/// registers, so no hot-path access is a divergent `__constant__` read.
pub fn upload_ntt_twiddles(twiddles: &[u32; UNISKIP_NTT_TABLES * UNISKIP_TAPS]) -> CudaResult<()> {
    unsafe { memcpy_to_symbol(&ab_gkr_uniskip_ntt_twiddles, twiddles) }
}

/// Upload the v3 R1 compaction schedule - [`crate::compact::schedule_words`], padded to
/// the symbol size so a stale tail can never be read as live work. The kernels copy it to
/// shared memory once per block; nothing reads it lane-indexed from `__constant__` in the
/// hot path.
pub fn upload_compact_schedule(
    schedule: &[UniskipCompactSlot; UNISKIP_COMPACT_MAX_ROUNDS * 32],
) -> CudaResult<()> {
    unsafe { memcpy_to_symbol(&ab_gkr_uniskip_compact_sched, schedule) }
}

/// Upload the staging tap permutation — [`crate::compact::bank_perm_words`]. The device
/// reads it once per thread, so the formula lives on the host alone and cannot drift.
pub fn upload_compact_perm(perm: &[u32; UNISKIP_TAPS]) -> CudaResult<()> {
    unsafe { memcpy_to_symbol(&ab_gkr_uniskip_compact_perm, perm) }
}

/// Whether this binary was built with `GPU_GKR_UNISKIP_BENCH_WINDOW_DIAG=1`.
pub const fn window_diag_build() -> bool {
    cfg!(window_diag)
}

/// Set the slot-poison flag (diagnostic builds only).
#[cfg(window_diag)]
pub fn upload_poison_slots(on: bool) -> CudaResult<()> {
    unsafe { memcpy_to_symbol(&ab_gkr_uniskip_poison_slots, &u32::from(on)) }
}

/// Read and reset the chain-execution counter. Exists only in a diagnostic build; the
/// shipped stand-in panics, so callers must gate on [`window_diag_build`] first.
#[cfg(window_diag)]
pub fn take_chain_calls() -> CudaResult<u64> {
    let mut host = 0u64;
    unsafe {
        cudaMemcpyFromSymbol(
            &mut host as *mut u64 as *mut c_void,
            &ab_gkr_uniskip_chain_calls as *const u64 as *const c_void,
            size_of::<u64>(),
            0,
            CudaMemoryCopyKind::DeviceToHost,
        )
        .wrap()?;
    }
    unsafe { memcpy_to_symbol(&ab_gkr_uniskip_chain_calls, &0u64) }?;
    Ok(host)
}

/// Shipped-build stand-ins: the diagnostics have no symbols to talk to here.
#[cfg(not(window_diag))]
pub fn upload_poison_slots(_on: bool) -> CudaResult<()> {
    unreachable!("guarded by window_diag_build()")
}

#[cfg(not(window_diag))]
pub fn take_chain_calls() -> CudaResult<u64> {
    unreachable!("guarded by window_diag_build()")
}

/// Fill a `bf` backing with the deterministic init generator; `dst` is one word
/// per element.
pub fn init_bf(dst: &mut DeviceSlice<u32>, seed: u32, stream: &CudaStream) -> CudaResult<()> {
    let count = dst.len() as u64;
    let args = InitBfArguments::new(dst.as_mut_ptr(), count, seed);
    InitBfFunction::default().launch(&config(count, stream), &args)
}

/// Fill an `e4` backing with the deterministic init generator; `dst` is four words
/// per element.
pub fn init_e4(dst: &mut DeviceSlice<u32>, seed: u32, stream: &CudaStream) -> CudaResult<()> {
    assert_eq!(dst.len() % 4, 0, "an e4 backing is four words per element");
    let count = (dst.len() / 4) as u64;
    let args = InitE4Arguments::new(dst.as_mut_ptr(), count, seed);
    InitE4Function::default().launch(&config(count, stream), &args)
}

fn lde_total(desc: &UniskipVmDesc, num_jobs: usize) -> u64 {
    (1u64 << desc.log_rows) * num_jobs as u64 * UNISKIP_TAPS as u64
}

/// Threads of a row-shape LDE launch: one per (job, row), times `lanes` — 1 for the
/// `bf` kernel, 4 for the `e4` kernel's limb lanes.
fn lde_row_total(desc: &UniskipVmDesc, num_jobs: usize, lanes: u64) -> u64 {
    (1u64 << desc.log_rows) * num_jobs as u64 * lanes
}

/// One coset cell per (job, cell, row) over the `bf` source records in `jobs`.
pub fn lde_bf(
    desc: &UniskipVmDesc,
    jobs: &DeviceSlice<u16>,
    num_jobs: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    if num_jobs == 0 {
        return Ok(());
    }
    let total = lde_total(desc, num_jobs);
    let args = LdeBfArguments::new(*desc, jobs.as_ptr(), num_jobs as u32);
    LdeBfFunction::default().launch(&config(total, stream), &args)
}

/// The `e4` counterpart of [`lde_bf`].
pub fn lde_e4(
    desc: &UniskipVmDesc,
    jobs: &DeviceSlice<u16>,
    num_jobs: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    if num_jobs == 0 {
        return Ok(());
    }
    let total = lde_total(desc, num_jobs);
    let args = LdeE4Arguments::new(*desc, jobs.as_ptr(), num_jobs as u32);
    LdeE4Function::default().launch(&config(total, stream), &args)
}

/// All 16 coset cells per (job, row) over the `bf` source records in `jobs` — the
/// row-shape counterpart of [`lde_bf`], writing the same bytes.
pub fn lde_bf_row(
    desc: &UniskipVmDesc,
    jobs: &DeviceSlice<u16>,
    num_jobs: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    if num_jobs == 0 {
        return Ok(());
    }
    let total = lde_row_total(desc, num_jobs, 1);
    let args = LdeBfRowArguments::new(*desc, jobs.as_ptr(), num_jobs as u32);
    LdeBfRowFunction::default().launch(&config(total, stream), &args)
}

/// The `e4` counterpart of [`lde_bf_row`]: one thread per (job, row, limb).
pub fn lde_e4_row(
    desc: &UniskipVmDesc,
    jobs: &DeviceSlice<u16>,
    num_jobs: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    if num_jobs == 0 {
        return Ok(());
    }
    let total = lde_row_total(desc, num_jobs, 4);
    let args = LdeE4RowArguments::new(*desc, jobs.as_ptr(), num_jobs as u32);
    LdeE4RowFunction::default().launch(&config(total, stream), &args)
}

fn fold_total(desc: &UniskipVmDesc, num_jobs: usize) -> u64 {
    (1u64 << desc.log_rows) * num_jobs as u64
}

/// One `e4` per (job, row) over the `bf` source records in `jobs`, written at
/// `source_id * rows + row` of `folded` (four words per element).
pub fn fold_bf(
    desc: &UniskipVmDesc,
    jobs: &DeviceSlice<u16>,
    num_jobs: usize,
    folded: &mut DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    if num_jobs == 0 {
        return Ok(());
    }
    let total = fold_total(desc, num_jobs);
    let args = FoldBfArguments::new(*desc, jobs.as_ptr(), num_jobs as u32, folded.as_mut_ptr());
    FoldBfFunction::default().launch(&config(total, stream), &args)
}

/// The `e4` counterpart of [`fold_bf`]. The two class job lists partition the
/// source ids, so both write into the same `folded` buffer without overlap.
pub fn fold_e4(
    desc: &UniskipVmDesc,
    jobs: &DeviceSlice<u16>,
    num_jobs: usize,
    folded: &mut DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    if num_jobs == 0 {
        return Ok(());
    }
    let total = fold_total(desc, num_jobs);
    let args = FoldE4Arguments::new(*desc, jobs.as_ptr(), num_jobs as u32, folded.as_mut_ptr());
    FoldE4Function::default().launch(&config(total, stream), &args)
}

/// One block per 32-row tile; writes `UNISKIP_CELLS` `e4` partials per block into
/// `desc.partials`. NOT grid-strided: the grid covers every row exactly once.
pub fn eval(desc: &UniskipVmDesc, blocks: u32, stream: &CudaStream) -> CudaResult<()> {
    let args = EvalArguments::new(*desc);
    let config = CudaLaunchConfig::basic(blocks, UNISKIP_THREADS_PER_BLOCK as u32, stream);
    EvalFunction::default().launch(&config, &args)
}

/// [`eval`] with the coset LDE recomputed on read: same partials, no coset backing.
pub fn eval_fused(desc: &UniskipVmDesc, blocks: u32, stream: &CudaStream) -> CudaResult<()> {
    let args = EvalFusedArguments::new(*desc);
    let config = CudaLaunchConfig::basic(blocks, UNISKIP_THREADS_PER_BLOCK as u32, stream);
    EvalFusedFunction::default().launch(&config, &args)
}

/// [`eval_fused`] under the interleaved cell map — warp `w` owns cells
/// `{w, w+8, w+16, w+24}`, so every warp carries two coset cells' recompute.
pub fn eval_fused_interleave(
    desc: &UniskipVmDesc,
    blocks: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let args = EvalFusedInterleaveArguments::new(*desc);
    let config = CudaLaunchConfig::basic(blocks, UNISKIP_THREADS_PER_BLOCK as u32, stream);
    EvalFusedInterleaveFunction::default().launch(&config, &args)
}

/// [`eval_fused`] with the planned sources' coset slabs cached in shared memory for
/// the block's row tile — filled once at tile start, read thereafter; uncached sources
/// keep the recompute path.
pub fn eval_fused_cached(desc: &UniskipVmDesc, blocks: u32, stream: &CudaStream) -> CudaResult<()> {
    let args = EvalFusedCachedArguments::new(*desc);
    let config = CudaLaunchConfig::basic(blocks, UNISKIP_THREADS_PER_BLOCK as u32, stream);
    EvalFusedCachedFunction::default().launch(&config, &args)
}

/// [`eval_fused_cached`] under the interleaved cell map.
pub fn eval_fused_cached_interleave(
    desc: &UniskipVmDesc,
    blocks: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let args = EvalFusedCachedInterleaveArguments::new(*desc);
    let config = CudaLaunchConfig::basic(blocks, UNISKIP_THREADS_PER_BLOCK as u32, stream);
    EvalFusedCachedInterleaveFunction::default().launch(&config, &args)
}

/// The v3 R0 arm: LSB-ordered taps, one half-warp per group with lane = tap, all 16
/// coset cells produced by a shuffle-NTT per reference (W = 0). `blocks` is
/// `rows / UNISKIP_LSB_ROWS_PER_BLOCK`, not the warp-wide tile the other modes use, and
/// it writes the same `partials[block][UNISKIP_CELLS]` layout so `finalize` is unchanged.
pub fn eval_lsb_w0(desc: &UniskipVmDesc, blocks: u32, stream: &CudaStream) -> CudaResult<()> {
    let args = EvalLsbW0Arguments::new(*desc);
    let config = CudaLaunchConfig::basic(blocks, UNISKIP_THREADS_PER_BLOCK as u32, stream);
    EvalLsbW0Function::default().launch(&config, &args)
}

/// The v3 R1 arm at 4 groups per warp: 8 warps x 4 rows = 32 logical rows per block.
pub fn eval_lsb_compact_g4(
    desc: &UniskipVmDesc,
    blocks: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let args = EvalLsbCompactG4Arguments::new(*desc);
    let config = CudaLaunchConfig::basic(blocks, UNISKIP_THREADS_PER_BLOCK as u32, stream);
    EvalLsbCompactG4Function::default().launch(&config, &args)
}

/// The v3 R1 arm at 8 groups per warp: 8 warps x 8 rows = 64 logical rows per block.
pub fn eval_lsb_compact_g8(
    desc: &UniskipVmDesc,
    blocks: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let args = EvalLsbCompactG8Arguments::new(*desc);
    let config = CudaLaunchConfig::basic(blocks, UNISKIP_THREADS_PER_BLOCK as u32, stream);
    EvalLsbCompactG8Function::default().launch(&config, &args)
}

/// The v3 R2 arm: pair-resident radix-2, 8 warps x 4 groups = 32 logical rows per block.
pub fn eval_lsb_pair(desc: &UniskipVmDesc, blocks: u32, stream: &CudaStream) -> CudaResult<()> {
    let args = EvalLsbPairArguments::new(*desc);
    let config = CudaLaunchConfig::basic(blocks, UNISKIP_THREADS_PER_BLOCK as u32, stream);
    EvalLsbPairFunction::default().launch(&config, &args)
}

/// The v3 R4 128-thread no-cache baseline: 4 warps x 4 groups = 16 logical rows per
/// block, so `blocks` is twice the 256 control's for the same trace.
pub fn eval_lsb_pair_128(desc: &UniskipVmDesc, blocks: u32, stream: &CudaStream) -> CudaResult<()> {
    let args = EvalLsbPair128Arguments::new(*desc);
    let config = CudaLaunchConfig::basic(blocks, UNISKIP_PAIR_THREADS_128 as u32, stream);
    EvalLsbPair128Function::default().launch(&config, &args)
}

/// The v3 R4 128-thread no-cache baseline under `__launch_bounds__(128, 7)` — the bounded
/// control, so the 128 cache contrast is not forced to assume cross-body bound additivity.
pub fn eval_lsb_pair_128_lb(
    desc: &UniskipVmDesc,
    blocks: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let args = EvalLsbPair128LbArguments::new(*desc);
    let config = CudaLaunchConfig::basic(blocks, UNISKIP_PAIR_THREADS_128 as u32, stream);
    EvalLsbPair128LbFunction::default().launch(&config, &args)
}

/// The v3 R4 cached kernel at 256 threads.
pub fn eval_lsb_pair_cached(
    desc: &UniskipVmDesc,
    plan: &UniskipCacheDesc,
    blocks: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let args = EvalLsbPairCachedArguments::new(*desc, *plan);
    let config = CudaLaunchConfig::basic(blocks, UNISKIP_THREADS_PER_BLOCK as u32, stream);
    EvalLsbPairCachedFunction::default().launch(&config, &args)
}

/// The v3 R4 cached kernel at 128 threads.
pub fn eval_lsb_pair_cached_128(
    desc: &UniskipVmDesc,
    plan: &UniskipCacheDesc,
    blocks: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let args = EvalLsbPairCached128Arguments::new(*desc, *plan);
    let config = CudaLaunchConfig::basic(blocks, UNISKIP_PAIR_THREADS_128 as u32, stream);
    EvalLsbPairCached128Function::default().launch(&config, &args)
}

/// The v3 R4 cached kernel at 128 threads under `__launch_bounds__(128, 7)` — the variant
/// that holds control128's block count. See the kernel comment for why both ship.
pub fn eval_lsb_pair_cached_128_lb(
    desc: &UniskipVmDesc,
    plan: &UniskipCacheDesc,
    blocks: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let args = EvalLsbPairCached128LbArguments::new(*desc, *plan);
    let config = CudaLaunchConfig::basic(blocks, UNISKIP_PAIR_THREADS_128 as u32, stream);
    EvalLsbPairCached128LbFunction::default().launch(&config, &args)
}

/// v3 R6: steer the shared-memory carveout of the bounded 128-thread cached kernel — the
/// one body every cached probe lane launches. A host-side function attribute (percent of
/// the maximum shared memory, rounded by the driver to a supported config), sticky for the
/// process; the SASS is untouched.
pub fn set_cached_128_lb_carveout(percent: u32) -> CudaResult<()> {
    unsafe {
        cudaFuncSetAttribute(
            EvalLsbPairCached128LbFunction::default().as_ptr(),
            CudaFuncAttribute::PreferredSharedMemoryCarveout,
            percent as std::os::raw::c_int,
        )
    }
    .wrap()
}

/// The v3 R3 `t` arm: the control body under `__launch_bounds__(256, 3)`.
pub fn eval_lsb_pair_lb(desc: &UniskipVmDesc, blocks: u32, stream: &CudaStream) -> CudaResult<()> {
    let args = EvalLsbPairLbArguments::new(*desc);
    let config = CudaLaunchConfig::basic(blocks, UNISKIP_THREADS_PER_BLOCK as u32, stream);
    EvalLsbPairLbFunction::default().launch(&config, &args)
}

/// The v3 R3 `w` arm — and `wnone`, which is this kernel with an all-`none` tag stream.
pub fn eval_lsb_pair_win(
    desc: &UniskipVmDesc,
    win: &UniskipWindowDesc,
    blocks: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let args = EvalLsbPairWinArguments::new(*desc, *win);
    let config = CudaLaunchConfig::basic(blocks, UNISKIP_THREADS_PER_BLOCK as u32, stream);
    EvalLsbPairWinFunction::default().launch(&config, &args)
}

/// The v3 R3 `wt` arm: window plus `__launch_bounds__`. The bound was meant as a
/// twiddle-remat trade and measured not to be one — bank-3 loads are byte-identical
/// either way; what it buys is the 82 -> 80 register cut back to 3 blocks/SM.
pub fn eval_lsb_pair_win_lb(
    desc: &UniskipVmDesc,
    win: &UniskipWindowDesc,
    blocks: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let args = EvalLsbPairWinLbArguments::new(*desc, *win);
    let config = CudaLaunchConfig::basic(blocks, UNISKIP_THREADS_PER_BLOCK as u32, stream);
    EvalLsbPairWinLbFunction::default().launch(&config, &args)
}

/// Bytes the fold-first reduction plane occupies at the slab head: one `e4` per warp per
/// cell. Public because a carrier-S launch must SIZE its dynamic slab to cover it.
pub const SEG_FOLD_PLANE_BYTES: u32 = (UNISKIP_SEG_K * UNISKIP_CELLS * 4 * size_of::<u32>()) as u32;
/// The accumulator-first plane is wider: four `e4` per thread for the three publishing warps.
pub const SEG_ACC_PLANE_BYTES: u32 = ((UNISKIP_SEG_K - 1) * 32 * 4 * 4 * size_of::<u32>()) as u32;

/// A 128-thread launch whose coset slab is DYNAMIC shared memory: `shared_bytes` is the
/// slab the carrier addresses, and the reduction plane aliases its head — so a launch that
/// does not cover the plane would corrupt shared memory rather than merely lose a slot.
fn seg_config(
    blocks: u32,
    shared_bytes: u32,
    plane_bytes: u32,
    stream: &CudaStream,
) -> CudaLaunchConfig<'_> {
    assert!(
        shared_bytes >= plane_bytes,
        "a seg slab of {shared_bytes} B cannot hold the {plane_bytes} B reduction plane"
    );
    CudaLaunchConfig::builder()
        .grid_dim(blocks)
        .block_dim(UNISKIP_PAIR_THREADS_128 as u32)
        .dynamic_smem_bytes(shared_bytes as usize)
        .stream(stream)
        .build()
}

/// The v3 R7 carrier-S arm at the 64 % carveout request.
pub fn eval_lsb_seg_s_cv64(
    desc: &UniskipVmDesc,
    plan: &UniskipCacheDesc,
    seg: &UniskipSegDesc,
    blocks: u32,
    shared_bytes: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let args = EvalLsbSegSCv64Arguments::new(*desc, *plan, *seg);
    EvalLsbSegSCv64Function::default().launch(
        &seg_config(blocks, shared_bytes, SEG_FOLD_PLANE_BYTES, stream),
        &args,
    )
}

/// [`eval_lsb_seg_s_cv64`]'s clone, carrying the second carveout request.
pub fn eval_lsb_seg_s_cv100(
    desc: &UniskipVmDesc,
    plan: &UniskipCacheDesc,
    seg: &UniskipSegDesc,
    blocks: u32,
    shared_bytes: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let args = EvalLsbSegSCv100Arguments::new(*desc, *plan, *seg);
    EvalLsbSegSCv100Function::default().launch(
        &seg_config(blocks, shared_bytes, SEG_FOLD_PLANE_BYTES, stream),
        &args,
    )
}

/// The accumulator-first reduction diagnostic: warps 1..3 publish their accumulators and
/// warp 0 finishes the reduction alone, pricing the fold-first epilogue's extra shuffles.
pub fn eval_lsb_seg_s_acc(
    desc: &UniskipVmDesc,
    plan: &UniskipCacheDesc,
    seg: &UniskipSegDesc,
    blocks: u32,
    shared_bytes: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let args = EvalLsbSegSAccArguments::new(*desc, *plan, *seg);
    EvalLsbSegSAccFunction::default().launch(
        &seg_config(blocks, shared_bytes, SEG_ACC_PLANE_BYTES, stream),
        &args,
    )
}

/// The v3 R7 carrier-G arm: the slab is a per-block region of `seg.slab_base` device
/// scratch, so the reduction plane is static shared and the launch takes no `shared_bytes`.
/// The caller owns the allocation and fills `slab_base` / `slab_stride_words`.
pub fn eval_lsb_seg_g(
    desc: &UniskipVmDesc,
    plan: &UniskipCacheDesc,
    seg: &UniskipSegDesc,
    blocks: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let args = EvalLsbSegGArguments::new(*desc, *plan, *seg);
    let config = CudaLaunchConfig::basic(blocks, UNISKIP_PAIR_THREADS_128 as u32, stream);
    EvalLsbSegGFunction::default().launch(&config, &args)
}

/// The machinery floor: the cohort loop and the segmented walk with no slab and no
/// prologue, so every reference recomputes. Static shared plane, hence no `shared_bytes`.
pub fn eval_lsb_seg_recompute(
    desc: &UniskipVmDesc,
    seg: &UniskipSegDesc,
    blocks: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let args = EvalLsbSegRecomputeArguments::new(*desc, *seg);
    let config = CudaLaunchConfig::basic(blocks, UNISKIP_PAIR_THREADS_128 as u32, stream);
    EvalLsbSegRecomputeFunction::default().launch(&config, &args)
}

/// Steer the shared-memory carveout of the carrier-S 64 % symbol — a host-side function
/// attribute (percent of the maximum shared memory, rounded by the driver to a supported
/// config), sticky for the process; the SASS is untouched.
pub fn set_seg_s_cv64_carveout(percent: u32) -> CudaResult<()> {
    unsafe {
        cudaFuncSetAttribute(
            EvalLsbSegSCv64Function::default().as_ptr(),
            CudaFuncAttribute::PreferredSharedMemoryCarveout,
            percent as std::os::raw::c_int,
        )
    }
    .wrap()
}

/// [`set_seg_s_cv64_carveout`] for the clone symbol.
pub fn set_seg_s_cv100_carveout(percent: u32) -> CudaResult<()> {
    unsafe {
        cudaFuncSetAttribute(
            EvalLsbSegSCv100Function::default().as_ptr(),
            CudaFuncAttribute::PreferredSharedMemoryCarveout,
            percent as std::os::raw::c_int,
        )
    }
    .wrap()
}

/// [`set_seg_s_cv64_carveout`] for the accumulator-first diagnostic.
pub fn set_seg_s_acc_carveout(percent: u32) -> CudaResult<()> {
    unsafe {
        cudaFuncSetAttribute(
            EvalLsbSegSAccFunction::default().as_ptr(),
            CudaFuncAttribute::PreferredSharedMemoryCarveout,
            percent as std::os::raw::c_int,
        )
    }
    .wrap()
}

/// [`set_seg_s_cv64_carveout`] for the carrier-G arm. Its slab is device memory, so what a
/// smaller shared partition buys here is L1 for the slab's own re-reads.
pub fn set_seg_g_carveout(percent: u32) -> CudaResult<()> {
    unsafe {
        cudaFuncSetAttribute(
            EvalLsbSegGFunction::default().as_ptr(),
            CudaFuncAttribute::PreferredSharedMemoryCarveout,
            percent as std::os::raw::c_int,
        )
    }
    .wrap()
}

/// [`set_seg_s_cv64_carveout`] for the machinery floor.
pub fn set_seg_recompute_carveout(percent: u32) -> CudaResult<()> {
    unsafe {
        cudaFuncSetAttribute(
            EvalLsbSegRecomputeFunction::default().as_ptr(),
            CudaFuncAttribute::PreferredSharedMemoryCarveout,
            percent as std::os::raw::c_int,
        )
    }
    .wrap()
}

/// Reduce the `blocks * UNISKIP_CELLS` partials into the `UNISKIP_CELLS` cells of `q`.
pub fn finalize(
    partials: &DeviceSlice<u32>,
    blocks: u32,
    q: &mut DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let args = FinalizeArguments::new(partials.as_ptr(), blocks, q.as_mut_ptr());
    let config = CudaLaunchConfig::basic(
        UNISKIP_CELLS as u32,
        UNISKIP_THREADS_PER_BLOCK as u32,
        stream,
    );
    FinalizeFunction::default().launch(&config, &args)
}

// NVTX. The cluster's wrapper lives in gpu_core, which is a dev-dependency here,
// so the bench exports the two calls it needs from its own archive (native/uniskip.cu).
#[cfg(not(no_cuda))]
unsafe extern "C" {
    fn ab_gkr_uniskip_nvtx_range_push(name: *const c_char);
    fn ab_gkr_uniskip_nvtx_range_pop();
}

// No Toolkit means no archive to link. NVTX only annotates, and real NVTX is inert
// with no profiler attached, so no-ops are the faithful degradation.
#[cfg(no_cuda)]
unsafe fn ab_gkr_uniskip_nvtx_range_push(_name: *const c_char) {}
#[cfg(no_cuda)]
unsafe fn ab_gkr_uniskip_nvtx_range_pop() {}

/// An open NVTX range, closed on drop. The underlying push/pop stack is
/// thread-local, so ranges nest but must not cross threads.
pub struct NvtxRange(());

impl NvtxRange {
    pub fn new(name: &CStr) -> Self {
        unsafe { ab_gkr_uniskip_nvtx_range_push(name.as_ptr()) };
        Self(())
    }
}

impl Drop for NvtxRange {
    fn drop(&mut self) {
        unsafe { ab_gkr_uniskip_nvtx_range_pop() };
    }
}
