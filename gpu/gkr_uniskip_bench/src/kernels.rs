//! Kernel declarations, `__constant__` symbol uploads and safe launchers.
//!
//! The device tracks a window's backing as `bf *` / `e4 *`; the host tracks it as
//! a `u32` word array (one word per `bf`, four per `e4`), so every pointer that
//! crosses here is a `*mut u32`.

use std::ffi::{c_char, c_void, CStr};

use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::occupancy::max_active_blocks_per_multiprocessor;
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
use crate::coset_cache::LaneKernel;

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
// The v3 R9 gate-first reordered cached bodies: same wire and same signature as the R4
// cached kernels, so the reorder contrast is taken body-to-body at one ABI.
cuda_kernel!(
    EvalLsbPairCachedReorder128Lb,
    ab_gkr_uniskip_eval_lsb_pair_cached_reorder_128_lb_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
cuda_kernel!(
    EvalLsbPairCachedReorder128,
    ab_gkr_uniskip_eval_lsb_pair_cached_reorder_128_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
// The v3 R9b grid: the four corrected grouped-path bodies (`c` = converged accumuland, `cd`
// = the same with the coefficient decode hoisted, `b` = hoisted class branch, `bd` = both)
// at three register budgets each — `_lb` = `(128, 7)`, `_lb6` = `(128, 6)`, bare = unbounded
// — plus the two reference bodies at the relaxed floor. Same wire and signature as every
// other cached kernel, so a grid cell is a body-to-body contrast at one ABI.
cuda_kernel!(
    EvalLsbPairCached128Lb6,
    ab_gkr_uniskip_eval_lsb_pair_cached_128_lb6_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
cuda_kernel!(
    EvalLsbPairCachedReorder128Lb6,
    ab_gkr_uniskip_eval_lsb_pair_cached_reorder_128_lb6_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
cuda_kernel!(
    EvalLsbPairCachedReorderC128Lb,
    ab_gkr_uniskip_eval_lsb_pair_cached_reorder_c_128_lb_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
cuda_kernel!(
    EvalLsbPairCachedReorderC128Lb6,
    ab_gkr_uniskip_eval_lsb_pair_cached_reorder_c_128_lb6_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
cuda_kernel!(
    EvalLsbPairCachedReorderC128,
    ab_gkr_uniskip_eval_lsb_pair_cached_reorder_c_128_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
cuda_kernel!(
    EvalLsbPairCachedReorderCk128Lb,
    ab_gkr_uniskip_eval_lsb_pair_cached_reorder_ck_128_lb_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
cuda_kernel!(
    EvalLsbPairCachedReorderCk128Lb6,
    ab_gkr_uniskip_eval_lsb_pair_cached_reorder_ck_128_lb6_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
cuda_kernel!(
    EvalLsbPairCachedReorderCk128,
    ab_gkr_uniskip_eval_lsb_pair_cached_reorder_ck_128_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
cuda_kernel!(
    EvalLsbPairCachedReorderCd128Lb,
    ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_128_lb_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
cuda_kernel!(
    EvalLsbPairCachedReorderCd128Lb6,
    ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_128_lb6_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
cuda_kernel!(
    EvalLsbPairCachedReorderCd128,
    ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_128_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
cuda_kernel!(
    EvalLsbPairCachedReorderB128Lb,
    ab_gkr_uniskip_eval_lsb_pair_cached_reorder_b_128_lb_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
cuda_kernel!(
    EvalLsbPairCachedReorderB128Lb6,
    ab_gkr_uniskip_eval_lsb_pair_cached_reorder_b_128_lb6_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
cuda_kernel!(
    EvalLsbPairCachedReorderB128,
    ab_gkr_uniskip_eval_lsb_pair_cached_reorder_b_128_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
cuda_kernel!(
    EvalLsbPairCachedReorderBk128Lb,
    ab_gkr_uniskip_eval_lsb_pair_cached_reorder_bk_128_lb_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
cuda_kernel!(
    EvalLsbPairCachedReorderBk128Lb6,
    ab_gkr_uniskip_eval_lsb_pair_cached_reorder_bk_128_lb6_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
cuda_kernel!(
    EvalLsbPairCachedReorderBk128,
    ab_gkr_uniskip_eval_lsb_pair_cached_reorder_bk_128_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
cuda_kernel!(
    EvalLsbPairCachedReorderBd128Lb,
    ab_gkr_uniskip_eval_lsb_pair_cached_reorder_bd_128_lb_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
cuda_kernel!(
    EvalLsbPairCachedReorderBd128Lb6,
    ab_gkr_uniskip_eval_lsb_pair_cached_reorder_bd_128_lb6_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
cuda_kernel!(
    EvalLsbPairCachedReorderBd128,
    ab_gkr_uniskip_eval_lsb_pair_cached_reorder_bd_128_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
// The v3 R10 lazy BF accumulator grid: the grouped-path member sums held wide — `w96` = u64 plus
// a carry word, `a64` = u64 under a conditional-subtract invariant — over both parent walks (no
// parent tag = the incumbent, `reorder_cd` = R9b's `C+D`) at the same three register budgets. Same
// wire and signature as every other cached kernel.
cuda_kernel!(
    EvalLsbPairCachedW96128Lb,
    ab_gkr_uniskip_eval_lsb_pair_cached_w96_128_lb_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
cuda_kernel!(
    EvalLsbPairCachedW96128Lb6,
    ab_gkr_uniskip_eval_lsb_pair_cached_w96_128_lb6_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
cuda_kernel!(
    EvalLsbPairCachedW96128,
    ab_gkr_uniskip_eval_lsb_pair_cached_w96_128_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
cuda_kernel!(
    EvalLsbPairCachedA64128Lb,
    ab_gkr_uniskip_eval_lsb_pair_cached_a64_128_lb_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
cuda_kernel!(
    EvalLsbPairCachedA64128Lb6,
    ab_gkr_uniskip_eval_lsb_pair_cached_a64_128_lb6_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
cuda_kernel!(
    EvalLsbPairCachedA64128,
    ab_gkr_uniskip_eval_lsb_pair_cached_a64_128_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
cuda_kernel!(
    EvalLsbPairCachedReorderCdW96128Lb,
    ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_w96_128_lb_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
cuda_kernel!(
    EvalLsbPairCachedReorderCdW96128Lb6,
    ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_w96_128_lb6_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
cuda_kernel!(
    EvalLsbPairCachedReorderCdW96128,
    ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_w96_128_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
cuda_kernel!(
    EvalLsbPairCachedReorderCdA64128Lb,
    ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_a64_128_lb_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
cuda_kernel!(
    EvalLsbPairCachedReorderCdA64128Lb6,
    ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_a64_128_lb6_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
);
cuda_kernel!(
    EvalLsbPairCachedReorderCdA64128,
    ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_a64_128_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc
    )
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
// v3 R7b transplant kernels: one cohort of four rows per block, per-warp output, no shared
// memory — so neither symbol takes `shared_bytes` and the grid is `rows / 4`.
cuda_kernel!(
    EvalLsbSegbG,
    ab_gkr_uniskip_eval_lsb_segb_g_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc,
        seg: UniskipSegDesc
    )
);
cuda_kernel!(
    EvalLsbSegbRecompute,
    ab_gkr_uniskip_eval_lsb_segb_recompute_kernel(desc: UniskipVmDesc, seg: UniskipSegDesc)
);
// The slotted-slab variant. `mask` is a SEPARATE fourth parameter: growing `UniskipSegDesc`
// would shift every seg kernel's parameter block and move the pinned digests.
cuda_kernel!(
    EvalLsbSegbGSlotted,
    ab_gkr_uniskip_eval_lsb_segb_g_slotted_kernel(
        desc: UniskipVmDesc,
        plan: UniskipCacheDesc,
        seg: UniskipSegDesc,
        mask: *mut u32
    )
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

/// The v3 R9 gate-first reordered cached kernel at 128 threads under
/// `__launch_bounds__(128, 7)` — the incumbent's bound, so the reorder contrast is taken at
/// one block count.
pub fn eval_lsb_pair_cached_reorder_128_lb(
    desc: &UniskipVmDesc,
    plan: &UniskipCacheDesc,
    blocks: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let args = EvalLsbPairCachedReorder128LbArguments::new(*desc, *plan);
    let config = CudaLaunchConfig::basic(blocks, UNISKIP_PAIR_THREADS_128 as u32, stream);
    EvalLsbPairCachedReorder128LbFunction::default().launch(&config, &args)
}

/// The UNBOUNDED R9 sibling: the register-attribution comparator against the unbounded
/// cached body, and what prices the bound on the reordered walk.
pub fn eval_lsb_pair_cached_reorder_128(
    desc: &UniskipVmDesc,
    plan: &UniskipCacheDesc,
    blocks: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let args = EvalLsbPairCachedReorder128Arguments::new(*desc, *plan);
    let config = CudaLaunchConfig::basic(blocks, UNISKIP_PAIR_THREADS_128 as u32, stream);
    EvalLsbPairCachedReorder128Function::default().launch(&config, &args)
}

/// One launcher per v3 R9b grid cell. Every cell takes the incumbent's `(desc, plan)` ABI at
/// 128 threads and differs only in which body and which register budget the symbol carries, so
/// the launchers are identical up to their three names; the cell is named at the call rather
/// than in fourteen copies of the same four lines.
macro_rules! regroup_launcher {
    ($launcher:ident, $arguments:ident, $function:ident) => {
        pub fn $launcher(
            desc: &UniskipVmDesc,
            plan: &UniskipCacheDesc,
            blocks: u32,
            stream: &CudaStream,
        ) -> CudaResult<()> {
            let args = $arguments::new(*desc, *plan);
            let config = CudaLaunchConfig::basic(blocks, UNISKIP_PAIR_THREADS_128 as u32, stream);
            $function::default().launch(&config, &args)
        }
    };
}

regroup_launcher!(
    eval_lsb_pair_cached_128_lb6,
    EvalLsbPairCached128Lb6Arguments,
    EvalLsbPairCached128Lb6Function
);
regroup_launcher!(
    eval_lsb_pair_cached_reorder_128_lb6,
    EvalLsbPairCachedReorder128Lb6Arguments,
    EvalLsbPairCachedReorder128Lb6Function
);
regroup_launcher!(
    eval_lsb_pair_cached_reorder_c_128_lb,
    EvalLsbPairCachedReorderC128LbArguments,
    EvalLsbPairCachedReorderC128LbFunction
);
regroup_launcher!(
    eval_lsb_pair_cached_reorder_c_128_lb6,
    EvalLsbPairCachedReorderC128Lb6Arguments,
    EvalLsbPairCachedReorderC128Lb6Function
);
regroup_launcher!(
    eval_lsb_pair_cached_reorder_c_128,
    EvalLsbPairCachedReorderC128Arguments,
    EvalLsbPairCachedReorderC128Function
);
regroup_launcher!(
    eval_lsb_pair_cached_reorder_ck_128_lb,
    EvalLsbPairCachedReorderCk128LbArguments,
    EvalLsbPairCachedReorderCk128LbFunction
);
regroup_launcher!(
    eval_lsb_pair_cached_reorder_ck_128_lb6,
    EvalLsbPairCachedReorderCk128Lb6Arguments,
    EvalLsbPairCachedReorderCk128Lb6Function
);
regroup_launcher!(
    eval_lsb_pair_cached_reorder_ck_128,
    EvalLsbPairCachedReorderCk128Arguments,
    EvalLsbPairCachedReorderCk128Function
);
regroup_launcher!(
    eval_lsb_pair_cached_reorder_cd_128_lb,
    EvalLsbPairCachedReorderCd128LbArguments,
    EvalLsbPairCachedReorderCd128LbFunction
);
regroup_launcher!(
    eval_lsb_pair_cached_reorder_cd_128_lb6,
    EvalLsbPairCachedReorderCd128Lb6Arguments,
    EvalLsbPairCachedReorderCd128Lb6Function
);
regroup_launcher!(
    eval_lsb_pair_cached_reorder_cd_128,
    EvalLsbPairCachedReorderCd128Arguments,
    EvalLsbPairCachedReorderCd128Function
);
regroup_launcher!(
    eval_lsb_pair_cached_reorder_b_128_lb,
    EvalLsbPairCachedReorderB128LbArguments,
    EvalLsbPairCachedReorderB128LbFunction
);
regroup_launcher!(
    eval_lsb_pair_cached_reorder_b_128_lb6,
    EvalLsbPairCachedReorderB128Lb6Arguments,
    EvalLsbPairCachedReorderB128Lb6Function
);
regroup_launcher!(
    eval_lsb_pair_cached_reorder_b_128,
    EvalLsbPairCachedReorderB128Arguments,
    EvalLsbPairCachedReorderB128Function
);
regroup_launcher!(
    eval_lsb_pair_cached_reorder_bk_128_lb,
    EvalLsbPairCachedReorderBk128LbArguments,
    EvalLsbPairCachedReorderBk128LbFunction
);
regroup_launcher!(
    eval_lsb_pair_cached_reorder_bk_128_lb6,
    EvalLsbPairCachedReorderBk128Lb6Arguments,
    EvalLsbPairCachedReorderBk128Lb6Function
);
regroup_launcher!(
    eval_lsb_pair_cached_reorder_bk_128,
    EvalLsbPairCachedReorderBk128Arguments,
    EvalLsbPairCachedReorderBk128Function
);
regroup_launcher!(
    eval_lsb_pair_cached_reorder_bd_128_lb,
    EvalLsbPairCachedReorderBd128LbArguments,
    EvalLsbPairCachedReorderBd128LbFunction
);
regroup_launcher!(
    eval_lsb_pair_cached_reorder_bd_128_lb6,
    EvalLsbPairCachedReorderBd128Lb6Arguments,
    EvalLsbPairCachedReorderBd128Lb6Function
);
regroup_launcher!(
    eval_lsb_pair_cached_reorder_bd_128,
    EvalLsbPairCachedReorderBd128Arguments,
    EvalLsbPairCachedReorderBd128Function
);
regroup_launcher!(
    eval_lsb_pair_cached_w96_128_lb,
    EvalLsbPairCachedW96128LbArguments,
    EvalLsbPairCachedW96128LbFunction
);
regroup_launcher!(
    eval_lsb_pair_cached_w96_128_lb6,
    EvalLsbPairCachedW96128Lb6Arguments,
    EvalLsbPairCachedW96128Lb6Function
);
regroup_launcher!(
    eval_lsb_pair_cached_w96_128,
    EvalLsbPairCachedW96128Arguments,
    EvalLsbPairCachedW96128Function
);
regroup_launcher!(
    eval_lsb_pair_cached_a64_128_lb,
    EvalLsbPairCachedA64128LbArguments,
    EvalLsbPairCachedA64128LbFunction
);
regroup_launcher!(
    eval_lsb_pair_cached_a64_128_lb6,
    EvalLsbPairCachedA64128Lb6Arguments,
    EvalLsbPairCachedA64128Lb6Function
);
regroup_launcher!(
    eval_lsb_pair_cached_a64_128,
    EvalLsbPairCachedA64128Arguments,
    EvalLsbPairCachedA64128Function
);
regroup_launcher!(
    eval_lsb_pair_cached_reorder_cd_w96_128_lb,
    EvalLsbPairCachedReorderCdW96128LbArguments,
    EvalLsbPairCachedReorderCdW96128LbFunction
);
regroup_launcher!(
    eval_lsb_pair_cached_reorder_cd_w96_128_lb6,
    EvalLsbPairCachedReorderCdW96128Lb6Arguments,
    EvalLsbPairCachedReorderCdW96128Lb6Function
);
regroup_launcher!(
    eval_lsb_pair_cached_reorder_cd_w96_128,
    EvalLsbPairCachedReorderCdW96128Arguments,
    EvalLsbPairCachedReorderCdW96128Function
);
regroup_launcher!(
    eval_lsb_pair_cached_reorder_cd_a64_128_lb,
    EvalLsbPairCachedReorderCdA64128LbArguments,
    EvalLsbPairCachedReorderCdA64128LbFunction
);
regroup_launcher!(
    eval_lsb_pair_cached_reorder_cd_a64_128_lb6,
    EvalLsbPairCachedReorderCdA64128Lb6Arguments,
    EvalLsbPairCachedReorderCdA64128Lb6Function
);
regroup_launcher!(
    eval_lsb_pair_cached_reorder_cd_a64_128,
    EvalLsbPairCachedReorderCdA64128Arguments,
    EvalLsbPairCachedReorderCdA64128Function
);

/// Blocks per SM the driver's own occupancy calculator gives one of the lane kernels at
/// `block_threads` and `dynamic_smem_bytes`. It reads the SAME function attributes a launch
/// will — the register count, the static shared plane and whatever
/// `PreferredSharedMemoryCarveout` was last set — so it is the in-binary answer to "how many
/// blocks will actually be resident", and must be asked AFTER the carveout is applied.
///
/// One function over [`LaneKernel`] rather than one per symbol: the enum is already the
/// single source of truth for which body a lane launches, and a per-symbol family would let
/// a lane be gated against a kernel it does not run.
pub fn max_blocks_per_sm(
    kernel: LaneKernel,
    block_threads: u32,
    dynamic_smem_bytes: u32,
) -> CudaResult<i32> {
    let threads = block_threads as i32;
    let dynamic = dynamic_smem_bytes as usize;
    match kernel {
        LaneKernel::Pair => occupancy(&EvalLsbPairFunction::default(), threads, dynamic),
        LaneKernel::Pair128 => occupancy(&EvalLsbPair128Function::default(), threads, dynamic),
        LaneKernel::Pair128Lb => occupancy(&EvalLsbPair128LbFunction::default(), threads, dynamic),
        LaneKernel::Cached => occupancy(&EvalLsbPairCachedFunction::default(), threads, dynamic),
        LaneKernel::Cached128 => {
            occupancy(&EvalLsbPairCached128Function::default(), threads, dynamic)
        }
        LaneKernel::Cached128Lb => {
            occupancy(&EvalLsbPairCached128LbFunction::default(), threads, dynamic)
        }
        LaneKernel::Reorder128Lb => occupancy(
            &EvalLsbPairCachedReorder128LbFunction::default(),
            threads,
            dynamic,
        ),
        LaneKernel::Reorder128 => occupancy(
            &EvalLsbPairCachedReorder128Function::default(),
            threads,
            dynamic,
        ),
        LaneKernel::Cached128Lb6 => occupancy(
            &EvalLsbPairCached128Lb6Function::default(),
            threads,
            dynamic,
        ),
        LaneKernel::Reorder128Lb6 => occupancy(
            &EvalLsbPairCachedReorder128Lb6Function::default(),
            threads,
            dynamic,
        ),
        LaneKernel::ReorderC128 => occupancy(
            &EvalLsbPairCachedReorderC128Function::default(),
            threads,
            dynamic,
        ),
        LaneKernel::ReorderC128Lb => occupancy(
            &EvalLsbPairCachedReorderC128LbFunction::default(),
            threads,
            dynamic,
        ),
        LaneKernel::ReorderC128Lb6 => occupancy(
            &EvalLsbPairCachedReorderC128Lb6Function::default(),
            threads,
            dynamic,
        ),
        LaneKernel::ReorderCk128 => occupancy(
            &EvalLsbPairCachedReorderCk128Function::default(),
            threads,
            dynamic,
        ),
        LaneKernel::ReorderCk128Lb => occupancy(
            &EvalLsbPairCachedReorderCk128LbFunction::default(),
            threads,
            dynamic,
        ),
        LaneKernel::ReorderCk128Lb6 => occupancy(
            &EvalLsbPairCachedReorderCk128Lb6Function::default(),
            threads,
            dynamic,
        ),
        LaneKernel::ReorderCd128 => occupancy(
            &EvalLsbPairCachedReorderCd128Function::default(),
            threads,
            dynamic,
        ),
        LaneKernel::ReorderCd128Lb => occupancy(
            &EvalLsbPairCachedReorderCd128LbFunction::default(),
            threads,
            dynamic,
        ),
        LaneKernel::ReorderCd128Lb6 => occupancy(
            &EvalLsbPairCachedReorderCd128Lb6Function::default(),
            threads,
            dynamic,
        ),
        LaneKernel::ReorderB128 => occupancy(
            &EvalLsbPairCachedReorderB128Function::default(),
            threads,
            dynamic,
        ),
        LaneKernel::ReorderB128Lb => occupancy(
            &EvalLsbPairCachedReorderB128LbFunction::default(),
            threads,
            dynamic,
        ),
        LaneKernel::ReorderB128Lb6 => occupancy(
            &EvalLsbPairCachedReorderB128Lb6Function::default(),
            threads,
            dynamic,
        ),
        LaneKernel::ReorderBk128 => occupancy(
            &EvalLsbPairCachedReorderBk128Function::default(),
            threads,
            dynamic,
        ),
        LaneKernel::ReorderBk128Lb => occupancy(
            &EvalLsbPairCachedReorderBk128LbFunction::default(),
            threads,
            dynamic,
        ),
        LaneKernel::ReorderBk128Lb6 => occupancy(
            &EvalLsbPairCachedReorderBk128Lb6Function::default(),
            threads,
            dynamic,
        ),
        LaneKernel::ReorderBd128 => occupancy(
            &EvalLsbPairCachedReorderBd128Function::default(),
            threads,
            dynamic,
        ),
        LaneKernel::ReorderBd128Lb => occupancy(
            &EvalLsbPairCachedReorderBd128LbFunction::default(),
            threads,
            dynamic,
        ),
        LaneKernel::ReorderBd128Lb6 => occupancy(
            &EvalLsbPairCachedReorderBd128Lb6Function::default(),
            threads,
            dynamic,
        ),
        LaneKernel::CachedW96128 => occupancy(
            &EvalLsbPairCachedW96128Function::default(),
            threads,
            dynamic,
        ),
        LaneKernel::CachedW96128Lb => occupancy(
            &EvalLsbPairCachedW96128LbFunction::default(),
            threads,
            dynamic,
        ),
        LaneKernel::CachedW96128Lb6 => occupancy(
            &EvalLsbPairCachedW96128Lb6Function::default(),
            threads,
            dynamic,
        ),
        LaneKernel::CachedA64128 => occupancy(
            &EvalLsbPairCachedA64128Function::default(),
            threads,
            dynamic,
        ),
        LaneKernel::CachedA64128Lb => occupancy(
            &EvalLsbPairCachedA64128LbFunction::default(),
            threads,
            dynamic,
        ),
        LaneKernel::CachedA64128Lb6 => occupancy(
            &EvalLsbPairCachedA64128Lb6Function::default(),
            threads,
            dynamic,
        ),
        LaneKernel::ReorderCdW96128 => occupancy(
            &EvalLsbPairCachedReorderCdW96128Function::default(),
            threads,
            dynamic,
        ),
        LaneKernel::ReorderCdW96128Lb => occupancy(
            &EvalLsbPairCachedReorderCdW96128LbFunction::default(),
            threads,
            dynamic,
        ),
        LaneKernel::ReorderCdW96128Lb6 => occupancy(
            &EvalLsbPairCachedReorderCdW96128Lb6Function::default(),
            threads,
            dynamic,
        ),
        LaneKernel::ReorderCdA64128 => occupancy(
            &EvalLsbPairCachedReorderCdA64128Function::default(),
            threads,
            dynamic,
        ),
        LaneKernel::ReorderCdA64128Lb => occupancy(
            &EvalLsbPairCachedReorderCdA64128LbFunction::default(),
            threads,
            dynamic,
        ),
        LaneKernel::ReorderCdA64128Lb6 => occupancy(
            &EvalLsbPairCachedReorderCdA64128Lb6Function::default(),
            threads,
            dynamic,
        ),
        LaneKernel::SegSCv64 => occupancy(&EvalLsbSegSCv64Function::default(), threads, dynamic),
        LaneKernel::SegSCv100 => occupancy(&EvalLsbSegSCv100Function::default(), threads, dynamic),
        LaneKernel::SegSAcc => occupancy(&EvalLsbSegSAccFunction::default(), threads, dynamic),
        LaneKernel::SegG => occupancy(&EvalLsbSegGFunction::default(), threads, dynamic),
        LaneKernel::SegRecompute => {
            occupancy(&EvalLsbSegRecomputeFunction::default(), threads, dynamic)
        }
        LaneKernel::SegbG => occupancy(&EvalLsbSegbGFunction::default(), threads, dynamic),
        LaneKernel::SegbRecompute => {
            occupancy(&EvalLsbSegbRecomputeFunction::default(), threads, dynamic)
        }
        LaneKernel::SegbGSlotted => {
            occupancy(&EvalLsbSegbGSlottedFunction::default(), threads, dynamic)
        }
    }
}

fn occupancy(
    function: &impl KernelFunction,
    block_threads: i32,
    dynamic_smem_bytes: usize,
) -> CudaResult<i32> {
    max_active_blocks_per_multiprocessor(function, block_threads, dynamic_smem_bytes)
}

/// v3 R6/R9/R9b: steer the shared-memory carveout of one LOCAL cached body. A host-side
/// function attribute (percent of the maximum shared memory, rounded by the driver to a
/// supported config), sticky for the process; the SASS is untouched.
///
/// The attribute is per FUNCTION, so every symbol a process launches needs its own call or a
/// body contrast spans two L1 configurations. One function over [`LaneKernel`] rather than one
/// per symbol, for [`max_blocks_per_sm`]'s reason: the enum is already the single source of
/// truth for which body a lane launches, and the match is exhaustive, so a new variant fails
/// to compile until it is classed as steerable or not.
pub fn set_local_carveout(kernel: LaneKernel, percent: u32) -> CudaResult<()> {
    match kernel {
        LaneKernel::Cached128Lb => carveout(&EvalLsbPairCached128LbFunction::default(), percent),
        LaneKernel::Cached128Lb6 => carveout(&EvalLsbPairCached128Lb6Function::default(), percent),
        LaneKernel::Cached128 => carveout(&EvalLsbPairCached128Function::default(), percent),
        LaneKernel::Reorder128Lb => {
            carveout(&EvalLsbPairCachedReorder128LbFunction::default(), percent)
        }
        LaneKernel::Reorder128Lb6 => {
            carveout(&EvalLsbPairCachedReorder128Lb6Function::default(), percent)
        }
        LaneKernel::Reorder128 => {
            carveout(&EvalLsbPairCachedReorder128Function::default(), percent)
        }
        LaneKernel::ReorderC128Lb => {
            carveout(&EvalLsbPairCachedReorderC128LbFunction::default(), percent)
        }
        LaneKernel::ReorderC128Lb6 => {
            carveout(&EvalLsbPairCachedReorderC128Lb6Function::default(), percent)
        }
        LaneKernel::ReorderC128 => {
            carveout(&EvalLsbPairCachedReorderC128Function::default(), percent)
        }
        LaneKernel::ReorderCk128Lb => {
            carveout(&EvalLsbPairCachedReorderCk128LbFunction::default(), percent)
        }
        LaneKernel::ReorderCk128Lb6 => carveout(
            &EvalLsbPairCachedReorderCk128Lb6Function::default(),
            percent,
        ),
        LaneKernel::ReorderCk128 => {
            carveout(&EvalLsbPairCachedReorderCk128Function::default(), percent)
        }
        LaneKernel::ReorderCd128Lb => {
            carveout(&EvalLsbPairCachedReorderCd128LbFunction::default(), percent)
        }
        LaneKernel::ReorderCd128Lb6 => carveout(
            &EvalLsbPairCachedReorderCd128Lb6Function::default(),
            percent,
        ),
        LaneKernel::ReorderCd128 => {
            carveout(&EvalLsbPairCachedReorderCd128Function::default(), percent)
        }
        LaneKernel::ReorderB128Lb => {
            carveout(&EvalLsbPairCachedReorderB128LbFunction::default(), percent)
        }
        LaneKernel::ReorderB128Lb6 => {
            carveout(&EvalLsbPairCachedReorderB128Lb6Function::default(), percent)
        }
        LaneKernel::ReorderB128 => {
            carveout(&EvalLsbPairCachedReorderB128Function::default(), percent)
        }
        LaneKernel::ReorderBk128Lb => {
            carveout(&EvalLsbPairCachedReorderBk128LbFunction::default(), percent)
        }
        LaneKernel::ReorderBk128Lb6 => carveout(
            &EvalLsbPairCachedReorderBk128Lb6Function::default(),
            percent,
        ),
        LaneKernel::ReorderBk128 => {
            carveout(&EvalLsbPairCachedReorderBk128Function::default(), percent)
        }
        LaneKernel::ReorderBd128Lb => {
            carveout(&EvalLsbPairCachedReorderBd128LbFunction::default(), percent)
        }
        LaneKernel::ReorderBd128Lb6 => carveout(
            &EvalLsbPairCachedReorderBd128Lb6Function::default(),
            percent,
        ),
        LaneKernel::ReorderBd128 => {
            carveout(&EvalLsbPairCachedReorderBd128Function::default(), percent)
        }
        // The v3 R10 grid is deliberately NOT steerable yet: the hint seam is one list with
        // [`LaneKernel::HINTED`], and extending it is the lane task's, so a run that reaches a
        // lazy-accumulator cell before then fails loudly instead of timing it at the driver's own
        // L1 sizing beside a hinted incumbent.
        LaneKernel::Pair
        | LaneKernel::Pair128
        | LaneKernel::Pair128Lb
        | LaneKernel::Cached
        | LaneKernel::CachedW96128
        | LaneKernel::CachedW96128Lb
        | LaneKernel::CachedW96128Lb6
        | LaneKernel::CachedA64128
        | LaneKernel::CachedA64128Lb
        | LaneKernel::CachedA64128Lb6
        | LaneKernel::ReorderCdW96128
        | LaneKernel::ReorderCdW96128Lb
        | LaneKernel::ReorderCdW96128Lb6
        | LaneKernel::ReorderCdA64128
        | LaneKernel::ReorderCdA64128Lb
        | LaneKernel::ReorderCdA64128Lb6
        | LaneKernel::SegSCv64
        | LaneKernel::SegSCv100
        | LaneKernel::SegSAcc
        | LaneKernel::SegG
        | LaneKernel::SegRecompute
        | LaneKernel::SegbG
        | LaneKernel::SegbRecompute
        | LaneKernel::SegbGSlotted => panic!(
            "{} is not a hinted local symbol — LaneKernel::HINTED and this dispatch are one \
             list",
            kernel.name()
        ),
    }
}

fn carveout(function: &impl KernelFunction, percent: u32) -> CudaResult<()> {
    unsafe {
        cudaFuncSetAttribute(
            function.as_ptr(),
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

/// The v3 R7b transplant arm: `blocks` covers four rows each, and every warp writes its own
/// partial slot, so the caller sizes partials at `blocks * UNISKIP_SEG_K` slots.
pub fn eval_lsb_segb_g(
    desc: &UniskipVmDesc,
    plan: &UniskipCacheDesc,
    seg: &UniskipSegDesc,
    blocks: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let args = EvalLsbSegbGArguments::new(*desc, *plan, *seg);
    let config = CudaLaunchConfig::basic(blocks, UNISKIP_PAIR_THREADS_128 as u32, stream);
    EvalLsbSegbGFunction::default().launch(&config, &args)
}

/// Slots per SM id, and the SM-id capacity the slotted body traps above — the raw `%smid`
/// space is sparse, so this bounds the index rather than counting SMs. The mask is
/// [`UNISKIP_SLOT_SM_CAPACITY`] words, zeroed before the launch; the pool is
/// `UNISKIP_SLOT_SM_CAPACITY * UNISKIP_SLOTS_PER_SM` slab regions.
pub const UNISKIP_SLOT_SM_CAPACITY: u32 = 1024;
pub const UNISKIP_SLOTS_PER_SM: u32 = 16;

/// [`eval_lsb_segb_g`] with the slab region claimed from `mask` per RESIDENT block, so the
/// pool is sized by the machine's residency instead of the grid.
pub fn eval_lsb_segb_g_slotted(
    desc: &UniskipVmDesc,
    plan: &UniskipCacheDesc,
    seg: &UniskipSegDesc,
    mask: &mut DeviceSlice<u32>,
    blocks: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(
        mask.len(),
        UNISKIP_SLOT_SM_CAPACITY as usize,
        "the slot mask is one word per SM id"
    );
    let args = EvalLsbSegbGSlottedArguments::new(*desc, *plan, *seg, mask.as_mut_ptr());
    let config = CudaLaunchConfig::basic(blocks, UNISKIP_PAIR_THREADS_128 as u32, stream);
    EvalLsbSegbGSlottedFunction::default().launch(&config, &args)
}

/// [`eval_lsb_segb_g`]'s machinery floor: no slab and no prologue, so every reference
/// recomputes.
pub fn eval_lsb_segb_recompute(
    desc: &UniskipVmDesc,
    seg: &UniskipSegDesc,
    blocks: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let args = EvalLsbSegbRecomputeArguments::new(*desc, *seg);
    let config = CudaLaunchConfig::basic(blocks, UNISKIP_PAIR_THREADS_128 as u32, stream);
    EvalLsbSegbRecomputeFunction::default().launch(&config, &args)
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

/// [`set_seg_s_cv64_carveout`] for the transplant arm. Its body allocates no shared memory
/// at all, so what a carveout request steers here is L1 alone.
pub fn set_segb_g_carveout(percent: u32) -> CudaResult<()> {
    unsafe {
        cudaFuncSetAttribute(
            EvalLsbSegbGFunction::default().as_ptr(),
            CudaFuncAttribute::PreferredSharedMemoryCarveout,
            percent as std::os::raw::c_int,
        )
    }
    .wrap()
}

/// [`set_segb_g_carveout`] for the slotted-slab variant.
pub fn set_segb_g_slotted_carveout(percent: u32) -> CudaResult<()> {
    unsafe {
        cudaFuncSetAttribute(
            EvalLsbSegbGSlottedFunction::default().as_ptr(),
            CudaFuncAttribute::PreferredSharedMemoryCarveout,
            percent as std::os::raw::c_int,
        )
    }
    .wrap()
}

/// [`set_segb_g_carveout`] for the transplant machinery floor.
pub fn set_segb_recompute_carveout(percent: u32) -> CudaResult<()> {
    unsafe {
        cudaFuncSetAttribute(
            EvalLsbSegbRecomputeFunction::default().as_ptr(),
            CudaFuncAttribute::PreferredSharedMemoryCarveout,
            percent as std::os::raw::c_int,
        )
    }
    .wrap()
}

/// Reduce the `partial_slots * UNISKIP_CELLS` partials into the `UNISKIP_CELLS` cells of `q`.
/// Slots, not blocks: a transplant carrier publishes one per warp.
pub fn finalize(
    partials: &DeviceSlice<u32>,
    partial_slots: u32,
    q: &mut DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let args = FinalizeArguments::new(partials.as_ptr(), partial_slots, q.as_mut_ptr());
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
