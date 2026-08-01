//! Launchers for the SEGMENTED lean VM (segmented-lean-VM design §3, §5, §6).
//!
//! The CUDA half is `native/prover/gkr/backward/segmented_vm.{cuh,cu}`. The
//! launch geometry is §3's, and it is the whole reason this module was built as a
//! separate lineage rather than a variant of the retired cell-era launcher:
//!
//!   * a block is `k` warps by 32 lanes, a LANE is a row of the block's 32-row
//!     tile, and the grid covers `logical_rows / 32` tiles — so `block_dim` is a
//!     descriptor-derived `32 * desc.k` rather than a constant, and `grid_dim`
//!     counts TILES rather than row-blocks;
//!   * dynamic shared memory is the epilogue's plane pair and nothing else (there
//!     is no cell file), so it is a function of the epilogue variant and `k`
//!     ([`bwd_seg_epilogue_smem_bytes`]);
//!   * the coefficient bank is this lineage's OWN `__constant__` symbol
//!     ([`bwd_seg_coeff_bank_device_ptr`]), never `ab_gkr_flat_coefficients`.
//!
//! Everything a launch needs beyond the by-value descriptor is out of band and is
//! the CALLER's to stage before the launch, on the same stream:
//!
//!   1. the reserved-inclusive coefficient payload ([`BwdSegSetup::coefficients`])
//!      → the `__constant__` bank under [`CoeffMode::Constant`], or a device
//!      buffer whose pointer the caller patches into its host copy of the
//!      descriptor under [`CoeffMode::DevPtr`];
//!   2. the claim point ([`BwdSegSetup::claim_point`]) →
//!      [`bwd_seg_claim_point_device_ptr`], the ONE authority on fold challenges;
//!   3. in [`ProgramMode::DevPtr`], the reordered stream
//!      ([`BwdSegSetup::program_words`]) → a device buffer whose pointer the
//!      caller patches into the descriptor;
//!   4. in a CONTINUATION round (round ≥ 1), that round's fold weights →
//!      [`launch_bwd_seg_build_fold_weights`], enqueued AFTER the claim point and
//!      BEFORE the round's segment launches; R0 folds nothing and must NOT call
//!      it. Skipping it is UNDETECTABLE at runtime: a stale or zeroed bank makes
//!      every fold collapse to its `leaf0`, and a release kernel carries no error
//!      channel, no assert, and no validation to say so.
//!
//! Every EXECUTOR launch here stages nothing, allocates nothing, and reads no
//! device memory, so it adds no obligations to the GPU scheduling contract beyond
//! "everything above is enqueued on `exec_stream` before the launch".
//!
//! One launch here is not an executor: [`launch_bwd_seg_build_fold_weights`] is
//! the per-round fold-weight prelude, which still stages and allocates nothing
//! but WRITES the [`bwd_seg_fold_weights_device_ptr`] `__constant__` bank through
//! that symbol's own address. So the bank is round-mutable shared state, exactly
//! like the claim point: `exec_stream` order is what makes a round's weights
//! visible to the segment launches behind it, but what keeps two proofs from
//! interleaving their rounds into the one bank is the proof-level serialization
//! invariant the claim point and the coefficient bank already rely on (flat-fold
//! design §4.2) — the scheduling contract governs stream ordering, not
//! orchestration concurrency.
//!
//! The shared-memory carveout PREFERENCE ([`CarveoutPlan`]) is per-function process
//! state of exactly that class. It is not stream-ordered at all: it is a property of
//! the entry point, read by the driver when a launch is configured, so two proofs
//! interleaving their rounds would interleave their preferences too. What makes it
//! safe is the same proof-level serialization invariant the claim point and the
//! fold-weight bank already require, and nothing weaker — the preference is set by
//! the measurement caller, BEFORE staging, on the same scheduling thread that writes
//! those banks, and restored to the exact prior value when the cell's plan drops. So
//! no new invariant is introduced and the scheduling contract gains no obligation.
//!
//! PRODUCTION WIRING IS OUT OF SCOPE. At `9bf7a80e` this whole family is bench-only:
//! the parity ladder and [`super::seg_report`] are its only callers, so there is no
//! production launch site to hang a `configure_kernel_attributes` hook on the way
//! `flat::kernel_setup::configure_flat_kernel_cache_preference` hangs off the flat
//! lineage's. Whoever cuts this lineage over owes that hook, and the obligation joins
//! the cutover list beside "the fold-weight prelude has no production caller" and
//! audit I-18's `SchedulerHostAllocator` obligation.

// The `seg_gpu_tests` parity ladder and the `seg_report` bench harness are the callers.
#![allow(dead_code)]

use std::mem::size_of;

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use era_cudart_sys::{cudaGetSymbolAddress, cuda_struct_and_stub};
use std::ffi::c_void;
use std::ptr::null_mut;
use std::sync::OnceLock;

use super::seg_desc::{
    BwdSegDesc, BwdSegProgPtrDesc, BWD_SEG_CONST_BANK, BWD_SEG_FOLD_WEIGHT_SLOTS, BWD_SEG_MAX_K,
};
use super::seg_lower::{BwdSegLaunchDesc, BwdSegSetup, CoeffMode, ProgramMode};
use crate::primitives::field::E4;
use crate::primitives::utils::{set_shared_carveout, smem_pool_bytes_per_sm, WARP_SIZE};
use crate::prover::gkr::backward::compact::get_main_layer_claim_point_device_ptr;
use crate::prover::ProverContext;
use crate::upstream::BwdRegime;

cuda_struct_and_stub! {
    static ab_gkr_bwd_seg_coeff_bank: [E4; BWD_SEG_CONST_BANK];
}

/// Device address of this lineage's OWN `__constant__` coefficient bank.
///
/// The upload target for [`BwdSegSetup::coefficients`] under
/// [`CoeffMode::Constant`]: the payload is reserved-INCLUSIVE
/// (`[ONE, NEG_ONE, recipes…]`) and the kernel indexes it raw with the wire's
/// thirteen-bit coefficient id.
pub(crate) fn bwd_seg_coeff_bank_device_ptr() -> *mut E4 {
    static PTR: OnceLock<usize> = OnceLock::new();
    let ptr = *PTR.get_or_init(|| {
        let mut ptr: *mut c_void = null_mut();
        // SAFETY: the Rust static is the stub for the exact CUDA `__constant__`
        // E4 bank `segmented_vm.cu` defines.
        unsafe {
            cudaGetSymbolAddress(
                &mut ptr,
                &ab_gkr_bwd_seg_coeff_bank as *const _ as *const c_void,
            )
        }
        .wrap()
        .expect("cudaGetSymbolAddress failed for ab_gkr_bwd_seg_coeff_bank");
        ptr as usize
    });
    ptr as *mut E4
}

/// Device address of the fold-challenge symbol the prologue reads.
///
/// Deliberately the INCUMBENT's `ab_gkr_main_layer_claim_point` rather than a
/// second symbol: fold challenges have exactly one authority, which is why the
/// descriptor carries no challenge pointer. Front-indexed — a catch-up of `delta`
/// steps at round `r` reads `[r - delta, r)` — so slot `i` must hold the challenge
/// drawn at round `i`, exactly as the incumbent's own round kernels expect. Being
/// shared, it is also stream-ordered state: an upload for this lineage overwrites
/// what the incumbent staged, so the two must not be interleaved inside one
/// fork/join window.
pub(crate) fn bwd_seg_claim_point_device_ptr() -> *mut E4 {
    get_main_layer_claim_point_device_ptr()
}

cuda_struct_and_stub! {
    static ab_gkr_bwd_seg_fold_weights: [E4; BWD_SEG_FOLD_WEIGHT_SLOTS];
}

/// Device address of the fold-weight bank — BOTH the prelude's write target
/// (passed as its `fold_weights` argument; the alias-write path, spec §4.2) and
/// the tests' readback window. Round-mutable shared state like the claim point:
/// safe under the proof-level serialization invariant, not by stream ordering
/// alone.
pub(crate) fn bwd_seg_fold_weights_device_ptr() -> *mut E4 {
    static PTR: OnceLock<usize> = OnceLock::new();
    let ptr = *PTR.get_or_init(|| {
        let mut ptr: *mut c_void = null_mut();
        // SAFETY: the Rust static is the stub for the exact CUDA `__constant__`
        // E4 bank `segmented_vm.cu` defines.
        unsafe {
            cudaGetSymbolAddress(
                &mut ptr,
                &ab_gkr_bwd_seg_fold_weights as *const _ as *const c_void,
            )
        }
        .wrap()
        .expect("cudaGetSymbolAddress failed for ab_gkr_bwd_seg_fold_weights");
        ptr as usize
    });
    ptr as *mut E4
}

// ── The kernel matrix ───────────────────────────────────────────────────────
//
// ONE by-value descriptor is the whole formal list of every symbol, so the
// families need exactly two signatures and the specialization axes select a
// SYMBOL rather than a signature. `seg_abi_tests`'s kernel-argument pin documents
// and asserts that formal list.

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GkrBwdSegInline,
    desc: BwdSegDesc,
);
cuda_kernel_signature_arguments_and_function!(
    pub(crate) GkrBwdSegProgPtr,
    desc: BwdSegProgPtrDesc,
);

macro_rules! declare_bwd_seg_kernel {
    ($symbol:ident, $desc:ty) => {
        cuda_kernel_declaration!(pub(crate) $symbol(desc: $desc));
    };
}

declare_bwd_seg_kernel!(ab_gkr_bwd_seg_r0_const_epi_staged_kernel, BwdSegDesc);
declare_bwd_seg_kernel!(ab_gkr_bwd_seg_r0_const_epi_plane_kernel, BwdSegDesc);
declare_bwd_seg_kernel!(ab_gkr_bwd_seg_r0_const_epi_wide_kernel, BwdSegDesc);
declare_bwd_seg_kernel!(ab_gkr_bwd_seg_r0_ptr_epi_staged_kernel, BwdSegDesc);
declare_bwd_seg_kernel!(ab_gkr_bwd_seg_r0_ptr_epi_plane_kernel, BwdSegDesc);
declare_bwd_seg_kernel!(ab_gkr_bwd_seg_r0_ptr_epi_wide_kernel, BwdSegDesc);
declare_bwd_seg_kernel!(ab_gkr_bwd_seg_cont_const_epi_staged_kernel, BwdSegDesc);
declare_bwd_seg_kernel!(ab_gkr_bwd_seg_cont_const_epi_plane_kernel, BwdSegDesc);
declare_bwd_seg_kernel!(ab_gkr_bwd_seg_cont_const_epi_wide_kernel, BwdSegDesc);
declare_bwd_seg_kernel!(ab_gkr_bwd_seg_cont_ptr_epi_staged_kernel, BwdSegDesc);
declare_bwd_seg_kernel!(ab_gkr_bwd_seg_cont_ptr_epi_plane_kernel, BwdSegDesc);
declare_bwd_seg_kernel!(ab_gkr_bwd_seg_cont_ptr_epi_wide_kernel, BwdSegDesc);
declare_bwd_seg_kernel!(
    ab_gkr_bwd_seg_cont_const_progptr_epi_staged_kernel,
    BwdSegProgPtrDesc
);
declare_bwd_seg_kernel!(
    ab_gkr_bwd_seg_cont_const_progptr_epi_plane_kernel,
    BwdSegProgPtrDesc
);
declare_bwd_seg_kernel!(
    ab_gkr_bwd_seg_cont_const_progptr_epi_wide_kernel,
    BwdSegProgPtrDesc
);

// ── The fold-weight prelude ─────────────────────────────────────────────────
//
// The one launched symbol outside the matrix, and the one with formals other than
// a descriptor: it writes the `__constant__` weight bank through that symbol's
// own address, because device code cannot name a `__constant__` as a store
// target.

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GkrBwdSegBuildFoldWeights,
    fold_weights: *mut E4,
    round: u32,
);
cuda_kernel_declaration!(
    pub(crate) ab_gkr_bwd_seg_build_fold_weights_kernel(fold_weights: *mut E4, round: u32)
);

/// Enqueue the per-round fold-weight build: one warp, grid 1, exec_stream.
/// Order per continuation round: claim-point update -> this -> segment kernels.
/// R0 rounds must not call it (no folds; round 0 has no challenges).
pub(crate) fn launch_bwd_seg_build_fold_weights(
    round: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(round >= 1, "the fold-weight prelude is continuation-only");
    let config = CudaLaunchConfig::builder()
        .grid_dim(1)
        .block_dim(WARP_SIZE)
        .stream(context.get_exec_stream())
        .build();
    let function = GkrBwdSegBuildFoldWeightsFunction(ab_gkr_bwd_seg_build_fold_weights_kernel);
    function.launch(
        &config,
        &GkrBwdSegBuildFoldWeightsArguments::new(bwd_seg_fold_weights_device_ptr(), round),
    )
}

/// The cross-warp reduction shape a launch is specialized for (§3).
///
/// NO default is pre-committed: all three are compiled and the spike's A/B
/// decides. They differ only in barrier count against shared-memory footprint,
/// and — field addition being exact and associative — never in the value they
/// produce.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BwdSegEpilogue {
    /// Serial read-modify-write through ONE 32-lane plane pair: `k - 1` barriers,
    /// ~1 KiB.
    Staged,
    /// The incumbent shape — one `[k - 1][32]` plane reused for `c0` then `c2`:
    /// 3 barriers, ~15.5 KiB at `k = 32`.
    Plane,
    /// Both planes at once: 1 barrier, ~31 KiB at `k = 32`.
    Wide,
}

/// Dynamic shared memory one block needs for `epilogue` at `k` warps.
///
/// MIRROR of `bwd_seg_epilogue_smem_bytes` in `segmented_vm.cuh`. Nothing at build
/// time compares the two — this value is the launch's dynamic-smem argument, so a
/// disagreement is an out-of-bounds shared-memory access rather than a compile
/// error, which is why the tests below pin the same numbers the header's
/// `static_assert`s pin.
pub(crate) fn bwd_seg_epilogue_smem_bytes(epilogue: BwdSegEpilogue, k: u32) -> usize {
    // `k == 1`: warp 0's register partials ARE the block result, so no plane is
    // touched at all.
    if k < 2 {
        return 0;
    }
    let lanes = WARP_SIZE as usize * size_of::<E4>();
    match epilogue {
        BwdSegEpilogue::Staged => 2 * lanes,
        BwdSegEpilogue::Plane => (k as usize - 1) * lanes,
        BwdSegEpilogue::Wide => 2 * (k as usize - 1) * lanes,
    }
}

// ── Shared-memory carveout control (spec §3) ─────────────────────────────────
//
// `compute_minimal_carveout` (gpu/core/src/primitives/utils.rs:94-124) MUST NOT be
// reused here. It reads `cudaFuncAttributes::sharedSizeBytes` and returns 0 when
// that is zero; every seg kernel declares `extern __shared__`
// (segmented_vm.cu:779) so its STATIC figure is 0 and the shared helper would
// return 0 for an accidental reason rather than the right one. That is the whole
// reason the seg path needs its own helper.

/// The per-block driver reserve, in bytes — QUERIED, not assumed.
///
/// A block consumes a fixed slice of the shared partition beyond its dynamic
/// request. Expected 1,024 B on this part (the figure the linked cubin's
/// `SHARED:1024` label reports), but read rather than assumed. It is **not** part
/// of `cudaFuncAttributes::sharedSizeBytes` — that field is user STATIC shared
/// only, which is why the header's 48 KiB `static_assert`s were already correct
/// and F4 was withdrawn (spec §2.2 row 3, §5.4).
pub(crate) fn bwd_seg_reserved_smem_bytes_per_block() -> usize {
    use era_cudart::device::{device_get_attribute, get_device};
    use era_cudart_sys::CudaDeviceAttr;
    let device = get_device().expect("get_device");
    device_get_attribute(CudaDeviceAttr::ReservedSharedMemoryPerBlock, device)
        .expect("query ReservedSharedMemoryPerBlock") as usize
}

/// The hardware per-SM resident block cap — QUERIED, not an empirically inferred
/// constant. Without it the occupancy formula predicts 48 blocks at `k == 1` and
/// doubles every `k == 1` demand row.
pub(crate) fn bwd_seg_max_blocks_per_sm() -> u32 {
    use era_cudart::device::{device_get_attribute, get_device};
    use era_cudart_sys::CudaDeviceAttr;
    let device = get_device().expect("get_device");
    u32::try_from(
        device_get_attribute(CudaDeviceAttr::MaxBlocksPerMultiprocessor, device)
            .expect("query MaxBlocksPerMultiprocessor"),
    )
    .expect("a non-negative block cap")
}

/// L2 capacity, for §7.2.2's per-direction conservative soft bound.
pub(crate) fn bwd_seg_l2_capacity_bytes() -> u64 {
    use era_cudart::device::{device_get_attribute, get_device};
    use era_cudart_sys::CudaDeviceAttr;
    let device = get_device().expect("get_device");
    u64::try_from(
        device_get_attribute(CudaDeviceAttr::L2CacheSize, device).expect("query L2CacheSize"),
    )
    .expect("a non-negative L2 size")
}

/// Warps per SM the thread cap allows: 1,536 threads / 32 lanes.
const BWD_SEG_WARP_CAP_PER_SM: u32 = 48;
/// Registers per SM the allocator partitions, and its granularity.
const BWD_SEG_REGS_PER_SM: u32 = 16_384;
const BWD_SEG_REG_ALLOC_GRANULARITY: u32 = 256;

/// Register-bound resident blocks per SM at `registers` per thread and `k` warps
/// per block (spec §3.1). Reproduces results §2.5's measured column exactly:
/// R40 -> `[24, 24, 12, 6, 3, 2, 1]` and R50 -> `[24, 18, 9, 4, 2, 1, 1]` at
/// `k = 1/2/4/8/16/24/32`.
pub(crate) fn bwd_seg_register_bound_blocks_per_sm(registers: u32, k: u32) -> u32 {
    assert!(registers >= 1 && k >= 1, "registers and k are positive");
    let regs_per_warp = (registers * WARP_SIZE).next_multiple_of(BWD_SEG_REG_ALLOC_GRANULARITY);
    let warp_budget = (4 * (BWD_SEG_REGS_PER_SM / regs_per_warp)).min(BWD_SEG_WARP_CAP_PER_SM);
    (warp_budget / k)
        .min(BWD_SEG_WARP_CAP_PER_SM / k)
        .min(bwd_seg_max_blocks_per_sm())
}

/// The supported realized shared-memory partitions on this part, in bytes.
///
/// DOCUMENTED, not measured — spec §9 item 4 flags that §3.1's zero-reclaim
/// finding for `wide` turns on 49,152 B needing the 64 KiB bucket rather than a
/// 48 KiB one, and that §1(b)'s whole "P1 is epilogue-dependent" reading follows
/// from it. The realized NCU field is the authority and step 7 confirms or
/// corrects this list BEFORE the demand table is trusted.
pub(crate) const BWD_SEG_SMEM_BUCKETS_BYTES: [usize; 6] =
    [0, 8 * 1024, 16 * 1024, 32 * 1024, 64 * 1024, 100 * 1024];

/// The bucket the driver is EXPECTED to realize for a per-SM demand: the smallest
/// supported partition that holds it. An expected value the realized field then
/// confirms or corrects, never an assertion in its own right.
pub(crate) fn bwd_seg_expected_smem_bucket_bytes(demand_bytes: usize) -> usize {
    BWD_SEG_SMEM_BUCKETS_BYTES
        .into_iter()
        .find(|bucket| *bucket >= demand_bytes)
        .unwrap_or_else(|| {
            panic!("per-SM demand {demand_bytes} B exceeds the largest supported partition")
        })
}

/// The requested carveout percentage for one launch shape.
///
/// The demand is per **SM**: `blocks * (dynamic + reserve)`. The percentage is a
/// HINT — the driver rounds it up to the next supported bucket, so several
/// distinct values land on the same realized split, and 0 is safe because the
/// driver still raises the configuration to the smallest bucket that satisfies the
/// launch's dynamic request. **The gate is the realized field, never this number**
/// (spec §3.4).
pub(crate) fn bwd_seg_carveout_pct(target_blocks_per_sm: u32, dynamic_smem_bytes: usize) -> i32 {
    let demand = target_blocks_per_sm as usize
        * (dynamic_smem_bytes + bwd_seg_reserved_smem_bytes_per_block());
    bwd_seg_pct_for_demand(demand)
}

/// The requested pct for a per-SM demand. **`pub(crate)`** because `seg_report.rs`'s
/// pin-decision assertion must use the SAME arithmetic the production path uses, and
/// the registry promises this visibility (§4.5).
pub(crate) fn bwd_seg_pct_for_demand(demand_bytes: usize) -> i32 {
    let pct = (demand_bytes * 100).div_ceil(smem_pool_bytes_per_sm());
    i32::try_from(pct)
        .expect("a percentage fits an i32")
        .clamp(0, 100)
}

/// The pct that lands on ONE EXPLICIT bucket, independent of either arm's demand —
/// exactly what `CarveoutMode::FixedBucket` requests, exposed so
/// `bwd_seg_pin_decision_cells` can assert the realized field **without restating the
/// arithmetic**. A thin wrapper on purpose: two expressions that must agree are better
/// written as one expression.
pub(crate) fn bwd_seg_carveout_pct_for_bucket(bucket_bytes: usize) -> i32 {
    bwd_seg_pct_for_demand(bucket_bytes)
}

/// Compute and set the minimal carveout for one entry point; returns the requested
/// percentage so the caller can record it beside the realized field.
///
/// `target_blocks_per_sm` is the REGISTER-BOUND count at the pin level of the
/// binary actually being timed — not `bwd_seg_blocks_per_sm`'s answer, which models
/// shared memory against the device's full pool rather than any realized
/// configuration (audit II-4). Setting the carveout from a stale block count would
/// ask for less shared memory than the pinned build's blocks need and cost
/// occupancy. This is the deliberate P1<->P2 coupling (spec §3.1).
pub(crate) fn bwd_seg_set_minimal_carveout(
    entry: *const std::ffi::c_void,
    target_blocks_per_sm: u32,
    dynamic_smem_bytes: usize,
) -> i32 {
    let pct = bwd_seg_carveout_pct(target_blocks_per_sm, dynamic_smem_bytes);
    set_shared_carveout(entry, pct);
    pct
}

/// Registers per thread the compiled entry point uses, cached per symbol.
///
/// A property of the BINARY, so one query per symbol per process is exact — and the
/// launch path needs it on every launch to size the carveout, which is why it is
/// cached rather than queried each time.
fn bwd_seg_entry_registers(entry: *const std::ffi::c_void) -> u32 {
    use era_cudart_sys::{cudaFuncGetAttributes, CudaFuncAttributes};
    static CACHE: OnceLock<std::sync::Mutex<std::collections::HashMap<usize, u32>>> =
        OnceLock::new();
    let cache = CACHE.get_or_init(Default::default);
    if let Some(hit) = cache.lock().expect("register cache").get(&(entry as usize)) {
        return *hit;
    }
    let mut attributes = std::mem::MaybeUninit::<CudaFuncAttributes>::zeroed();
    // SAFETY: `CudaFuncAttributes` is plain data and `entry` is a valid `__global__`
    // entry point from one of this module's accessors.
    unsafe { cudaFuncGetAttributes(attributes.as_mut_ptr(), entry) }
        .wrap()
        .expect("cudaFuncGetAttributes for a register query");
    // SAFETY: initialized by the call above.
    let registers = u32::try_from(unsafe { attributes.assume_init() }.numRegs)
        .expect("a non-negative register count");
    cache
        .lock()
        .expect("register cache")
        .insert(entry as usize, registers);
    registers
}

/// How many [`CarveoutPlan`]s are alive. Nonzero means a MEASUREMENT caller owns the
/// preference and the launch path must not touch it.
static SEG_CARVEOUT_PLANS_ALIVE: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);

/// The percentage the LAUNCH PATH last requested per entry point, so a repeat launch
/// of the same shape costs no driver call.
///
/// It is a cache of what this module set, not of what the driver holds — anything
/// else that writes a preference must invalidate it
/// ([`seg_forget_launch_carveout`]), or the next launch would skip a set it needs.
static SEG_LAUNCH_CARVEOUT: OnceLock<std::sync::Mutex<std::collections::HashMap<usize, i32>>> =
    OnceLock::new();

fn seg_launch_carveout_cache() -> &'static std::sync::Mutex<std::collections::HashMap<usize, i32>> {
    SEG_LAUNCH_CARVEOUT.get_or_init(Default::default)
}

/// Drop this entry point's cached request, because someone else just wrote the
/// preference and the cache no longer describes the driver's state.
fn seg_forget_launch_carveout(entry: *const std::ffi::c_void) {
    seg_launch_carveout_cache()
        .lock()
        .expect("carveout cache")
        .remove(&(entry as usize));
}

/// Set the launch's own minimal carveout, unless a [`CarveoutPlan`] owns the
/// preference.
///
/// **Why the launch path owns this at all.** The preference is worth +1.23 % of
/// summed continuation time at the committed policy's `K = 16` and +2.82 % at
/// `K = 32`, measured against setting none at all
/// (`.agents/bench/2026-08-01-decode-fold`, the `carveout-off` point). The loss
/// scales with per-block demand and its mechanism is block RESIDENCY: at `K = 16`
/// this executor is two blocks/SM by registers, and a driver-default split that
/// hosts one 7,680-byte block instead of two halves occupancy — which no amount of
/// extra L1 pays back. A caller that forgets to ask therefore pays, silently, and
/// nothing in a release build says so. So it is not a caller's obligation any more.
///
/// The block count is the REGISTER-BOUND one at this binary's pin level, not
/// [`bwd_seg_blocks_per_sm`]'s answer — that one models shared memory against the
/// device's full pool rather than any realized configuration (audit II-4), and
/// sizing the request from it would ask for the wrong partition.
///
/// Idempotent per `(entry, pct)`: one symbol serves every `K`, so the requested
/// percentage moves with `K`, the epilogue and the placement; the cache suppresses
/// only the repeats, which is what makes this free on the hot path.
fn seg_apply_launch_carveout(
    entry: *const std::ffi::c_void,
    k: u32,
    dynamic_smem_bytes: usize,
) -> Option<i32> {
    if SEG_CARVEOUT_PLANS_ALIVE.load(std::sync::atomic::Ordering::Acquire) != 0 {
        // A measurement caller is in charge — including `CarveoutMode::Off`, whose
        // whole point is that NO preference is set anywhere. Setting one here would
        // silently defeat the control arm.
        return None;
    }
    let blocks = bwd_seg_register_bound_blocks_per_sm(bwd_seg_entry_registers(entry), k);
    let pct = bwd_seg_carveout_pct(blocks, dynamic_smem_bytes);
    let mut cache = seg_launch_carveout_cache().lock().expect("carveout cache");
    if cache.get(&(entry as usize)) == Some(&pct) {
        return Some(pct);
    }
    set_shared_carveout(entry, pct);
    cache.insert(entry as usize, pct);
    Some(pct)
}

/// The entry point's CURRENT preference, so a restore can write back the exact
/// prior value rather than the driver default.
pub(crate) fn bwd_seg_query_carveout(entry: *const std::ffi::c_void) -> i32 {
    use era_cudart_sys::{cudaFuncGetAttributes, CudaFuncAttributes};
    let mut attributes = std::mem::MaybeUninit::<CudaFuncAttributes>::zeroed();
    // SAFETY: `CudaFuncAttributes` is plain data and `entry` is a valid
    // `__global__` entry point from one of this module's accessors.
    unsafe { cudaFuncGetAttributes(attributes.as_mut_ptr(), entry) }
        .wrap()
        .expect("cudaFuncGetAttributes for a carveout query");
    // SAFETY: initialized by the call above.
    unsafe { attributes.assume_init() }.preferredShmemCarveout
}

/// **The reference clock's ONE predeclared realized partition (§4.5, round-2
/// blocker 4).**
///
/// `CommonBucket` derives its pct from `max(candidate, baseline)` demand, so the
/// flat-R0 reference clock would run at a DIFFERENT L1 partition at each pin level
/// — `plane` K24 demands `1 x 12,800 = 12,800 B` (16 KiB bucket) at the natural
/// band and `2 x 12,800 = 25,600 B` (32 KiB) at a 40-pin. A denominator whose own
/// cache configuration moves with the level is not invariant, and §4.5's entire
/// cross-build argument rests on its invariance.
///
/// So the pin-decision pairs are configured at ONE FIXED bucket, predeclared here:
/// **64 KiB**, on two independent grounds.
///
/// **(i) Demand.** Over the decision set (`plane`, `const`, inline,
/// `K in {1,2,4,8,16,24,32}`, pins 40/48/50/56) the worst per-SM demand is R40
/// **K=2 = 36,864 B** — 24 register-bound blocks × (512 B epilogue + 1,024 B
/// reserve). Small `K` is RESERVE-DOMINATED, which is why the worst cell is not the
/// widest one: the epilogue plane shrinks faster with `K` than the block count grows.
/// 36,864 B exceeds 32,768 B, and the realized-partition probe settled §9 item 4 —
/// a 49,152 B request realized 65,536 B, so **there is no 48 KiB bucket** — leaving
/// 65,536 B as the smallest supported bucket that covers every decision cell at
/// every level.
///
/// **(ii) Mechanism, which is the stronger ground.** The requested percentage is a
/// FLOOR, not a setting: measured over this pass's captures,
/// `realized = max(driver heuristic, bucket)`, and the heuristic alone picks 64 KiB
/// for a `K = 4` seg launch. So every bucket below 64 KiB can be silently overridden
/// upward by the driver, per kernel and per launch shape, and 64 KiB is the ONLY
/// partition the driver can never raise. Invariance — not speed — is the reference
/// clock's whole job: a denominator whose own cache configuration moves with the
/// level would void §4.5's cross-build argument, and the L1 that costs is a price
/// paid identically by both arms at every level.
///
/// A fixed sub-64 bucket was rejected for the same reason: the observed
/// same-request divergence (both arms asked for one partition, one realized 64 KiB
/// and the other 32 KiB) kills commonality below 64 KiB regardless of the demand
/// arithmetic.
///
/// **What is asserted in-process, stated exactly (ruling R8).**
/// `bwd_seg_pin_decision_cells` asserts `SegMatrixRow::carveout_requested_pct` equals
/// [`bwd_seg_carveout_pct_for_bucket`] of this constant — i.e. **the REQUEST landed**, not
/// that a particular partition was realized. An earlier revision of this comment claimed
/// the assertion checked the realized field; it does not, and it cannot: the realized
/// partition is an `ncu` metric (`launch__shared_mem_config_size`), not something the
/// launching process observes. **The realized field is verified out of process, per level,
/// by `pair_gate.py`** over the campaign's NCU captures.
///
/// **And what that out-of-process gate asserts is PER-ARM LEVEL-INVARIANCE, not pair
/// equality (ruling R8).** §4.5's estimator is a ratio of ratios: each level's number is
/// candidate/clock from that level's own build. Its validity needs each arm to sit at the
/// same partition **across levels**, so that the partition cancels between levels — it does
/// **not** need the two arms to sit at the same partition as each other, which is §7.2.1's
/// question and a different one. Both per-arm conditions are measured and hold:
///   * the **clock** arm (flat, zero-dynamic, 1,024 B/block, not on the sweep axis) realizes
///     **65,536 B** under this request at every level, and its normalized SASS body is
///     hash-identical across all four builds;
///   * the **candidate** arm realizes **102,400 B** — the pool maximum, clamped — at every
///     measurable level, an L1 spread of 0.26 pp, i.e. session noise.
/// The two differ from each other (102,400 vs 65,536), and that is fine here: it is a
/// constant offset present identically in every level's ratio. Demanding pair convergence
/// would fail the gate for a property §4.5 never rests on — and, per the reachability
/// finding below, is only satisfiable at the pool maximum and only at an asymmetric cost.
pub(crate) const SEG_REFERENCE_CLOCK_BUCKET_BYTES: usize = 64 * 1024;

/// How a pair is configured (spec §7.1.0, §7.2.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CarveoutMode {
    /// No preference set anywhere; the driver's own split. §7.1.0's `off` arm —
    /// the control half of the same-binary isolation, so the `off`-to-
    /// `CommonBucket` delta IS P1 and nothing else.
    Off,
    /// BOTH arms asked for ONE bucket, derived from the larger demand — the intent being
    /// one SM partition with no reconfiguration at any sample boundary, so the ratio would
    /// be a statement about the two kernels. Also the mode every solo cell uses.
    ///
    /// **It is NOT §7.2.1's primary column, and no mode currently is: that column is
    /// UNPOPULATED pending RR.** This mode was the primary until the forced pairs were
    /// actually measured, and it FAILED at the R0 headline cell — asked for 30 % on both
    /// arms, the pair realized 65,536 B and 32,768 B and `pair_gate.py` recorded
    /// `PROTOCOL FAILURE` (3 of 4 forced pairs over). It is retained because §7.1.0's
    /// isolation needs it and because it is the empirical record of why the primary moved.
    ///
    /// The request is a FLOOR: `realized = max(driver heuristic, bucket)`, and the overshoot
    /// is a function of the launch's K-shape rather than of the request, so commonality is
    /// VERIFIED per capture by `pair_gate.py` and never assumed at ANY bucket — a heuristic
    /// override above the requested bucket is a recorded protocol failure.
    CommonBucket,
    /// Both arms forced to ONE EXPLICIT bucket, independent of either arm's demand.
    /// §4.5's pin-decision pairs use this so the reference clock's own realized
    /// partition is identical at every pin level — see
    /// [`SEG_REFERENCE_CLOCK_BUCKET_BYTES`].
    ///
    /// **Reachable from `BWD_SEG_CARVEOUT=fixed-bucket[:<bytes>]`** — see
    /// [`parse_carveout_mode`](super::seg_report) for the grammar and the validation. The
    /// bare form binds to [`SEG_REFERENCE_CLOCK_BUCKET_BYTES`]; an explicit byte count must
    /// name a member of [`BWD_SEG_SMEM_BUCKETS_BYTES`], so an environment may select a
    /// documented partition but may not invent one.
    ///
    /// **MEASURED, and it corrects what an earlier revision of this comment asserted: 64 KiB
    /// is NOT a bucket the driver cannot raise.** At the R0 headline shape (`plane K=4`,
    /// 2,560 B/block, 12 resident blocks) a 64 KiB request realized **102,400 B — the whole
    /// SM pool** — while the zero-dynamic flat incumbent realized 65,536 B, so
    /// `pair_gate.py` recorded `PROTOCOL FAILURE` there too. The floor law's fixed point on
    /// this device is the **102,400 B pool maximum**, which is the only value measured to
    /// converge both arms **AT THE HEADLINE CELL** (`REALIZED OK` against a predeclared
    /// `--expect-bucket 102400`). The scoping is load-bearing: the same 64 KiB request DOES
    /// converge at `K = 24`, so the overshoot is K-shape dependent, not a property of the
    /// bucket.
    ///
    /// **§7.2.1's primary column is UNPOPULATED pending RR**: the pool-max configuration
    /// converges but costs the flat incumbent 30.53 pp of L1 hit rate against the
    /// candidate's 13.02 pp, so "equal realized partitions" is reachable at this pair only
    /// via an asymmetric handicap. That is a judgement, not a measurement, and this type
    /// takes no position on it.
    ///
    /// The mode alone therefore does not identify a reference-clock pairing: §4.5's pairs
    /// clock a continuation candidate against the flat R0 kernel, while the R0 headline's
    /// pairs are candidate-vs-incumbent and keep §6(b)'s inversion vocabulary — and both can
    /// run at a fixed bucket. That distinction is carried by `SegMatrixRow::pairing`, not by
    /// this label. The label does not carry the BUCKET either, which is why a probe verdict
    /// is keyed on `CarveoutMode::mode_key` instead: a 64 KiB convergence must not license a
    /// 100 KiB confirmation.
    FixedBucket(usize),
    /// Each arm at the preference this bench design gives it: the candidate its own
    /// computed pct, the baseline the preference it already carries (the flat R0
    /// incumbent's explicit 0%, written behind the `Once` in
    /// `flat/kernel_setup.rs:20-38`). §7.2.1's SECONDARY column — a stress test of
    /// the repartition transition, reported with its four order-conditional
    /// medians, and NOT an acceptance gate (M7).
    AsConfigured,
}

impl CarveoutMode {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::Off => "off",
            Self::CommonBucket => "common-bucket",
            Self::AsConfigured => "as-configured",
            Self::FixedBucket(_) => "fixed-bucket",
        }
    }

    /// The FULL configuration key, bucket included — what a convergence probe is a verdict
    /// ABOUT.
    ///
    /// [`Self::label`] deliberately collapses every `FixedBucket` to one string, because it
    /// names the emitted CSV column and two spellings there would drift. That collapse is
    /// wrong for probe evidence: `fixed-bucket` at 64 KiB DIVERGED at the R0 headline cell
    /// and `fixed-bucket` at 102,400 B CONVERGED, so a verdict keyed on the label alone would
    /// let the 64 KiB failure and the 100 KiB success stand for each other. Keying on this
    /// closes that license.
    pub(crate) fn mode_key(self) -> String {
        match self {
            Self::FixedBucket(bucket) => format!("fixed-bucket:{bucket}"),
            other => other.label().to_owned(),
        }
    }

    /// Whether this configuration FORCES both arms toward one partition, and therefore
    /// whether a convergence probe of it means anything.
    ///
    /// `Off` is the driver-default control, where divergence is the expected outcome and the
    /// data; `AsConfigured` gives the two arms deliberately different preferences. Neither
    /// claims equal partitions, so neither can supply — or require — convergence evidence.
    pub(crate) fn forces_one_partition(self) -> bool {
        matches!(self, Self::CommonBucket | Self::FixedBucket(_))
    }
}

/// One arm's launch shape, as the plan needs to see it.
///
/// Carried EXPLICITLY with each arm rather than inferred: the harness's paired
/// baselines are not all the flat R0 incumbent — the Stage-B ladder pairs a rung
/// against a segmented twin and the corpus pairs K against the K4 same-cell twin,
/// and an opaque launch callback carries no shape at all.
#[derive(Clone, Copy, Debug)]
pub(crate) struct CarveoutShape {
    pub(crate) entry: *const std::ffi::c_void,
    pub(crate) dynamic_smem_bytes: usize,
    /// Register-bound resident blocks at the ACTIVE pin level of this binary.
    pub(crate) target_blocks_per_sm: u32,
    /// Names the shape in the emitted row.
    pub(crate) label: &'static str,
}

impl CarveoutShape {
    pub(crate) fn demand_bytes(&self) -> usize {
        self.target_blocks_per_sm as usize
            * (self.dynamic_smem_bytes + bwd_seg_reserved_smem_bytes_per_block())
    }

    /// The prelude's shape: grid 1, block 32 — ONE block on one SM for the whole
    /// device. Feeding it an occupancy-maximum block count would reserve shared
    /// memory for blocks that can never coexist. It declares no shared memory at
    /// all, so 0% both maximizes L1 and lets the driver raise the configuration to
    /// the smallest bucket satisfying its (zero) dynamic request. The one symbol
    /// whose preference is a constant (spec §3.1).
    pub(crate) fn prelude() -> Self {
        Self {
            entry: bwd_seg_prelude_entry_point(),
            dynamic_smem_bytes: 0,
            target_blocks_per_sm: 1,
            label: "prelude",
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct CarveoutEntry {
    entry: *const std::ffi::c_void,
    requested_pct: i32,
    /// `Some` exactly once this slot's prior has been QUERIED, and that is the whole
    /// point: the restore set is the queried set, per slot, never a whole-plan flag.
    ///
    /// A single `applied: bool` cannot express it and both placements are wrong. Set
    /// AFTER the loop, an unwind on entry `n` skips the restore entirely and leaks
    /// the overrides already installed on `1..n` for the rest of the process — the
    /// exact failure this type exists to eliminate. Hoisted BEFORE the loop, the
    /// restore writes a default over slots whose priors were never read, which
    /// installs a value the driver never had.
    prior_pct: Option<i32>,
}

/// The pair-scoped owner of the carveout preference (spec §3.2).
///
/// `SegCell::stage` knows ONE shape and is never passed the baseline, so it cannot
/// compute a two-arm maximum — the plan is therefore built by the caller that owns
/// both closures, and staging keeps its existing job (uploads and descriptor
/// patching). There is NO process-lifetime configuration of this family and `Once`
/// has no role here: one continuation entry point serves every runtime `K` while
/// its block count and dynamic demand move with `K`, pin, epilogue and placement.
///
/// Per-cell sequence, and the order is load-bearing: **build plan (both arms +
/// prelude) -> `apply()` -> stage arm A -> stage arm B -> balanced warmup ->
/// timed blocks -> restore (on drop)**. `apply()` runs before EITHER arm stages,
/// not merely before the warmup, because `SegCell::stage` LAUNCHES the fold-weight
/// prelude — applying after staging would run the prelude at whatever preference
/// the previous cell left behind, silently, on every continuation cell, and would
/// leave a twin baseline staged under the wrong preference too.
/// While one of these is alive the launch path does NOT set a preference of its own
/// ([`seg_apply_launch_carveout`]). That is what keeps a measurement's control arms
/// honest: `CarveoutMode::Off` means no preference is set anywhere, and a launcher
/// quietly asking for one would turn the column into a measurement of itself.
pub(crate) struct CarveoutPlan {
    mode: CarveoutMode,
    entries: Vec<CarveoutEntry>,
    demand_source: String,
}

impl CarveoutPlan {
    /// Registers this plan as the preference's owner. Every constructor ends here, and
    /// [`Drop`] releases it — so the launch path defers for exactly the plan's
    /// lifetime, whether or not [`Self::apply`] was reached.
    fn own_the_preference(self) -> Self {
        SEG_CARVEOUT_PLANS_ALIVE.fetch_add(1, std::sync::atomic::Ordering::AcqRel);
        self
    }
}

impl CarveoutPlan {
    fn push_unique(entries: &mut Vec<CarveoutEntry>, entry: *const std::ffi::c_void, pct: i32) {
        // DEDUPE BY ENTRY POINTER. One symbol serves every `K`, so a pair's two
        // arms can be the SAME function — the corpus's K-vs-K4 twin always is. Two
        // entries for one pointer would query the second `prior_pct` AFTER the
        // first `set`, capturing the override as the "prior" value, and the restore
        // would then reinstall it and leak into every later cell in the process.
        if let Some(existing) = entries
            .iter_mut()
            .find(|slot| std::ptr::eq(slot.entry, entry))
        {
            // Same symbol, two demands: the larger request wins, for the same
            // reason a cross-shape pair takes the maximum.
            existing.requested_pct = existing.requested_pct.max(pct);
            return;
        }
        entries.push(CarveoutEntry {
            entry,
            requested_pct: pct,
            prior_pct: None,
        });
    }

    /// Both arms plus (optionally) the prelude.
    ///
    /// In `CommonBucket`, cross-shape pairs take `max(demand_a, demand_b)` and both
    /// arms are configured from that one number: a pair whose two sides request
    /// different partitions is defect (a) reintroduced. Where the two demands
    /// quantize to DIFFERENT buckets the smaller-demand side ran at less L1 than it
    /// could have had alone, and that asymmetry statement must travel with the
    /// reported number; where they quantize to the SAME bucket the note is vacuous
    /// and is omitted (spec §3.2 rule 3).
    ///
    /// In `AsConfigured`, the candidate gets its own pct and the baseline is LEFT
    /// ALONE — its shipped preference is data, not a constant to assume.
    pub(crate) fn for_pair(
        mode: CarveoutMode,
        candidate: CarveoutShape,
        baseline: CarveoutShape,
        with_prelude: bool,
    ) -> Self {
        let (a, b) = (candidate.demand_bytes(), baseline.demand_bytes());
        let mut entries = Vec::with_capacity(3);
        let demand_source = match mode {
            CarveoutMode::Off => "driver default (no preference set)".to_owned(),
            CarveoutMode::CommonBucket => {
                let (winner, demand) = if a >= b {
                    (candidate.label, a)
                } else {
                    (baseline.label, b)
                };
                let pct = bwd_seg_pct_for_demand(demand);
                Self::push_unique(&mut entries, candidate.entry, pct);
                Self::push_unique(&mut entries, baseline.entry, pct);
                if bwd_seg_expected_smem_bucket_bytes(a) == bwd_seg_expected_smem_bucket_bytes(b) {
                    format!("{winner}, {demand} B (both arms quantize alike)")
                } else {
                    format!(
                        "{winner}, {demand} B (ASYMMETRIC: {a} B vs {b} B quantize to \
                         different buckets; the smaller-demand arm ran at less L1)"
                    )
                }
            }
            CarveoutMode::AsConfigured => {
                Self::push_unique(&mut entries, candidate.entry, bwd_seg_pct_for_demand(a));
                format!(
                    "{} only, {a} B; baseline left at its own preference",
                    candidate.label
                )
            }
            CarveoutMode::FixedBucket(bucket) => {
                // A pct that lands exactly on `bucket`, independent of demand. Both
                // arms get it, so the reference clock's partition is level-invariant.
                assert!(
                    a <= bucket && b <= bucket,
                    "the fixed reference-clock bucket {bucket} B cannot hold demands \
                     {a} B / {b} B; re-derive SEG_REFERENCE_CLOCK_BUCKET_BYTES from \
                     the demand table before timing"
                );
                let pct = bwd_seg_pct_for_demand(bucket);
                Self::push_unique(&mut entries, candidate.entry, pct);
                Self::push_unique(&mut entries, baseline.entry, pct);
                format!("FIXED {bucket} B (predeclared, level-invariant)")
            }
        };
        if with_prelude && mode != CarveoutMode::Off {
            Self::push_unique(&mut entries, CarveoutShape::prelude().entry, 0);
        }
        Self {
            mode,
            entries,
            demand_source,
        }
        .own_the_preference()
    }

    /// One arm, for a solo-timed cell.
    ///
    /// `FixedBucket` carries the SAME containment gate as [`Self::for_pair`], because
    /// the pin-decision set contains solo cells: a solo cell over the fixed bucket
    /// would under-request the reference clock's partition, and the requested pct is
    /// not a gate, so nothing downstream would say so.
    pub(crate) fn for_solo(mode: CarveoutMode, shape: CarveoutShape, with_prelude: bool) -> Self {
        let demand = shape.demand_bytes();
        let mut entries = Vec::with_capacity(2);
        if mode != CarveoutMode::Off {
            let target = match mode {
                CarveoutMode::FixedBucket(bucket) => {
                    assert!(
                        demand <= bucket,
                        "the fixed reference-clock bucket {bucket} B cannot hold demand \
                         {demand} B; re-derive SEG_REFERENCE_CLOCK_BUCKET_BYTES from \
                         the demand table before timing"
                    );
                    bucket
                }
                _ => demand,
            };
            Self::push_unique(&mut entries, shape.entry, bwd_seg_pct_for_demand(target));
            if with_prelude {
                Self::push_unique(&mut entries, CarveoutShape::prelude().entry, 0);
            }
        }
        Self {
            mode,
            entries,
            demand_source: format!("{} only, {demand} B", shape.label),
        }
        .own_the_preference()
    }

    /// Query each entry point's current preference, then set it. Called OUTSIDE
    /// every timed region, re-computed and re-applied per cell, never once per
    /// process or per shape family.
    ///
    /// UNWIND-SAFE per slot: each prior is committed to its own slot BEFORE that
    /// slot is overridden, so if a query or a set panics on entry `n` the plan's
    /// restore set is exactly `1..n` — the slots actually touched — and `drop` puts
    /// every one of them back. See [`CarveoutEntry::prior_pct`] for why a whole-plan
    /// flag cannot do this.
    pub(crate) fn apply(&mut self) {
        // `Off` pushes no entries in either constructor, so the loop would already be
        // inert; the guard is kept so the control arm of §7.1.0's isolation stays
        // structurally incapable of touching a preference even if a future variant
        // starts pushing entries.
        if self.mode == CarveoutMode::Off {
            return;
        }
        for slot in &mut self.entries {
            let prior = bwd_seg_query_carveout(slot.entry);
            slot.prior_pct = Some(prior);
            set_shared_carveout(slot.entry, slot.requested_pct);
        }
    }

    pub(crate) fn mode(&self) -> CarveoutMode {
        self.mode
    }

    pub(crate) fn requested_pct_of(&self, entry: *const std::ffi::c_void) -> Option<i32> {
        self.entries
            .iter()
            .find(|slot| std::ptr::eq(slot.entry, entry))
            .map(|slot| slot.requested_pct)
    }

    pub(crate) fn demand_source_label(&self) -> &str {
        &self.demand_source
    }
}

impl Drop for CarveoutPlan {
    /// Restores the EXACT prior value, never the driver default.
    ///
    /// `reset_shared_carveout` (gpu/core/src/primitives/utils.rs:148-150) writes
    /// `cudaSharedmemCarveoutDefault == -1`, which is NOT a synonym for "put it
    /// back". The incumbent R0 kernel is the case that proves it: its shipped state
    /// is an explicit `0` written once behind a `Once`, so a probe that overrides it
    /// and then "resets" leaves it at DEFAULT and the `Once` will never reapply the
    /// 0 — a later column believing it measured the as-shipped incumbent would be
    /// measuring the driver's heuristic instead. RAII, so an early return or a panic
    /// inside a probe cannot leak state into every later sample. Entries are unique
    /// by construction (`push_unique`), so the restore order cannot matter.
    ///
    /// Restores exactly the slots whose priors were captured — no more, so a slot
    /// `apply` never reached keeps the value the driver already had, and no less, so
    /// a mid-`apply` unwind cannot leave an override installed.
    fn drop(&mut self) {
        for slot in &self.entries {
            if let Some(prior) = slot.prior_pct {
                set_shared_carveout(slot.entry, prior);
            }
            // The restore wrote a preference this module did not choose, so the launch
            // path's memory of what it last requested is stale for this symbol. Left
            // in place it would suppress the very `set` a later production launch
            // needs — the same silent occupancy loss the launch-path request exists to
            // prevent, reintroduced by a cache.
            seg_forget_launch_carveout(slot.entry);
        }
        // Released AFTER the restores, so the launch path cannot observe a window in
        // which nobody owns the preference and the priors are not yet back.
        SEG_CARVEOUT_PLANS_ALIVE.fetch_sub(1, std::sync::atomic::Ordering::AcqRel);
    }
}

/// The four launch quantities every family shares, read out of whichever
/// descriptor variant the setup carries.
struct SegGeometry {
    k: u32,
    logical_rows: u32,
    /// `true` when the descriptor is the device-program twin.
    progptr: bool,
}

fn seg_geometry(desc: &BwdSegLaunchDesc) -> SegGeometry {
    match desc {
        BwdSegLaunchDesc::Inline(desc) => SegGeometry {
            k: u32::from(desc.k),
            logical_rows: desc.logical_rows,
            progptr: false,
        },
        BwdSegLaunchDesc::ProgPtr(desc) => SegGeometry {
            k: u32::from(desc.k),
            logical_rows: desc.logical_rows,
            progptr: true,
        },
    }
}

/// §3's geometry: one 32-row tile per block, `k` warps per block, the epilogue
/// plane in dynamic shared memory.
fn seg_launch_config<'a>(
    geometry: &SegGeometry,
    epilogue: BwdSegEpilogue,
    context: &'a ProverContext,
) -> CudaLaunchConfig<'a> {
    assert!(
        geometry.k >= 1 && geometry.k <= BWD_SEG_MAX_K as u32,
        "segmented lean VM list count k={} is outside 1..={BWD_SEG_MAX_K}; `lower_bwd_seg` is the only legal source of this value",
        geometry.k
    );
    assert!(
        geometry.logical_rows > 0,
        "segmented lean VM launch has no rows; `lower_bwd_seg` rejects a zero row count"
    );
    CudaLaunchConfig::builder()
        .grid_dim(geometry.logical_rows.div_ceil(WARP_SIZE))
        .block_dim(geometry.k * WARP_SIZE)
        .dynamic_smem_bytes(bwd_seg_epilogue_smem_bytes(epilogue, geometry.k))
        .stream(context.get_exec_stream())
        .build()
}

/// The inline-program family's symbol for one `(regime, coefficient loader,
/// epilogue)` triple.
fn seg_inline_symbol(
    regime: BwdRegime,
    coeff: CoeffMode,
    epilogue: BwdSegEpilogue,
) -> GkrBwdSegInlineSignature {
    match (regime, coeff, epilogue) {
        (BwdRegime::R0, CoeffMode::Constant, BwdSegEpilogue::Staged) => {
            ab_gkr_bwd_seg_r0_const_epi_staged_kernel
        }
        (BwdRegime::R0, CoeffMode::Constant, BwdSegEpilogue::Plane) => {
            ab_gkr_bwd_seg_r0_const_epi_plane_kernel
        }
        (BwdRegime::R0, CoeffMode::Constant, BwdSegEpilogue::Wide) => {
            ab_gkr_bwd_seg_r0_const_epi_wide_kernel
        }
        (BwdRegime::R0, CoeffMode::DevPtr, BwdSegEpilogue::Staged) => {
            ab_gkr_bwd_seg_r0_ptr_epi_staged_kernel
        }
        (BwdRegime::R0, CoeffMode::DevPtr, BwdSegEpilogue::Plane) => {
            ab_gkr_bwd_seg_r0_ptr_epi_plane_kernel
        }
        (BwdRegime::R0, CoeffMode::DevPtr, BwdSegEpilogue::Wide) => {
            ab_gkr_bwd_seg_r0_ptr_epi_wide_kernel
        }
        (BwdRegime::Ext, CoeffMode::Constant, BwdSegEpilogue::Staged) => {
            ab_gkr_bwd_seg_cont_const_epi_staged_kernel
        }
        (BwdRegime::Ext, CoeffMode::Constant, BwdSegEpilogue::Plane) => {
            ab_gkr_bwd_seg_cont_const_epi_plane_kernel
        }
        (BwdRegime::Ext, CoeffMode::Constant, BwdSegEpilogue::Wide) => {
            ab_gkr_bwd_seg_cont_const_epi_wide_kernel
        }
        (BwdRegime::Ext, CoeffMode::DevPtr, BwdSegEpilogue::Staged) => {
            ab_gkr_bwd_seg_cont_ptr_epi_staged_kernel
        }
        (BwdRegime::Ext, CoeffMode::DevPtr, BwdSegEpilogue::Plane) => {
            ab_gkr_bwd_seg_cont_ptr_epi_plane_kernel
        }
        (BwdRegime::Ext, CoeffMode::DevPtr, BwdSegEpilogue::Wide) => {
            ab_gkr_bwd_seg_cont_ptr_epi_wide_kernel
        }
    }
}

/// The device-program family's symbol. Only the continuation regime and only the
/// `const` coefficient loader are instantiated: this family exists to measure ONE
/// axis (§5's param-space-versus-device-memory program), so the others would be
/// code with no comparison point.
fn seg_progptr_symbol(epilogue: BwdSegEpilogue) -> GkrBwdSegProgPtrSignature {
    match epilogue {
        BwdSegEpilogue::Staged => ab_gkr_bwd_seg_cont_const_progptr_epi_staged_kernel,
        BwdSegEpilogue::Plane => ab_gkr_bwd_seg_cont_const_progptr_epi_plane_kernel,
        BwdSegEpilogue::Wide => ab_gkr_bwd_seg_cont_const_progptr_epi_wide_kernel,
    }
}

/// Whether the `(regime, program source, coefficient loader)` triple HAS a
/// compiled kernel.
///
/// The ONE statement of the instantiation matrix, because two paths need the same
/// answer: launching a triple with no symbol, and ASKING ABOUT one. The occupancy
/// helper answering an R0 or `ptr` device-program query with the cont/const
/// kernel's number would feed Task 9's report a measurement of a different kernel
/// than the one it asked about, which is worse than a failed launch.
fn seg_family_is_instantiated(regime: BwdRegime, program: ProgramMode, coeff: CoeffMode) -> bool {
    match program {
        // Every (regime, loader) pair is compiled for the by-value program.
        ProgramMode::Inline => true,
        // The device-program family exists to measure ONE axis (§5's
        // param-space-versus-device-memory program), so the other cells would be
        // code with no comparison point.
        ProgramMode::DevPtr => regime == BwdRegime::Ext && coeff == CoeffMode::Constant,
    }
}

/// Reject an uninstantiated triple — a panic, matching how the rest of this module
/// rejects a launch geometry no `lower_bwd_seg` output can produce. Both the launch
/// path and the occupancy path go through here, so they cannot diverge on which
/// cells exist.
fn assert_seg_family_is_instantiated(regime: BwdRegime, program: ProgramMode, coeff: CoeffMode) {
    assert!(
        seg_family_is_instantiated(regime, program, coeff),
        "only the continuation regime with the const coefficient loader is instantiated for the \
         device-program family (spec §5: it measures the program source axis alone); asked for \
         {regime:?} with the {coeff:?} coefficient loader"
    );
}

/// Launch the exact `(regime, program source, coefficient loader, epilogue)`
/// executor for this setup. Enqueue-only.
///
/// `regime` and `coeff` are the caller's because [`BwdSegSetup`] carries neither:
/// lowering takes them as inputs and keeps only what a launch must UPLOAD. The
/// program source is not a parameter — the descriptor variant IS it.
pub(crate) fn launch_bwd_seg(
    setup: &BwdSegSetup,
    regime: BwdRegime,
    coeff: CoeffMode,
    epilogue: BwdSegEpilogue,
    context: &ProverContext,
) -> CudaResult<()> {
    let geometry = seg_geometry(&setup.desc);
    let config = seg_launch_config(&geometry, epilogue, context);
    let dynamic = bwd_seg_epilogue_smem_bytes(epilogue, geometry.k);
    match &setup.desc {
        BwdSegLaunchDesc::Inline(desc) => {
            if coeff == CoeffMode::DevPtr {
                assert!(
                    !desc.coefficients.is_null(),
                    "the ptr coefficient loader needs `desc.coefficients` patched to the uploaded bank; \
                     lowering leaves it null on purpose"
                );
            }
            let function = GkrBwdSegInlineFunction(seg_inline_symbol(regime, coeff, epilogue));
            seg_apply_launch_carveout(function.as_ptr(), geometry.k, dynamic);
            function.launch(&config, &GkrBwdSegInlineArguments::new(**desc))
        }
        BwdSegLaunchDesc::ProgPtr(desc) => {
            // The descriptor variant IS the program source, so this is the triple.
            assert_seg_family_is_instantiated(regime, ProgramMode::DevPtr, coeff);
            assert!(
                desc.program.is_null() == (desc.program_words == 0),
                "the device program pointer must be patched to the uploaded stream; lowering leaves \
                 it null and records the word count"
            );
            let function = GkrBwdSegProgPtrFunction(seg_progptr_symbol(epilogue));
            seg_apply_launch_carveout(function.as_ptr(), geometry.k, dynamic);
            function.launch(&config, &GkrBwdSegProgPtrArguments::new(**desc))
        }
    }
}

/// Blocks per SM the exact executor this setup would launch can hold — the
/// THEORETICAL occupancy ceiling, not an achieved one.
///
/// Answers for the triple ASKED ABOUT or not at all: the device-program family has
/// one compiled cell, and reporting its number for an R0 or `ptr` query would be a
/// measurement of a different kernel. Same guard as the launch path, by
/// construction.
pub(crate) fn bwd_seg_blocks_per_sm(
    regime: BwdRegime,
    program: ProgramMode,
    coeff: CoeffMode,
    epilogue: BwdSegEpilogue,
    k: u32,
) -> CudaResult<i32> {
    assert_seg_family_is_instantiated(regime, program, coeff);
    assert!(
        k >= 1 && k <= BWD_SEG_MAX_K as u32,
        "segmented lean VM occupancy list count outside 1..={BWD_SEG_MAX_K}"
    );
    let threads = (k * WARP_SIZE) as i32;
    let smem = bwd_seg_epilogue_smem_bytes(epilogue, k);
    match program {
        ProgramMode::Inline => era_cudart::occupancy::max_active_blocks_per_multiprocessor(
            &GkrBwdSegInlineFunction(seg_inline_symbol(regime, coeff, epilogue)),
            threads,
            smem,
        ),
        ProgramMode::DevPtr => era_cudart::occupancy::max_active_blocks_per_multiprocessor(
            &GkrBwdSegProgPtrFunction(seg_progptr_symbol(epilogue)),
            threads,
            smem,
        ),
    }
}

// ── Task 9 Stage B: the AccPlacement rungs ──────────────────────────────────
//
// Design section 6's register fallback ladder, compiled ON the Stage-A winner
// (`plane` epilogue, `const` loader) and nowhere else. Deliberately a SEPARATE,
// narrow API rather than a placement parameter threaded through the launchers
// above: the fifteen release symbols have exactly one placement, and widening
// their signatures would make every call site state a constant.

declare_bwd_seg_kernel!(
    ab_gkr_bwd_seg_r0_const_epi_plane_acc2smem_kernel,
    BwdSegDesc
);
declare_bwd_seg_kernel!(
    ab_gkr_bwd_seg_r0_const_epi_plane_accbothsmem_kernel,
    BwdSegDesc
);
declare_bwd_seg_kernel!(
    ab_gkr_bwd_seg_cont_const_epi_plane_acc2smem_kernel,
    BwdSegDesc
);
declare_bwd_seg_kernel!(
    ab_gkr_bwd_seg_cont_const_epi_plane_accbothsmem_kernel,
    BwdSegDesc
);

/// Where a launch keeps its two accumulators between terms (design §6's ladder).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BwdSegAccPlacement {
    /// (b): `acc_c2` per thread in shared memory.
    AccC2Smem,
    /// (c): both accumulators per thread in shared memory.
    AccBothSmem,
}

impl BwdSegAccPlacement {
    /// Accumulators this placement keeps in shared memory, per thread.
    fn slots(self) -> usize {
        match self {
            Self::AccC2Smem => 1,
            Self::AccBothSmem => 2,
        }
    }

    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::AccC2Smem => "acc2smem",
            Self::AccBothSmem => "accbothsmem",
        }
    }
}

/// Shared-memory bytes the per-thread accumulator carveout needs at `k` warps.
///
/// MIRROR of `bwd_seg_acc_smem_bytes` in `segmented_vm.cuh`, and mirrored for the
/// same reason [`bwd_seg_epilogue_smem_bytes`] is: it is a launch argument, so a
/// disagreement is an out-of-bounds shared access rather than a build error.
pub(crate) fn bwd_seg_acc_smem_bytes(placement: BwdSegAccPlacement, k: u32) -> usize {
    placement.slots() * size_of::<E4>() * k as usize * WARP_SIZE as usize
}

/// Total dynamic shared memory of an AccPlacement rung: the winning epilogue's
/// plane, then the carveout — the same order the kernel addresses them in.
pub(crate) fn bwd_seg_acc_dynamic_smem_bytes(placement: BwdSegAccPlacement, k: u32) -> usize {
    bwd_seg_epilogue_smem_bytes(BWD_SEG_ACC_RUNG_EPILOGUE, k) + bwd_seg_acc_smem_bytes(placement, k)
}

/// The epilogue the rungs are compiled on — Stage A's winner.
pub(crate) const BWD_SEG_ACC_RUNG_EPILOGUE: BwdSegEpilogue = BwdSegEpilogue::Plane;

fn seg_acc_symbol(regime: BwdRegime, placement: BwdSegAccPlacement) -> GkrBwdSegInlineSignature {
    match (regime, placement) {
        (BwdRegime::R0, BwdSegAccPlacement::AccC2Smem) => {
            ab_gkr_bwd_seg_r0_const_epi_plane_acc2smem_kernel
        }
        (BwdRegime::R0, BwdSegAccPlacement::AccBothSmem) => {
            ab_gkr_bwd_seg_r0_const_epi_plane_accbothsmem_kernel
        }
        (BwdRegime::Ext, BwdSegAccPlacement::AccC2Smem) => {
            ab_gkr_bwd_seg_cont_const_epi_plane_acc2smem_kernel
        }
        (BwdRegime::Ext, BwdSegAccPlacement::AccBothSmem) => {
            ab_gkr_bwd_seg_cont_const_epi_plane_accbothsmem_kernel
        }
    }
}

/// Launch one AccPlacement rung. Enqueue-only, and `const`-loader only: the rung
/// reads this lineage's `__constant__` bank, so a setup lowered for
/// [`CoeffMode::DevPtr`] has no kernel here.
pub(crate) fn launch_bwd_seg_acc(
    setup: &BwdSegSetup,
    regime: BwdRegime,
    placement: BwdSegAccPlacement,
    context: &ProverContext,
) -> CudaResult<()> {
    let BwdSegLaunchDesc::Inline(desc) = &setup.desc else {
        panic!("the AccPlacement rungs are compiled on the by-value program only")
    };
    let geometry = seg_geometry(&setup.desc);
    let dynamic = bwd_seg_acc_dynamic_smem_bytes(placement, geometry.k);
    let config = CudaLaunchConfig::builder()
        .grid_dim(geometry.logical_rows.div_ceil(WARP_SIZE))
        .block_dim(geometry.k * WARP_SIZE)
        .dynamic_smem_bytes(dynamic)
        .stream(context.get_exec_stream())
        .build();
    let function = GkrBwdSegInlineFunction(seg_acc_symbol(regime, placement));
    // The rungs carry the accumulator carveout on TOP of the epilogue's planes, so
    // their demand is the larger of the family — the arm that most needs the request.
    seg_apply_launch_carveout(function.as_ptr(), geometry.k, dynamic);
    function.launch(&config, &GkrBwdSegInlineArguments::new(**desc))
}

/// Blocks per SM of one AccPlacement rung, at its own total carveout.
pub(crate) fn bwd_seg_acc_blocks_per_sm(
    regime: BwdRegime,
    placement: BwdSegAccPlacement,
    k: u32,
) -> CudaResult<i32> {
    assert!(
        k >= 1 && k <= BWD_SEG_MAX_K as u32,
        "segmented lean VM occupancy list count outside 1..={BWD_SEG_MAX_K}"
    );
    era_cudart::occupancy::max_active_blocks_per_multiprocessor(
        &GkrBwdSegInlineFunction(seg_acc_symbol(regime, placement)),
        (k * WARP_SIZE) as i32,
        bwd_seg_acc_dynamic_smem_bytes(placement, k),
    )
}

/// The device entry point of one AccPlacement rung, for `cudaFuncGetAttributes`.
pub(crate) fn bwd_seg_acc_entry_point(
    regime: BwdRegime,
    placement: BwdSegAccPlacement,
) -> *const std::ffi::c_void {
    GkrBwdSegInlineFunction(seg_acc_symbol(regime, placement)).as_ptr()
}

/// The fold-weight prelude's device entry point. Added because the macro's
/// `…Function` wrapper holds its signature in a PRIVATE tuple field, so a caller
/// in another module cannot construct one — the same reason [`bwd_seg_entry_point`]
/// exists. With this, entry-point coverage is 15 executors + 4 rungs + 1 prelude =
/// the full 20-symbol family.
pub(crate) fn bwd_seg_prelude_entry_point() -> *const std::ffi::c_void {
    GkrBwdSegBuildFoldWeightsFunction(ab_gkr_bwd_seg_build_fold_weights_kernel).as_ptr()
}

/// The device entry point of the exact `(regime, program source, coefficient
/// loader, epilogue)` executor — what `cudaFuncGetAttributes` and a profiler
/// filter need, and nothing that can launch.
///
/// It exists because the macro-generated `…Function` wrappers hold their
/// signature in a PRIVATE tuple field: a caller in another module cannot
/// construct one, so without this it would have to restate the fifteen-way symbol
/// match — a second statement of the instantiation matrix, which is exactly what
/// [`seg_family_is_instantiated`] exists to prevent. Same guard as the launch and
/// occupancy paths, by construction.
pub(crate) fn bwd_seg_entry_point(
    regime: BwdRegime,
    program: ProgramMode,
    coeff: CoeffMode,
    epilogue: BwdSegEpilogue,
) -> *const std::ffi::c_void {
    assert_seg_family_is_instantiated(regime, program, coeff);
    match program {
        ProgramMode::Inline => {
            GkrBwdSegInlineFunction(seg_inline_symbol(regime, coeff, epilogue)).as_ptr()
        }
        ProgramMode::DevPtr => GkrBwdSegProgPtrFunction(seg_progptr_symbol(epilogue)).as_ptr(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The four sizes `segmented_vm.cuh`'s `static_assert`s pin, restated here
    /// because the two halves are compared by nothing at build time.
    #[test]
    fn seg_epilogue_smem_matches_the_cuda_mirror() {
        assert_eq!(bwd_seg_epilogue_smem_bytes(BwdSegEpilogue::Staged, 1), 0);
        assert_eq!(bwd_seg_epilogue_smem_bytes(BwdSegEpilogue::Plane, 1), 0);
        assert_eq!(bwd_seg_epilogue_smem_bytes(BwdSegEpilogue::Wide, 1), 0);
        let k = BWD_SEG_MAX_K as u32;
        assert_eq!(
            bwd_seg_epilogue_smem_bytes(BwdSegEpilogue::Staged, k),
            1_024
        );
        assert_eq!(
            bwd_seg_epilogue_smem_bytes(BwdSegEpilogue::Plane, k),
            15_872
        );
        assert_eq!(bwd_seg_epilogue_smem_bytes(BwdSegEpilogue::Wide, k), 31_744);
        // Every variant stays inside the 48 KB a block gets without an opt-in
        // carveout, which is what lets the launcher pass these as plain dynamic
        // shared memory.
        assert!(bwd_seg_epilogue_smem_bytes(BwdSegEpilogue::Wide, k) <= 48 * 1_024);
        // The staged plane pair does not grow with k; that is its whole point.
        assert_eq!(
            bwd_seg_epilogue_smem_bytes(BwdSegEpilogue::Staged, 2),
            bwd_seg_epilogue_smem_bytes(BwdSegEpilogue::Staged, k)
        );
    }

    /// The instantiation matrix, over EVERY `(regime, program, loader)` triple —
    /// the twelve inline symbols plus the device-program family's single cell.
    #[test]
    fn seg_family_matrix_covers_every_triple() {
        for regime in [BwdRegime::R0, BwdRegime::Ext] {
            for coeff in [CoeffMode::Constant, CoeffMode::DevPtr] {
                assert!(
                    seg_family_is_instantiated(regime, ProgramMode::Inline, coeff),
                    "{regime:?}/{coeff:?} is one of the twelve inline symbols"
                );
            }
        }
        assert!(seg_family_is_instantiated(
            BwdRegime::Ext,
            ProgramMode::DevPtr,
            CoeffMode::Constant
        ));
        for (regime, coeff) in [
            (BwdRegime::R0, CoeffMode::Constant),
            (BwdRegime::R0, CoeffMode::DevPtr),
            (BwdRegime::Ext, CoeffMode::DevPtr),
        ] {
            assert!(
                !seg_family_is_instantiated(regime, ProgramMode::DevPtr, coeff),
                "{regime:?}/{coeff:?} has no device-program symbol"
            );
        }
    }

    /// The occupancy helper must REJECT a triple with no symbol rather than answer
    /// with the one compiled device-program kernel's number. The guard runs ahead of
    /// any CUDA call, so these need no device.
    #[test]
    #[should_panic(expected = "device-program family")]
    fn seg_occupancy_rejects_an_r0_device_program_query() {
        let _ = bwd_seg_blocks_per_sm(
            BwdRegime::R0,
            ProgramMode::DevPtr,
            CoeffMode::Constant,
            BwdSegEpilogue::Staged,
            4,
        );
    }

    #[test]
    #[should_panic(expected = "device-program family")]
    fn seg_occupancy_rejects_a_ptr_loader_device_program_query() {
        let _ = bwd_seg_blocks_per_sm(
            BwdRegime::Ext,
            ProgramMode::DevPtr,
            CoeffMode::DevPtr,
            BwdSegEpilogue::Staged,
            4,
        );
    }

    /// The attribute path shares the occupancy path's guard, so it cannot answer
    /// about a kernel that was never instantiated either.
    #[test]
    #[should_panic(expected = "device-program family")]
    fn seg_entry_point_rejects_an_r0_device_program_query() {
        let _ = bwd_seg_entry_point(
            BwdRegime::R0,
            ProgramMode::DevPtr,
            CoeffMode::Constant,
            BwdSegEpilogue::Staged,
        );
    }

    /// The occupancy formula must reproduce results §2.5's MEASURED column, or the
    /// whole demand table is fiction.
    #[test]
    fn seg_register_bound_blocks_reproduce_the_measured_column() {
        const K: [u32; 7] = [1, 2, 4, 8, 16, 24, 32];
        let at = |registers: u32| K.map(|k| bwd_seg_register_bound_blocks_per_sm(registers, k));
        assert_eq!(at(40), [24, 24, 12, 6, 3, 2, 1], "R40 plane");
        assert_eq!(at(50), [24, 18, 9, 4, 2, 1, 1], "R50 cont");
        // The pins this pass installs, whose rows the demand table needs.
        assert_eq!(at(48)[2], 10, "R48 at k=4");
        assert_eq!(at(48)[1], 20, "R48 at k=2");
        assert_eq!(at(56)[5], 1, "R56 at k=24");
        assert_eq!(at(64)[0], 24, "R64 at k=1");
        assert_eq!(at(64)[2], 8, "R64 at k=4");
    }

    #[test]
    fn seg_expected_buckets_match_the_specs_generated_rows() {
        let kib = |n: usize| n * 1024;
        assert_eq!(
            bwd_seg_expected_smem_bucket_bytes(6_144),
            kib(8),
            "staged R40 k16"
        );
        assert_eq!(
            bwd_seg_expected_smem_bucket_bytes(4_096),
            kib(8),
            "staged R40 k24"
        );
        assert_eq!(
            bwd_seg_expected_smem_bucket_bytes(12_800),
            kib(16),
            "plane natural k24"
        );
        assert_eq!(
            bwd_seg_expected_smem_bucket_bytes(23_040),
            kib(32),
            "cont natural k4"
        );
        assert_eq!(
            bwd_seg_expected_smem_bucket_bytes(25_600),
            kib(32),
            "cont R48 k4"
        );
        assert_eq!(
            bwd_seg_expected_smem_bucket_bytes(30_720),
            kib(32),
            "cont R40 k4"
        );
        assert_eq!(
            bwd_seg_expected_smem_bucket_bytes(25_088),
            kib(32),
            "acc2 k24, both regimes"
        );
        assert_eq!(
            bwd_seg_expected_smem_bucket_bytes(49_152),
            kib(64),
            "wide R40 k=4..24 — ZERO reclaim"
        );
        assert_eq!(
            bwd_seg_expected_smem_bucket_bytes(32_768),
            kib(32),
            "wide R40 k32"
        );
        assert_eq!(
            bwd_seg_expected_smem_bucket_bytes(66_560),
            kib(100),
            "accboth R0 pin48 k4"
        );
        assert_eq!(
            bwd_seg_expected_smem_bucket_bytes(71_680),
            kib(100),
            "accboth R0 pin48 k2"
        );
    }

    /// `wide`'s "exactly 49,152 B" is a 40-PIN IDENTITY, not a property of the
    /// epilogue: dynamic bytes are `2(k-1)*512 ~= 1024(k-1)`, so with the reserve the
    /// per-block figure is ~`1024k` and at R40 the block count is exactly `48/k`.
    #[test]
    fn seg_wide_zero_reclaim_is_a_forty_pin_identity() {
        let reserve = bwd_seg_reserved_smem_bytes_per_block();
        let at = |registers: u32, k: u32| {
            (bwd_seg_epilogue_smem_bytes(BwdSegEpilogue::Wide, k) + reserve)
                * bwd_seg_register_bound_blocks_per_sm(registers, k) as usize
        };
        for k in [4u32, 8, 16, 24] {
            assert_eq!(
                at(40, k),
                49_152,
                "wide at R40 k={k} must be exactly 48 KiB"
            );
        }
        // At looser pins the demand differs AND so does the bucket.
        assert_eq!(at(48, 16), 32_768, "R48 wide k16");
        assert_eq!(at(48, 24), 24_576, "R48 wide k24");
        assert_eq!(at(50, 24), 24_576, "natural wide k24");
    }

    /// The rungs need their own demand rows because `bwd_seg_acc_smem_bytes` is
    /// non-zero at every `k` including 1, where the plain executors are 0.
    #[test]
    fn seg_acc_rung_demand_is_non_zero_at_k_one() {
        assert_eq!(
            bwd_seg_acc_smem_bytes(BwdSegAccPlacement::AccC2Smem, 1),
            512
        );
        assert_eq!(
            bwd_seg_acc_smem_bytes(BwdSegAccPlacement::AccBothSmem, 1),
            1_024
        );
        assert_eq!(
            bwd_seg_acc_dynamic_smem_bytes(BwdSegAccPlacement::AccC2Smem, 24),
            24_064
        );
        assert_eq!(
            bwd_seg_epilogue_smem_bytes(BwdSegEpilogue::Plane, 24),
            11_776
        );
    }

    /// The predeclared reference-clock bucket must cover EVERY pin-decision cell at
    /// EVERY level, or the level comparison is starving one of them. Re-derived here
    /// from the same formula the demand table uses, so a future edit to the decision
    /// set or the pin ladder breaks this test rather than a published number.
    #[test]
    fn the_reference_clock_bucket_covers_every_decision_cell() {
        let reserve = bwd_seg_reserved_smem_bytes_per_block();
        let mut worst = 0usize;
        for pin in [40u32, 48, 50, 56] {
            for k in [1u32, 2, 4, 8, 16, 24, 32] {
                let demand = bwd_seg_register_bound_blocks_per_sm(pin, k) as usize
                    * (bwd_seg_epilogue_smem_bytes(BwdSegEpilogue::Plane, k) + reserve);
                worst = worst.max(demand);
                assert!(
                    demand <= SEG_REFERENCE_CLOCK_BUCKET_BYTES,
                    "plane pin{pin} K{k} demands {demand} B > the fixed reference-clock \
                     bucket {SEG_REFERENCE_CLOCK_BUCKET_BYTES} B"
                );
            }
        }
        // And it is the SMALLEST supported bucket that does: 32 KiB would not hold the
        // worst cell, so 64 KiB is the right predeclared value rather than a round one.
        assert_eq!(
            worst, 36_864,
            "the worst plane decision cell is R40 K=2 (24 register-bound blocks x \
             (512 B epilogue + 1,024 B reserve))"
        );
        assert!(worst > 32 * 1024, "32 KiB would starve the worst cell");
        assert_eq!(
            bwd_seg_expected_smem_bucket_bytes(worst),
            SEG_REFERENCE_CLOCK_BUCKET_BYTES
        );
    }

    /// One symbol serves every `K`, so a pair's two arms can be the SAME pointer. The
    /// plan must hold ONE entry for it, or the restore reinstalls the override.
    #[test]
    // Shares the process-global carveout state (the preference itself and the
    // plans-alive counter `the_launch_path_owns_the_carveout_unless_a_plan_does`
    // reads), so it cannot run beside another test that touches either.
    #[serial_test::serial]
    fn a_same_symbol_pair_yields_one_deduped_entry() {
        let entry = bwd_seg_entry_point(
            BwdRegime::Ext,
            ProgramMode::Inline,
            CoeffMode::Constant,
            BwdSegEpilogue::Plane,
        );
        let shape = |k: u32| CarveoutShape {
            entry,
            dynamic_smem_bytes: bwd_seg_epilogue_smem_bytes(BwdSegEpilogue::Plane, k),
            target_blocks_per_sm: bwd_seg_register_bound_blocks_per_sm(50, k),
            label: "same-symbol",
        };
        let prior = bwd_seg_query_carveout(entry);
        {
            let mut plan =
                CarveoutPlan::for_pair(CarveoutMode::CommonBucket, shape(8), shape(4), false);
            plan.apply();
            assert_eq!(plan.entries.len(), 1, "two arms, one symbol, ONE entry");
            let requested = plan
                .requested_pct_of(entry)
                .expect("the deduped entry carries the request");
            // The restore assertion below is vacuous unless the override was really
            // INSTALLED: a plan that silently set nothing would also "restore" the
            // prior. Read it back through the driver while the plan is alive.
            assert_eq!(
                bwd_seg_query_carveout(entry),
                requested,
                "the plan must install the requested preference while it lives"
            );
            assert_ne!(
                requested, prior,
                "the fixture must actually CHANGE the preference, or neither this \
                 assertion nor the restore below proves anything"
            );
        }
        assert_eq!(
            bwd_seg_query_carveout(entry),
            prior,
            "the restore must return the EXACT prior value, not the override"
        );
    }

    /// `apply` must be unwind-safe PER SLOT: when it panics part-way, the plan
    /// restores exactly the slots whose priors it captured, and touches nothing else.
    ///
    /// This is a DEVICE test and it has to be. The only way to fail `apply` mid-loop
    /// without inserting a fake indirection layer into production code is to hand
    /// `cudaFuncGetAttributes` an address that is not a registered `__global__` entry
    /// point, and that needs a live runtime to reject it.
    ///
    /// It uses the `wide` symbol rather than `plane` so it cannot race
    /// [`a_same_symbol_pair_yields_one_deduped_entry`] over one preference when the
    /// suite runs multi-threaded.
    #[test]
    // Shares the process-global carveout state (the preference itself and the
    // plans-alive counter `the_launch_path_owns_the_carveout_unless_a_plan_does`
    // reads), so it cannot run beside another test that touches either.
    #[serial_test::serial]
    fn a_mid_apply_unwind_restores_the_queried_prefix_and_nothing_else() {
        static NOT_A_KERNEL: u8 = 0;
        let good = bwd_seg_entry_point(
            BwdRegime::Ext,
            ProgramMode::Inline,
            CoeffMode::Constant,
            BwdSegEpilogue::Wide,
        );
        // A host data address: `cudaFuncGetAttributes` fails to find it in the
        // registered-function table, so `apply` unwinds on the SECOND slot — after the
        // first is already overridden.
        let bogus = &NOT_A_KERNEL as *const u8 as *const std::ffi::c_void;
        let prior = bwd_seg_query_carveout(good);
        let mut plan = CarveoutPlan::for_solo(
            CarveoutMode::CommonBucket,
            CarveoutShape {
                entry: good,
                dynamic_smem_bytes: bwd_seg_epilogue_smem_bytes(BwdSegEpilogue::Wide, 8),
                target_blocks_per_sm: bwd_seg_register_bound_blocks_per_sm(50, 8),
                label: "unwind-probe",
            },
            false,
        );
        CarveoutPlan::push_unique(&mut plan.entries, bogus, 50);
        assert_eq!(
            plan.entries.len(),
            2,
            "one real slot then one that will fail"
        );

        let hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| plan.apply()));
        std::panic::set_hook(hook);
        assert!(
            outcome.is_err(),
            "the bogus entry point must make `apply` panic"
        );

        assert!(
            plan.entries[0].prior_pct.is_some(),
            "slot 0's prior was captured, so it IS in the restore set"
        );
        assert!(
            plan.entries[1].prior_pct.is_none(),
            "slot 1 unwound before its prior existed, so it is NOT in the restore set \
             and drop must not write a default over it"
        );
        assert_eq!(
            bwd_seg_query_carveout(good),
            plan.entries[0].requested_pct,
            "slot 0 is genuinely overridden at the moment of the unwind — which is what \
             makes the restore below load-bearing rather than decorative"
        );

        drop(plan);
        assert_eq!(
            bwd_seg_query_carveout(good),
            prior,
            "the unwind path must still restore the exact prior of every touched slot"
        );
        // The rejected query latched a non-sticky error on the runtime; clear it so no
        // later `cudaGetLastError` in this process inherits this test's failure.
        let _ = era_cudart::error::get_last_error();
    }

    /// The launch path asks for its own carveout, and a live [`CarveoutPlan`] takes
    /// that away from it.
    ///
    /// Both halves matter and for opposite reasons. Without the request, a production
    /// launch pays +1.23 % at the committed policy's `K = 16` for a preference nobody
    /// set. Without the deferral, `CarveoutMode::Off` — the control arm whose whole
    /// definition is "no preference set anywhere" — would silently acquire one from
    /// the launcher, and every carveout column measured against it would be measuring
    /// this function.
    #[test]
    #[serial_test::serial]
    fn the_launch_path_owns_the_carveout_unless_a_plan_does() {
        // The staged R0 symbol: no other test in this module touches it, so the
        // process-global preference cannot be raced.
        let entry = bwd_seg_entry_point(
            BwdRegime::R0,
            ProgramMode::Inline,
            CoeffMode::Constant,
            BwdSegEpilogue::Staged,
        );
        let k = 8;
        let dynamic = bwd_seg_epilogue_smem_bytes(BwdSegEpilogue::Staged, k);
        let expected = bwd_seg_carveout_pct(
            bwd_seg_register_bound_blocks_per_sm(bwd_seg_entry_registers(entry), k),
            dynamic,
        );

        seg_forget_launch_carveout(entry);
        assert_eq!(
            seg_apply_launch_carveout(entry, k, dynamic),
            Some(expected),
            "with no plan alive the launch path requests the register-bound partition"
        );
        assert_eq!(bwd_seg_query_carveout(entry), expected);

        // An `Off` plan writes no preference at all, and the launch path must still
        // stand down: that mode's definition is "nothing set anywhere".
        {
            let _plan = CarveoutPlan::for_solo(
                CarveoutMode::Off,
                CarveoutShape {
                    entry,
                    dynamic_smem_bytes: dynamic,
                    target_blocks_per_sm: 1,
                    label: "deferral-probe",
                },
                false,
            );
            assert_eq!(
                seg_apply_launch_carveout(entry, k, dynamic),
                None,
                "a live plan owns the preference — even `Off`, which sets none at all"
            );
        }
        assert!(
            seg_launch_carveout_cache()
                .lock()
                .expect("carveout cache")
                .contains_key(&(entry as usize)),
            "an `Off` plan touched no preference, so the cache still describes the driver"
        );

        // A plan that DOES write one must invalidate the cache when it restores: the
        // restored value is not what the launch path asked for, so a surviving cache
        // entry would suppress the next request and reintroduce exactly the occupancy
        // loss the request exists to prevent.
        {
            let mut plan = CarveoutPlan::for_solo(
                CarveoutMode::FixedBucket(64 * 1024),
                CarveoutShape {
                    entry,
                    dynamic_smem_bytes: dynamic,
                    target_blocks_per_sm: 1,
                    label: "invalidation-probe",
                },
                false,
            );
            plan.apply();
            assert_ne!(
                bwd_seg_query_carveout(entry),
                expected,
                "the probe must actually move the preference, or it proves nothing"
            );
        }
        assert_eq!(
            bwd_seg_query_carveout(entry),
            expected,
            "the plan restored the prior it found, which is the launch path's request"
        );
        assert!(
            !seg_launch_carveout_cache()
                .lock()
                .expect("carveout cache")
                .contains_key(&(entry as usize)),
            "a plan's drop must invalidate the launch path's cache for every entry it touched"
        );
        assert_eq!(
            seg_apply_launch_carveout(entry, k, dynamic),
            Some(expected),
            "and the launch path takes the preference back afterwards"
        );
    }

    /// `for_solo` must carry `for_pair`'s containment gate. The pin-decision set has
    /// SOLO cells, the requested pct is never itself a gate, and a solo cell over the
    /// fixed bucket would therefore under-request the reference clock's partition with
    /// nothing anywhere to say so.
    #[test]
    // Shares the process-global carveout state (the preference itself and the
    // plans-alive counter `the_launch_path_owns_the_carveout_unless_a_plan_does`
    // reads), so it cannot run beside another test that touches either.
    #[serial_test::serial]
    fn solo_fixed_bucket_gates_the_demand_against_the_bucket() {
        const BUCKET: usize = 8 * 1024;
        let reserve = bwd_seg_reserved_smem_bytes_per_block();
        let entry = bwd_seg_entry_point(
            BwdRegime::R0,
            ProgramMode::Inline,
            CoeffMode::Constant,
            BwdSegEpilogue::Plane,
        );
        // One block, so `demand == dynamic + reserve` and the boundary is exact.
        let shape = |dynamic: usize| CarveoutShape {
            entry,
            dynamic_smem_bytes: dynamic,
            target_blocks_per_sm: 1,
            label: "solo-gate",
        };

        // Exactly filling the bucket is legal: the gate is `<=`, not `<`. And the
        // request is the BUCKET's pct, not the demand's — that is the whole point of
        // `FixedBucket`, and it is why the two helpers must agree.
        let exact = CarveoutPlan::for_solo(
            CarveoutMode::FixedBucket(BUCKET),
            shape(BUCKET - reserve),
            false,
        );
        assert_eq!(
            exact.requested_pct_of(entry),
            Some(bwd_seg_carveout_pct_for_bucket(BUCKET)),
        );
        drop(exact);

        // One byte over is not.
        let over_demand = BUCKET + 1;
        let hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            CarveoutPlan::for_solo(
                CarveoutMode::FixedBucket(BUCKET),
                shape(over_demand - reserve),
                false,
            )
        }));
        std::panic::set_hook(hook);
        let message = *outcome
            .err()
            .expect("a solo demand over the fixed bucket must not be silently accepted")
            .downcast::<String>()
            .expect("a formatted assertion message");
        assert!(
            message.contains("SEG_REFERENCE_CLOCK_BUCKET_BYTES"),
            "the message must name what to re-derive, got {message:?}"
        );
        assert!(
            message.contains(&format!("{over_demand} B")),
            "the message must name the offending demand, got {message:?}"
        );
    }
}
