//! Launchers for the SEGMENTED lean VM (segmented-lean-VM design §3, §5, §6).
//!
//! The CUDA half is `native/prover/gkr/backward/segmented_vm.{cuh,cu}`. The
//! launch geometry is §3's and it is the whole reason this module exists as a
//! separate lineage from the cell-era [`launch_bwd_coeff`](super::launch_bwd_coeff):
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
//!      caller patches into the descriptor.
//!
//! This module launches; it stages nothing, allocates nothing, and reads no
//! device memory, so it adds no obligations to the GPU scheduling contract beyond
//! "everything above is enqueued on `exec_stream` before the launch".

// TASK 8's parity ladder and TASK 9's report are the first callers.
#![allow(dead_code)]

use std::mem::size_of;

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use era_cudart_sys::{cudaGetSymbolAddress, cuda_struct_and_stub};
use std::ffi::c_void;
use std::ptr::null_mut;
use std::sync::OnceLock;

use super::seg_desc::{BwdSegDesc, BwdSegProgPtrDesc, BWD_SEG_CONST_BANK, BWD_SEG_MAX_K};
use super::seg_lower::{BwdSegLaunchDesc, BwdSegSetup, CoeffMode, ProgramMode};
use crate::primitives::field::E4;
use crate::primitives::utils::WARP_SIZE;
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
}
