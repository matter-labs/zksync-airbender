//! CUDA launchers for the R0 and continuation backward VMs.

use std::ffi::c_void;
use std::mem::size_of;
use std::ptr::null_mut;

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use era_cudart_sys::{cudaGetSymbolAddress, cuda_struct_and_stub};
use gpu_core::primitives::field::E4;
use gpu_core::primitives::utils::WARP_SIZE;
use gpu_prover_context::ProverContext;

use super::seg_desc::{BwdSegDesc, BWD_SEG_FOLD_WEIGHT_SLOTS, BWD_SEG_MAX_K, BWD_SEG_OUTPUT_BANK};
use super::seg_lower::BwdSegSetup;

cuda_struct_and_stub! {
    static ab_gkr_bwd_seg_coeff_bank: [E4; BWD_SEG_OUTPUT_BANK];
}

pub(crate) fn bwd_seg_coeff_bank_device_ptr() -> *mut E4 {
    let mut ptr: *mut c_void = null_mut();
    // SAFETY: the Rust static is the stub for the matching CUDA symbol.
    unsafe {
        cudaGetSymbolAddress(
            &mut ptr,
            &ab_gkr_bwd_seg_coeff_bank as *const _ as *const c_void,
        )
    }
    .wrap()
    .expect("cudaGetSymbolAddress failed for ab_gkr_bwd_seg_coeff_bank");
    ptr.cast()
}

cuda_struct_and_stub! {
    static ab_gkr_bwd_seg_fold_weights: [E4; BWD_SEG_FOLD_WEIGHT_SLOTS];
}

fn bwd_seg_fold_weights_device_ptr() -> *mut E4 {
    let mut ptr: *mut c_void = null_mut();
    // SAFETY: the Rust static is the stub for the matching CUDA symbol.
    unsafe {
        cudaGetSymbolAddress(
            &mut ptr,
            &ab_gkr_bwd_seg_fold_weights as *const _ as *const c_void,
        )
    }
    .wrap()
    .expect("cudaGetSymbolAddress failed for ab_gkr_bwd_seg_fold_weights");
    ptr.cast()
}

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GkrBwdSeg,
    desc: BwdSegDesc,
);
cuda_kernel_declaration!(
    pub(crate) ab_gkr_bwd_seg_r0_const_epi_plane_kernel(desc: BwdSegDesc)
);
cuda_kernel_declaration!(
    pub(crate) ab_gkr_bwd_seg_cont_const_epi_plane_kernel(desc: BwdSegDesc)
);

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GkrBwdSegBuildFoldWeights,
    fold_weights: *mut E4,
    round: u32,
);
cuda_kernel_declaration!(
    pub(crate) ab_gkr_bwd_seg_build_fold_weights_kernel(fold_weights: *mut E4, round: u32)
);

/// The fold-weight bank one launch fills: the symbol address the launch passed
/// and the bytes its slots occupy. Returned so a caller that must account for a
/// launch's pointer arguments reuses the address that launch used instead of
/// resolving the symbol again.
pub(crate) type BwdSegFoldWeightSpan = (usize, usize);

pub(crate) fn launch_bwd_seg_build_fold_weights(
    round: u32,
    context: &ProverContext,
) -> CudaResult<BwdSegFoldWeightSpan> {
    assert!(round >= 1, "fold weights are continuation-only");
    let config = CudaLaunchConfig::builder()
        .grid_dim(1)
        .block_dim(WARP_SIZE)
        .stream(context.get_exec_stream())
        .build();
    let fold_weights = bwd_seg_fold_weights_device_ptr();
    #[cfg(all(
        any(test, feature = "task8_continuation_differential_test"),
        not(no_cuda)
    ))]
    crate::backward::task8_probe::task8_register_symbol(
        "bwd_seg_fold_weights",
        fold_weights as usize,
        BWD_SEG_FOLD_WEIGHT_SLOTS * size_of::<E4>(),
    );
    crate::backward::task8_enqueue_scope!(_task8, "fold-weight-build", Kernel, {
        use crate::backward::task8_probe::Task8Span;
        vec![
            Task8Span::symbol_read(
                "ab_gkr_main_layer_claim_point",
                0,
                round as usize * size_of::<E4>(),
            ),
            Task8Span::write(
                "bwd_seg_fold_weights",
                fold_weights as usize,
                BWD_SEG_FOLD_WEIGHT_SLOTS * size_of::<E4>(),
            ),
        ]
    });
    GkrBwdSegBuildFoldWeightsFunction(ab_gkr_bwd_seg_build_fold_weights_kernel).launch(
        &config,
        &GkrBwdSegBuildFoldWeightsArguments::new(fold_weights, round),
    )?;
    Ok((
        fold_weights as usize,
        BWD_SEG_FOLD_WEIGHT_SLOTS * size_of::<E4>(),
    ))
}

const fn plane_smem_bytes(k: u32) -> usize {
    k.saturating_sub(1) as usize * WARP_SIZE as usize * size_of::<E4>()
}

const _: () = {
    assert!(plane_smem_bytes(BWD_SEG_MAX_K as u32) == 7_680);
    assert!(plane_smem_bytes(BWD_SEG_MAX_K as u32) <= 48 * 1_024);
};

fn launch_config<'a>(desc: &BwdSegDesc, context: &'a ProverContext) -> CudaLaunchConfig<'a> {
    let k = u32::from(desc.k);
    assert!((1..=BWD_SEG_MAX_K as u32).contains(&k));
    assert!(desc.logical_rows > 0);
    CudaLaunchConfig::builder()
        .grid_dim(desc.logical_rows.div_ceil(WARP_SIZE))
        .block_dim(k * WARP_SIZE)
        .dynamic_smem_bytes(plane_smem_bytes(k))
        .stream(context.get_exec_stream())
        .build()
}

/// The pointer arguments one segmented-VM launch names, taken from the
/// descriptor it is about to hand the runtime: every live source column at its
/// own base, stride and row extent, every published column, the factored Eq
/// tables' active prefixes, the coefficient bank and fold-weight banks, and the
/// contribution buffer.
#[cfg(all(
    any(test, feature = "task8_continuation_differential_test"),
    not(no_cuda)
))]
fn task8_seg_spans(desc: &BwdSegDesc) -> Vec<crate::backward::task8_probe::Task8Span> {
    use super::seg_desc::{
        bwd_seg_lane_slot, BWD_COEFF_ORIGIN_READ_EXT, BWD_SEG_ADDR_COLUMN_BITS, BWD_SEG_ADDR_NONE,
    };
    use crate::backward::task8_probe::{task8_descriptor_sources, Task8Span};
    use crate::backward::{GKR_EQ_GROUP_TABLE_LEN, GKR_EQ_HIGH_SLOTS};

    let element = size_of::<E4>();
    let rows = desc.logical_rows as usize;
    let sources = task8_descriptor_sources(desc as *const BwdSegDesc as usize)
        .expect("a Task 8 segmented launch needs its descriptor's live source count");
    let column_of = |lane: u16| usize::from(lane) & ((1 << BWD_SEG_ADDR_COLUMN_BITS) - 1);
    let width_of = |slot: &super::seg_desc::BwdSegAddrSlot| {
        if slot.origin == BWD_COEFF_ORIGIN_READ_EXT {
            element
        } else {
            size_of::<gpu_core::primitives::field::BF>()
        }
    };
    let mut spans = Vec::with_capacity(2 * sources + 8);
    for record in &desc.source[..sources] {
        let slot = &desc.slot[bwd_seg_lane_slot(record.src)];
        if !slot.base.is_null() {
            let width = width_of(slot);
            spans.push(Task8Span::read(
                "source_column",
                slot.base as usize + column_of(record.src) * (width << slot.log2_stride),
                2 * rows * (1usize << record.delta) * width,
            ));
        }
        if record.cache != BWD_SEG_ADDR_NONE {
            let slot = &desc.slot[bwd_seg_lane_slot(record.cache)];
            if !slot.base.is_null() {
                let width = width_of(slot);
                spans.push(Task8Span::write(
                    "published_column",
                    slot.base as usize + column_of(record.cache) * (width << slot.log2_stride),
                    2 * rows * element,
                ));
            }
        }
    }
    if !desc.eq_low.is_null() {
        spans.push(Task8Span::read(
            "eq_low",
            desc.eq_low as usize,
            (1usize << desc.eq_sizes.low) * element,
        ));
    }
    for slot in 0..GKR_EQ_HIGH_SLOTS {
        let size = desc.eq_sizes.high[slot];
        spans.push(Task8Span::symbol_read(
            "ab_gkr_eq_high",
            slot * GKR_EQ_GROUP_TABLE_LEN * element,
            if size == 0 {
                element
            } else {
                (1usize << size) * element
            },
        ));
    }
    spans.push(Task8Span::symbol_region("ab_gkr_bwd_seg_coeff_bank"));
    spans.push(Task8Span::symbol_region("bwd_seg_fold_weights"));
    spans.push(Task8Span::write(
        "contributions",
        desc.contributions as usize,
        2 * rows.div_ceil(WARP_SIZE as usize) * element,
    ));
    spans
}

fn launch(
    setup: &BwdSegSetup,
    symbol: GkrBwdSegSignature,
    context: &ProverContext,
) -> CudaResult<()> {
    crate::backward::task8_enqueue_scope!(
        _task8,
        "segmented-round",
        Kernel,
        task8_seg_spans(setup)
    );
    GkrBwdSegFunction(symbol).launch(
        &launch_config(setup, context),
        &GkrBwdSegArguments::new(**setup),
    )
}

pub(crate) fn launch_bwd_seg_r0(setup: &BwdSegSetup, context: &ProverContext) -> CudaResult<()> {
    launch(setup, ab_gkr_bwd_seg_r0_const_epi_plane_kernel, context)
}

pub(crate) fn launch_bwd_seg_continuation(
    round: u32,
    setup: &BwdSegSetup,
    context: &ProverContext,
) -> CudaResult<BwdSegFoldWeightSpan> {
    let fold_weights = launch_bwd_seg_build_fold_weights(round, context)?;
    launch(setup, ab_gkr_bwd_seg_cont_const_epi_plane_kernel, context)?;
    Ok(fold_weights)
}

fn blocks_per_sm(symbol: GkrBwdSegSignature, k: u32) -> CudaResult<i32> {
    assert!((1..=BWD_SEG_MAX_K as u32).contains(&k));
    era_cudart::occupancy::max_active_blocks_per_multiprocessor(
        &GkrBwdSegFunction(symbol),
        (k * WARP_SIZE) as i32,
        plane_smem_bytes(k),
    )
}

pub(crate) fn bwd_seg_r0_blocks_per_sm(k: u32) -> CudaResult<i32> {
    blocks_per_sm(ab_gkr_bwd_seg_r0_const_epi_plane_kernel, k)
}

pub(crate) fn bwd_seg_continuation_blocks_per_sm(k: u32) -> CudaResult<i32> {
    blocks_per_sm(ab_gkr_bwd_seg_cont_const_epi_plane_kernel, k)
}
