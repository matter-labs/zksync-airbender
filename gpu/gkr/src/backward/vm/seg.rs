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

use super::seg_desc::{BwdSegDesc, BWD_SEG_CONST_BANK, BWD_SEG_FOLD_WEIGHT_SLOTS, BWD_SEG_MAX_K};
use super::seg_lower::BwdSegSetup;

cuda_struct_and_stub! {
    static ab_gkr_bwd_seg_coeff_bank: [E4; BWD_SEG_CONST_BANK];
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

fn launch_bwd_seg_build_fold_weights(round: u32, context: &ProverContext) -> CudaResult<()> {
    assert!(round >= 1, "fold weights are continuation-only");
    let config = CudaLaunchConfig::builder()
        .grid_dim(1)
        .block_dim(WARP_SIZE)
        .stream(context.get_exec_stream())
        .build();
    GkrBwdSegBuildFoldWeightsFunction(ab_gkr_bwd_seg_build_fold_weights_kernel).launch(
        &config,
        &GkrBwdSegBuildFoldWeightsArguments::new(bwd_seg_fold_weights_device_ptr(), round),
    )
}

fn plane_smem_bytes(k: u32) -> usize {
    k.saturating_sub(1) as usize * WARP_SIZE as usize * size_of::<E4>()
}

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

fn launch(
    setup: &BwdSegSetup,
    symbol: GkrBwdSegSignature,
    context: &ProverContext,
) -> CudaResult<()> {
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
) -> CudaResult<()> {
    launch_bwd_seg_build_fold_weights(round, context)?;
    launch(setup, ab_gkr_bwd_seg_cont_const_epi_plane_kernel, context)
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
