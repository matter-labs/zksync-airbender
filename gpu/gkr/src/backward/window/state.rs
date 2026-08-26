use std::ffi::c_void;
use std::ptr::null_mut;

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use era_cudart_sys::{cudaGetSymbolAddress, cuda_struct_and_stub};
use gpu_core::primitives::field::E4;
use gpu_core::primitives::utils::WARP_SIZE;
use gpu_prover_context::ProverContext;

use super::common::{BWD_COEFF_BANK_CAPACITY, BWD_FOLD_WEIGHT_SLOTS};

cuda_struct_and_stub! {
    static ab_gkr_bwd_coeff_bank: [E4; BWD_COEFF_BANK_CAPACITY];
}

pub(crate) fn bwd_coeff_bank_device_ptr() -> *mut E4 {
    let mut ptr: *mut c_void = null_mut();
    // SAFETY: the Rust static is the stub for the matching CUDA symbol.
    unsafe {
        cudaGetSymbolAddress(
            &mut ptr,
            &ab_gkr_bwd_coeff_bank as *const _ as *const c_void,
        )
    }
    .wrap()
    .expect("cudaGetSymbolAddress failed for ab_gkr_bwd_coeff_bank");
    ptr.cast()
}

cuda_struct_and_stub! {
    static ab_gkr_bwd_fold_weights: [E4; BWD_FOLD_WEIGHT_SLOTS];
}

fn bwd_fold_weights_device_ptr() -> *mut E4 {
    let mut ptr: *mut c_void = null_mut();
    // SAFETY: the Rust static is the stub for the matching CUDA symbol.
    unsafe {
        cudaGetSymbolAddress(
            &mut ptr,
            &ab_gkr_bwd_fold_weights as *const _ as *const c_void,
        )
    }
    .wrap()
    .expect("cudaGetSymbolAddress failed for ab_gkr_bwd_fold_weights");
    ptr.cast()
}

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GkrBwdBuildFoldWeights,
    fold_weights: *mut E4,
    round: u32,
);
cuda_kernel_declaration!(
    pub(crate) ab_gkr_bwd_build_fold_weights_kernel(fold_weights: *mut E4, round: u32)
);

pub(crate) fn launch_bwd_build_fold_weights(round: u32, context: &ProverContext) -> CudaResult<()> {
    assert!(round >= 1, "fold weights are continuation-only");
    let config = CudaLaunchConfig::builder()
        .grid_dim(1)
        .block_dim(WARP_SIZE)
        .stream(context.get_exec_stream())
        .build();
    let fold_weights = bwd_fold_weights_device_ptr();
    GkrBwdBuildFoldWeightsFunction(ab_gkr_bwd_build_fold_weights_kernel).launch(
        &config,
        &GkrBwdBuildFoldWeightsArguments::new(fold_weights, round),
    )
}
