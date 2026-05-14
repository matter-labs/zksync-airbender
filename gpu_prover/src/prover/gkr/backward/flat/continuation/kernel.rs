use std::ffi::c_void;

use era_cudart::execution::KernelFunction;
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use era_cudart_sys::cudaGetSymbolAddress;

use super::types::FLAT_CONT_CONST_MAX;
use crate::primitives::field::E4;
use crate::prover::gkr::eval_recipes::GpuFlatRecipeEvalDesc;

// ---------------------------------------------------------------------------
// Continuation kernel declarations and launch
// ---------------------------------------------------------------------------

// Eval recipes kernel for continuation coefficients. Each challenge is read
// from its own device pointer (mirrors the round-0 kernel signature).
cuda_kernel_signature_arguments_and_function!(
    GpuFlatContEvalRecipes<T>,
    batch_base: *const T,
    lookup_mul: *const T,
    lookup_add: *const T,
    ext_challenges: *const T,
    desc: GpuFlatRecipeEvalDesc,
    coefficients: *mut T,
    num_recipes: u32,
);

cuda_kernel_declaration!(
    ab_gkr_flat_continuation_eval_recipes_e4_kernel(
        batch_base: *const E4,
        lookup_mul: *const E4,
        lookup_add: *const E4,
        ext_challenges: *const E4,
        desc: GpuFlatRecipeEvalDesc,
        coefficients: *mut E4,
        num_recipes: u32,
    )
);

// ---------------------------------------------------------------------------
// __constant__ symbol address for continuation coefficients
// ---------------------------------------------------------------------------

extern "C" {
    static ab_gkr_flat_continuation_coefficients: [E4; FLAT_CONT_CONST_MAX];
}

pub(crate) fn get_constant_continuation_coefficients_device_ptr() -> *mut E4 {
    let mut ptr: *mut c_void = std::ptr::null_mut();
    // SAFETY: ab_gkr_flat_continuation_coefficients is a valid __constant__ symbol
    // defined in main_backward_round3_compute_coeff.cu.
    unsafe {
        cudaGetSymbolAddress(
            &mut ptr,
            &ab_gkr_flat_continuation_coefficients as *const _ as *const c_void,
        )
    }
    .wrap()
    .expect("cudaGetSymbolAddress failed for ab_gkr_flat_continuation_coefficients");
    ptr as *mut E4
}

// ---------------------------------------------------------------------------
// Eval recipes launch for continuation
// ---------------------------------------------------------------------------

pub(crate) fn eval_continuation_recipes_e4(
    batch_base: *const E4,
    lookup_mul: *const E4,
    lookup_add: *const E4,
    ext_challenges: *const E4,
    desc: &GpuFlatRecipeEvalDesc,
    num_recipes: usize,
    coefficients: *mut E4,
    stream: &era_cudart::stream::CudaStream,
) -> CudaResult<()> {
    use crate::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
    use era_cudart::execution::CudaLaunchConfig;

    if num_recipes == 0 {
        return Ok(());
    }
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(WARP_SIZE * 4, num_recipes as u32);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GpuFlatContEvalRecipesArguments::new(
        batch_base,
        lookup_mul,
        lookup_add,
        ext_challenges,
        *desc,
        coefficients,
        num_recipes as u32,
    );
    GpuFlatContEvalRecipesFunction(ab_gkr_flat_continuation_eval_recipes_e4_kernel)
        .launch(&config, &args)
}
