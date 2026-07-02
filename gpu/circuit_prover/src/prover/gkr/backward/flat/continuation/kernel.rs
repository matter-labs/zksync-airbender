use era_cudart::execution::KernelFunction;
use era_cudart::result::CudaResult;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};

use crate::primitives::field::E4;
use crate::prover::gkr::eval_recipes::{GpuFlatRecipeEvalDesc, GpuFlatRecipeEvalDescDevptr};

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

// Device-pointer variant of the continuation eval-recipes kernel: reads the
// recipe/term/immediate tables from device buffers via a four-pointer
// `GpuFlatRecipeEvalDescDevptr`. Used when the continuation recipe count
// overflows the inline `GpuFlatRecipeEvalDesc` caps.
cuda_kernel_signature_arguments_and_function!(
    GpuFlatContEvalRecipesDevptr<T>,
    batch_base: *const T,
    lookup_mul: *const T,
    lookup_add: *const T,
    ext_challenges: *const T,
    desc: GpuFlatRecipeEvalDescDevptr,
    coefficients: *mut T,
    num_recipes: u32,
);

cuda_kernel_declaration!(
    ab_gkr_flat_continuation_eval_recipes_e4_devptr_kernel(
        batch_base: *const E4,
        lookup_mul: *const E4,
        lookup_add: *const E4,
        ext_challenges: *const E4,
        desc: GpuFlatRecipeEvalDescDevptr,
        coefficients: *mut E4,
        num_recipes: u32,
    )
);

// The `__constant__` coefficient symbol address comes from the shared
// `flat::kernel_setup::get_constant_coefficients_device_ptr` helper;
// round-0 and continuation phases use the same device pointer.

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

/// Device-pointer variant of [`eval_continuation_recipes_e4`]. Identical launch
/// geometry and semantics; the recipe/term/immediate tables are read from the
/// device buffers referenced by `desc` instead of an inline descriptor. Used
/// when the continuation recipe count overflows the inline caps.
pub(crate) fn eval_continuation_recipes_e4_devptr(
    batch_base: *const E4,
    lookup_mul: *const E4,
    lookup_add: *const E4,
    ext_challenges: *const E4,
    desc: &GpuFlatRecipeEvalDescDevptr,
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
    let args = GpuFlatContEvalRecipesDevptrArguments::new(
        batch_base,
        lookup_mul,
        lookup_add,
        ext_challenges,
        *desc,
        coefficients,
        num_recipes as u32,
    );
    GpuFlatContEvalRecipesDevptrFunction(ab_gkr_flat_continuation_eval_recipes_e4_devptr_kernel)
        .launch(&config, &args)
}
