use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};

use crate::primitives::field::{BF, E4};
use crate::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};

/// Mirrors `gpu_recipe_header` in `flat_backward_coeff.cuh`.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct GpuRecipeHeader {
    pub batch_power: u32,
    pub immediate_factor: E4,
    pub num_groups: u16,
    pub group_counts: [u16; 2],
    pub terms_offset: u32,
}

/// Mirrors `gpu_prefactor_term` in `flat_backward_coeff.cuh`.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct GpuPrefactorTerm {
    pub coeff: BF,
    pub source: u32,
    pub power: u32,
}

// challenges layout: [batch_base, lookup_mul, lookup_add, constraint_batch]
cuda_kernel_signature_arguments_and_function!(
    EvalRecipesE4,
    challenges: *const E4,
    recipes: *const GpuRecipeHeader,
    terms: *const GpuPrefactorTerm,
    coefficients: *mut E4,
    num_recipes: u32,
);

cuda_kernel_declaration!(
    ab_gkr_flat_round0_eval_recipes_e4_kernel(
        challenges: *const E4,
        recipes: *const GpuRecipeHeader,
        terms: *const GpuPrefactorTerm,
        coefficients: *mut E4,
        num_recipes: u32,
    )
);

/// Launch the eval_recipes kernel.
///
/// `challenges` must point to a device buffer of 4 E4 values:
/// `[batch_base, lookup_mul, lookup_add, constraint_batch]`.
///
/// `coefficients` is the output buffer (can point to `__constant__` symbol
/// address or a regular device allocation).
pub fn eval_recipes_e4(
    challenges: *const E4,
    recipes: &DeviceSlice<GpuRecipeHeader>,
    terms: &DeviceSlice<GpuPrefactorTerm>,
    coefficients: *mut E4,
    stream: &CudaStream,
) -> CudaResult<()> {
    let num_recipes = recipes.len();
    assert!(num_recipes <= u32::MAX as usize);
    if num_recipes == 0 {
        return Ok(());
    }
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(WARP_SIZE * 4, num_recipes as u32);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = EvalRecipesE4Arguments::new(
        challenges,
        recipes.as_ptr(),
        terms.as_ptr(),
        coefficients,
        num_recipes as u32,
    );
    EvalRecipesE4Function(ab_gkr_flat_round0_eval_recipes_e4_kernel).launch(&config, &args)
}
