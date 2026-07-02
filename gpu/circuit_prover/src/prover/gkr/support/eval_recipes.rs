use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};

use crate::primitives::field::{BF, E4};
use crate::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
use crate::prover::gkr::immediate_factors::{ImmediateFactorMonomial, ImmediateFactorRecipeHeader};

pub(crate) const FLAT_RECIPE_MAX_HEADERS: usize = 2816;
pub(crate) const FLAT_RECIPE_MAX_TERMS: usize = 640;
pub(crate) const FLAT_IMMEDIATE_MAX_RECIPES: usize = 128;
pub(crate) const FLAT_IMMEDIATE_MAX_MONOMIALS: usize = 384;

/// Mirrors `gpu_recipe_header` in `backward/coeff.cuh`.
#[repr(C)]
#[derive(Clone, Copy, Default)]
pub(crate) struct GpuRecipeHeader {
    pub batch_power: u16,
    pub group_count_0: u8,
    pub group_count_1: u8,
    pub terms_offset: u16,
    pub immediate_idx: u16,
}

/// Mirrors `gpu_prefactor_term` in `backward/coeff.cuh`.
#[repr(C)]
#[derive(Clone, Copy, Default)]
pub(crate) struct GpuPrefactorTerm {
    pub coeff: BF,
    pub source: u8,
    pub power: u8,
    pub _pad: u16,
}

/// Mirrors `gpu_flat_recipe_eval_desc` in `backward/coeff.cuh`.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuFlatRecipeEvalDesc {
    pub headers: [GpuRecipeHeader; FLAT_RECIPE_MAX_HEADERS],
    pub terms: [GpuPrefactorTerm; FLAT_RECIPE_MAX_TERMS],
    pub immediate_recipes: [ImmediateFactorRecipeHeader; FLAT_IMMEDIATE_MAX_RECIPES],
    pub immediate_monomials: [ImmediateFactorMonomial; FLAT_IMMEDIATE_MAX_MONOMIALS],
}

impl Default for GpuFlatRecipeEvalDesc {
    fn default() -> Self {
        Self {
            headers: [GpuRecipeHeader::default(); FLAT_RECIPE_MAX_HEADERS],
            terms: [GpuPrefactorTerm::default(); FLAT_RECIPE_MAX_TERMS],
            immediate_recipes: [ImmediateFactorRecipeHeader::default(); FLAT_IMMEDIATE_MAX_RECIPES],
            immediate_monomials: [ImmediateFactorMonomial::default(); FLAT_IMMEDIATE_MAX_MONOMIALS],
        }
    }
}

/// Device-pointer companion of [`GpuFlatRecipeEvalDesc`] for delegations whose
/// recipe/term/immediate tables overflow the inline caps (e.g. bigint's 3006
/// recipes vs the 2816-header cap). Mirrors `gpu_flat_recipe_eval_desc_devptr`
/// in `backward/coeff.cuh`: four device pointers, passed by value as a
/// `__grid_constant__` kernel argument. The pointed-to device buffers are owned
/// by `RecipeEvalDeviceBuffers` in the layer plan and outlive every scheduled
/// launch that reads them.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuFlatRecipeEvalDescDevptr {
    pub headers: *const GpuRecipeHeader,
    pub terms: *const GpuPrefactorTerm,
    pub immediate_recipes: *const ImmediateFactorRecipeHeader,
    pub immediate_monomials: *const ImmediateFactorMonomial,
}

/// Host-side recipe/term/immediate arrays retained for H2D upload when the
/// compiled recipe tables overflow the inline `GpuFlatRecipeEvalDesc` caps.
/// Produced by `compile_recipes_for_device` (as the `device_arrays` field of
/// [`CompiledRecipeBuffers`]) and consumed by `upload_recipe_eval_arrays`, which
/// copies each `Vec` into a device buffer bit-identically to the inline arrays.
pub(crate) struct RecipeEvalHostArrays {
    pub headers: Vec<GpuRecipeHeader>,
    pub terms: Vec<GpuPrefactorTerm>,
    pub immediate_recipes: Vec<ImmediateFactorRecipeHeader>,
    pub immediate_monomials: Vec<ImmediateFactorMonomial>,
}

const _: () = {
    assert!(std::mem::size_of::<GpuRecipeHeader>() == 8);
    assert!(std::mem::size_of::<GpuPrefactorTerm>() == 8);
    assert!(std::mem::size_of::<ImmediateFactorRecipeHeader>() == 4);
    assert!(std::mem::size_of::<ImmediateFactorMonomial>() == 8);
    assert!(
        std::mem::size_of::<GpuFlatRecipeEvalDesc>() <= 32 * 1024,
        "GpuFlatRecipeEvalDesc must fit under the 32 KB inline kernel-arg ceiling"
    );
};

// Each challenge is read from its own device pointer.
cuda_kernel_signature_arguments_and_function!(
    EvalRecipesE4,
    batch_base: *const E4,
    lookup_mul: *const E4,
    lookup_add: *const E4,
    ext_challenges: *const E4,
    desc: GpuFlatRecipeEvalDesc,
    coefficients: *mut E4,
    num_recipes: u32,
);

cuda_kernel_declaration!(
    ab_gkr_flat_round0_eval_recipes_e4_kernel(
        batch_base: *const E4,
        lookup_mul: *const E4,
        lookup_add: *const E4,
        ext_challenges: *const E4,
        desc: GpuFlatRecipeEvalDesc,
        coefficients: *mut E4,
        num_recipes: u32,
    )
);

// Device-pointer variant: the recipe/term/immediate tables are read from device
// buffers via a small (four-pointer) `GpuFlatRecipeEvalDescDevptr` instead of the
// inline descriptor. Used when the recipe count overflows the inline caps.
cuda_kernel_signature_arguments_and_function!(
    EvalRecipesE4Devptr,
    batch_base: *const E4,
    lookup_mul: *const E4,
    lookup_add: *const E4,
    ext_challenges: *const E4,
    desc: GpuFlatRecipeEvalDescDevptr,
    coefficients: *mut E4,
    num_recipes: u32,
);

cuda_kernel_declaration!(
    ab_gkr_flat_round0_eval_recipes_e4_devptr_kernel(
        batch_base: *const E4,
        lookup_mul: *const E4,
        lookup_add: *const E4,
        ext_challenges: *const E4,
        desc: GpuFlatRecipeEvalDescDevptr,
        coefficients: *mut E4,
        num_recipes: u32,
    )
);

/// Launch the eval_recipes kernel. Each challenge is read from its own
/// 1-element device pointer (`batch_base`, `lookup_mul`, `lookup_add`),
/// eliminating the need for a packed 3-element challenges scratch buffer
/// and the two D2D copies that populated it.
///
/// `coefficients` is the output buffer (can point to `__constant__` symbol
/// address or a regular device allocation).
pub(crate) fn eval_recipes_e4(
    batch_base: *const E4,
    lookup_mul: *const E4,
    lookup_add: *const E4,
    ext_challenges: *const E4,
    desc: &GpuFlatRecipeEvalDesc,
    num_recipes: usize,
    coefficients: *mut E4,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(num_recipes <= u32::MAX as usize);
    if num_recipes == 0 {
        return Ok(());
    }
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(WARP_SIZE * 4, num_recipes as u32);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = EvalRecipesE4Arguments::new(
        batch_base,
        lookup_mul,
        lookup_add,
        ext_challenges,
        *desc,
        coefficients,
        num_recipes as u32,
    );
    EvalRecipesE4Function(ab_gkr_flat_round0_eval_recipes_e4_kernel).launch(&config, &args)
}

/// Device-pointer variant of [`eval_recipes_e4`]. Identical launch geometry and
/// semantics; the recipe/term/immediate tables are read from the device buffers
/// referenced by `desc` (four pointers) instead of an inline descriptor. Used
/// when the recipe count overflows the inline `GpuFlatRecipeEvalDesc` caps.
pub(crate) fn eval_recipes_e4_devptr(
    batch_base: *const E4,
    lookup_mul: *const E4,
    lookup_add: *const E4,
    ext_challenges: *const E4,
    desc: &GpuFlatRecipeEvalDescDevptr,
    num_recipes: usize,
    coefficients: *mut E4,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(num_recipes <= u32::MAX as usize);
    if num_recipes == 0 {
        return Ok(());
    }
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(WARP_SIZE * 4, num_recipes as u32);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = EvalRecipesE4DevptrArguments::new(
        batch_base,
        lookup_mul,
        lookup_add,
        ext_challenges,
        *desc,
        coefficients,
        num_recipes as u32,
    );
    EvalRecipesE4DevptrFunction(ab_gkr_flat_round0_eval_recipes_e4_devptr_kernel)
        .launch(&config, &args)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::allocator::tracker::AllocationPlacement;
    use crate::prover::gkr::immediate_factors::{
        ImmediateFactorMonomial, ImmediateFactorRecipeHeader, IMMEDIATE_FACTOR_ABSENT,
        IMMEDIATE_FACTOR_ADDITIVE_PART_IDX,
    };
    use crate::prover::test_utils::make_test_context;
    use era_cudart::memory::memory_copy_async;
    use field::{Field, FieldExtension};
    use serial_test::serial;

    fn sample_ext(seed: u32) -> E4 {
        E4::from_array_of_base([
            BF::new(seed),
            BF::new(seed + 1),
            BF::new(seed + 2),
            BF::new(seed + 3),
        ])
    }

    #[test]
    #[serial]
    fn eval_recipes_reads_external_challenges_from_durable_e4_buffer() {
        let context = make_test_context(64, 8);
        let stream = context.get_exec_stream();
        let batch_base = [sample_ext(3)];
        let lookup_mul = [sample_ext(20)];
        let lookup_add = [sample_ext(30)];
        let external_challenges = (0..7).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();

        let mut d_batch = context.alloc(1, AllocationPlacement::BestFit).unwrap();
        let mut d_lookup_mul = context.alloc(1, AllocationPlacement::BestFit).unwrap();
        let mut d_lookup_add = context.alloc(1, AllocationPlacement::BestFit).unwrap();
        let mut d_external_challenges = context
            .alloc(external_challenges.len(), AllocationPlacement::BestFit)
            .unwrap();
        let mut d_out = context.alloc(1, AllocationPlacement::BestFit).unwrap();
        memory_copy_async(&mut d_batch, &batch_base, stream).unwrap();
        memory_copy_async(&mut d_lookup_mul, &lookup_mul, stream).unwrap();
        memory_copy_async(&mut d_lookup_add, &lookup_add, stream).unwrap();
        memory_copy_async(&mut d_external_challenges, &external_challenges, stream).unwrap();

        let mut desc = GpuFlatRecipeEvalDesc::default();
        desc.headers[0] = GpuRecipeHeader {
            batch_power: 2,
            group_count_0: 0,
            group_count_1: 0,
            terms_offset: 0,
            immediate_idx: 1,
        };
        desc.immediate_recipes[1] = ImmediateFactorRecipeHeader {
            monomial_offset: 0,
            monomial_count: 2,
            _pad: 0,
        };
        desc.immediate_monomials[0] = ImmediateFactorMonomial {
            coeff: BF::new(5),
            challenge_idx_0: 0,
            challenge_idx_1: IMMEDIATE_FACTOR_ABSENT,
            power_0: 1,
            power_1: 0,
        };
        desc.immediate_monomials[1] = ImmediateFactorMonomial {
            coeff: BF::new(7),
            challenge_idx_0: IMMEDIATE_FACTOR_ADDITIVE_PART_IDX,
            challenge_idx_1: IMMEDIATE_FACTOR_ABSENT,
            power_0: 2,
            power_1: 0,
        };

        eval_recipes_e4(
            d_batch.as_ptr(),
            d_lookup_mul.as_ptr(),
            d_lookup_add.as_ptr(),
            d_external_challenges.as_ptr(),
            &desc,
            1,
            d_out.as_mut_ptr(),
            stream,
        )
        .unwrap();

        let mut out_host = unsafe { context.alloc_host_uninit_slice::<E4>(1) };
        memory_copy_async(&mut out_host, &d_out, stream).unwrap();
        stream.synchronize().unwrap();

        let mut expected_immediate = external_challenges[0];
        expected_immediate.mul_assign_by_base(&BF::new(5));
        let mut additive_sq = external_challenges[IMMEDIATE_FACTOR_ADDITIVE_PART_IDX as usize];
        additive_sq.square();
        additive_sq.mul_assign_by_base(&BF::new(7));
        expected_immediate.add_assign(&additive_sq);
        let mut expected = batch_base[0].pow(2);
        expected.mul_assign(&expected_immediate);

        let got = unsafe { out_host.get_accessor().get()[0] };
        assert_eq!(got, expected);
    }
}
