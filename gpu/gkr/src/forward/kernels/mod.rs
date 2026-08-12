use std::ptr::null;

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use gpu_core::primitives::field::E4;

pub(crate) const GKR_DIM_REDUCING_FORWARD_TOWER_LOG_BLOCK: u32 = 8;
pub(crate) const GKR_DIM_REDUCING_FORWARD_TOWER_BLOCK: u32 =
    1 << GKR_DIM_REDUCING_FORWARD_TOWER_LOG_BLOCK;
pub(crate) const GKR_DIM_REDUCING_FORWARD_TOWER_MAX_ROUNDS: usize =
    GKR_DIM_REDUCING_FORWARD_TOWER_LOG_BLOCK as usize;

#[repr(C)]
pub(crate) struct GpuGKRDimensionReducingForwardTowerPairwiseBatch<E> {
    pub(crate) input: *const E,
    pub(crate) round_outputs: [*mut E; GKR_DIM_REDUCING_FORWARD_TOWER_MAX_ROUNDS],
    pub(crate) input_len: u32,
    pub(crate) round_count: u32,
}

impl<E> Copy for GpuGKRDimensionReducingForwardTowerPairwiseBatch<E> {}

impl<E> Clone for GpuGKRDimensionReducingForwardTowerPairwiseBatch<E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<E> Default for GpuGKRDimensionReducingForwardTowerPairwiseBatch<E> {
    fn default() -> Self {
        Self {
            input: null(),
            round_outputs: [null::<E>().cast_mut(); GKR_DIM_REDUCING_FORWARD_TOWER_MAX_ROUNDS],
            input_len: 0,
            round_count: 0,
        }
    }
}

unsafe impl<E> Send for GpuGKRDimensionReducingForwardTowerPairwiseBatch<E> {}
unsafe impl<E> Sync for GpuGKRDimensionReducingForwardTowerPairwiseBatch<E> {}

#[repr(C)]
pub(crate) struct GpuGKRDimensionReducingForwardTowerLookupBatch<E> {
    pub(crate) input_num: *const E,
    pub(crate) input_den: *const E,
    pub(crate) round_outputs_num: [*mut E; GKR_DIM_REDUCING_FORWARD_TOWER_MAX_ROUNDS],
    pub(crate) round_outputs_den: [*mut E; GKR_DIM_REDUCING_FORWARD_TOWER_MAX_ROUNDS],
    pub(crate) input_len: u32,
    pub(crate) round_count: u32,
}

impl<E> Copy for GpuGKRDimensionReducingForwardTowerLookupBatch<E> {}

impl<E> Clone for GpuGKRDimensionReducingForwardTowerLookupBatch<E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<E> Default for GpuGKRDimensionReducingForwardTowerLookupBatch<E> {
    fn default() -> Self {
        Self {
            input_num: null(),
            input_den: null(),
            round_outputs_num: [null::<E>().cast_mut(); GKR_DIM_REDUCING_FORWARD_TOWER_MAX_ROUNDS],
            round_outputs_den: [null::<E>().cast_mut(); GKR_DIM_REDUCING_FORWARD_TOWER_MAX_ROUNDS],
            input_len: 0,
            round_count: 0,
        }
    }
}

unsafe impl<E> Send for GpuGKRDimensionReducingForwardTowerLookupBatch<E> {}
unsafe impl<E> Sync for GpuGKRDimensionReducingForwardTowerLookupBatch<E> {}

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuGKRDimensionReducingForwardTowerPairwise<T>,
    batch: GpuGKRDimensionReducingForwardTowerPairwiseBatch<T>,
);

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuGKRDimensionReducingForwardTowerLookup<T>,
    batch: GpuGKRDimensionReducingForwardTowerLookupBatch<T>,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_dim_reducing_forward_tower_pairwise_e4_kernel(
        batch: GpuGKRDimensionReducingForwardTowerPairwiseBatch<E4>,
    )
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_dim_reducing_forward_tower_lookup_e4_kernel(
        batch: GpuGKRDimensionReducingForwardTowerLookupBatch<E4>,
    )
);

pub(crate) fn launch_dimension_reducing_forward_tower_pairwise<E: crate::ForwardKernels>(
    batch: &GpuGKRDimensionReducingForwardTowerPairwiseBatch<E>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let block_size = GKR_DIM_REDUCING_FORWARD_TOWER_BLOCK;
    let input_len = batch.input_len;
    assert!(input_len > 0, "tower pairwise batch has empty input");
    let config = CudaLaunchConfig::builder()
        .grid_dim(input_len.div_ceil(block_size).max(1))
        .block_dim(block_size)
        .dynamic_smem_bytes(block_size as usize * std::mem::size_of::<E>())
        .stream(stream)
        .build();
    let args = GpuGKRDimensionReducingForwardTowerPairwiseArguments::new(*batch);
    GpuGKRDimensionReducingForwardTowerPairwiseFunction(
        E::DIMENSION_REDUCING_FORWARD_TOWER_PAIRWISE,
    )
    .launch(&config, &args)
}

pub(crate) fn launch_dimension_reducing_forward_tower_lookup<E: crate::ForwardKernels>(
    batch: &GpuGKRDimensionReducingForwardTowerLookupBatch<E>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let block_size = GKR_DIM_REDUCING_FORWARD_TOWER_BLOCK;
    let input_len = batch.input_len;
    assert!(input_len > 0, "tower lookup batch has empty input");
    let config = CudaLaunchConfig::builder()
        .grid_dim(input_len.div_ceil(block_size).max(1))
        .block_dim(block_size)
        .dynamic_smem_bytes(2 * block_size as usize * std::mem::size_of::<E>())
        .stream(stream)
        .build();
    let args = GpuGKRDimensionReducingForwardTowerLookupArguments::new(*batch);
    GpuGKRDimensionReducingForwardTowerLookupFunction(E::DIMENSION_REDUCING_FORWARD_TOWER_LOOKUP)
        .launch(&config, &args)
}

pub(crate) trait ForwardKernels: Copy + Sized {
    const DIMENSION_REDUCING_FORWARD_TOWER_PAIRWISE:
        GpuGKRDimensionReducingForwardTowerPairwiseSignature<Self>;
    const DIMENSION_REDUCING_FORWARD_TOWER_LOOKUP:
        GpuGKRDimensionReducingForwardTowerLookupSignature<Self>;
}

impl ForwardKernels for E4 {
    const DIMENSION_REDUCING_FORWARD_TOWER_PAIRWISE:
        GpuGKRDimensionReducingForwardTowerPairwiseSignature<Self> =
        ab_gkr_dim_reducing_forward_tower_pairwise_e4_kernel;
    const DIMENSION_REDUCING_FORWARD_TOWER_LOOKUP:
        GpuGKRDimensionReducingForwardTowerLookupSignature<Self> =
        ab_gkr_dim_reducing_forward_tower_lookup_e4_kernel;
}
