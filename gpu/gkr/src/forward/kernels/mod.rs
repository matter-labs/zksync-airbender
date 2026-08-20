use std::ptr::{null, null_mut};

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use gpu_core::primitives::field::E4;

use super::vm::desc::REDUCTION_PAIR_CAP;

pub(crate) const GKR_DIM_REDUCING_FORWARD_TOWER_LOG_BLOCK: u32 = 8;
pub(crate) const GKR_DIM_REDUCING_FORWARD_TOWER_BLOCK: u32 =
    1 << GKR_DIM_REDUCING_FORWARD_TOWER_LOG_BLOCK;
pub(crate) const GKR_DIM_REDUCING_FORWARD_TOWER_MAX_ROUNDS: usize =
    GKR_DIM_REDUCING_FORWARD_TOWER_LOG_BLOCK as usize;

#[repr(C)]
pub(crate) struct GpuGKRDimensionReducingForwardTowerPair<E> {
    pub(crate) input: [*const E; 2],
    pub(crate) round_outputs: [[*mut E; 2]; GKR_DIM_REDUCING_FORWARD_TOWER_MAX_ROUNDS],
}

impl<E> Copy for GpuGKRDimensionReducingForwardTowerPair<E> {}

impl<E> Clone for GpuGKRDimensionReducingForwardTowerPair<E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<E> Default for GpuGKRDimensionReducingForwardTowerPair<E> {
    fn default() -> Self {
        Self {
            input: [null(); 2],
            round_outputs: [[null_mut(); 2]; GKR_DIM_REDUCING_FORWARD_TOWER_MAX_ROUNDS],
        }
    }
}

/// `pairwise_mask` carries bit `i` for pair `i`: set means PAIRWISE2 (two
/// independent product towers), clear means LOOKUP (one tower's num/den). Pairs
/// stay densely packed, so the grid's y extent stays `pair_count`.
#[repr(C)]
pub(crate) struct GpuGKRDimensionReducingForwardTowerBatch<E> {
    pub(crate) pairs: [GpuGKRDimensionReducingForwardTowerPair<E>; REDUCTION_PAIR_CAP],
    pub(crate) pair_count: u32,
    pub(crate) input_len: u32,
    pub(crate) round_count: u32,
    pub(crate) pairwise_mask: u32,
}

impl<E> Default for GpuGKRDimensionReducingForwardTowerBatch<E> {
    fn default() -> Self {
        Self {
            pairs: [GpuGKRDimensionReducingForwardTowerPair::default(); REDUCTION_PAIR_CAP],
            pair_count: 0,
            input_len: 0,
            round_count: 0,
            pairwise_mask: 0,
        }
    }
}

/// ABI size guards, paired with the CUDA `static_assert`s in `descriptors.cuh`.
const _: () = {
    assert!(core::mem::size_of::<GpuGKRDimensionReducingForwardTowerPair<E4>>() == 144);
    assert!(core::mem::size_of::<GpuGKRDimensionReducingForwardTowerBatch<E4>>() == 736);
    assert!(core::mem::align_of::<GpuGKRDimensionReducingForwardTowerBatch<E4>>() == 8);
};

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuGKRDimensionReducingForwardTower<T>,
    batch: GpuGKRDimensionReducingForwardTowerBatch<T>,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_dim_reducing_forward_tower_e4_kernel(
        batch: GpuGKRDimensionReducingForwardTowerBatch<E4>,
    )
);

pub(crate) fn launch_dimension_reducing_forward_tower<E: crate::ForwardKernels>(
    batch: GpuGKRDimensionReducingForwardTowerBatch<E>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let block_size = GKR_DIM_REDUCING_FORWARD_TOWER_BLOCK;
    let input_len = batch.input_len;
    assert!(input_len > 0, "tower batch has empty input");
    let config = CudaLaunchConfig::builder()
        .grid_dim((input_len.div_ceil(block_size).max(1), batch.pair_count))
        .block_dim(block_size)
        .dynamic_smem_bytes(2 * block_size as usize * std::mem::size_of::<E>())
        .stream(stream)
        .build();
    let args = GpuGKRDimensionReducingForwardTowerArguments::new(batch);
    GpuGKRDimensionReducingForwardTowerFunction(E::DIMENSION_REDUCING_FORWARD_TOWER)
        .launch(&config, &args)
}

pub(crate) trait ForwardKernels: Copy + Sized {
    const DIMENSION_REDUCING_FORWARD_TOWER: GpuGKRDimensionReducingForwardTowerSignature<Self>;
}

impl ForwardKernels for E4 {
    const DIMENSION_REDUCING_FORWARD_TOWER: GpuGKRDimensionReducingForwardTowerSignature<Self> =
        ab_gkr_dim_reducing_forward_tower_e4_kernel;
}
