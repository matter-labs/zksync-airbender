use era_cudart::cuda_kernel_declaration;
use gpu_core::primitives::field::E4;

use crate::forward::kernels::*;

/// ABI size guards, paired with the CUDA `static_assert`s in `descriptors.cuh`.
const _: () = {
    assert!(core::mem::size_of::<GpuGKRDimensionReducingForwardTowerPair<E4>>() == 144);
    assert!(core::mem::size_of::<GpuGKRDimensionReducingForwardTowerBatch<E4>>() == 736);
    assert!(core::mem::align_of::<GpuGKRDimensionReducingForwardTowerBatch<E4>>() == 8);
};

cuda_kernel_declaration!(pub(crate)
    ab_gkr_dim_reducing_forward_tower_e4_kernel(
        batch: GpuGKRDimensionReducingForwardTowerBatch<E4>,
    )
);

impl ForwardKernels for E4 {
    const DIMENSION_REDUCING_FORWARD_TOWER: GpuGKRDimensionReducingForwardTowerSignature<Self> =
        ab_gkr_dim_reducing_forward_tower_e4_kernel;
}
