//! Launcher plumbing shared verbatim across the NTT launcher modules
//! (`forward`, `inverse`, `lde`, `hypercube`, `dit`). These helpers factor out
//! idioms that were previously copy-pasted into every multi-stage launcher;
//! each is behavior-preserving (identical launch geometry, identical kernel
//! args — only the panic-message text is unified into one equally-informative
//! form where it differed).

use era_cudart::execution::KernelFunction;
use era_cudart::result::CudaResult;

use gpu_core::primitives::device_structures::{DeviceMatrixChunkImpl, DeviceMatrixChunkMutImpl};
use gpu_core::primitives::field::BaseField;

use std::mem::size_of;

type BF = BaseField;

/// Assert both NTT operands satisfy the 16-byte alignment the multi-stage
/// kernels require: base pointer, row stride (`stride * sizeof(BF)`) and offset
/// (`offset * sizeof(BF)`) of inputs and outputs must all be 16-byte aligned,
/// because the kernels stage global memory through `__pipeline_memcpy_async`.
///
/// Intentional divergence: the compact-1-pass, subwarp and smem-packed
/// launchers do NOT call this — they issue no async-pipeline loads and so carry
/// no alignment requirement.
#[track_caller]
pub(super) fn assert_ntt_16b_aligned(
    inputs: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs: &(impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
) {
    // __pipeline_memcpy_asyncs in the kernel require 16 byte alignment
    assert_eq!(inputs.slice().as_ptr() as usize % 16, 0);
    assert_eq!(outputs.slice().as_ptr() as usize % 16, 0);
    assert_eq!((inputs.stride() * size_of::<BF>()) % 16, 0);
    assert_eq!((outputs.stride() * size_of::<BF>()) % 16, 0);
    assert_eq!((inputs.offset() * size_of::<BF>()) % 16, 0);
    assert_eq!((outputs.offset() * size_of::<BF>()) % 16, 0);
}

/// Opt a kernel into a dynamic shared-memory allocation larger than the default
/// 48 KB cap. Folds the `usize -> i32` cast behind a single bound check; safe to
/// call once above a launch loop (nothing here is loop-bound) or per launch.
#[track_caller]
pub(crate) fn set_max_dynamic_smem(func: &impl KernelFunction, bytes: usize) -> CudaResult<()> {
    assert!(bytes <= i32::MAX as usize);
    crate::shared::set_max_dynamic_smem(func, bytes as i32)
}
