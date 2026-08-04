//! Launcher plumbing shared verbatim across the NTT launcher modules
//! (`forward`, `inverse`, `lde`, `hypercube`, `dit`). These helpers factor out
//! idioms that were previously copy-pasted into every multi-stage launcher;
//! each is behavior-preserving (identical launch geometry, identical kernel
//! args — only the panic-message text is unified into one equally-informative
//! form where it differed).

use era_cudart::execution::KernelFunction;
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart_sys::{cudaFuncSetAttribute, CudaFuncAttribute};

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
    unsafe {
        cudaFuncSetAttribute(
            func.as_ptr(),
            CudaFuncAttribute::MaxDynamicSharedMemorySize,
            bytes as i32,
        )
        .wrap()?;
    }
    Ok(())
}

/// Assert a multi-coset output buffer is wide enough for every virtual column
/// the launcher will write: `num_cosets` cosets spaced `num_cols_per_coset`
/// apart, with `num_ntts` columns written per coset. The highest column touched
/// is `(num_cosets - 1) * num_cols_per_coset + num_ntts - 1`.
///
/// Bundles two checks (`num_cols_per_coset >= num_ntts`, then the output-width
/// bound): at call sites that also assert pow2/workload preconditions (subwarp,
/// smem_packed), the cols-per-coset check here fires after those intervening
/// asserts when multiple preconditions are violated at once.
#[track_caller]
pub(super) fn assert_multi_coset_output_cols(
    output_cols: usize,
    num_cosets: usize,
    num_cols_per_coset: usize,
    num_ntts: usize,
) {
    assert!(
        num_cols_per_coset >= num_ntts,
        "num_cols_per_coset ({num_cols_per_coset}) < num_ntts ({num_ntts})",
    );
    let max_col_offset_exclusive = (num_cosets - 1) * num_cols_per_coset + num_ntts;
    assert!(
        output_cols >= max_col_offset_exclusive,
        "outputs_matrix.cols() = {output_cols} < {max_col_offset_exclusive} (num_cosets={num_cosets}, stride={num_cols_per_coset}, num_ntts={num_ntts})",
    );
}

/// Narrow a caller-controlled value to `i32` for a kernel argument struct,
/// panicking on truncation (assert taxonomy class 1: a silently wrapped
/// negative feeds device-side column addressing / twiddle indexing and would
/// corrupt memory or the result). Use this only for caller-controlled values;
/// log-domain and launch-geometry casts (which CUDA already rejects loudly, or
/// which cannot exceed range for any valid input) do NOT use it. `u32` sources
/// widen losslessly through `usize` before the narrowing check.
#[track_caller]
pub(super) fn checked_i32(v: usize, what: &str) -> i32 {
    assert!(
        v <= i32::MAX as usize,
        "{what} ({v}) exceeds i32::MAX for its kernel-argument cast",
    );
    v as i32
}

/// Narrow a caller-controlled value to `u32` for a kernel argument struct,
/// panicking on truncation. Same class-1 rationale as [`checked_i32`].
#[track_caller]
pub(super) fn checked_u32(v: usize, what: &str) -> u32 {
    assert!(
        v <= u32::MAX as usize,
        "{what} ({v}) exceeds u32::MAX for its kernel-argument cast",
    );
    v as u32
}
