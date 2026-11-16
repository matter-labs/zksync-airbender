//! Field-independent NTT launcher support.

use era_cudart::execution::KernelFunction;
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart_sys::{cudaFuncSetAttribute, CudaFuncAttribute::MaxDynamicSharedMemorySize};

pub(crate) fn set_max_dynamic_smem(function: &impl KernelFunction, bytes: i32) -> CudaResult<()> {
    unsafe { cudaFuncSetAttribute(function.as_ptr(), MaxDynamicSharedMemorySize, bytes).wrap() }
}

/// Narrow a caller-controlled value to `i32` for a kernel argument struct,
/// panicking on truncation (assert taxonomy class 1: a silently wrapped
/// negative feeds device-side column addressing / twiddle indexing and would
/// corrupt memory or the result). Use this only for caller-controlled values;
/// log-domain and launch-geometry casts (which CUDA already rejects loudly, or
/// which cannot exceed range for any valid input) do NOT use it. `u32` sources
/// widen losslessly through `usize` before the narrowing check.
#[track_caller]
pub(crate) fn checked_i32(v: usize, what: &str) -> i32 {
    assert!(
        v <= i32::MAX as usize,
        "{what} ({v}) exceeds i32::MAX for its kernel-argument cast",
    );
    v as i32
}

/// Narrow a caller-controlled value to `u32` for a kernel argument struct,
/// panicking on truncation. Same class-1 rationale as [`checked_i32`].
#[track_caller]
pub(crate) fn checked_u32(v: usize, what: &str) -> u32 {
    assert!(
        v <= u32::MAX as usize,
        "{what} ({v}) exceeds u32::MAX for its kernel-argument cast",
    );
    v as u32
}

/// TMA and programmatic dependent launch were introduced with Hopper.
/// Ampere kernels must use the ordinary scalar-egress and same-stream paths.
pub(crate) const fn supports_tma_pdl(compute_capability_major: usize) -> bool {
    compute_capability_major >= 9
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
pub(crate) fn assert_multi_coset_output_cols(
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

#[cfg(test)]
mod tests {
    use super::supports_tma_pdl;

    #[test]
    fn tma_pdl_requires_compute_capability_9() {
        assert!(!supports_tma_pdl(8));
        assert!(supports_tma_pdl(9));
        assert!(supports_tma_pdl(12));
    }
}
