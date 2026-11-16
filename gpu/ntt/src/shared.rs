//! Field-independent NTT launcher support.

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
