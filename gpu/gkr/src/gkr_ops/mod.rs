use era_cudart::{
    cuda_kernel,
    execution::{CudaLaunchConfig, KernelFunction},
    result::CudaResult,
    slice::DeviceSlice,
    stream::CudaStream,
};
use gpu_core::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};

/// Maximum `(batch_challenge_offset, claim_idx)` pairs the
/// `build_combined_claim` kernel-arg descriptor can hold.
pub(crate) const GKR_COMBINED_CLAIM_MAX_PAIRS: usize = 1024;

/// Kernel-arg descriptor for `build_combined_claim`. Inline form: passed
/// by value as `__grid_constant__` data, avoiding per-layer H2D.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuCombinedClaimDesc {
    /// Number of `(exp, idx)` pairs populated in `entries`.
    pub num_terms: u32,
    /// Reserved padding to keep `entries` aligned at offset 8.
    pub _pad: u32,
    /// Flattened `(exp_0, idx_0, exp_1, idx_1, ...)` pairs.
    pub entries: [u32; GKR_COMBINED_CLAIM_MAX_PAIRS * 2],
}

impl Default for GpuCombinedClaimDesc {
    fn default() -> Self {
        Self {
            num_terms: 0,
            _pad: 0,
            entries: [0u32; GKR_COMBINED_CLAIM_MAX_PAIRS * 2],
        }
    }
}

const _: () = {
    assert!(
        std::mem::size_of::<GpuCombinedClaimDesc>() <= 32 * 1024,
        "GpuCombinedClaimDesc must fit under the 32 KB inline kernel-arg ceiling"
    );
};

impl GpuCombinedClaimDesc {
    pub(crate) fn from_pairs(desc_pairs: &[u32]) -> Self {
        assert_eq!(
            desc_pairs.len() % 2,
            0,
            "combined-claim descriptor must be (exponent, claim_idx) pairs"
        );
        let num_pairs = desc_pairs.len() / 2;
        assert!(
            num_pairs <= GKR_COMBINED_CLAIM_MAX_PAIRS,
            "combined-claim descriptor has {num_pairs} pairs; exceeds {GKR_COMBINED_CLAIM_MAX_PAIRS}"
        );
        let mut desc = Self {
            num_terms: num_pairs as u32,
            ..Default::default()
        };
        desc.entries[..desc_pairs.len()].copy_from_slice(desc_pairs);
        desc
    }
}

cuda_kernel!(
    AssembleQueryIndexes,
    ab_assemble_query_indexes_kernel(
        raw_bits: *const u32,
        indexes_out: *mut u32,
        num_queries: u32,
        log_domain_size: u32,
    )
);

/// Assembles `num_queries` query indexes on device from a padded random u32
/// buffer as produced by `transcript_squeeze`.
///
/// Mirrors the host `draw_query_bits_after_verified_pow` + `BitSource` +
/// `assemble_query_index` chain: the first 32 bits of `raw_bits` are skipped
/// (they were the PoW header word), and each query reads `log_domain_size`
/// LE-packed bits thereafter. `raw_bits.len()` must cover `ceil((32 +
/// num_queries * log_domain_size) / 32)` u32 words (the caller typically
/// over-allocates to a multiple of `STATE_SIZE` to match the squeeze output).
pub fn assemble_query_indexes(
    raw_bits: &DeviceSlice<u32>,
    indexes_out: &mut DeviceSlice<u32>,
    log_domain_size: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let num_queries = indexes_out.len() as u32;
    assert!(num_queries > 0);
    assert!(log_domain_size > 0);
    assert!(log_domain_size <= 32);
    let total_bits = 32u64 + (num_queries as u64) * (log_domain_size as u64);
    let required_words = total_bits.div_ceil(32) as usize;
    assert!(
        raw_bits.len() >= required_words,
        "raw_bits buffer is too small for query index assembly"
    );
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, num_queries);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = AssembleQueryIndexesArguments::new(
        raw_bits.as_ptr(),
        indexes_out.as_mut_ptr(),
        num_queries,
        log_domain_size,
    );
    AssembleQueryIndexesFunction::default().launch(&config, &args)
}
#[cfg(test)]
pub(crate) mod tests;
