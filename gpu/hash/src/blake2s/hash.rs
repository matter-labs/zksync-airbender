//! Blake2s leaf-hashing kernel launchers: flat single-coset leaves (test
//! reference), packed multi-coset leaves, and the fused leaves-from-NTT
//! variant that reads the natural multi-coset NTT output directly.

use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::field::BF;
use gpu_core::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};

use super::{checked_u32, Digest};

cuda_kernel!(
    Leaves,
    ab_blake2s_leaves_kernel(
        values: *const BF,
        results: *mut Digest,
        log_rows_per_hash: u32,
        cols_count: u32,
        count: u32,
    )
);

pub(super) fn hash_leaves(
    values: &DeviceSlice<BF>,
    results: &mut DeviceSlice<Digest>,
    log_rows_per_hash: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let values_len = values.len();
    let count = results.len();
    let values = values.as_ptr();
    let results = results.as_mut_ptr();
    assert!(log_rows_per_hash < 32);
    assert_eq!(values_len % (count << log_rows_per_hash), 0);
    let cols_count = checked_u32(values_len / (count << log_rows_per_hash));
    // `cols_count == 0` is legitimate — a zero-width trace part commits to a
    // dummy tree (empty cap) on the CPU reference; this launcher's degenerate
    // output for it is discarded downstream. No lower bound on cols_count.
    let count = checked_u32(count);
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = LeavesArguments::new(values, results, log_rows_per_hash, cols_count, count);
    LeavesFunction::default().launch(&config, &args)
}

cuda_kernel!(
    LeavesPhysical,
    ab_blake2s_leaves_physical_kernel(
        values: *const BF,
        results: *mut Digest,
        log_rows_per_hash: u32,
        cols_count: u32,
        count: u32,
    )
);

/// LSB sibling of [`hash_leaves`]: `values` is the BITREVERSED-order codeword,
/// so each leaf is one physically contiguous block of `1 << log_rows_per_hash`
/// rows and digest `j` is the old logical leaf `bitreverse(j)`.
#[allow(dead_code)]
pub(super) fn hash_leaves_physical(
    values: &DeviceSlice<BF>,
    results: &mut DeviceSlice<Digest>,
    log_rows_per_hash: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let values_len = values.len();
    let count = results.len();
    let values = values.as_ptr();
    let results = results.as_mut_ptr();
    assert!(log_rows_per_hash < 32);
    assert_eq!(values_len % (count << log_rows_per_hash), 0);
    let cols_count = checked_u32(values_len / (count << log_rows_per_hash));
    let count = checked_u32(count);
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = LeavesPhysicalArguments::new(values, results, log_rows_per_hash, cols_count, count);
    LeavesPhysicalFunction::default().launch(&config, &args)
}

cuda_kernel!(
    LeavesMultiCoset,
    ab_blake2s_leaves_multi_coset_kernel(
        values: *const BF,
        results: *mut Digest,
        log_rows_per_hash: u32,
        cols_count: u32,
        log_per_coset_count: u32,
        per_coset_values_stride_bf: u32,
        per_coset_results_stride_digests: u32,
        count: u32,
    )
);

/// Multi-coset leaf hashing: hashes `per_coset_leaves_count * cosets_in_tile`
/// leaves in one launch. Each coset's inputs sit in an independent per-coset
/// slab strided by `per_coset_values_stride_bf`; each coset's outputs sit at
/// offset `coset * per_coset_results_stride_digests` inside `results`. The
/// caller passes the full `results` backing and the kernel addresses each
/// coset's leaves slab via the stride.
///
/// Production code reaches this only through `build_merkle_tree_multi_coset`;
/// `pub` (hidden) for circuit_prover's whir/kernels parity tests.
#[doc(hidden)]
pub fn hash_leaves_multi_coset(
    values: &DeviceSlice<BF>,
    results: &mut DeviceSlice<Digest>,
    log_rows_per_hash: u32,
    cosets_in_tile: usize,
    per_coset_leaves_count: usize,
    per_coset_values_stride_bf: usize,
    per_coset_results_stride_digests: usize,
    cols_count: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(cosets_in_tile >= 1);
    assert!(log_rows_per_hash < 32);
    // `cols_count == 0` is legitimate — a zero-width trace part commits to a
    // dummy tree (empty cap) on the CPU reference; this launcher's degenerate
    // output for it is discarded downstream. No lower bound on cols_count.
    assert!(
        per_coset_leaves_count.is_power_of_two(),
        "per_coset_leaves_count must be a power of two (got {per_coset_leaves_count})"
    );
    let log_per_coset_count = per_coset_leaves_count.trailing_zeros();
    let total_count = per_coset_leaves_count
        .checked_mul(cosets_in_tile)
        .expect("leaves total count overflow");
    // Each coset's input slab must cover cols_count * (per_coset_leaves_count
    // << log_rows_per_hash) BFs starting at `coset * per_coset_values_stride_bf`.
    let per_coset_values_required = cols_count * (per_coset_leaves_count << log_rows_per_hash);
    assert!(per_coset_values_stride_bf >= per_coset_values_required);
    let last_coset_values_end =
        (cosets_in_tile - 1) * per_coset_values_stride_bf + per_coset_values_required;
    assert!(values.len() >= last_coset_values_end);
    // Each coset's output region occupies `per_coset_leaves_count` digests
    // starting at `coset * per_coset_results_stride_digests`.
    assert!(per_coset_results_stride_digests >= per_coset_leaves_count);
    let last_coset_results_end =
        (cosets_in_tile - 1) * per_coset_results_stride_digests + per_coset_leaves_count;
    assert!(results.len() >= last_coset_results_end);
    let total_count = checked_u32(total_count);
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, total_count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = LeavesMultiCosetArguments::new(
        values.as_ptr(),
        results.as_mut_ptr(),
        log_rows_per_hash,
        checked_u32(cols_count),
        log_per_coset_count,
        checked_u32(per_coset_values_stride_bf),
        checked_u32(per_coset_results_stride_digests),
        total_count,
    );
    LeavesMultiCosetFunction::default().launch(&config, &args)
}

cuda_kernel!(
    LeavesMultiCosetPhysical,
    ab_blake2s_leaves_multi_coset_physical_kernel(
        values: *const BF,
        results: *mut Digest,
        log_rows_per_hash: u32,
        cols_count: u32,
        log_per_coset_count: u32,
        per_coset_values_stride_bf: u32,
        per_coset_results_stride_digests: u32,
        count: u32,
    )
);

/// LSB sibling of [`hash_leaves_multi_coset`]: each coset slab of `values` is the
/// BITREVERSED-order codeword, so each leaf is one physically contiguous block of
/// `1 << log_rows_per_hash` rows and per-coset digest `j` is the old logical leaf
/// `bitreverse(j)`.
pub fn hash_leaves_multi_coset_physical(
    values: &DeviceSlice<BF>,
    results: &mut DeviceSlice<Digest>,
    log_rows_per_hash: u32,
    cosets_in_tile: usize,
    per_coset_leaves_count: usize,
    per_coset_values_stride_bf: usize,
    per_coset_results_stride_digests: usize,
    cols_count: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(cosets_in_tile >= 1);
    assert!(log_rows_per_hash < 32);
    assert!(
        per_coset_leaves_count.is_power_of_two(),
        "per_coset_leaves_count must be a power of two (got {per_coset_leaves_count})"
    );
    let log_per_coset_count = per_coset_leaves_count.trailing_zeros();
    let total_count = per_coset_leaves_count
        .checked_mul(cosets_in_tile)
        .expect("leaves total count overflow");
    let per_coset_values_required = cols_count * (per_coset_leaves_count << log_rows_per_hash);
    assert!(per_coset_values_stride_bf >= per_coset_values_required);
    let last_coset_values_end =
        (cosets_in_tile - 1) * per_coset_values_stride_bf + per_coset_values_required;
    assert!(values.len() >= last_coset_values_end);
    assert!(per_coset_results_stride_digests >= per_coset_leaves_count);
    let last_coset_results_end =
        (cosets_in_tile - 1) * per_coset_results_stride_digests + per_coset_leaves_count;
    assert!(results.len() >= last_coset_results_end);
    let total_count = checked_u32(total_count);
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, total_count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = LeavesMultiCosetPhysicalArguments::new(
        values.as_ptr(),
        results.as_mut_ptr(),
        log_rows_per_hash,
        checked_u32(cols_count),
        log_per_coset_count,
        checked_u32(per_coset_values_stride_bf),
        checked_u32(per_coset_results_stride_digests),
        total_count,
    );
    LeavesMultiCosetPhysicalFunction::default().launch(&config, &args)
}

cuda_kernel!(
    LeavesFromNttMultiCosetToStaging,
    ab_blake2s_leaves_from_ntt_multi_coset_to_staging_kernel(
        ntt_output: *const BF,
        staging: *mut Digest,
        log_values_per_leaf: u32,
        src_cols_per_coset: u32,
        per_coset_count: u32,
        log_per_coset_count: u32,
        trace_len: u32,
        count: u32,
    )
);

pub fn hash_leaves_from_ntt_multi_coset_to_staging(
    ntt_output: &DeviceSlice<BF>,
    staging: &mut DeviceSlice<Digest>,
    log_values_per_leaf: u32,
    src_cols_per_coset: u32,
    log_lde_factor: u32,
    coset_index_base: u32,
    cosets_in_tile: usize,
    per_coset_leaves_count: usize,
    trace_len: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(cosets_in_tile >= 1);
    assert!(src_cols_per_coset.is_power_of_two());
    assert!(trace_len.is_power_of_two());
    assert!(per_coset_leaves_count.is_power_of_two());
    assert_eq!(
        per_coset_leaves_count,
        trace_len as usize >> log_values_per_leaf
    );
    assert!(coset_index_base as usize + cosets_in_tile <= 1usize << log_lde_factor);
    let count = per_coset_leaves_count
        .checked_mul(cosets_in_tile)
        .expect("leaf count overflow");
    assert_eq!(staging.len(), count);
    assert!(ntt_output.len() >= trace_len as usize * src_cols_per_coset as usize * cosets_in_tile);
    let count = checked_u32(count);
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = LeavesFromNttMultiCosetToStagingArguments::new(
        ntt_output.as_ptr(),
        staging.as_mut_ptr(),
        log_values_per_leaf,
        src_cols_per_coset,
        checked_u32(per_coset_leaves_count),
        per_coset_leaves_count.trailing_zeros(),
        trace_len,
        count,
    );
    LeavesFromNttMultiCosetToStagingFunction::default().launch(&config, &args)
}
