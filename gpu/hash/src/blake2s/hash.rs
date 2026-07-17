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

pub(crate) fn launch_leaves_kernel(
    values: &DeviceSlice<BF>,
    results: &mut DeviceSlice<Digest>,
    log_rows_per_hash: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let values_len = values.len();
    let count = results.len();
    let values = values.as_ptr();
    let results = results.as_mut_ptr();
    assert_eq!(values_len % (count << log_rows_per_hash), 0);
    let cols_count = checked_u32(values_len / (count << log_rows_per_hash));
    let count = checked_u32(count);
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = LeavesArguments::new(values, results, log_rows_per_hash, cols_count, count);
    LeavesFunction::default().launch(&config, &args)
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
pub fn launch_leaves_kernel_multi_coset(
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
    LeavesFromNttMultiCoset,
    ab_blake2s_leaves_from_ntt_multi_coset_kernel(
        ntt_output: *const BF,
        results: *mut Digest,
        log_values_per_leaf: u32,
        src_cols_per_coset: u32,
        log_lde_factor: u32,
        coset_index_base: u32,
        per_coset_count: u32,
        log_per_coset_count: u32,
        trace_len: u32,
        count: u32,
    )
);

/// Hashes `cosets_in_tile * per_coset_leaves_count` WHIR leaves in one launch,
/// reading the natural multi-coset NTT output directly and writing digests at
/// the flat-tree leaf positions. The output tree backing layout: digest for
/// natural coset `C`, leaf `i` lives at
/// `results[(bitreverse(C, log_lde_factor) * per_coset_leaves_count + i) *
/// STATE_SIZE]`.
///
/// `ntt_output` logical shape: rows = `trace_len`, cols =
/// `cosets_in_tile * src_cols_per_coset`, coset-major outer (`col /
/// src_cols_per_coset = coset_in_tile`), column-major within each coset. The
/// total backing length must be at least `cosets_in_tile * trace_len *
/// src_cols_per_coset` BFs.
pub fn launch_leaves_kernel_from_ntt_multi_coset(
    ntt_output: &DeviceSlice<BF>,
    results: &mut DeviceSlice<Digest>,
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
    assert!(
        per_coset_leaves_count.is_power_of_two(),
        "per_coset_leaves_count must be a power of two (got {per_coset_leaves_count})"
    );
    assert!(src_cols_per_coset >= 1);
    assert!(trace_len.is_power_of_two());
    assert!(trace_len >= 1 << log_values_per_leaf);
    let log_per_coset_count = per_coset_leaves_count.trailing_zeros();
    assert_eq!(
        1usize << log_per_coset_count,
        trace_len as usize >> log_values_per_leaf,
        "per_coset_leaves_count must equal trace_len / values_per_leaf"
    );
    let total_count = checked_u32(
        per_coset_leaves_count
            .checked_mul(cosets_in_tile)
            .expect("leaves total count overflow"),
    );
    let required_ntt_bf = (trace_len as usize) * (src_cols_per_coset as usize) * cosets_in_tile;
    assert!(ntt_output.len() >= required_ntt_bf);
    assert!(results.len() >= total_count as usize);
    assert!(coset_index_base as usize + cosets_in_tile <= 1usize << log_lde_factor);
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, total_count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = LeavesFromNttMultiCosetArguments::new(
        ntt_output.as_ptr(),
        results.as_mut_ptr(),
        log_values_per_leaf,
        src_cols_per_coset,
        log_lde_factor,
        coset_index_base,
        per_coset_leaves_count as u32,
        log_per_coset_count,
        trace_len,
        total_count,
    );
    LeavesFromNttMultiCosetFunction::default().launch(&config, &args)
}
