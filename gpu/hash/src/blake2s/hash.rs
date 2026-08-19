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

/// Host mirror of the kernel-side `bitreverse_low_bits`.
fn bitreverse_low_bits(value: u32, num_bits: u32) -> u32 {
    if num_bits == 0 {
        0
    } else {
        value.reverse_bits() >> (32 - num_bits)
    }
}

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
pub fn hash_leaves_physical(
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
/// `bitreverse(j)`. Coset strides and digest destinations are unchanged.
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
/// the GLOBAL flat-tree leaf positions (not tile-relative): the digest for
/// natural coset `C`, leaf `i` lives at
/// `results[bitreverse(C, log_lde_factor) * per_coset_leaves_count + i]`, so
/// `results` must cover the largest bit-reversed slot the tile touches
/// (asserted below) — pass the full leaves backing, not a tile-sized slice.
///
/// `ntt_output` logical shape: rows = `trace_len`, cols =
/// `cosets_in_tile * src_cols_per_coset`, coset-major outer (`col /
/// src_cols_per_coset = coset_in_tile`), column-major within each coset. The
/// total backing length must be at least `cosets_in_tile * trace_len *
/// src_cols_per_coset` BFs.
pub fn hash_leaves_from_ntt_multi_coset(
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
    assert!(log_lde_factor < 32);
    assert!(
        per_coset_leaves_count.is_power_of_two(),
        "per_coset_leaves_count must be a power of two (got {per_coset_leaves_count})"
    );
    // The kernel decomposes read offsets with mask/shift (`__ffs`-derived log),
    // which silently mis-maps inputs for non-power-of-two column counts.
    assert!(
        src_cols_per_coset.is_power_of_two(),
        "src_cols_per_coset must be a power of two (got {src_cols_per_coset})"
    );
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
    assert!(coset_index_base as usize + cosets_in_tile <= 1usize << log_lde_factor);
    // The kernel writes at global bit-reversed coset slots; `results` must
    // reach the end of the highest slot this tile writes.
    let max_bitrev_coset = (0..cosets_in_tile as u32)
        .map(|i| bitreverse_low_bits(coset_index_base + i, log_lde_factor))
        .max()
        .unwrap();
    let required_results = (max_bitrev_coset as usize + 1) * per_coset_leaves_count;
    assert!(
        results.len() >= required_results,
        "results len {} < {} required by the tile's highest bit-reversed coset slot",
        results.len(),
        required_results,
    );
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

cuda_kernel!(
    LeavesFromNttMultiCosetPhysical,
    ab_blake2s_leaves_from_ntt_multi_coset_physical_kernel(
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

/// LSB sibling of [`hash_leaves_from_ntt_multi_coset`]: `ntt_output` holds the
/// BITREVERSED-order codeword per column, so each leaf is one physically
/// contiguous run of `1 << log_values_per_leaf` rows and per-coset digest `j` is
/// the old logical leaf `bitreverse(j)`. The bit-reversed coset placement of the
/// destination is unchanged.
pub fn hash_leaves_from_ntt_multi_coset_physical(
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
    assert!(log_lde_factor < 32);
    assert!(
        per_coset_leaves_count.is_power_of_two(),
        "per_coset_leaves_count must be a power of two (got {per_coset_leaves_count})"
    );
    assert!(
        src_cols_per_coset.is_power_of_two(),
        "src_cols_per_coset must be a power of two (got {src_cols_per_coset})"
    );
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
    assert!(coset_index_base as usize + cosets_in_tile <= 1usize << log_lde_factor);
    let max_bitrev_coset = (0..cosets_in_tile as u32)
        .map(|i| bitreverse_low_bits(coset_index_base + i, log_lde_factor))
        .max()
        .unwrap();
    let required_results = (max_bitrev_coset as usize + 1) * per_coset_leaves_count;
    assert!(
        results.len() >= required_results,
        "results len {} < {} required by the tile's highest bit-reversed coset slot",
        results.len(),
        required_results,
    );
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, total_count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = LeavesFromNttMultiCosetPhysicalArguments::new(
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
    LeavesFromNttMultiCosetPhysicalFunction::default().launch(&config, &args)
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

cuda_kernel!(
    LeavesFromNttMultiCosetToStagingPhysical,
    ab_blake2s_leaves_from_ntt_multi_coset_to_staging_physical_kernel(
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

/// LSB sibling of [`hash_leaves_from_ntt_multi_coset_to_staging`]: `ntt_output`
/// holds the BITREVERSED-order codeword per column, so per-coset staging digest
/// `j` is the old logical leaf `bitreverse(j)`.
pub fn hash_leaves_from_ntt_multi_coset_to_staging_physical(
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
    let args = LeavesFromNttMultiCosetToStagingPhysicalArguments::new(
        ntt_output.as_ptr(),
        staging.as_mut_ptr(),
        log_values_per_leaf,
        src_cols_per_coset,
        checked_u32(per_coset_leaves_count),
        per_coset_leaves_count.trailing_zeros(),
        trace_len,
        count,
    );
    LeavesFromNttMultiCosetToStagingPhysicalFunction::default().launch(&config, &args)
}

cuda_kernel!(
    LeavesFromNttFlatRangeToStaging,
    ab_blake2s_leaves_from_ntt_flat_range_to_staging_kernel(
        ntt_output: *const BF,
        staging: *mut Digest,
        log_values_per_leaf: u32,
        src_cols_per_coset: u32,
        log_lde_factor: u32,
        flat_leaf_base: u32,
        per_coset_count: u32,
        log_per_coset_count: u32,
        trace_len: u32,
        count: u32,
    )
);

pub fn hash_leaves_from_ntt_flat_range_to_staging(
    ntt_output: &DeviceSlice<BF>,
    staging: &mut DeviceSlice<Digest>,
    log_values_per_leaf: u32,
    src_cols_per_coset: u32,
    log_lde_factor: u32,
    flat_leaf_base: usize,
    leaves_count: usize,
    per_coset_leaves_count: usize,
    trace_len: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(src_cols_per_coset.is_power_of_two());
    assert!(trace_len.is_power_of_two());
    assert!(per_coset_leaves_count.is_power_of_two());
    assert_eq!(
        per_coset_leaves_count,
        trace_len as usize >> log_values_per_leaf
    );
    assert_eq!(flat_leaf_base % WARP_SIZE as usize, 0);
    assert!(leaves_count > 0);
    assert_eq!(leaves_count % WARP_SIZE as usize, 0);
    let total_leaves = per_coset_leaves_count << log_lde_factor;
    assert!(flat_leaf_base + leaves_count <= total_leaves);
    assert_eq!(staging.len(), leaves_count);
    assert!(
        ntt_output.len()
            >= trace_len as usize * src_cols_per_coset as usize * (1usize << log_lde_factor)
    );
    let count = checked_u32(leaves_count);
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = LeavesFromNttFlatRangeToStagingArguments::new(
        ntt_output.as_ptr(),
        staging.as_mut_ptr(),
        log_values_per_leaf,
        src_cols_per_coset,
        log_lde_factor,
        checked_u32(flat_leaf_base),
        checked_u32(per_coset_leaves_count),
        per_coset_leaves_count.trailing_zeros(),
        trace_len,
        count,
    );
    LeavesFromNttFlatRangeToStagingFunction::default().launch(&config, &args)
}

cuda_kernel!(
    LeavesFromNttFlatRangeToStagingPhysical,
    ab_blake2s_leaves_from_ntt_flat_range_to_staging_physical_kernel(
        ntt_output: *const BF,
        staging: *mut Digest,
        log_values_per_leaf: u32,
        src_cols_per_coset: u32,
        log_lde_factor: u32,
        flat_leaf_base: u32,
        per_coset_count: u32,
        log_per_coset_count: u32,
        trace_len: u32,
        count: u32,
    )
);

/// LSB sibling of [`hash_leaves_from_ntt_flat_range_to_staging`]: `ntt_output`
/// holds the BITREVERSED-order codeword per column, so per-coset staging digest
/// `j` is the old logical leaf `bitreverse(j)`. The flat-range → coset/leaf
/// decomposition of the destination is unchanged.
pub fn hash_leaves_from_ntt_flat_range_to_staging_physical(
    ntt_output: &DeviceSlice<BF>,
    staging: &mut DeviceSlice<Digest>,
    log_values_per_leaf: u32,
    src_cols_per_coset: u32,
    log_lde_factor: u32,
    flat_leaf_base: usize,
    leaves_count: usize,
    per_coset_leaves_count: usize,
    trace_len: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(src_cols_per_coset.is_power_of_two());
    assert!(trace_len.is_power_of_two());
    assert!(per_coset_leaves_count.is_power_of_two());
    assert_eq!(
        per_coset_leaves_count,
        trace_len as usize >> log_values_per_leaf
    );
    assert_eq!(flat_leaf_base % WARP_SIZE as usize, 0);
    assert!(leaves_count > 0);
    assert_eq!(leaves_count % WARP_SIZE as usize, 0);
    let total_leaves = per_coset_leaves_count << log_lde_factor;
    assert!(flat_leaf_base + leaves_count <= total_leaves);
    assert_eq!(staging.len(), leaves_count);
    assert!(
        ntt_output.len()
            >= trace_len as usize * src_cols_per_coset as usize * (1usize << log_lde_factor)
    );
    let count = checked_u32(leaves_count);
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = LeavesFromNttFlatRangeToStagingPhysicalArguments::new(
        ntt_output.as_ptr(),
        staging.as_mut_ptr(),
        log_values_per_leaf,
        src_cols_per_coset,
        log_lde_factor,
        checked_u32(flat_leaf_base),
        checked_u32(per_coset_leaves_count),
        per_coset_leaves_count.trailing_zeros(),
        trace_len,
        count,
    );
    LeavesFromNttFlatRangeToStagingPhysicalFunction::default().launch(&config, &args)
}
