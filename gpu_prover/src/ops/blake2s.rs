use crate::ops::bit_reverse::bit_reverse_in_place;
use crate::primitives::device_structures::{
    DeviceMatrixChunkImpl, DeviceMatrixChunkMutImpl, MutPtrAndStride, PtrAndStride,
};
use crate::primitives::field::{BF, E4};
use crate::primitives::utils::{get_grid_block_dims_for_threads_count, LOG_WARP_SIZE, WARP_SIZE};
use era_cudart::cuda_kernel;
use era_cudart::device::{device_get_attribute, get_device};
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::memory::memory_set_async;
use era_cudart::occupancy::max_active_blocks_per_multiprocessor;
use era_cudart::result::CudaResult;
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart::stream::CudaStream;
use era_cudart_sys::CudaDeviceAttr;

pub const STATE_SIZE: usize = 8;
pub const BLOCK_SIZE: usize = 16;

pub type Digest = [u32; STATE_SIZE];

pub type DG = Digest;

cuda_kernel!(
    Leaves,
    ab_blake2s_leaves_kernel(
        values: *const BF,
        results: *mut DG,
        log_rows_per_hash: u32,
        cols_count: u32,
        count: u32,
    )
);

pub fn launch_leaves_kernel(
    values: &DeviceSlice<BF>,
    results: &mut DeviceSlice<DG>,
    log_rows_per_hash: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let values_len = values.len();
    let count = results.len();
    let values = values.as_ptr();
    let results = results.as_mut_ptr();
    assert_eq!(values_len % (count << log_rows_per_hash), 0);
    let cols_count = values_len / (count << log_rows_per_hash);
    assert!(cols_count <= u32::MAX as usize);
    let cols_count = cols_count as u32;
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = LeavesArguments::new(values, results, log_rows_per_hash, cols_count, count);
    LeavesFunction::default().launch(&config, &args)
}

pub fn build_merkle_tree_leaves(
    values: &DeviceSlice<BF>,
    results: &mut DeviceSlice<DG>,
    log_rows_per_hash: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let values_len = values.len();
    let leaves_count = results.len();
    assert_eq!(values_len % leaves_count, 0);
    launch_leaves_kernel(values, results, log_rows_per_hash, stream)
}

cuda_kernel!(Nodes, ab_blake2s_nodes_kernel(values: *const DG, results: *mut DG, count: u32,));

pub fn launch_nodes_kernel(
    values: &DeviceSlice<DG>,
    results: &mut DeviceSlice<DG>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let values_len = values.len();
    let results_len = results.len();
    assert_eq!(values_len, results_len * 2);
    let values = values.as_ptr();
    let results = results.as_mut_ptr();
    assert!(results_len <= u32::MAX as usize);
    let count = results_len as u32;
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = NodesArguments::new(values, results, count);
    NodesFunction::default().launch(&config, &args)
}

pub fn build_merkle_tree_nodes(
    values: &DeviceSlice<DG>,
    results: &mut DeviceSlice<DG>,
    layers_count: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    if layers_count == 0 {
        Ok(())
    } else {
        let values_len = values.len();
        let results_len = results.len();
        let layer = values_len.trailing_zeros();
        assert_eq!(values_len, 1 << layer);
        assert_eq!(values_len, results_len);
        let (nodes, nodes_remaining) = results.split_at_mut(results_len >> 1);
        launch_nodes_kernel(values, nodes, stream)?;
        build_merkle_tree_nodes(nodes, nodes_remaining, layers_count - 1, stream)
    }
}

pub fn build_merkle_tree(
    values: &DeviceSlice<BF>,
    results: &mut DeviceSlice<DG>,
    log_rows_per_hash: u32,
    stream: &CudaStream,
    layers_count: u32,
    bit_reverse_leaves: bool,
) -> CudaResult<()> {
    assert_ne!(layers_count, 0);
    let values_len = values.len();
    let results_len = results.len();
    assert_eq!(results_len % 2, 0);
    let leaves_count = results_len / 2;
    assert!(1 << (layers_count - 1) <= leaves_count);
    assert_eq!(values_len % leaves_count, 0);
    let (leaves, nodes) = results.split_at_mut(leaves_count);
    build_merkle_tree_leaves(values, leaves, log_rows_per_hash, stream)?;
    if bit_reverse_leaves {
        bit_reverse_in_place(leaves, stream)?;
    }
    build_merkle_tree_nodes(leaves, nodes, layers_count - 1, stream)
}

cuda_kernel!(
GatherRows,
ab_gather_rows_kernel(
    indexes: *const u32,
    indexes_count: u32,
    bit_reversed_indexes: bool,
    log_rows_count: u32,
    values: PtrAndStride<BF>,
    results: MutPtrAndStride<BF>,
)
);

pub fn gather_rows(
    indexes: &DeviceSlice<u32>,
    bit_reverse_indexes: bool,
    log_rows_per_index: u32,
    values: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    result: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    stream: &CudaStream,
) -> CudaResult<()> {
    let indexes_len = indexes.len();
    let values_cols = values.cols();
    let values_rows = values.rows();
    assert!(values_rows.is_power_of_two());
    let log_rows_count = values_rows.trailing_zeros();
    let result_rows = result.rows();
    let result_cols = result.cols();
    let rows_per_index = 1 << log_rows_per_index;
    assert_eq!(result_cols, values_cols);
    assert_eq!(result_rows, indexes_len << log_rows_per_index);
    assert!(indexes_len <= u32::MAX as usize);
    let indexes_count = indexes_len as u32;
    let (mut grid_dim, block_dim) = if log_rows_per_index < LOG_WARP_SIZE {
        get_grid_block_dims_for_threads_count(
            1 << (LOG_WARP_SIZE - log_rows_per_index),
            indexes_count,
        )
    } else {
        (indexes_count.into(), 1.into())
    };
    let block_dim = (rows_per_index, block_dim.x);
    assert!(result_cols <= u32::MAX as usize);
    grid_dim.y = result_cols as u32;
    let indexes = indexes.as_ptr();
    let values = values.as_ptr_and_stride();
    let result = result.as_mut_ptr_and_stride();
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GatherRowsArguments::new(
        indexes,
        indexes_count,
        bit_reverse_indexes,
        log_rows_count,
        values,
        result,
    );
    GatherRowsFunction::default().launch(&config, &args)
}

cuda_kernel!(
    GatherLeafRows,
    ab_gather_leaf_rows_kernel(
        indexes: *const u32,
        indexes_count: u32,
        bit_reversed_indexes: bool,
        log_leaves_count: u32,
        log_rows_per_leaf: u32,
        values: PtrAndStride<BF>,
        results: MutPtrAndStride<BF>,
    )
);

pub fn gather_leaf_rows(
    indexes: &DeviceSlice<u32>,
    bit_reverse_indexes: bool,
    log_rows_per_leaf: u32,
    values: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    result: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    stream: &CudaStream,
) -> CudaResult<()> {
    let indexes_len = indexes.len();
    let values_cols = values.cols();
    let values_rows = values.rows();
    assert!(values_rows.is_power_of_two());
    let log_rows_count = values_rows.trailing_zeros();
    assert!(log_rows_count >= log_rows_per_leaf);
    let log_leaves_count = log_rows_count - log_rows_per_leaf;
    let result_rows = result.rows();
    let result_cols = result.cols();
    let rows_per_leaf = 1 << log_rows_per_leaf;
    assert_eq!(result_cols, values_cols);
    assert_eq!(result_rows, indexes_len << log_rows_per_leaf);
    assert!(indexes_len <= u32::MAX as usize);
    let indexes_count = indexes_len as u32;
    let (mut grid_dim, block_dim) = if log_rows_per_leaf < LOG_WARP_SIZE {
        get_grid_block_dims_for_threads_count(
            1 << (LOG_WARP_SIZE - log_rows_per_leaf),
            indexes_count,
        )
    } else {
        (indexes_count.into(), 1.into())
    };
    let block_dim = (rows_per_leaf, block_dim.x);
    assert!(result_cols <= u32::MAX as usize);
    grid_dim.y = result_cols as u32;
    let indexes = indexes.as_ptr();
    let values = values.as_ptr_and_stride();
    let result = result.as_mut_ptr_and_stride();
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GatherLeafRowsArguments::new(
        indexes,
        indexes_count,
        bit_reverse_indexes,
        log_leaves_count,
        log_rows_per_leaf,
        values,
        result,
    );
    GatherLeafRowsFunction::default().launch(&config, &args)
}

cuda_kernel!(
    GatherMerklePaths,
    ab_gather_merkle_paths_kernel(
        indexes: *const u32,
        indexes_count: u32,
        values: *const DG,
        log_leaves_count: u32,
        results: *mut DG,
    )
);

pub fn gather_merkle_paths_device(
    indexes: &DeviceSlice<u32>,
    values: &DeviceSlice<DG>,
    results: &mut DeviceSlice<DG>,
    layers_count: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(indexes.len() <= u32::MAX as usize);
    let indexes_count = indexes.len() as u32;
    let values_count = values.len();
    assert!(values_count.is_power_of_two());
    let log_values_count = values_count.trailing_zeros();
    assert_ne!(log_values_count, 0);
    let log_leaves_count = log_values_count - 1;
    // A per-coset cap of size 1 means the query path spans the full coset subtree depth.
    assert!(layers_count <= log_leaves_count);
    assert_eq!(indexes.len() * layers_count as usize, results.len());
    assert_eq!(WARP_SIZE % STATE_SIZE as u32, 0);
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(WARP_SIZE / STATE_SIZE as u32, indexes_count);
    let grid_dim = (grid_dim.x, layers_count);
    let block_dim = (STATE_SIZE as u32, block_dim.x);
    let indexes = indexes.as_ptr();
    let values = values.as_ptr();
    let result = results.as_mut_ptr();
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args =
        GatherMerklePathsArguments::new(indexes, indexes_count, values, log_leaves_count, result);
    GatherMerklePathsFunction::default().launch(&config, &args)
}

cuda_kernel!(
    GatherRowsAndMerklePaths,
    ab_gather_rows_and_merkle_paths_kernel(
        indexes: *const u32,
        indexes_count: u32,
        bit_reverse_indexes: bool,
        values: *const BF,
        log_rows_per_leaf: u32,
        cols_count: u32,
        log_total_leaves_count: u32,
        leaf_values: MutPtrAndStride<BF>,
        tree_bottom: *const Digest,
        layers_count: u32,
        merkle_paths: *mut Digest,
    )
);

pub fn gather_rows_and_merkle_paths(
    indexes: &DeviceSlice<u32>,
    bit_reverse_indexes: bool,
    values: &DeviceSlice<BF>,
    log_rows_per_leaf: u32,
    leaf_values: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    tree_bottom: &DeviceSlice<Digest>,
    merkle_paths: &mut DeviceSlice<Digest>,
    layers_count: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let indexes_len = indexes.len();
    let values_len = values.len();
    let cols_count = leaf_values.cols();
    assert_eq!(values_len % cols_count, 0);
    let log_rows_count = (values_len / cols_count).trailing_zeros();
    assert_eq!(leaf_values.rows(), indexes_len << log_rows_per_leaf);
    assert!(indexes_len <= u32::MAX as usize);
    let indexes_count = indexes_len as u32;
    assert!(layers_count >= LOG_WARP_SIZE);
    assert_eq!(indexes_len * layers_count as usize, merkle_paths.len());
    assert!(cols_count <= u32::MAX as usize);
    let cols_count = cols_count as u32;
    let log_total_leaves_count = log_rows_count as u32 - log_rows_per_leaf;
    // The fused path is only used for partial-tree queries: it hashes queried leaves, emits the
    // first LOG_WARP_SIZE sibling layers from warp-local reductions, then resumes from tree_bottom.
    let config = CudaLaunchConfig::basic(indexes_count, WARP_SIZE, stream);
    let indexes = indexes.as_ptr();
    let values = values.as_ptr();
    let leaf_values = leaf_values.as_mut_ptr_and_stride();
    let tree_bottom = tree_bottom.as_ptr();
    let merkle_paths = merkle_paths.as_mut_ptr();
    let args = GatherRowsAndMerklePathsArguments::new(
        indexes,
        indexes_count,
        bit_reverse_indexes,
        values,
        log_rows_per_leaf,
        cols_count,
        log_total_leaves_count,
        leaf_values,
        tree_bottom,
        layers_count,
        merkle_paths,
    );
    GatherRowsAndMerklePathsFunction::default().launch(&config, &args)
}

cuda_kernel!(
    GatherMerklePathsFromRows,
    ab_gather_merkle_paths_from_rows_kernel(
        indexes: *const u32,
        indexes_count: u32,
        bit_reverse_indexes: bool,
        values: *const BF,
        log_rows_per_leaf: u32,
        cols_count: u32,
        log_total_leaves_count: u32,
        tree_bottom: *const Digest,
        layers_count: u32,
        merkle_paths: *mut Digest,
    )
);

pub fn gather_merkle_paths_from_rows(
    indexes: &DeviceSlice<u32>,
    bit_reverse_indexes: bool,
    values: &DeviceSlice<BF>,
    log_rows_per_leaf: u32,
    cols_count: usize,
    tree_bottom: &DeviceSlice<Digest>,
    merkle_paths: &mut DeviceSlice<Digest>,
    layers_count: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let indexes_len = indexes.len();
    let values_len = values.len();
    assert_eq!(values_len % cols_count, 0);
    let log_rows_count = (values_len / cols_count).trailing_zeros();
    assert!(indexes_len <= u32::MAX as usize);
    let indexes_count = indexes_len as u32;
    assert!(layers_count >= LOG_WARP_SIZE);
    assert_eq!(indexes_len * layers_count as usize, merkle_paths.len());
    assert!(cols_count <= u32::MAX as usize);
    let cols_count = cols_count as u32;
    let log_total_leaves_count = log_rows_count as u32 - log_rows_per_leaf;
    let config = CudaLaunchConfig::basic(indexes_count, WARP_SIZE, stream);
    let indexes = indexes.as_ptr();
    let values = values.as_ptr();
    let tree_bottom = tree_bottom.as_ptr();
    let merkle_paths = merkle_paths.as_mut_ptr();
    let args = GatherMerklePathsFromRowsArguments::new(
        indexes,
        indexes_count,
        bit_reverse_indexes,
        values,
        log_rows_per_leaf,
        cols_count,
        log_total_leaves_count,
        tree_bottom,
        layers_count,
        merkle_paths,
    );
    GatherMerklePathsFromRowsFunction::default().launch(&config, &args)
}

pub fn merkle_tree_cap(values: &DeviceSlice<DG>, log_tree_cap_size: u32) -> &DeviceSlice<DG> {
    let values_len = values.len();
    assert_ne!(values_len, 0);
    assert!(values_len.is_power_of_two());
    let log_values_len = values_len.trailing_zeros();
    assert!(log_values_len > log_tree_cap_size);
    let offset = values_len - (1 << (log_tree_cap_size + 1));
    &values[offset..offset + (1 << log_tree_cap_size)]
}

cuda_kernel!(Blake2SPow, ab_blake2s_pow_kernel(seed: *const u32, bits_count: u32, max_nonce: u64, result: *mut u64));

cuda_kernel!(
    TranscriptCommit,
    ab_transcript_commit_kernel(seed_io: *mut u32, input: *const u32, input_len: u32)
);

cuda_kernel!(
    TranscriptSqueeze,
    ab_transcript_squeeze_kernel(seed_io: *mut u32, output: *mut u32, output_len: u32)
);

cuda_kernel!(
    TranscriptSqueezeE4,
    ab_transcript_squeeze_e4_kernel(seed_io: *mut u32, output_e4: *mut E4, count: u32)
);

/// Device-side `commit_with_seed`: computes `new_seed = Blake2s(old_seed || input)`.
///
/// `seed` must be exactly `STATE_SIZE` u32 words. Updated in place.
/// `input` contains the field-element data to absorb.
pub fn transcript_commit(
    seed: &mut DeviceSlice<u32>,
    input: &DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(seed.len(), STATE_SIZE);
    let seed_ptr = seed.as_mut_ptr();
    let input_ptr = input.as_ptr();
    let input_len = input.len() as u32;
    let config = CudaLaunchConfig::basic(1u32, 1u32, stream);
    let args = TranscriptCommitArguments::new(seed_ptr, input_ptr, input_len);
    TranscriptCommitFunction::default().launch(&config, &args)
}

/// Device-side `draw_randomness`: expands the seed into `output.len()` u32 words.
///
/// The first `STATE_SIZE` words of `output` are the seed itself (no hashing).
/// If more than `STATE_SIZE` words are requested, additional chunks are produced
/// by iteratively hashing the seed. `seed` is updated in place when
/// `output.len() > STATE_SIZE`.
///
/// `output.len()` must be a positive multiple of `STATE_SIZE`.
pub fn transcript_squeeze(
    seed: &mut DeviceSlice<u32>,
    output: &mut DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(seed.len(), STATE_SIZE);
    let output_len = output.len();
    assert!(output_len > 0);
    assert_eq!(output_len % STATE_SIZE, 0);
    let seed_ptr = seed.as_mut_ptr();
    let output_ptr = output.as_mut_ptr();
    let config = CudaLaunchConfig::basic(1u32, 1u32, stream);
    let args = TranscriptSqueezeArguments::new(seed_ptr, output_ptr, output_len as u32);
    TranscriptSqueezeFunction::default().launch(&config, &args)
}

/// Device-side `draw_random_field_els::<BF, E4>(seed, count)`. Produces `count` E4 challenges
/// in Montgomery form by squeezing raw u32 words from `seed` and applying per-limb
/// `from_raw_repr_with_reduction`. `seed` is updated in place to the post-draw state.
pub fn transcript_squeeze_e4(
    seed: &mut DeviceSlice<u32>,
    output: &mut DeviceSlice<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(seed.len(), STATE_SIZE);
    let count = output.len();
    assert!(count > 0);
    assert!(count <= u32::MAX as usize);
    let seed_ptr = seed.as_mut_ptr();
    let output_ptr = output.as_mut_ptr();
    let config = CudaLaunchConfig::basic(1u32, 1u32, stream);
    let args = TranscriptSqueezeE4Arguments::new(seed_ptr, output_ptr, count as u32);
    TranscriptSqueezeE4Function::default().launch(&config, &args)
}

cuda_kernel!(
    BackwardSumcheckRoundUpdate,
    ab_backward_sumcheck_round_update_kernel(
        reduction_output: *const E4,
        prev_claim_coord: *const E4,
        seed_io: *mut u32,
        claim_io: *mut E4,
        eq_prefactor_io: *mut E4,
        coeffs_out: *mut E4,
        challenge_out: *mut E4,
    )
);

/// Fused device-side per-round backward sumcheck state update.
///
/// Replaces the host callback that runs after each CUB reduction in the
/// backward sumcheck loop. Consumes device-resident state and writes back
/// updated state plus the new folding challenge — no host round-trip.
///
/// Buffer contracts:
/// - `reduction_output`: 2 E4 values `[e_partial, c_partial]` (constant and
///   quadratic coefficients from the CUB reduction over round accumulators).
/// - `prev_claim_coord`: 1 E4, the previous-round claim point coordinate.
/// - `seed`: `STATE_SIZE` u32 words, updated in place with the new Blake2s seed.
/// - `claim`: 1 E4, updated in place to `poly(challenge)`.
/// - `eq_prefactor`: 1 E4, updated in place to `eq(challenge, prev_coord)`.
/// - `coeffs_out`: 4 E4 values `[c0, c1, c2, c3]`, the round's univariate
///   coefficients, written for later bulk readback.
/// - `challenge_out`: 1 E4, the next round's folding challenge.
pub fn backward_sumcheck_round_update(
    reduction_output: &DeviceSlice<E4>,
    prev_claim_coord: &DeviceSlice<E4>,
    seed: &mut DeviceSlice<u32>,
    claim: &mut DeviceSlice<E4>,
    eq_prefactor: &mut DeviceSlice<E4>,
    coeffs_out: &mut DeviceSlice<E4>,
    challenge_out: &mut DeviceSlice<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(reduction_output.len(), 2);
    assert_eq!(prev_claim_coord.len(), 1);
    assert_eq!(seed.len(), STATE_SIZE);
    assert_eq!(claim.len(), 1);
    assert_eq!(eq_prefactor.len(), 1);
    assert_eq!(coeffs_out.len(), 4);
    assert_eq!(challenge_out.len(), 1);
    let config = CudaLaunchConfig::basic(1u32, 1u32, stream);
    let args = BackwardSumcheckRoundUpdateArguments::new(
        reduction_output.as_ptr(),
        prev_claim_coord.as_ptr(),
        seed.as_mut_ptr(),
        claim.as_mut_ptr(),
        eq_prefactor.as_mut_ptr(),
        coeffs_out.as_mut_ptr(),
        challenge_out.as_mut_ptr(),
    );
    BackwardSumcheckRoundUpdateFunction::default().launch(&config, &args)
}

cuda_kernel!(
    WhirFoldRoundUpdate,
    ab_whir_fold_round_update_kernel(
        reduction_output: *const E4,
        seed_io: *mut u32,
        coeffs_out: *mut E4,
        challenge_out: *mut E4,
    )
);

/// Fused device-side per-round WHIR fold state update.
///
/// Replaces the host callback that runs after each special 3-point reduction
/// in the WHIR folding loop. Consumes device-resident state and writes back
/// the new coefficients, challenge, and updated seed — no host round-trip.
///
/// Buffer contracts:
/// - `reduction_output`: 3 E4 values `[f(0), f(1), ⟨eval_l+eval_h, eq_l+eq_h⟩]`
///   as produced by the three reductions in `schedule_special_three_point_eval_device`.
///   The kernel scales the third element by `1/4` internally to obtain `f(1/2)`.
/// - `seed`: `STATE_SIZE` u32 words, updated in place with the new Blake2s seed.
/// - `coeffs_out`: 3 E4 values `[c0, c1, c2]`, the round's sumcheck polynomial
///   coefficients, written for later bulk readback.
/// - `challenge_out`: 1 E4, the next round's folding challenge.
pub fn whir_fold_round_update(
    reduction_output: &DeviceSlice<E4>,
    seed: &mut DeviceSlice<u32>,
    coeffs_out: &mut DeviceSlice<E4>,
    challenge_out: &mut DeviceSlice<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(reduction_output.len(), 3);
    assert_eq!(seed.len(), STATE_SIZE);
    assert_eq!(coeffs_out.len(), 3);
    assert_eq!(challenge_out.len(), 1);
    let config = CudaLaunchConfig::basic(1u32, 1u32, stream);
    let args = WhirFoldRoundUpdateArguments::new(
        reduction_output.as_ptr(),
        seed.as_mut_ptr(),
        coeffs_out.as_mut_ptr(),
        challenge_out.as_mut_ptr(),
    );
    WhirFoldRoundUpdateFunction::default().launch(&config, &args)
}

cuda_kernel!(
    BackwardNewClaimsTwoVar,
    ab_backward_new_claims_two_var_kernel(
        last_evals_packed: *const E4,
        challenges: *const E4,
        new_claims_out: *mut E4,
        num_addresses: u32,
    )
);

cuda_kernel!(
    BackwardNewClaimsLinear,
    ab_backward_new_claims_linear_kernel(
        last_evals_packed: *const E4,
        challenges: *const E4,
        new_claims_out: *mut E4,
        num_addresses: u32,
    )
);

/// Device-side per-address dim-reducing `new_claims` evaluator.
///
/// Replaces the host loop inside the end-of-layer final-readback callback
/// that computed `evaluate_with_two_variable_eq_ext(values, r_before_last,
/// r_last)` per address. `last_evals_packed` holds 4 E4 values per address,
/// `challenges` holds `[r_before_last, r_last]`. Produces `num_addresses`
/// E4 outputs.
pub fn backward_new_claims_two_var(
    last_evals_packed: &DeviceSlice<E4>,
    challenges: &DeviceSlice<E4>,
    new_claims_out: &mut DeviceSlice<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let num_addresses = new_claims_out.len();
    assert!(num_addresses > 0);
    assert!(num_addresses <= u32::MAX as usize);
    assert_eq!(last_evals_packed.len(), num_addresses * 4);
    assert!(challenges.len() >= 2);
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(WARP_SIZE * 4, num_addresses as u32);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = BackwardNewClaimsTwoVarArguments::new(
        last_evals_packed.as_ptr(),
        challenges.as_ptr(),
        new_claims_out.as_mut_ptr(),
        num_addresses as u32,
    );
    BackwardNewClaimsTwoVarFunction::default().launch(&config, &args)
}

/// Device-side per-address main-layer `new_claims` evaluator.
///
/// Replaces the host loop inside the end-of-layer final-readback callback
/// that computed `interpolate_linear(f0, f1, last_r)` per address.
/// `last_evals_packed` holds 2 E4 values per address, `challenges` holds
/// `[last_r, ..]`. Produces `num_addresses` E4 outputs.
pub fn backward_new_claims_linear(
    last_evals_packed: &DeviceSlice<E4>,
    challenges: &DeviceSlice<E4>,
    new_claims_out: &mut DeviceSlice<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let num_addresses = new_claims_out.len();
    assert!(num_addresses > 0);
    assert!(num_addresses <= u32::MAX as usize);
    assert_eq!(last_evals_packed.len(), num_addresses * 2);
    assert!(!challenges.is_empty());
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(WARP_SIZE * 4, num_addresses as u32);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = BackwardNewClaimsLinearArguments::new(
        last_evals_packed.as_ptr(),
        challenges.as_ptr(),
        new_claims_out.as_mut_ptr(),
        num_addresses as u32,
    );
    BackwardNewClaimsLinearFunction::default().launch(&config, &args)
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

pub fn blake2s_pow(
    seed: &DeviceSlice<u32>,
    bits_count: u32,
    max_nonce: u64,
    result: &mut DeviceVariable<u64>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(seed.len(), STATE_SIZE);
    unsafe {
        memory_set_async(result.transmute_mut(), 0xff, stream)?;
    }
    const BLOCK_SIZE: u32 = WARP_SIZE * 4;
    let device_id = get_device()?;
    let mpc = device_get_attribute(CudaDeviceAttr::MultiProcessorCount, device_id)?;
    let kernel_function = Blake2SPowFunction::default();
    let max_blocks = max_active_blocks_per_multiprocessor(&kernel_function, BLOCK_SIZE as i32, 0)?;
    let num_blocks = (mpc * max_blocks) as u32;
    let config = CudaLaunchConfig::basic(num_blocks, BLOCK_SIZE, stream);
    let seed = seed.as_ptr();
    let result = result.as_mut_ptr();
    let args = Blake2SPowArguments {
        seed,
        bits_count,
        max_nonce,
        result,
    };
    kernel_function.launch(&config, &args)
}

#[cfg(test)]
mod tests {
    use std::default::Default;

    use blake2s_u32::Blake2sState;
    use era_cudart::memory::{memory_copy_async, DeviceAllocation};
    use field::Field;
    use itertools::Itertools;
    use prover::transcript::Seed;
    type Blake2sTranscript = prover::transcript::Blake2sTranscript<
        { prover::definitions::USE_REDUCED_BLAKE2_ROUNDS },
    >;
    use rand::Rng;
    #[cfg(feature = "deterministic_pow")]
    use worker::Worker;

    use super::*;
    use crate::ops::simple::set_to_zero;
    use crate::primitives::device_structures::{DeviceMatrix, DeviceMatrixMut};
    use crate::primitives::utils::GetChunksCount;

    const USE_REDUCED_BLAKE2_ROUNDS: bool = true;

    fn bitreverse_index(index: usize, num_bits: u32) -> usize {
        if num_bits == 0 {
            0
        } else {
            index.reverse_bits() >> (usize::BITS - num_bits)
        }
    }

    fn leaf_source_row(
        leaf_index: usize,
        row_slot: usize,
        log_rows_per_hash: u32,
        leaves_count: usize,
    ) -> usize {
        leaf_index + bitreverse_index(row_slot, log_rows_per_hash) * leaves_count
    }

    fn verify_leaves(values: &[BF], results: &[Digest], log_rows_per_hash: u32) {
        let leaves_count = results.len();
        let values_len = values.len();
        assert_eq!(values_len % (leaves_count << log_rows_per_hash), 0);
        let cols_count = values_len / (leaves_count << log_rows_per_hash);
        let rows_count = 1 << log_rows_per_hash;
        let domain_size = leaves_count << log_rows_per_hash;
        for leaf_index in 0..leaves_count {
            let mut input = vec![];
            for col in 0..cols_count {
                for row_slot in 0..rows_count {
                    let row =
                        leaf_source_row(leaf_index, row_slot, log_rows_per_hash, leaves_count);
                    input.push(values[col * domain_size + row]);
                }
            }
            let blocks_count = input.len().get_chunks_count(BLOCK_SIZE);
            let mut state = Blake2sState::new();
            let mut expected = Digest::default();
            for (block_index, chunk) in input.iter().chunks(BLOCK_SIZE).into_iter().enumerate() {
                let chunk = chunk.cloned().collect_vec();
                let block_len = chunk.len();
                let mut block = [0; BLOCK_SIZE];
                let chunk = chunk
                    .into_iter()
                    .map(|x| x.0)
                    .chain(std::iter::repeat(0))
                    .take(BLOCK_SIZE)
                    .collect_vec();
                block.copy_from_slice(&chunk);
                if block_index == blocks_count - 1 {
                    state.absorb_final_block::<USE_REDUCED_BLAKE2_ROUNDS>(
                        &block,
                        block_len,
                        &mut expected,
                    );
                } else {
                    state.absorb::<USE_REDUCED_BLAKE2_ROUNDS>(&block);
                }
            }
            let actual = results[leaf_index];
            assert_eq!(expected, actual);
        }
    }

    fn verify_nodes(values: &[Digest], results: &[Digest]) {
        let results_len = results.len();
        let values_len = values.len();
        assert_eq!(values_len, results_len * 2);
        values
            .chunks_exact(2)
            .zip(results)
            .for_each(|(input, &actual)| {
                let state = input
                    .iter()
                    .flat_map(|&x| x.into_iter())
                    .collect_vec()
                    .try_into()
                    .unwrap();
                let mut expected = Digest::default();
                Blake2sState::compress_two_to_one::<USE_REDUCED_BLAKE2_ROUNDS>(
                    &state,
                    &mut expected,
                );
                assert_eq!(expected, actual);
            });
    }

    fn random_digest() -> Digest {
        let mut rng = rand::rng();
        let mut result = Digest::default();
        result.fill_with(|| rng.random());
        result
    }

    #[test]
    fn leaves() {
        const LOG_N: usize = 10;
        const N: usize = 1 << LOG_N;
        const VALUES_PER_ROW: usize = 125;
        const LOG_ROWS_PER_HASH: u32 = 1;
        let mut values_host = vec![BF::ZERO; (N * VALUES_PER_ROW) << LOG_ROWS_PER_HASH];
        let mut rng = rand::rng();
        values_host.fill_with(|| BF::from_nonreduced_u32(rng.random()));
        let mut results_host = vec![Digest::default(); N];
        let stream = CudaStream::default();
        let mut values_device = DeviceAllocation::alloc(values_host.len()).unwrap();
        let mut results_device = DeviceAllocation::alloc(results_host.len()).unwrap();
        memory_copy_async(&mut values_device, &values_host, &stream).unwrap();
        launch_leaves_kernel(
            &values_device,
            &mut results_device,
            LOG_ROWS_PER_HASH,
            &stream,
        )
        .unwrap();
        memory_copy_async(&mut results_host, &results_device, &stream).unwrap();
        stream.synchronize().unwrap();
        verify_leaves(&values_host, &results_host, LOG_ROWS_PER_HASH);
    }

    #[test]
    fn blake2s_nodes() {
        const LOG_N: usize = 10;
        const N: usize = 1 << LOG_N;
        let mut values_host = vec![Digest::default(); N * 2];
        values_host.fill_with(random_digest);
        let mut results_host = vec![Digest::default(); N];
        let stream = CudaStream::default();
        let mut values_device = DeviceAllocation::alloc(values_host.len()).unwrap();
        let mut results_device = DeviceAllocation::alloc(results_host.len()).unwrap();
        memory_copy_async(&mut values_device, &values_host, &stream).unwrap();
        launch_nodes_kernel(&values_device, &mut results_device, &stream).unwrap();
        memory_copy_async(&mut results_host, &results_device, &stream).unwrap();
        stream.synchronize().unwrap();
        verify_nodes(&values_host, &results_host);
    }

    fn verify_tree(values: &[Digest], results: &[Digest], layers_count: u32) {
        assert_eq!(values.len(), results.len());
        if layers_count == 0 {
            assert!(results.iter().all(|x| x.iter().all(|&x| x == 0)));
        } else {
            let (nodes, nodes_remaining) = results.split_at(results.len() >> 1);
            verify_nodes(values, nodes);
            verify_tree(nodes, nodes_remaining, layers_count - 1);
        }
    }

    fn test_merkle_tree(log_n: usize) {
        const VALUES_PER_ROW: usize = 125;
        const LOG_ROWS_PER_HASH: u32 = 1;
        let n = 1 << log_n;
        let layers_count: u32 = (log_n + 1) as u32;
        let mut values_host = vec![BF::ZERO; (n * VALUES_PER_ROW) << LOG_ROWS_PER_HASH];
        let mut rng = rand::rng();
        values_host.fill_with(|| BF::from_nonreduced_u32(rng.random()));
        let mut results_host = vec![Digest::default(); n * 2];
        let stream = CudaStream::default();
        let mut values_device = DeviceAllocation::alloc(values_host.len()).unwrap();
        let mut results_device = DeviceAllocation::alloc(results_host.len()).unwrap();
        set_to_zero(&mut results_device, &stream).unwrap();
        memory_copy_async(&mut values_device, &values_host, &stream).unwrap();
        build_merkle_tree(
            &values_device,
            &mut results_device,
            LOG_ROWS_PER_HASH,
            &stream,
            layers_count,
            false,
        )
        .unwrap();
        memory_copy_async(&mut results_host, &results_device, &stream).unwrap();
        stream.synchronize().unwrap();
        let (nodes, nodes_remaining) = results_host.split_at(results_host.len() >> 1);
        verify_leaves(&values_host, nodes, LOG_ROWS_PER_HASH);
        verify_tree(nodes, nodes_remaining, layers_count - 1);
    }

    #[test]
    fn merkle_tree_small() {
        test_merkle_tree(8);
    }

    #[test]
    #[ignore]
    fn merkle_tree_large() {
        test_merkle_tree(16);
    }

    #[test]
    fn gather_rows() {
        const SRC_LOG_ROWS: usize = 12;
        const SRC_ROWS: usize = 1 << SRC_LOG_ROWS;
        const COLS: usize = 16;
        const INDEXES_COUNT: usize = 42;
        const LOG_ROWS_PER_INDEX: usize = 1;
        const DST_ROWS: usize = INDEXES_COUNT << LOG_ROWS_PER_INDEX;
        let mut rng = rand::rng();
        let mut indexes_host = vec![0; INDEXES_COUNT];
        indexes_host.fill_with(|| rng.random_range(0..INDEXES_COUNT as u32));
        let mut values_host = vec![BF::ZERO; SRC_ROWS * COLS];
        values_host.fill_with(|| BF::from_nonreduced_u32(rng.random()));
        let mut results_host = vec![BF::ZERO; DST_ROWS * COLS];
        let stream = CudaStream::default();
        let mut indexes_device = DeviceAllocation::<u32>::alloc(indexes_host.len()).unwrap();
        let mut values_device = DeviceAllocation::<BF>::alloc(values_host.len()).unwrap();
        let mut results_device = DeviceAllocation::<BF>::alloc(results_host.len()).unwrap();
        memory_copy_async(&mut indexes_device, &indexes_host, &stream).unwrap();
        memory_copy_async(&mut values_device, &values_host, &stream).unwrap();
        super::gather_rows(
            &indexes_device,
            false,
            LOG_ROWS_PER_INDEX as u32,
            &DeviceMatrix::new(&values_device, SRC_ROWS),
            &mut DeviceMatrixMut::new(&mut results_device, DST_ROWS),
            &stream,
        )
        .unwrap();
        memory_copy_async(&mut results_host, &results_device, &stream).unwrap();
        stream.synchronize().unwrap();
        for (i, index) in indexes_host.into_iter().enumerate() {
            let src_index = (index as usize) << LOG_ROWS_PER_INDEX;
            let dst_index = i << LOG_ROWS_PER_INDEX;
            for j in 0..1 << LOG_ROWS_PER_INDEX {
                let src_index = src_index + j;
                let dst_index = dst_index + j;
                for k in 0..COLS {
                    let expected = values_host[(k << SRC_LOG_ROWS) + src_index];
                    let actual = results_host[(k * DST_ROWS) + dst_index];
                    assert_eq!(expected, actual);
                }
            }
        }
    }

    #[test]
    fn gather_leaf_rows() {
        const SRC_LOG_ROWS: usize = 12;
        const SRC_ROWS: usize = 1 << SRC_LOG_ROWS;
        const COLS: usize = 16;
        const LOG_ROWS_PER_LEAF: usize = 2;
        const LEAVES_COUNT: usize = SRC_ROWS >> LOG_ROWS_PER_LEAF;
        const INDEXES_COUNT: usize = 42;
        const DST_ROWS: usize = INDEXES_COUNT << LOG_ROWS_PER_LEAF;
        let mut rng = rand::rng();
        let mut indexes_host = vec![0; INDEXES_COUNT];
        indexes_host.fill_with(|| rng.random_range(0..LEAVES_COUNT as u32));
        let mut values_host = vec![BF::ZERO; SRC_ROWS * COLS];
        values_host.fill_with(|| BF::from_nonreduced_u32(rng.random()));
        let mut results_host = vec![BF::ZERO; DST_ROWS * COLS];
        let stream = CudaStream::default();
        let mut indexes_device = DeviceAllocation::<u32>::alloc(indexes_host.len()).unwrap();
        let mut values_device = DeviceAllocation::<BF>::alloc(values_host.len()).unwrap();
        let mut results_device = DeviceAllocation::<BF>::alloc(results_host.len()).unwrap();
        memory_copy_async(&mut indexes_device, &indexes_host, &stream).unwrap();
        memory_copy_async(&mut values_device, &values_host, &stream).unwrap();
        super::gather_leaf_rows(
            &indexes_device,
            false,
            LOG_ROWS_PER_LEAF as u32,
            &DeviceMatrix::new(&values_device, SRC_ROWS),
            &mut DeviceMatrixMut::new(&mut results_device, DST_ROWS),
            &stream,
        )
        .unwrap();
        memory_copy_async(&mut results_host, &results_device, &stream).unwrap();
        stream.synchronize().unwrap();
        for (i, index) in indexes_host.into_iter().enumerate() {
            let src_leaf = index as usize;
            let dst_row_base = i << LOG_ROWS_PER_LEAF;
            for j in 0..(1 << LOG_ROWS_PER_LEAF) {
                let src_row = leaf_source_row(src_leaf, j, LOG_ROWS_PER_LEAF as u32, LEAVES_COUNT);
                let dst_row = dst_row_base + j;
                for k in 0..COLS {
                    let expected = values_host[(k << SRC_LOG_ROWS) + src_row];
                    let actual = results_host[(k * DST_ROWS) + dst_row];
                    assert_eq!(expected, actual);
                }
            }
        }
    }

    #[test]
    fn gather_merkle_paths() {
        const LOG_LEAVES_COUNT: usize = 12;
        const INDEXES_COUNT: usize = 42;
        const LAYERS_COUNT: usize = LOG_LEAVES_COUNT - 4;
        let mut rng = rand::rng();
        let mut indexes_host = vec![0; INDEXES_COUNT];
        indexes_host.fill_with(|| rng.random_range(0..1u32 << LOG_LEAVES_COUNT));
        let mut values_host = vec![Digest::default(); 1 << (LOG_LEAVES_COUNT + 1)];
        values_host.fill_with(random_digest);
        let mut results_host = vec![Digest::default(); INDEXES_COUNT * LAYERS_COUNT];
        let stream = CudaStream::default();
        let mut indexes_device = DeviceAllocation::alloc(indexes_host.len()).unwrap();
        let mut values_device = DeviceAllocation::alloc(values_host.len()).unwrap();
        let mut results_device = DeviceAllocation::alloc(results_host.len()).unwrap();
        memory_copy_async(&mut indexes_device, &indexes_host, &stream).unwrap();
        memory_copy_async(&mut values_device, &values_host, &stream).unwrap();
        gather_merkle_paths_device(
            &indexes_device,
            &values_device,
            &mut results_device,
            LAYERS_COUNT as u32,
            &stream,
        )
        .unwrap();
        memory_copy_async(&mut results_host, &results_device, &stream).unwrap();
        stream.synchronize().unwrap();
        fn verify_merkle_path(indexes: &[u32], values: &[Digest], results: &[Digest]) {
            let (values, values_next) = values.split_at(values.len() >> 1);
            let (results, results_next) = results.split_at(INDEXES_COUNT);
            for (row_index, &index) in indexes.iter().enumerate() {
                let sibling_index = (index ^ 1) as usize;
                let expected = values[sibling_index];
                let actual = results[row_index];
                assert_eq!(expected, actual);
            }
            if !results_next.is_empty() {
                let indexes_next = indexes.iter().map(|&x| x >> 1).collect_vec();
                verify_merkle_path(&indexes_next, values_next, results_next);
            }
        }
        verify_merkle_path(&indexes_host, &values_host, &results_host);
    }

    #[test]
    fn merkle_tree_cap() {
        const LOG_N: u32 = 10;
        const N: usize = 1 << LOG_N;
        const LOG_CAP_SIZE: u32 = LOG_N - 1;
        const CAP_SIZE: usize = 1 << LOG_CAP_SIZE;
        let mut values_host = vec![Digest::default(); N * 2];
        let mut counter: u32 = 0;
        values_host.fill_with(|| {
            let value = counter;
            counter += 1;
            [value; STATE_SIZE]
        });
        let mut values_device = DeviceAllocation::alloc(values_host.len()).unwrap();
        let stream = CudaStream::create().unwrap();
        memory_copy_async(&mut values_device, &values_host, &stream).unwrap();
        let cap_device = super::merkle_tree_cap(&values_device, LOG_CAP_SIZE);
        let mut cap_host = vec![Digest::default(); CAP_SIZE];
        memory_copy_async(&mut cap_host, cap_device, &stream).unwrap();
        stream.synchronize().unwrap();
        assert_eq!(cap_host.len(), CAP_SIZE);
        assert_eq!(cap_host, values_host[N..3 * N / 2]);
    }

    #[test]
    fn pow() {
        const BITS_COUNT: u32 = 24;
        let h_seed = [42u32; STATE_SIZE];
        let mut h_result = [0u64; 1];
        let mut d_seed = DeviceAllocation::alloc(STATE_SIZE).unwrap();
        let mut d_result = DeviceAllocation::alloc(1).unwrap();
        let stream = CudaStream::default();
        memory_copy_async(&mut d_seed, &h_seed, &stream).unwrap();
        blake2s_pow(&d_seed, BITS_COUNT, u64::MAX, &mut d_result[0], &stream).unwrap();
        memory_copy_async(&mut h_result, &d_result, &stream).unwrap();
        stream.synchronize().unwrap();
        let mut state = Blake2sState::new();
        let mut block = [0; BLOCK_SIZE];
        block[..STATE_SIZE].copy_from_slice(&h_seed);
        block[STATE_SIZE] = h_result[0] as u32;
        block[STATE_SIZE + 1] = (h_result[0] >> 32) as u32;
        let mut digest = Digest::default();
        state.absorb_final_block::<USE_REDUCED_BLAKE2_ROUNDS>(&block, STATE_SIZE + 2, &mut digest);
        assert!(digest[0].leading_zeros() >= BITS_COUNT);
    }

    #[cfg(feature = "deterministic_pow")]
    #[test]
    fn pow_deterministic_matches_cpu_baseline() {
        let seeds = [
            Seed([0, 1, 2, 3, 4, 5, 6, 7]),
            Seed([42, 42, 42, 42, 42, 42, 42, 42]),
            Seed([
                0x01234567, 0x89abcdef, 0xfedcba98, 0x76543210, 0x0f0f0f0f, 0xf0f0f0f0, 0x13579bdf,
                0x2468ace0,
            ]),
        ];
        let worker = Worker::new_with_num_threads(4);
        let stream = CudaStream::default();

        for seed in seeds {
            for pow_bits in [17, 18, 20] {
                let (_, expected_nonce) = Blake2sTranscript::search_pow(&seed, pow_bits, &worker);
                let mut h_result = [0u64; 1];
                let mut d_seed = DeviceAllocation::alloc(STATE_SIZE).unwrap();
                let mut d_result = DeviceAllocation::alloc(1).unwrap();
                memory_copy_async(&mut d_seed, &seed.0, &stream).unwrap();
                blake2s_pow(&d_seed, pow_bits, u64::MAX, &mut d_result[0], &stream).unwrap();
                memory_copy_async(&mut h_result, &d_result, &stream).unwrap();
                stream.synchronize().unwrap();
                assert_eq!(
                    h_result[0], expected_nonce,
                    "seed={seed:?}, pow_bits={pow_bits}"
                );
            }
        }
    }

    // -----------------------------------------------------------------------
    // Device-side transcript parity tests
    // -----------------------------------------------------------------------

    /// Helper: run device-side transcript_commit and return the resulting seed.
    fn device_commit(seed: &[u32; STATE_SIZE], input: &[u32]) -> [u32; STATE_SIZE] {
        let stream = CudaStream::default();
        let mut d_seed = DeviceAllocation::alloc(STATE_SIZE).unwrap();
        let mut d_input = DeviceAllocation::alloc(input.len()).unwrap();
        memory_copy_async(&mut d_seed, &seed[..], &stream).unwrap();
        memory_copy_async(&mut d_input, input, &stream).unwrap();
        super::transcript_commit(&mut d_seed, &d_input, &stream).unwrap();
        let mut h_result = [0u32; STATE_SIZE];
        memory_copy_async(&mut h_result[..], &d_seed, &stream).unwrap();
        stream.synchronize().unwrap();
        h_result
    }

    /// Helper: run host-side commit_with_seed and return the resulting seed.
    fn host_commit(seed: &[u32; STATE_SIZE], input: &[u32]) -> [u32; STATE_SIZE] {
        let mut s = Seed(*seed);
        Blake2sTranscript::commit_with_seed(&mut s, input);
        s.0
    }

    #[test]
    fn transcript_commit_parity_small() {
        // 8 (seed) + 4 (input) = 12 words — fits in one block with padding.
        let seed = [1, 2, 3, 4, 5, 6, 7, 8];
        let input: Vec<u32> = (10..14).collect();
        assert_eq!(device_commit(&seed, &input), host_commit(&seed, &input));
    }

    #[test]
    fn transcript_commit_parity_exact_block() {
        // 8 + 8 = 16 words — exactly one full block.
        let seed = [0xaa; STATE_SIZE];
        let input: Vec<u32> = (0..8).collect();
        assert_eq!(device_commit(&seed, &input), host_commit(&seed, &input));
    }

    #[test]
    fn transcript_commit_parity_two_blocks() {
        // 8 + 12 = 20 words — two blocks (16 + 4). This is the typical backward
        // sumcheck case: commit_field_els with 3 E4 elements.
        let seed = [0x42; STATE_SIZE];
        let input: Vec<u32> = (100..112).collect();
        assert_eq!(device_commit(&seed, &input), host_commit(&seed, &input));
    }

    #[test]
    fn transcript_commit_parity_large() {
        // 8 + 32 = 40 words — three blocks (16 + 16 + 8).
        let seed = [0xde, 0xad, 0xbe, 0xef, 0xca, 0xfe, 0xba, 0xbe];
        let input: Vec<u32> = (0..32).collect();
        assert_eq!(device_commit(&seed, &input), host_commit(&seed, &input));
    }

    #[test]
    fn transcript_commit_parity_randomized() {
        let mut rng = rand::rng();
        let stream = CudaStream::default();
        for input_len in [1, 4, 7, 8, 12, 15, 16, 20, 24, 31, 32, 48, 64] {
            let seed: [u32; STATE_SIZE] = std::array::from_fn(|_| rng.random());
            let input: Vec<u32> = (0..input_len).map(|_| rng.random()).collect();

            let expected = host_commit(&seed, &input);

            let mut d_seed = DeviceAllocation::alloc(STATE_SIZE).unwrap();
            let mut d_input = DeviceAllocation::alloc(input_len).unwrap();
            memory_copy_async(&mut d_seed, &seed[..], &stream).unwrap();
            memory_copy_async(&mut d_input, &input, &stream).unwrap();
            super::transcript_commit(&mut d_seed, &d_input, &stream).unwrap();
            let mut actual = [0u32; STATE_SIZE];
            memory_copy_async(&mut actual[..], &d_seed, &stream).unwrap();
            stream.synchronize().unwrap();

            assert_eq!(
                actual, expected,
                "commit mismatch for input_len={input_len}"
            );
        }
    }

    /// Helper: run device-side transcript_squeeze and return output + final seed.
    fn device_squeeze(
        seed: &[u32; STATE_SIZE],
        output_len: usize,
    ) -> (Vec<u32>, [u32; STATE_SIZE]) {
        let stream = CudaStream::default();
        let mut d_seed = DeviceAllocation::alloc(STATE_SIZE).unwrap();
        let mut d_output = DeviceAllocation::alloc(output_len).unwrap();
        memory_copy_async(&mut d_seed, &seed[..], &stream).unwrap();
        super::transcript_squeeze(&mut d_seed, &mut d_output, &stream).unwrap();
        let mut h_output = vec![0u32; output_len];
        let mut h_seed = [0u32; STATE_SIZE];
        memory_copy_async(&mut h_output, &d_output, &stream).unwrap();
        memory_copy_async(&mut h_seed[..], &d_seed, &stream).unwrap();
        stream.synchronize().unwrap();
        (h_output, h_seed)
    }

    /// Helper: run host-side draw_randomness and return output + final seed.
    fn host_squeeze(seed: &[u32; STATE_SIZE], output_len: usize) -> (Vec<u32>, [u32; STATE_SIZE]) {
        let mut s = Seed(*seed);
        let mut output = vec![0u32; output_len];
        Blake2sTranscript::draw_randomness(&mut s, &mut output);
        (output, s.0)
    }

    #[test]
    fn transcript_squeeze_parity_one_round() {
        // 8 words = 1 round, seed unchanged, output = seed.
        let seed = [10, 20, 30, 40, 50, 60, 70, 80];
        let (d_out, d_seed) = device_squeeze(&seed, STATE_SIZE);
        let (h_out, h_seed) = host_squeeze(&seed, STATE_SIZE);
        assert_eq!(d_out, h_out);
        assert_eq!(d_seed, h_seed);
        // Seed must be unchanged for single-round squeeze.
        assert_eq!(d_seed, seed);
    }

    #[test]
    fn transcript_squeeze_parity_two_rounds() {
        // 16 words = 2 rounds. Second round hashes the seed.
        let seed = [0xff; STATE_SIZE];
        let (d_out, d_seed) = device_squeeze(&seed, STATE_SIZE * 2);
        let (h_out, h_seed) = host_squeeze(&seed, STATE_SIZE * 2);
        assert_eq!(d_out, h_out);
        assert_eq!(d_seed, h_seed);
    }

    #[test]
    fn transcript_squeeze_parity_many_rounds() {
        // 40 words = 5 rounds.
        let seed = [0x42; STATE_SIZE];
        let (d_out, d_seed) = device_squeeze(&seed, STATE_SIZE * 5);
        let (h_out, h_seed) = host_squeeze(&seed, STATE_SIZE * 5);
        assert_eq!(d_out, h_out);
        assert_eq!(d_seed, h_seed);
    }

    #[test]
    fn transcript_commit_then_squeeze_parity() {
        // Simulates the backward sumcheck pattern: commit 3 E4 coefficients (12
        // words), then draw 1 E4 challenge (4 words, padded to 8 = 1 round).
        let seed = [0xab; STATE_SIZE];
        let coeffs: Vec<u32> = (0..12).collect();

        // Host path.
        let mut h_seed = Seed(seed);
        Blake2sTranscript::commit_with_seed(&mut h_seed, &coeffs);
        let mut h_challenge = vec![0u32; STATE_SIZE];
        Blake2sTranscript::draw_randomness(&mut h_seed, &mut h_challenge);

        // Device path.
        let stream = CudaStream::default();
        let mut d_seed = DeviceAllocation::alloc(STATE_SIZE).unwrap();
        let mut d_input = DeviceAllocation::alloc(coeffs.len()).unwrap();
        let mut d_challenge = DeviceAllocation::alloc(STATE_SIZE).unwrap();
        memory_copy_async(&mut d_seed, &seed[..], &stream).unwrap();
        memory_copy_async(&mut d_input, &coeffs, &stream).unwrap();
        super::transcript_commit(&mut d_seed, &d_input, &stream).unwrap();
        super::transcript_squeeze(&mut d_seed, &mut d_challenge, &stream).unwrap();
        let mut actual_seed = [0u32; STATE_SIZE];
        let mut actual_challenge = vec![0u32; STATE_SIZE];
        memory_copy_async(&mut actual_seed[..], &d_seed, &stream).unwrap();
        memory_copy_async(&mut actual_challenge, &d_challenge, &stream).unwrap();
        stream.synchronize().unwrap();

        assert_eq!(actual_seed, h_seed.0);
        assert_eq!(actual_challenge, h_challenge);
    }

    /// Helper: run device-side `transcript_squeeze_e4` and return output E4s + final seed.
    fn device_squeeze_e4(seed: &[u32; STATE_SIZE], count: usize) -> (Vec<E4>, [u32; STATE_SIZE]) {
        let stream = CudaStream::default();
        let mut d_seed = DeviceAllocation::alloc(STATE_SIZE).unwrap();
        let mut d_output: DeviceAllocation<E4> = DeviceAllocation::alloc(count).unwrap();
        memory_copy_async(&mut d_seed, &seed[..], &stream).unwrap();
        super::transcript_squeeze_e4(&mut d_seed, &mut d_output, &stream).unwrap();
        let mut h_output = vec![E4::ZERO; count];
        let mut h_seed = [0u32; STATE_SIZE];
        memory_copy_async(&mut h_output, &d_output, &stream).unwrap();
        memory_copy_async(&mut h_seed[..], &d_seed, &stream).unwrap();
        stream.synchronize().unwrap();
        (h_output, h_seed)
    }

    /// Helper: host `draw_random_field_els::<BF, E4>` returning challenges + final seed.
    fn host_draw_e4(seed: &[u32; STATE_SIZE], count: usize) -> (Vec<E4>, [u32; STATE_SIZE]) {
        use prover::gkr::prover::transcript_utils::draw_random_field_els;
        let mut s = Seed(*seed);
        let challenges = draw_random_field_els::<BF, E4>(&mut s, count);
        (challenges, s.0)
    }

    #[test]
    fn transcript_squeeze_e4_parity_single() {
        // 1 E4 = 4 u32 words, padded to 1 round (STATE_SIZE = 8).
        let seed = [0x11; STATE_SIZE];
        let (d_out, d_seed) = device_squeeze_e4(&seed, 1);
        let (h_out, h_seed) = host_draw_e4(&seed, 1);
        assert_eq!(d_out, h_out);
        assert_eq!(d_seed, h_seed);
    }

    #[test]
    fn transcript_squeeze_e4_parity_two_in_one_round() {
        // 2 E4 = 8 u32 words, exactly 1 round. Both E4s drawn from the verbatim seed.
        let seed = [0x22; STATE_SIZE];
        let (d_out, d_seed) = device_squeeze_e4(&seed, 2);
        let (h_out, h_seed) = host_draw_e4(&seed, 2);
        assert_eq!(d_out, h_out);
        assert_eq!(d_seed, h_seed);
    }

    #[test]
    fn transcript_squeeze_e4_parity_three() {
        // 3 E4 = 12 u32 words, padded to 16 = 2 rounds. Matches the initial lookup
        // challenge draw in prove(): 3 E4 challenges off the seed.
        let seed = [0xab; STATE_SIZE];
        let (d_out, d_seed) = device_squeeze_e4(&seed, 3);
        let (h_out, h_seed) = host_draw_e4(&seed, 3);
        assert_eq!(d_out, h_out);
        assert_eq!(d_seed, h_seed);
    }

    #[test]
    fn transcript_squeeze_e4_parity_many_rounds() {
        // 10 E4 = 40 u32 words, padded to 40 = 5 rounds.
        let seed = [0xcd; STATE_SIZE];
        let (d_out, d_seed) = device_squeeze_e4(&seed, 10);
        let (h_out, h_seed) = host_draw_e4(&seed, 10);
        assert_eq!(d_out, h_out);
        assert_eq!(d_seed, h_seed);
    }

    #[test]
    fn transcript_squeeze_e4_parity_randomized() {
        let mut rng = rand::rng();
        for count in [1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17] {
            let seed: [u32; STATE_SIZE] = std::array::from_fn(|_| rng.random());
            let (d_out, d_seed) = device_squeeze_e4(&seed, count);
            let (h_out, h_seed) = host_draw_e4(&seed, count);
            assert_eq!(d_out, h_out, "output mismatch for count={count}");
            assert_eq!(d_seed, h_seed, "seed mismatch for count={count}");
        }
    }

    // -----------------------------------------------------------------------
    // Fused backward sumcheck round-update kernel parity test.
    //
    // Mirrors the host per-round callback in
    // backward.rs:schedule_execute_dimension_reducing_layer_from_workflow_state
    // (and its main-layer twin) and checks that the device kernel produces
    // bit-exact state updates: new seed, coefficients, challenge, claim,
    // eq_prefactor.
    // -----------------------------------------------------------------------

    fn sample_e4(seed: u32) -> E4 {
        use field::{FieldExtension, PrimeField};
        E4::from_array_of_base([
            BF::from_u32_with_reduction(seed.wrapping_mul(0x9E3779B1)),
            BF::from_u32_with_reduction(seed.wrapping_mul(0x85EBCA77)),
            BF::from_u32_with_reduction(seed.wrapping_mul(0xC2B2AE3D)),
            BF::from_u32_with_reduction(seed.wrapping_mul(0x27D4EB2F)),
        ])
    }

    /// Runs the exact host-side per-round callback logic and returns the
    /// updated state plus the derived round coefficients and challenge.
    fn host_backward_round_update(
        mut seed: Seed,
        mut claim: E4,
        mut eq_prefactor: E4,
        prev_coord: E4,
        e_partial: E4,
        c_partial: E4,
    ) -> (Seed, E4, E4, [E4; 4], E4) {
        use prover::gkr::prover::transcript_utils::{commit_field_els, draw_random_field_els};
        use prover::gkr::sumcheck::{
            evaluate_eq_poly, evaluate_small_univariate_poly,
            output_univariate_monomial_form_max_quadratic,
        };

        let eq_prefactor_inv = eq_prefactor.inverse().expect("non-zero");
        let mut normalized_claim = claim;
        normalized_claim.mul_assign(&eq_prefactor_inv);

        let coeffs = output_univariate_monomial_form_max_quadratic::<BF, E4>(
            prev_coord,
            normalized_claim,
            e_partial,
            c_partial,
        );
        commit_field_els::<BF, E4>(&mut seed, &coeffs);
        let challenge = draw_random_field_els::<BF, E4>(&mut seed, 1)[0];
        claim = evaluate_small_univariate_poly::<BF, E4, 4>(&coeffs, &challenge);
        eq_prefactor = evaluate_eq_poly::<BF, E4>(&challenge, &prev_coord);
        (seed, claim, eq_prefactor, coeffs, challenge)
    }

    fn run_device_backward_round_update(
        seed_in: Seed,
        claim_in: E4,
        eq_prefactor_in: E4,
        prev_coord: E4,
        e_partial: E4,
        c_partial: E4,
    ) -> (Seed, E4, E4, [E4; 4], E4) {
        let stream = CudaStream::default();

        // Inputs.
        let mut d_reduction: DeviceAllocation<E4> = DeviceAllocation::alloc(2).unwrap();
        let mut d_prev_coord: DeviceAllocation<E4> = DeviceAllocation::alloc(1).unwrap();
        memory_copy_async(&mut d_reduction, &[e_partial, c_partial], &stream).unwrap();
        memory_copy_async(&mut d_prev_coord, &[prev_coord], &stream).unwrap();

        // In/out state.
        let mut d_seed: DeviceAllocation<u32> = DeviceAllocation::alloc(STATE_SIZE).unwrap();
        let mut d_claim: DeviceAllocation<E4> = DeviceAllocation::alloc(1).unwrap();
        let mut d_eq_prefactor: DeviceAllocation<E4> = DeviceAllocation::alloc(1).unwrap();
        memory_copy_async(&mut d_seed, &seed_in.0[..], &stream).unwrap();
        memory_copy_async(&mut d_claim, &[claim_in], &stream).unwrap();
        memory_copy_async(&mut d_eq_prefactor, &[eq_prefactor_in], &stream).unwrap();

        // Outputs.
        let mut d_coeffs: DeviceAllocation<E4> = DeviceAllocation::alloc(4).unwrap();
        let mut d_challenge: DeviceAllocation<E4> = DeviceAllocation::alloc(1).unwrap();

        super::backward_sumcheck_round_update(
            &d_reduction,
            &d_prev_coord,
            &mut d_seed,
            &mut d_claim,
            &mut d_eq_prefactor,
            &mut d_coeffs,
            &mut d_challenge,
            &stream,
        )
        .unwrap();

        let mut seed_out = Seed::default();
        let mut claim_out = [E4::ZERO];
        let mut eq_prefactor_out = [E4::ZERO];
        let mut coeffs_out = [E4::ZERO; 4];
        let mut challenge_out = [E4::ZERO];
        memory_copy_async(&mut seed_out.0[..], &d_seed, &stream).unwrap();
        memory_copy_async(&mut claim_out[..], &d_claim, &stream).unwrap();
        memory_copy_async(&mut eq_prefactor_out[..], &d_eq_prefactor, &stream).unwrap();
        memory_copy_async(&mut coeffs_out[..], &d_coeffs, &stream).unwrap();
        memory_copy_async(&mut challenge_out[..], &d_challenge, &stream).unwrap();
        stream.synchronize().unwrap();

        (
            seed_out,
            claim_out[0],
            eq_prefactor_out[0],
            coeffs_out,
            challenge_out[0],
        )
    }

    fn assert_backward_round_parity(
        seed_in: Seed,
        claim_in: E4,
        eq_prefactor_in: E4,
        prev_coord: E4,
        e_partial: E4,
        c_partial: E4,
    ) {
        let (h_seed, h_claim, h_eq, h_coeffs, h_challenge) = host_backward_round_update(
            seed_in,
            claim_in,
            eq_prefactor_in,
            prev_coord,
            e_partial,
            c_partial,
        );
        let (d_seed, d_claim, d_eq, d_coeffs, d_challenge) = run_device_backward_round_update(
            seed_in,
            claim_in,
            eq_prefactor_in,
            prev_coord,
            e_partial,
            c_partial,
        );
        assert_eq!(d_seed.0, h_seed.0, "seed mismatch");
        assert_eq!(d_coeffs, h_coeffs, "coeffs mismatch");
        assert_eq!(d_challenge, h_challenge, "challenge mismatch");
        assert_eq!(d_claim, h_claim, "claim mismatch");
        assert_eq!(d_eq, h_eq, "eq_prefactor mismatch");
    }

    #[test]
    fn backward_round_update_parity_fixed() {
        let seed = Seed([
            0x11111111, 0x22222222, 0x33333333, 0x44444444, 0x55555555, 0x66666666, 0x77777777,
            0x88888888,
        ]);
        let claim = sample_e4(1);
        let eq_prefactor = sample_e4(2);
        let prev_coord = sample_e4(3);
        let e_partial = sample_e4(4);
        let c_partial = sample_e4(5);
        assert_backward_round_parity(seed, claim, eq_prefactor, prev_coord, e_partial, c_partial);
    }

    #[test]
    fn backward_round_update_parity_randomized() {
        let mut rng = rand::rng();
        for _ in 0..16 {
            let seed = Seed(std::array::from_fn(|_| rng.random()));
            let claim = sample_e4(rng.random());
            let eq_prefactor = sample_e4(rng.random::<u32>() | 1); // avoid zero
            let prev_coord = sample_e4(rng.random::<u32>() | 1); // prev_coord is also used as a_plus_b, must be non-zero
            let e_partial = sample_e4(rng.random());
            let c_partial = sample_e4(rng.random());
            assert_backward_round_parity(
                seed,
                claim,
                eq_prefactor,
                prev_coord,
                e_partial,
                c_partial,
            );
        }
    }

    // -----------------------------------------------------------------------
    // Fused WHIR fold round-update kernel parity test.
    //
    // Mirrors the host per-round callback in whir_fold.rs:schedule_fold_round
    // and checks that the device kernel produces bit-exact state updates: new
    // seed, coefficients, challenge.
    // -----------------------------------------------------------------------

    /// Reference host-side implementation of the sumcheck Lagrange interpolant
    /// at (0, 1, random_point). Mirrors `whir_fold::special_lagrange_interpolate`,
    /// inlined here so this module's tests stay self-contained.
    fn special_lagrange_interpolate_host(
        eval_at_0: E4,
        eval_at_1: E4,
        eval_at_random: E4,
        random_point: E4,
    ) -> [E4; 3] {
        use field::Field;

        let mut coeffs_for_0 = [E4::ZERO, E4::ZERO, E4::ONE];
        coeffs_for_0[1] = E4::ONE;
        coeffs_for_0[1].add_assign(&random_point);
        coeffs_for_0[1].negate();
        coeffs_for_0[0] = random_point;

        let mut coeffs_for_1 = [E4::ZERO, E4::ZERO, E4::ONE];
        coeffs_for_1[1] = random_point;
        coeffs_for_1[1].negate();

        let mut coeffs_for_random = [E4::ZERO, E4::ZERO, E4::ONE];
        coeffs_for_random[1] = E4::ONE;
        coeffs_for_random[1].negate();

        let mut dens = [E4::ONE, E4::ONE, E4::ONE];
        let mut t = E4::ZERO;
        t.sub_assign(&E4::ONE);
        dens[0].mul_assign(&t);
        let mut t = E4::ZERO;
        t.sub_assign(&random_point);
        dens[0].mul_assign(&t);

        let mut t = E4::ONE;
        t.sub_assign(&random_point);
        dens[1].mul_assign(&t);

        let mut t = random_point;
        dens[2].mul_assign(&t);
        let mut t = random_point;
        t.sub_assign(&E4::ONE);
        dens[2].mul_assign(&t);

        for d in dens.iter_mut() {
            *d = d.inverse().expect("non-zero denominator");
        }

        let mut result = [E4::ZERO; 3];
        for (eval, den, coeffs) in [
            (eval_at_0, dens[0], coeffs_for_0),
            (eval_at_1, dens[1], coeffs_for_1),
            (eval_at_random, dens[2], coeffs_for_random),
        ] {
            for (dst, coeff) in result.iter_mut().zip(coeffs.into_iter()) {
                let mut term = coeff;
                term.mul_assign(&den);
                term.mul_assign(&eval);
                dst.add_assign(&term);
            }
        }
        result
    }

    /// Runs the exact host-side per-round callback logic and returns the
    /// updated state plus the derived sumcheck coefficients and challenge.
    fn host_whir_fold_round_update(
        mut seed: Seed,
        f_at_0: E4,
        f_at_1: E4,
        raw_half_input: E4,
    ) -> (Seed, [E4; 3], E4) {
        use field::{Field, FieldExtension, PrimeField};
        use prover::gkr::prover::transcript_utils::{commit_field_els, draw_random_field_els};

        let quart = BF::from_u32_unchecked(4).inverse().unwrap();
        let two_inv = BF::from_u32_unchecked(2).inverse().unwrap();
        let mut f_half = raw_half_input;
        f_half.mul_assign_by_base(&quart);

        let coeffs =
            special_lagrange_interpolate_host(f_at_0, f_at_1, f_half, E4::from_base(two_inv));
        commit_field_els::<BF, E4>(&mut seed, &coeffs);
        let challenge = draw_random_field_els::<BF, E4>(&mut seed, 1)[0];
        (seed, coeffs, challenge)
    }

    fn run_device_whir_fold_round_update(
        seed_in: Seed,
        f_at_0: E4,
        f_at_1: E4,
        raw_half_input: E4,
    ) -> (Seed, [E4; 3], E4) {
        let stream = CudaStream::default();

        let mut d_reduction: DeviceAllocation<E4> = DeviceAllocation::alloc(3).unwrap();
        memory_copy_async(&mut d_reduction, &[f_at_0, f_at_1, raw_half_input], &stream).unwrap();

        let mut d_seed: DeviceAllocation<u32> = DeviceAllocation::alloc(STATE_SIZE).unwrap();
        memory_copy_async(&mut d_seed, &seed_in.0[..], &stream).unwrap();

        let mut d_coeffs: DeviceAllocation<E4> = DeviceAllocation::alloc(3).unwrap();
        let mut d_challenge: DeviceAllocation<E4> = DeviceAllocation::alloc(1).unwrap();

        super::whir_fold_round_update(
            &d_reduction,
            &mut d_seed,
            &mut d_coeffs,
            &mut d_challenge,
            &stream,
        )
        .unwrap();

        let mut seed_out = Seed::default();
        let mut coeffs_out = [E4::ZERO; 3];
        let mut challenge_out = [E4::ZERO];
        memory_copy_async(&mut seed_out.0[..], &d_seed, &stream).unwrap();
        memory_copy_async(&mut coeffs_out[..], &d_coeffs, &stream).unwrap();
        memory_copy_async(&mut challenge_out[..], &d_challenge, &stream).unwrap();
        stream.synchronize().unwrap();

        (seed_out, coeffs_out, challenge_out[0])
    }

    fn assert_whir_fold_round_parity(seed_in: Seed, f_at_0: E4, f_at_1: E4, raw_half_input: E4) {
        let (h_seed, h_coeffs, h_challenge) =
            host_whir_fold_round_update(seed_in, f_at_0, f_at_1, raw_half_input);
        let (d_seed, d_coeffs, d_challenge) =
            run_device_whir_fold_round_update(seed_in, f_at_0, f_at_1, raw_half_input);
        assert_eq!(d_seed.0, h_seed.0, "seed mismatch");
        assert_eq!(d_coeffs, h_coeffs, "coeffs mismatch");
        assert_eq!(d_challenge, h_challenge, "challenge mismatch");
    }

    #[test]
    fn whir_fold_round_update_parity_fixed() {
        let seed = Seed([
            0x11111111, 0x22222222, 0x33333333, 0x44444444, 0x55555555, 0x66666666, 0x77777777,
            0x88888888,
        ]);
        let f_at_0 = sample_e4(1);
        let f_at_1 = sample_e4(2);
        let raw_half_input = sample_e4(3);
        assert_whir_fold_round_parity(seed, f_at_0, f_at_1, raw_half_input);
    }

    #[test]
    fn whir_fold_round_update_parity_randomized() {
        let mut rng = rand::rng();
        for _ in 0..16 {
            let seed = Seed(std::array::from_fn(|_| rng.random()));
            let f_at_0 = sample_e4(rng.random());
            let f_at_1 = sample_e4(rng.random());
            let raw_half_input = sample_e4(rng.random());
            assert_whir_fold_round_parity(seed, f_at_0, f_at_1, raw_half_input);
        }
    }

    #[test]
    fn whir_fold_round_update_parity_chained() {
        // Emulates multiple sequential fold rounds: the output seed of one
        // round becomes the input of the next. Catches state-propagation
        // mismatches that a single-round test would miss.
        let mut seed = Seed([0xcc; STATE_SIZE]);

        for round in 0..8u32 {
            let f_at_0 = sample_e4(round * 17 + 1);
            let f_at_1 = sample_e4(round * 19 + 2);
            let raw_half_input = sample_e4(round * 23 + 3);

            let (h_seed, h_coeffs, h_challenge) =
                host_whir_fold_round_update(seed, f_at_0, f_at_1, raw_half_input);
            let (d_seed, d_coeffs, d_challenge) =
                run_device_whir_fold_round_update(seed, f_at_0, f_at_1, raw_half_input);

            assert_eq!(d_seed.0, h_seed.0, "round {round}: seed");
            assert_eq!(d_coeffs, h_coeffs, "round {round}: coeffs");
            assert_eq!(d_challenge, h_challenge, "round {round}: challenge");

            seed = h_seed;
        }
    }

    // -----------------------------------------------------------------------
    // Assemble-query-indexes kernel parity test.
    //
    // Mirrors `draw_query_bits_after_verified_pow` + `BitSource` +
    // `assemble_query_index` chain: the kernel consumes the squeezed random
    // buffer and produces query indexes matching the host reference.
    // -----------------------------------------------------------------------

    fn host_assemble_query_indexes(
        raw_bits: &[u32],
        num_queries: usize,
        log_domain_size: usize,
    ) -> Vec<u32> {
        use prover::query_utils::{assemble_query_index, BitSource};

        // Host path: skip the first word (PoW header), then assemble LE.
        let source_after_skip = raw_bits[1..].to_vec();
        let mut bit_source = BitSource::new(source_after_skip);
        (0..num_queries)
            .map(|_| assemble_query_index(log_domain_size, &mut bit_source) as u32)
            .collect()
    }

    fn assert_assemble_query_indexes_parity(
        raw_bits: &[u32],
        num_queries: usize,
        log_domain_size: u32,
    ) {
        let expected = host_assemble_query_indexes(raw_bits, num_queries, log_domain_size as usize);

        let stream = CudaStream::default();
        let mut d_raw: DeviceAllocation<u32> = DeviceAllocation::alloc(raw_bits.len()).unwrap();
        let mut d_indexes: DeviceAllocation<u32> = DeviceAllocation::alloc(num_queries).unwrap();
        memory_copy_async(&mut d_raw, raw_bits, &stream).unwrap();
        super::assemble_query_indexes(&d_raw, &mut d_indexes, log_domain_size, &stream).unwrap();

        let mut actual = vec![0u32; num_queries];
        memory_copy_async(&mut actual, &d_indexes, &stream).unwrap();
        stream.synchronize().unwrap();

        assert_eq!(actual, expected);
    }

    #[test]
    fn assemble_query_indexes_parity_small() {
        // 4 queries, 8-bit domain: 32 + 4*8 = 64 bits = 2 words (pad to 8 for
        // squeeze alignment).
        let raw_bits: Vec<u32> = (0..8).map(|i| 0xDEADBEEFu32.wrapping_mul(i + 1)).collect();
        assert_assemble_query_indexes_parity(&raw_bits, 4, 8);
    }

    #[test]
    fn assemble_query_indexes_parity_realistic() {
        // Matches a typical WHIR round: ~32-64 queries with ~20-24-bit domain.
        let mut rng = rand::rng();
        for &(num_queries, log_domain_size) in
            &[(32usize, 24u32), (48, 20), (64, 16), (16, 30), (1, 24)]
        {
            // Pad to multiple of 8 (squeeze output granularity).
            let bits_needed = 32 + num_queries * log_domain_size as usize;
            let words_needed = bits_needed.div_ceil(32);
            let padded_words = words_needed.next_multiple_of(STATE_SIZE);
            let raw_bits: Vec<u32> = (0..padded_words).map(|_| rng.random()).collect();
            assert_assemble_query_indexes_parity(&raw_bits, num_queries, log_domain_size);
        }
    }

    #[test]
    fn backward_round_update_parity_chained() {
        // Emulates multiple sequential rounds: the output seed/claim/eq of one
        // round becomes the input of the next. This catches state-propagation
        // mismatches that a single-round test would miss.
        let mut seed = Seed([0xaa; STATE_SIZE]);
        let mut claim = sample_e4(100);
        let mut eq_prefactor = sample_e4(200);

        for round in 0..8u32 {
            let prev_coord = sample_e4(round * 7 + 1);
            let e_partial = sample_e4(round * 11 + 3);
            let c_partial = sample_e4(round * 13 + 5);

            let (h_seed, h_claim, h_eq, h_coeffs, h_challenge) = host_backward_round_update(
                seed,
                claim,
                eq_prefactor,
                prev_coord,
                e_partial,
                c_partial,
            );
            let (d_seed, d_claim, d_eq, d_coeffs, d_challenge) = run_device_backward_round_update(
                seed,
                claim,
                eq_prefactor,
                prev_coord,
                e_partial,
                c_partial,
            );

            assert_eq!(d_seed.0, h_seed.0, "round {round}: seed");
            assert_eq!(d_coeffs, h_coeffs, "round {round}: coeffs");
            assert_eq!(d_challenge, h_challenge, "round {round}: challenge");
            assert_eq!(d_claim, h_claim, "round {round}: claim");
            assert_eq!(d_eq, h_eq, "round {round}: eq_prefactor");

            seed = h_seed;
            claim = h_claim;
            eq_prefactor = h_eq;
        }
    }

    // -----------------------------------------------------------------------
    // Per-address backward new_claims evaluator parity tests.
    //
    // `backward_new_claims_two_var` must match the host
    // `evaluate_with_two_variable_eq_ext(values, r_before_last, r_last)`.
    // `backward_new_claims_linear` must match the host
    // `interpolate_linear(f0, f1, last_r)`. Both kernels are called once per
    // layer boundary in the backward pass and produce `num_addresses` E4s.
    // -----------------------------------------------------------------------

    fn host_new_claim_two_var(values: &[E4; 4], r_before_last: E4, r_last: E4) -> E4 {
        let mut result = E4::ZERO;
        let mut w00 = E4::ONE;
        w00.sub_assign(&r_before_last);
        let mut tmp = E4::ONE;
        tmp.sub_assign(&r_last);
        w00.mul_assign(&tmp);
        let mut term = values[0];
        term.mul_assign(&w00);
        result.add_assign(&term);

        let mut w01 = E4::ONE;
        w01.sub_assign(&r_before_last);
        w01.mul_assign(&r_last);
        let mut term = values[1];
        term.mul_assign(&w01);
        result.add_assign(&term);

        let mut w10 = r_before_last;
        let mut tmp = E4::ONE;
        tmp.sub_assign(&r_last);
        w10.mul_assign(&tmp);
        let mut term = values[2];
        term.mul_assign(&w10);
        result.add_assign(&term);

        let mut w11 = r_before_last;
        w11.mul_assign(&r_last);
        let mut term = values[3];
        term.mul_assign(&w11);
        result.add_assign(&term);
        result
    }

    fn host_new_claim_linear(f0: E4, f1: E4, r: E4) -> E4 {
        let mut result = f1;
        result.sub_assign(&f0);
        result.mul_assign(&r);
        result.add_assign(&f0);
        result
    }

    fn run_device_new_claims_two_var(
        packed_values: &[E4],
        r_before_last: E4,
        r_last: E4,
    ) -> Vec<E4> {
        let stream = CudaStream::default();
        let num_addresses = packed_values.len() / 4;
        let mut d_packed: DeviceAllocation<E4> =
            DeviceAllocation::alloc(packed_values.len()).unwrap();
        memory_copy_async(&mut d_packed, packed_values, &stream).unwrap();
        let mut d_challenges: DeviceAllocation<E4> = DeviceAllocation::alloc(2).unwrap();
        memory_copy_async(&mut d_challenges, &[r_before_last, r_last], &stream).unwrap();
        let mut d_out: DeviceAllocation<E4> = DeviceAllocation::alloc(num_addresses).unwrap();
        super::backward_new_claims_two_var(&d_packed, &d_challenges, &mut d_out, &stream).unwrap();
        let mut out = vec![E4::ZERO; num_addresses];
        memory_copy_async(&mut out[..], &d_out, &stream).unwrap();
        stream.synchronize().unwrap();
        out
    }

    fn run_device_new_claims_linear(packed_values: &[E4], last_r: E4) -> Vec<E4> {
        let stream = CudaStream::default();
        let num_addresses = packed_values.len() / 2;
        let mut d_packed: DeviceAllocation<E4> =
            DeviceAllocation::alloc(packed_values.len()).unwrap();
        memory_copy_async(&mut d_packed, packed_values, &stream).unwrap();
        let mut d_challenges: DeviceAllocation<E4> = DeviceAllocation::alloc(1).unwrap();
        memory_copy_async(&mut d_challenges, &[last_r], &stream).unwrap();
        let mut d_out: DeviceAllocation<E4> = DeviceAllocation::alloc(num_addresses).unwrap();
        super::backward_new_claims_linear(&d_packed, &d_challenges, &mut d_out, &stream).unwrap();
        let mut out = vec![E4::ZERO; num_addresses];
        memory_copy_async(&mut out[..], &d_out, &stream).unwrap();
        stream.synchronize().unwrap();
        out
    }

    #[test]
    fn backward_new_claims_two_var_parity_fixed() {
        let r_before_last = sample_e4(17);
        let r_last = sample_e4(23);
        let num_addresses = 7usize;
        let mut packed = Vec::with_capacity(num_addresses * 4);
        for i in 0..num_addresses * 4 {
            packed.push(sample_e4(100 + i as u32));
        }
        let device = run_device_new_claims_two_var(&packed, r_before_last, r_last);
        for i in 0..num_addresses {
            let v: [E4; 4] = packed[i * 4..i * 4 + 4].try_into().unwrap();
            let host = host_new_claim_two_var(&v, r_before_last, r_last);
            assert_eq!(device[i], host, "address {i} mismatch");
        }
    }

    #[test]
    fn backward_new_claims_two_var_parity_randomized() {
        use rand::Rng;
        let mut rng = rand::rng();
        for num_addresses in [1usize, 2, 3, 8, 17, 64, 257] {
            let r_before_last = sample_e4(rng.random::<u32>());
            let r_last = sample_e4(rng.random::<u32>());
            let packed: Vec<E4> = (0..num_addresses * 4)
                .map(|_| sample_e4(rng.random::<u32>()))
                .collect();
            let device = run_device_new_claims_two_var(&packed, r_before_last, r_last);
            for i in 0..num_addresses {
                let v: [E4; 4] = packed[i * 4..i * 4 + 4].try_into().unwrap();
                let host = host_new_claim_two_var(&v, r_before_last, r_last);
                assert_eq!(device[i], host, "N={num_addresses} addr {i} mismatch");
            }
        }
    }

    #[test]
    fn backward_new_claims_linear_parity_fixed() {
        let last_r = sample_e4(31);
        let num_addresses = 5usize;
        let mut packed = Vec::with_capacity(num_addresses * 2);
        for i in 0..num_addresses * 2 {
            packed.push(sample_e4(200 + i as u32));
        }
        let device = run_device_new_claims_linear(&packed, last_r);
        for i in 0..num_addresses {
            let f0 = packed[i * 2];
            let f1 = packed[i * 2 + 1];
            let host = host_new_claim_linear(f0, f1, last_r);
            assert_eq!(device[i], host, "address {i} mismatch");
        }
    }

    #[test]
    fn backward_new_claims_linear_parity_randomized() {
        use rand::Rng;
        let mut rng = rand::rng();
        for num_addresses in [1usize, 2, 3, 8, 17, 64, 257] {
            let last_r = sample_e4(rng.random::<u32>());
            let packed: Vec<E4> = (0..num_addresses * 2)
                .map(|_| sample_e4(rng.random::<u32>()))
                .collect();
            let device = run_device_new_claims_linear(&packed, last_r);
            for i in 0..num_addresses {
                let f0 = packed[i * 2];
                let f1 = packed[i * 2 + 1];
                let host = host_new_claim_linear(f0, f1, last_r);
                assert_eq!(device[i], host, "N={num_addresses} addr {i} mismatch");
            }
        }
    }
}
