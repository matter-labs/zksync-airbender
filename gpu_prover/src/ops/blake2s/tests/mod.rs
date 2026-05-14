use blake2s_u32::Blake2sState;
use itertools::Itertools;
use rand::Rng;

use super::*;

use crate::primitives::utils::GetChunksCount;

pub(crate) const BLOCK_SIZE: usize = 16;
pub(super) const USE_REDUCED_BLAKE2_ROUNDS: bool = true;

pub(crate) fn gather_rows(
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

/// Runtime-pointer-table form: `src_ptrs` is read from a device-resident
/// buffer. Prefer `gather_tree_caps_inline` for `prove()` paths so the
/// pointer table rides inline as `__grid_constant__` kernel-arg data.
pub(crate) fn gather_tree_caps(
    src_ptrs: &DeviceSlice<u64>,
    dst: &mut DeviceSlice<u32>,
    cap_words_per_coset: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let coset_count = src_ptrs.len();
    assert!(coset_count > 0);
    assert!(coset_count <= u32::MAX as usize);
    assert!(cap_words_per_coset > 0);
    assert_eq!(
        dst.len(),
        coset_count * cap_words_per_coset as usize,
        "gather_tree_caps dst length must match coset_count * cap_words_per_coset",
    );
    let threads_per_block = std::cmp::min(cap_words_per_coset, 256u32);
    let config = CudaLaunchConfig::basic(coset_count as u32, threads_per_block, stream);
    let args = GatherTreeCapsArguments::new(
        src_ptrs.as_ptr(),
        dst.as_mut_ptr(),
        cap_words_per_coset,
        coset_count as u32,
    );
    GatherTreeCapsFunction::default().launch(&config, &args)
}

/// Device-side `Transcript::commit_initial`: computes `seed = Blake2s(input)`
/// from the IV.
///
/// `seed` must be exactly `STATE_SIZE` u32 words. Written.
/// `input` contains the field-element data to absorb (entire transcript prefix).
pub(crate) fn transcript_commit_initial(
    seed: &mut DeviceSlice<u32>,
    input: &DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(seed.len(), STATE_SIZE);
    let seed_ptr = seed.as_mut_ptr();
    let input_ptr = input.as_ptr();
    let input_len = input.len();
    assert!(input_len <= u32::MAX as usize);
    let config = CudaLaunchConfig::basic(1u32, 1u32, stream);
    let args = TranscriptCommitInitialArguments::new(seed_ptr, input_ptr, input_len as u32);
    TranscriptCommitInitialFunction::default().launch(&config, &args)
}

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
                let row = leaf_source_row(leaf_index, row_slot, log_rows_per_hash, leaves_count);
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
            Blake2sState::compress_two_to_one::<USE_REDUCED_BLAKE2_ROUNDS>(&state, &mut expected);
            assert_eq!(expected, actual);
        });
}

fn random_digest() -> Digest {
    let mut rng = rand::rng();
    let mut result = Digest::default();
    result.fill_with(|| rng.random());
    result
}

mod merkle_tests;
mod transcript_tests;
mod whir_and_claims_tests;
