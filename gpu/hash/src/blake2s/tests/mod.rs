use itertools::Itertools;
use rand::Rng;

use super::*;
use crate::upstream::{Blake2sState, USE_REDUCED_BLAKE2_ROUNDS};

use gpu_core::primitives::field::BF;
use gpu_core::primitives::utils::GetChunksCount;

const BLOCK_SIZE: usize = 16;

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
    for (leaf_index, &actual) in results.iter().enumerate() {
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
        assert_eq!(expected, actual);
    }
}

fn verify_nodes(values: &[Digest], results: &[Digest]) {
    let results_len = results.len();
    let values_len = values.len();
    assert_eq!(values_len, results_len * 2);
    values
        .as_chunks::<2>()
        .0
        .iter()
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
mod physical_leaf_tests;
mod transcript_tests;
