use blake2s_u32::{DelegatedBlake2sState, BLAKE2S_DIGEST_SIZE_U32_WORDS};
use non_determinism_source::NonDeterminismSource;
use transcript::{Blake2sTranscript, Seed};

use crate::gkr::LazyVec;
use crate::structs::{assemble_query_index, BitSource};

#[inline(always)]
pub fn read_and_commit_merkle_cap<I: NonDeterminismSource, const CAP_WORDS: usize>(
    seed: &mut Seed,
) {
    let mut buf = LazyVec::<u32, CAP_WORDS>::new();
    for _ in 0..CAP_WORDS {
        buf.push(I::read_word());
    }
    Blake2sTranscript::commit_with_seed(seed, buf.as_slice());
}

#[inline(always)]
pub fn read_and_verify_pow<I: NonDeterminismSource>(seed: &mut Seed, pow_bits: u32) {
    let lo = I::read_word();
    let hi = I::read_word();
    let nonce = (lo as u64) | ((hi as u64) << 32);
    Blake2sTranscript::verify_pow(seed, nonce, pow_bits);
}

#[inline(always)]
pub fn draw_query_indices<const MAX_QUERIES: usize, const DRAW_WORDS: usize>(
    hasher: &mut DelegatedBlake2sState,
    seed: &mut Seed,
    num_queries: usize,
    query_index_bits: usize,
) -> LazyVec<usize, MAX_QUERIES> {
    let mut source_words = LazyVec::<u32, DRAW_WORDS>::new();
    // SAFETY: draw_randomness_using_hasher writes exactly DRAW_WORDS u32s before any are read.
    unsafe {
        source_words.set_len(DRAW_WORDS);
        Blake2sTranscript::draw_randomness_using_hasher(hasher, seed, source_words.as_mut_slice());
    }

    // Skip first word (matches prover's draw_query_bits convention)
    let bit_words = &source_words.as_slice()[1..];
    let mut bit_source = BitSource::new(bit_words);

    let mut indices = LazyVec::<usize, MAX_QUERIES>::new();
    for _ in 0..num_queries {
        indices.push(assemble_query_index(query_index_bits, &mut bit_source));
    }
    indices
}

#[inline(always)]
pub fn verify_merkle_path<I: NonDeterminismSource>(
    hasher: &mut DelegatedBlake2sState,
    mut leaf_index: usize,
    depth: usize,
    cap: &[u32],
) -> bool {
    for _ in 0..depth {
        let is_right = leaf_index & 1 == 1;
        let witness_buf = hasher.get_witness_buffer();
        for i in 0..BLAKE2S_DIGEST_SIZE_U32_WORDS {
            witness_buf[i] = I::read_word();
        }
        hasher.compress_node::<true>(is_right);
        leaf_index >>= 1;
    }

    let output_hash = hasher.read_state_for_output_ref();
    debug_assert!(cap.len() >= (leaf_index + 1) * BLAKE2S_DIGEST_SIZE_U32_WORDS);
    let cap_entry = &cap[leaf_index * BLAKE2S_DIGEST_SIZE_U32_WORDS..];
    let mut equal = true;
    for i in 0..BLAKE2S_DIGEST_SIZE_U32_WORDS {
        equal &= output_hash[i] == cap_entry[i];
    }
    equal
}

#[cfg(any(test, feature = "proof_utils"))]
pub fn draw_query_indices_vec(
    hasher: &mut DelegatedBlake2sState,
    seed: &mut Seed,
    num_queries: usize,
    query_index_bits: usize,
    draw_words: usize,
) -> Vec<usize> {
    debug_assert_eq!(draw_words % BLAKE2S_DIGEST_SIZE_U32_WORDS, 0);
    let mut source_words = vec![0u32; draw_words];
    Blake2sTranscript::draw_randomness_using_hasher(hasher, seed, &mut source_words);

    let bit_words = &source_words[1..];
    let mut bit_source = BitSource::new(bit_words);

    let mut indices = Vec::with_capacity(num_queries);
    for _ in 0..num_queries {
        indices.push(assemble_query_index(query_index_bits, &mut bit_source));
    }
    indices
}
