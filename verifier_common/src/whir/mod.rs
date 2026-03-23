use blake2s_u32::DelegatedBlake2sState;
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
