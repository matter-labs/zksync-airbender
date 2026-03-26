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

/// Read a Merkle cap from NDS, commit it to the transcript, and return it.
#[inline(always)]
pub fn read_commit_return_merkle_cap<I: NonDeterminismSource, const CAP_WORDS: usize>(
    seed: &mut Seed,
) -> [u32; CAP_WORDS] {
    let mut buf = LazyVec::<u32, CAP_WORDS>::new();
    for _ in 0..CAP_WORDS {
        buf.push(I::read_word());
    }
    Blake2sTranscript::commit_with_seed(seed, buf.as_slice());
    unsafe { core::ptr::read(buf.as_slice().as_ptr().cast::<[u32; CAP_WORDS]>()) }
}

/// Read a Merkle cap from NDS and return it (no transcript commit).
#[inline(always)]
pub fn read_return_merkle_cap<I: NonDeterminismSource, const CAP_WORDS: usize>() -> [u32; CAP_WORDS]
{
    let mut buf = LazyVec::<u32, CAP_WORDS>::new();
    for _ in 0..CAP_WORDS {
        buf.push(I::read_word());
    }
    unsafe { core::ptr::read(buf.as_slice().as_ptr().cast::<[u32; CAP_WORDS]>()) }
}

#[inline(always)]
pub fn read_and_verify_pow<I: NonDeterminismSource>(seed: &mut Seed, pow_bits: u32) {
    let lo = I::read_word();
    let hi = I::read_word();
    let nonce = (lo as u64) | ((hi as u64) << 32);
    Blake2sTranscript::verify_pow(seed, nonce, pow_bits);
}

#[inline(always)]
pub fn draw_query_indices<const MAX_QUERIES: usize, const MAX_DRAW_WORDS: usize>(
    hasher: &mut DelegatedBlake2sState,
    seed: &mut Seed,
    num_queries: usize,
    query_index_bits: usize,
    draw_words: usize,
) -> LazyVec<usize, MAX_QUERIES> {
    let mut source_words = LazyVec::<u32, MAX_DRAW_WORDS>::new();
    // SAFETY: draw_randomness_using_hasher writes exactly draw_words u32s before any are read.
    unsafe {
        source_words.set_len(draw_words);
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
    let mut level = 0;
    while level < depth {
        let is_right = leaf_index & 1 == 1;
        let witness_buf = hasher.get_witness_buffer();
        witness_buf[0] = I::read_word();
        witness_buf[1] = I::read_word();
        witness_buf[2] = I::read_word();
        witness_buf[3] = I::read_word();
        witness_buf[4] = I::read_word();
        witness_buf[5] = I::read_word();
        witness_buf[6] = I::read_word();
        witness_buf[7] = I::read_word();
        hasher.compress_node::<true>(is_right);
        leaf_index >>= 1;
        level += 1;
    }

    let output_hash = hasher.read_state_for_output_ref();
    debug_assert!(cap.len() >= (leaf_index + 1) * BLAKE2S_DIGEST_SIZE_U32_WORDS);
    let cap_start = leaf_index * BLAKE2S_DIGEST_SIZE_U32_WORDS;
    unsafe {
        *output_hash.get_unchecked(0) == *cap.get_unchecked(cap_start)
            && *output_hash.get_unchecked(1) == *cap.get_unchecked(cap_start + 1)
            && *output_hash.get_unchecked(2) == *cap.get_unchecked(cap_start + 2)
            && *output_hash.get_unchecked(3) == *cap.get_unchecked(cap_start + 3)
            && *output_hash.get_unchecked(4) == *cap.get_unchecked(cap_start + 4)
            && *output_hash.get_unchecked(5) == *cap.get_unchecked(cap_start + 5)
            && *output_hash.get_unchecked(6) == *cap.get_unchecked(cap_start + 6)
            && *output_hash.get_unchecked(7) == *cap.get_unchecked(cap_start + 7)
    }
}

/// Hash leaf data (raw u32 words, already in tree-hashing order) into the
/// delegated hasher's state so that `verify_merkle_path` can be called
/// immediately afterwards.
///
/// **IMPORTANT**: `buf` must be an `AlignedArray64` whose total size `N` is a
/// multiple of `BLAKE2S_BLOCK_SIZE_U32_WORDS` (16).  Words beyond
/// `num_words` must be zero (the caller is responsible for this; typically
/// the buffer is zero-initialised once and the active region is overwritten
/// each iteration).
///
/// With the `blake2_with_compression` feature, this uses hardware-delegated
/// Blake2s via aligned buffers.  Without it, falls back to the software
/// `absorb`/`absorb_final_block` path on the hasher directly.
#[inline(always)]
pub fn hash_leaf_data_into_state<const N: usize>(
    hasher: &mut DelegatedBlake2sState,
    buf: &blake2s_u32::AlignedArray64<u32, N>,
    num_words: usize,
) {
    use blake2s_u32::BLAKE2S_BLOCK_SIZE_U32_WORDS;

    debug_assert_eq!(N % BLAKE2S_BLOCK_SIZE_U32_WORDS, 0);
    const BLOCK_LOG2: usize = BLAKE2S_BLOCK_SIZE_U32_WORDS.trailing_zeros() as usize;
    let num_full_blocks = num_words >> BLOCK_LOG2;
    let last_block_words = num_words & (BLAKE2S_BLOCK_SIZE_U32_WORDS - 1);
    let num_blocks = num_full_blocks + if last_block_words > 0 { 1 } else { 0 };
    debug_assert!(num_blocks > 0);

    hasher.reset();

    #[cfg(feature = "blake2_with_compression")]
    unsafe {
        for i in 0..num_blocks - 1 {
            let block_ptr = buf.as_ptr().add(i * BLAKE2S_BLOCK_SIZE_U32_WORDS);
            let block = &*(block_ptr
                as *const blake2s_u32::AlignedArray64<u32, BLAKE2S_BLOCK_SIZE_U32_WORDS>);
            hasher.run_round_function_with_input::<true>(
                block,
                BLAKE2S_BLOCK_SIZE_U32_WORDS,
                false,
            );
        }
        let last_ptr = buf
            .as_ptr()
            .add((num_blocks - 1) * BLAKE2S_BLOCK_SIZE_U32_WORDS);
        let last_block =
            &*(last_ptr as *const blake2s_u32::AlignedArray64<u32, BLAKE2S_BLOCK_SIZE_U32_WORDS>);
        let last_active = if last_block_words > 0 {
            last_block_words
        } else {
            BLAKE2S_BLOCK_SIZE_U32_WORDS
        };
        hasher.run_round_function_with_input::<true>(last_block, last_active, true);
    }

    #[cfg(not(feature = "blake2_with_compression"))]
    {
        let data: &[u32] = &buf[..num_words];
        for block_idx in 0..num_full_blocks {
            let block_start = block_idx * BLAKE2S_BLOCK_SIZE_U32_WORDS;
            let block: &[u32; BLAKE2S_BLOCK_SIZE_U32_WORDS] = unsafe {
                &*(data.as_ptr().add(block_start) as *const [u32; BLAKE2S_BLOCK_SIZE_U32_WORDS])
            };
            if block_idx == num_full_blocks - 1 && last_block_words == 0 {
                let mut dst = [0u32; BLAKE2S_DIGEST_SIZE_U32_WORDS];
                hasher.absorb_final_block::<true>(block, BLAKE2S_BLOCK_SIZE_U32_WORDS, &mut dst);
                hasher.state = dst;
                return;
            }
            hasher.absorb::<true>(block);
        }
        let mut last_block = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
        let tail_start = num_full_blocks * BLAKE2S_BLOCK_SIZE_U32_WORDS;
        last_block[..last_block_words].copy_from_slice(&data[tail_start..]);
        let mut dst = [0u32; BLAKE2S_DIGEST_SIZE_U32_WORDS];
        hasher.absorb_final_block::<true>(&last_block, last_block_words, &mut dst);
        hasher.state = dst;
    }
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
