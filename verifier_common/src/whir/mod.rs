use blake2s_u32::{DelegatedBlake2sState, BLAKE2S_DIGEST_SIZE_U32_WORDS};
use non_determinism_source::NonDeterminismSource;
use transcript::Blake2sTranscript;

use crate::gkr::LazyVec;
use crate::structs::{assemble_query_index, BitSource, CommitBuf, TranscriptState};

/// Read a Merkle cap from NDS, commit via aligned buffer, and return it.
///
/// `BUF` must be `(DIGEST_SIZE + CAP_WORDS)` rounded up to block size.
#[inline(always)]
pub fn read_commit_return_merkle_cap<
    I: NonDeterminismSource,
    const CAP_WORDS: usize,
    const BUF: usize,
>(
    ts: &mut TranscriptState,
) -> [u32; CAP_WORDS] {
    let mut buf = CommitBuf::<BUF>::new();
    let mut i = 0;
    while i < CAP_WORDS {
        buf.data_write(i, I::read_word());
        i += 1;
    }
    let cap: [u32; CAP_WORDS] = unsafe { buf.read_one() };
    ts.commit(&mut buf, CAP_WORDS);
    cap
}

/// Read a Merkle cap from NDS and return it (no transcript commit).
#[inline(always)]
pub fn read_return_merkle_cap<I: NonDeterminismSource, const CAP_WORDS: usize>() -> [u32; CAP_WORDS]
{
    let mut buf = LazyVec::<u32, CAP_WORDS>::new();
    let mut i = 0;
    while i < CAP_WORDS {
        buf.push(I::read_word());
        i += 1;
    }
    unsafe { buf.into_array() }
}

#[inline(always)]
pub fn read_and_verify_pow<I: NonDeterminismSource>(ts: &mut TranscriptState, pow_bits: u32) {
    let lo = I::read_word();
    let hi = I::read_word();
    let nonce = (lo as u64) | ((hi as u64) << 32);
    Blake2sTranscript::verify_pow(&mut ts.seed, nonce, pow_bits);
}

#[inline(always)]
pub fn draw_query_indices<const MAX_QUERIES: usize, const MAX_DRAW_WORDS: usize>(
    ts: &mut TranscriptState,
    num_queries: usize,
    query_index_bits: usize,
    draw_words: usize,
) -> LazyVec<usize, MAX_QUERIES> {
    let mut source_words = LazyVec::<u32, MAX_DRAW_WORDS>::new();
    unsafe {
        source_words.set_len(draw_words);
        ts.draw_raw(source_words.as_mut_slice());
    }

    // Skip first word (matches prover's draw_query_bits convention)
    let bit_words = &source_words.as_slice()[1..];
    let mut bit_source = BitSource::new(bit_words);

    let mut indices = LazyVec::<usize, MAX_QUERIES>::new();
    let mut q = 0;
    while q < num_queries {
        indices.push(assemble_query_index(query_index_bits, &mut bit_source));
        q += 1;
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
        #[cfg(any(feature = "blake2_with_compression", feature = "blake2_g_function"))]
        {
            let proof_buf = hasher.get_merkle_path_proof_buffer(is_right);
            let mut i = 0;
            while i < BLAKE2S_DIGEST_SIZE_U32_WORDS {
                proof_buf[i] = I::read_word();
                i += 1;
            }
            hasher.compress_node::<true>(is_right);
        }
        #[cfg(not(any(feature = "blake2_with_compression", feature = "blake2_g_function")))]
        {
            use blake2s_u32::BLAKE2S_BLOCK_SIZE_U32_WORDS;
            let state = hasher.read_state_for_output();
            let offset = if is_right { 0 } else { 8 };
            let mut i = 0;
            while i < BLAKE2S_DIGEST_SIZE_U32_WORDS {
                hasher.input_buffer[offset + i] = I::read_word();
                i += 1;
            }
            let state_offset = if is_right { 8 } else { 0 };
            hasher.input_buffer[state_offset..state_offset + 8].copy_from_slice(&state);
            hasher.reset();
            unsafe {
                hasher.run_round_function::<true>(BLAKE2S_BLOCK_SIZE_U32_WORDS, true);
            }
        }
        leaf_index >>= 1;
        level += 1;
    }

    // A zero-column oracle has no Merkle tree — nothing to verify.
    if cap.is_empty() {
        return true;
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
    hasher.reset();

    #[cfg(any(feature = "blake2_with_compression", feature = "blake2_g_function"))]
    unsafe {
        if num_blocks == 0 {
            // Empty leaf: hash a single zero-filled finalization block.
            let empty = &*(buf.as_ptr()
                as *const blake2s_u32::AlignedArray64<u32, BLAKE2S_BLOCK_SIZE_U32_WORDS>);
            hasher.run_round_function_with_input::<true>(empty, 0, true);
        } else {
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
            let last_block = &*(last_ptr
                as *const blake2s_u32::AlignedArray64<u32, BLAKE2S_BLOCK_SIZE_U32_WORDS>);
            let last_active = if last_block_words > 0 {
                last_block_words
            } else {
                BLAKE2S_BLOCK_SIZE_U32_WORDS
            };
            hasher.run_round_function_with_input::<true>(last_block, last_active, true);
        }
    }

    #[cfg(not(any(feature = "blake2_with_compression", feature = "blake2_g_function")))]
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
