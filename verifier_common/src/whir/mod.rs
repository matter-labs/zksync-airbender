use crate::lazy_vec::LazyVec;
use crate::structs::{assemble_query_index, BitSource};
use blake2s_u32::{DelegatedBlake2sState, BLAKE2S_DIGEST_SIZE_U32_WORDS};
use non_determinism_source::U32WordNonDeterminismSource;
use transcript::{Blake2sTranscript, CommitBuf, TranscriptState};

#[derive(Clone, Copy)]
pub struct WhirPowEntry<E: Copy> {
    pub current_scalar: E,
    pub prefactor: E,
    pub coefficient: E,
}

pub struct WhirAccumulator<E: Copy, const MAX_POW: usize> {
    pub z_initial_idx: usize,
    pub z_initial_prefactor: E,
    pub pow_entries: LazyVec<WhirPowEntry<E>, MAX_POW>,
}

impl<E: Copy, const MAX_POW: usize> WhirAccumulator<E, MAX_POW> {
    #[inline(always)]
    pub const fn new(z_initial_prefactor: E) -> Self {
        Self {
            z_initial_idx: 0,
            z_initial_prefactor,
            pow_entries: LazyVec::new(),
        }
    }
}

/// Read a Merkle cap from NDS, commit via aligned buffer, and return it.
///
/// `BUF` must be `(DIGEST_SIZE + CAP_WORDS)` rounded up to block size.
#[inline(always)]
pub fn read_commit_return_merkle_cap<
    I: U32WordNonDeterminismSource,
    const CAP_WORDS: usize,
    const BUF: usize,
>(
    ts: &mut TranscriptState,
    nd_source: &mut I,
) -> [u32; CAP_WORDS] {
    let mut buf = CommitBuf::<BUF>::new();
    let mut i = 0;
    while i < CAP_WORDS {
        buf.data_write(i, nd_source.read_word());
        i += 1;
    }
    let cap: [u32; CAP_WORDS] = unsafe { buf.read_one() };
    ts.commit(&mut buf, CAP_WORDS);
    cap
}

#[inline(always)]
pub fn read_and_verify_pow<I: U32WordNonDeterminismSource>(
    ts: &mut TranscriptState,
    pow_bits: u32,
    nd_source: &mut I,
) {
    let lo = nd_source.read_word();
    let hi = nd_source.read_word();
    let nonce = (lo as u64) | ((hi as u64) << 32);
    Blake2sTranscript::<{ ::prover::definitions::USE_REDUCED_BLAKE2_ROUNDS }>::verify_pow_using_hasher(
        &mut ts.hasher,
        &mut ts.seed,
        nonce,
        pow_bits,
    );
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
pub fn verify_merkle_path<I: U32WordNonDeterminismSource>(
    hasher: &mut DelegatedBlake2sState,
    mut leaf_index: usize,
    depth: usize,
    cap: &[u32],
    nd_source: &mut I,
) -> bool {
    let mut level = 0;
    while level < depth {
        let is_right = leaf_index & 1 == 1;
        {
            let proof_buf = hasher.get_merkle_path_proof_buffer(is_right);
            let mut i = 0;
            while i < BLAKE2S_DIGEST_SIZE_U32_WORDS {
                proof_buf[i] = nd_source.read_word();
                i += 1;
            }
            hasher.compress_node::<true>(is_right);
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
}

/// A tree-space query index and its slot in the original query-order leaf hashes.
/// Sorting these small records avoids moving eight-word digests during sorting.
#[derive(Clone, Copy)]
pub struct MerkleQueryIndex {
    pub index: usize,
    pub query: usize,
}

#[derive(Clone, Copy)]
struct MerkleQueryStep {
    index: usize,
    query: usize,
    stop: usize,
}

/// A query-only authentication plan, reusable across oracles with the same
/// sampled indices. Proof data cannot supply or alter this plan.
pub struct MerkleQueryPlan<const MAX_QUERIES: usize> {
    steps: LazyVec<MerkleQueryStep, MAX_QUERIES>,
    duplicates: LazyVec<(usize, usize), MAX_QUERIES>,
    num_queries: usize,
    max_index: usize,
}

pub fn prepare_merkle_queries<const MAX_QUERIES: usize>(
    queries: &mut [MerkleQueryIndex],
) -> MerkleQueryPlan<MAX_QUERIES> {
    assert!(queries.len() <= MAX_QUERIES);
    queries.sort_unstable_by_key(|node| node.index);
    let mut plan = MerkleQueryPlan {
        steps: LazyVec::<MerkleQueryStep, MAX_QUERIES>::new(),
        duplicates: LazyVec::new(),
        num_queries: queries.len(),
        max_index: queries.last().map_or(0, |node| node.index),
    };
    for node in queries {
        assert!(node.query < plan.num_queries);
        if let Some(previous) = plan.steps.as_mut_slice().last_mut() {
            if previous.index == node.index {
                plan.duplicates.push((previous.query, node.query));
                continue;
            }
            previous.stop =
                (usize::BITS - (previous.index ^ node.index).leading_zeros() - 1) as usize;
        }
        plan.steps.push(MerkleQueryStep {
            index: node.index,
            query: node.query,
            stop: usize::BITS as usize,
        });
    }
    plan
}

/// Authenticate sorted queries in depth-first order, consuming missing boundary
/// hashes after the queried subtree they authenticate. Unary paths stay in the
/// hasher state; only branch points need a saved digest. Duplicate query leaves
/// are checked for equality before authentication deduplicates their indices.
/// The depth and cap come from verifier parameters, never from the proof stream.
#[inline(always)]
pub fn verify_merkle_multiproof<I: U32WordNonDeterminismSource, const MAX_QUERIES: usize>(
    hasher: &mut DelegatedBlake2sState,
    plan: &MerkleQueryPlan<MAX_QUERIES>,
    leaf_hashes: &[[u32; BLAKE2S_DIGEST_SIZE_U32_WORDS]],
    depth: usize,
    cap: &[u32],
    nd_source: &mut I,
) -> bool {
    if depth >= usize::BITS as usize
        || cap.len() % BLAKE2S_DIGEST_SIZE_U32_WORDS != 0
        || leaf_hashes.len() != plan.num_queries
    {
        return false;
    }
    let cap_len = cap.len() / BLAKE2S_DIGEST_SIZE_U32_WORDS;
    if plan.num_queries != 0 && plan.max_index >> depth >= cap_len {
        return false;
    }
    for &(first, duplicate) in plan.duplicates.as_slice() {
        if !merkle_digest_matches(&leaf_hashes[first], &leaf_hashes[duplicate]) {
            return false;
        }
    }
    // At most one completed left subtree is pending at each tree level.
    let mut saved_levels = LazyVec::<usize, { usize::BITS as usize }>::new();
    let mut saved_hashes =
        [const { core::mem::MaybeUninit::<[u32; 8]>::uninit() }; usize::BITS as usize];
    for node in plan.steps.as_slice() {
        let stop = node.stop.min(depth);
        unsafe {
            blake2s_u32::spec_memcopy_u32_nonoverlapping(
                leaf_hashes[node.query].as_ptr(),
                hasher.state.as_mut_ptr(),
                8,
            );
        }
        let mut index = node.index;
        let mut level = 0;
        while level < stop {
            let merge_level = saved_levels
                .as_slice()
                .last()
                .map_or(stop, |level| (*level).min(stop));
            while level < merge_level {
                let is_right = index & 1 != 0;
                let proof_buf = hasher.get_merkle_path_proof_buffer(is_right);
                for word in proof_buf.iter_mut() {
                    *word = nd_source.read_word();
                }
                hasher.compress_node::<true>(is_right);
                index >>= 1;
                level += 1;
            }
            if level < stop {
                let last = saved_levels.len() - 1;
                unsafe {
                    // Each saved level has exactly one initialized digest.
                    blake2s_u32::spec_memcopy_u32_nonoverlapping(
                        saved_hashes.get_unchecked(last).as_ptr().cast::<u32>(),
                        hasher.get_merkle_path_proof_buffer(true).as_mut_ptr(),
                        8,
                    );
                    saved_levels.set_len(last);
                }
                hasher.compress_node::<true>(true);
                index >>= 1;
                level += 1;
            }
        }
        if stop == depth {
            let start = index * BLAKE2S_DIGEST_SIZE_U32_WORDS;
            if !merkle_digest_matches(
                hasher.read_state_for_output_ref(),
                &cap[start..start + BLAKE2S_DIGEST_SIZE_U32_WORDS],
            ) {
                return false;
            }
        } else {
            unsafe {
                // Pending branch levels strictly decrease, so their count is
                // bounded by depth, which is less than usize::BITS.
                blake2s_u32::spec_memcopy_u32_nonoverlapping(
                    hasher.read_state_for_output_ref().as_ptr(),
                    saved_hashes
                        .get_unchecked_mut(saved_levels.len())
                        .as_mut_ptr()
                        .cast::<u32>(),
                    8,
                );
            }
            saved_levels.push(stop);
        }
    }
    saved_levels.is_empty()
}

// Explicit word comparisons avoid LLVM lowering slice equality to byte-wise
// memcmp, which is unsupported by the word-only RISC-V verifier machine.
#[inline(always)]
fn merkle_digest_matches(left: &[u32; 8], right: &[u32]) -> bool {
    left[0] == right[0]
        && left[1] == right[1]
        && left[2] == right[2]
        && left[3] == right[3]
        && left[4] == right[4]
        && left[5] == right[5]
        && left[6] == right[6]
        && left[7] == right[7]
}
