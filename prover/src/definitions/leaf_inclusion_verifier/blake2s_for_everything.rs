use super::*;
use blake2s_u32::{BLAKE2S_BLOCK_SIZE_U32_WORDS, BLAKE2S_DIGEST_SIZE_U32_WORDS};

#[derive(Debug)]
pub struct Blake2sForEverythingVerifier {
    hasher: blake2s_u32::DelegatedBlake2sState,
}

impl LeafInclusionVerifier for Blake2sForEverythingVerifier {
    #[inline(always)]
    fn new() -> Self {
        Self {
            hasher: blake2s_u32::DelegatedBlake2sState::new(),
        }
    }

    #[unroll::unroll_for_loops]
    unsafe fn verify_leaf_inclusion<
        I: NonDeterminismSource,
        const CAP_SIZE: usize,
        const NUM_COSETS: usize,
    >(
        &mut self,
        coset_index: u32,
        leaf_index: u32,
        depth: usize,
        leaf_encoding: &AlignedSlice64<u32>,
        merkle_cap: &[MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
    ) -> bool {
        // our strategy is:
        // - since leaf is used for other purposes, we have to copy it into the buffer, no options here
        // - but when we output the leaf hash, we will put it into the input buffer of our first of `merkle_path_hashers`,
        // and then alternate between them
        self.hasher.reset();

        let input_len_words = leaf_encoding.len();
        let mut num_full_rounds = input_len_words / BLAKE2S_BLOCK_SIZE_U32_WORDS;
        let mut last_round_len = input_len_words % BLAKE2S_BLOCK_SIZE_U32_WORDS;
        if last_round_len == 0 {
            if num_full_rounds > 0 {
                num_full_rounds -= 1;
            }
            last_round_len = BLAKE2S_BLOCK_SIZE_U32_WORDS;
        }

        // full rounds, unrolled
        let mut src_ptr = leaf_encoding
            .as_ptr()
            .cast::<[u32; BLAKE2S_BLOCK_SIZE_U32_WORDS]>();
        for _ in 0..num_full_rounds {
            let dst = self.hasher.input_buffer.as_mut_ptr().cast::<u32>();
            blake2s_u32::spec_memcopy_u32_nonoverlapping(
                src_ptr.cast::<u32>(),
                dst,
                BLAKE2S_BLOCK_SIZE_U32_WORDS,
            );
            self.hasher.run_round_function::<USE_REDUCED_BLAKE2_ROUNDS>(
                BLAKE2S_BLOCK_SIZE_U32_WORDS,
                false,
            );
            src_ptr = src_ptr.add(1);
        }

        // last round unrolled padding
        {
            let src_ptr = src_ptr.cast::<u32>();
            let mut dst_ptr = self.hasher.input_buffer.as_mut_ptr().cast::<u32>();
            blake2s_u32::spec_memcopy_u32_nonoverlapping(src_ptr, dst_ptr, last_round_len);
            dst_ptr = dst_ptr.add(last_round_len);
            blake2s_u32::spec_memzero_u32(
                dst_ptr,
                self.hasher
                    .input_buffer
                    .as_mut_ptr_range()
                    .end
                    .cast::<u32>(),
            );
            self.hasher
                .run_round_function::<USE_REDUCED_BLAKE2_ROUNDS>(last_round_len, true);
        }

        // now hash output is in state, and we will use it to verify a path below by asking for witness elements
        let mut index = leaf_index as usize;

        if depth == 0 {
            // quick path
            let output_hash = self.hasher.read_state_for_output_ref();
            let cap = merkle_cap
                .get_unchecked(coset_index as usize)
                .cap
                .get_unchecked(index);
            let mut equal = true;
            for i in 0..8 {
                // BLAKE2S_DIGEST_SIZE_U32_WORDS
                equal &= output_hash[i] == cap[i];
            }

            return equal;
        }

        if blake2s_u32::DelegatedBlake2sState::SUPPORT_SPEC_SINGLE_ROUND {
            // special case for first round
            {
                let input_is_right = index & 1 == 1;
                let previous_hash_dst_ptr = self
                    .hasher
                    .input_buffer
                    .as_mut_ptr()
                    .cast::<u32>()
                    .add(BLAKE2S_DIGEST_SIZE_U32_WORDS * input_is_right as usize);
                let mut witness_dst_ptr = self
                    .hasher
                    .input_buffer
                    .as_mut_ptr()
                    .cast::<u32>()
                    .add(BLAKE2S_DIGEST_SIZE_U32_WORDS * (!input_is_right) as usize);
                let current_state = self.hasher.read_state_for_output_ref();
                blake2s_u32::spec_memcopy_u32_nonoverlapping(
                    current_state.as_ptr().cast::<u32>(),
                    previous_hash_dst_ptr,
                    BLAKE2S_DIGEST_SIZE_U32_WORDS,
                );
                for _ in 0..8 {
                    // BLAKE2S_DIGEST_SIZE_U32_WORDS
                    // hashes are unstructured u32
                    witness_dst_ptr.write(I::read_word());
                    witness_dst_ptr = witness_dst_ptr.add(1);
                }
                index >>= 1;
                let output_is_right = index & 1 == 1;
                // we break aliasing, but fine, we know that we will delay writing there
                let dst_ptr = self
                    .hasher
                    .input_buffer
                    .as_mut_ptr()
                    .cast::<[u32; BLAKE2S_DIGEST_SIZE_U32_WORDS]>()
                    .add(output_is_right as usize);

                self.hasher.reset();
                self.hasher
                    .spec_run_single_round_into_destination::<USE_REDUCED_BLAKE2_ROUNDS>(
                        BLAKE2S_BLOCK_SIZE_U32_WORDS,
                        dst_ptr,
                    );
            }

            // every step we:
            // - place witness elements into the other part of input buffer
            // - run round function
            for _ in 1..depth {
                let input_is_right = index & 1 == 1;
                let mut witness_dst_ptr = self
                    .hasher
                    .input_buffer
                    .as_mut_ptr()
                    .add(BLAKE2S_DIGEST_SIZE_U32_WORDS * (!input_is_right) as usize);
                for _ in 0..8 {
                    // BLAKE2S_DIGEST_SIZE_U32_WORDS
                    // hashes are unstructured u32
                    witness_dst_ptr.write(I::read_word());
                    witness_dst_ptr = witness_dst_ptr.add(1);
                }
                index >>= 1;
                let output_is_right = index & 1 == 1;
                // we break aliasing, but fine, we know that we will delay writing there
                let dst_ptr = self
                    .hasher
                    .input_buffer
                    .as_mut_ptr()
                    .cast::<[u32; BLAKE2S_DIGEST_SIZE_U32_WORDS]>()
                    .add(output_is_right as usize);

                self.hasher.reset();
                self.hasher
                    .spec_run_single_round_into_destination::<USE_REDUCED_BLAKE2_ROUNDS>(
                        BLAKE2S_BLOCK_SIZE_U32_WORDS,
                        dst_ptr,
                    );
            }

            let output_is_right = index & 1 == 1;
            let output_hash = self
                .hasher
                .input_buffer
                .as_ptr()
                .cast::<[u32; BLAKE2S_DIGEST_SIZE_U32_WORDS]>()
                .add(output_is_right as usize)
                .as_ref_unchecked();

            // here we manually compare, otherwise it's compiled as memcmp that does by byte(!) comparison
            // output_hash == &merkle_cap[coset_index as usize].cap[index]

            let cap = merkle_cap
                .get_unchecked(coset_index as usize)
                .cap
                .get_unchecked(index);
            let mut equal = true;
            for i in 0..8 {
                // BLAKE2S_DIGEST_SIZE_U32_WORDS
                equal &= output_hash[i] == cap[i];
            }

            equal
        } else {
            // every step we:
            // - copy previous from the state into corresponding place of the input buffer
            // - place witness elements into the other part of input buffer
            // - run round function
            for _ in 0..depth {
                let input_is_right = index & 1 == 1;
                let previous_hash_dst_ptr = self
                    .hasher
                    .input_buffer
                    .as_mut_ptr()
                    .cast::<u32>()
                    .add(BLAKE2S_DIGEST_SIZE_U32_WORDS * input_is_right as usize);
                let mut witness_dst_ptr = self
                    .hasher
                    .input_buffer
                    .as_mut_ptr()
                    .add(BLAKE2S_DIGEST_SIZE_U32_WORDS * (!input_is_right) as usize);
                // copy element of the state - 8 of them
                let current_state = self.hasher.read_state_for_output_ref();
                blake2s_u32::spec_memcopy_u32_nonoverlapping(
                    current_state.as_ptr().cast::<u32>(),
                    previous_hash_dst_ptr,
                    BLAKE2S_DIGEST_SIZE_U32_WORDS,
                );
                for _ in 0..8 {
                    // BLAKE2S_DIGEST_SIZE_U32_WORDS
                    // hashes are unstructured u32
                    witness_dst_ptr.write(I::read_word());
                    witness_dst_ptr = witness_dst_ptr.add(1);
                }
                index >>= 1;

                self.hasher.reset();
                self.hasher.run_round_function::<USE_REDUCED_BLAKE2_ROUNDS>(
                    BLAKE2S_BLOCK_SIZE_U32_WORDS,
                    true,
                );
            }

            let output_hash = self.hasher.read_state_for_output_ref();

            // here we manually compare, otherwise it's compiled as memcmp that does by byte(!) comparison
            // output_hash == &merkle_cap[coset_index as usize].cap[index]

            let cap = merkle_cap
                .get_unchecked(coset_index as usize)
                .cap
                .get_unchecked(index);
            let mut equal = true;
            for i in 0..8 {
                // BLAKE2S_DIGEST_SIZE_U32_WORDS
                equal &= output_hash[i] == cap[i];
            }

            equal
        }
    }
}
