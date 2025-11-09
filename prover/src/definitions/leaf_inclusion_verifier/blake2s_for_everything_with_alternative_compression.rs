use core::mem::MaybeUninit;

use super::*;
use blake2s_u32::state_with_extended_control::*;
use blake2s_u32::AlignedArray64;
use blake2s_u32::BLAKE2S_BLOCK_SIZE_U32_WORDS;

#[derive(Debug)]
pub struct Blake2sForEverythingVerifierWithAlternativeCompression {
    hasher: Blake2RoundFunctionEvaluator,
}

impl LeafInclusionVerifier for Blake2sForEverythingVerifierWithAlternativeCompression {
    #[inline(always)]
    fn new() -> Self {
        Self {
            hasher: Blake2RoundFunctionEvaluator::new(),
        }
    }

    #[allow(invalid_value)]
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
            .cast::<AlignedArray64<u32, BLAKE2S_BLOCK_SIZE_U32_WORDS>>();
        for _ in 0..num_full_rounds {
            // here we do not need to copy anything
            self.hasher
                .run_round_function_with_input::<USE_REDUCED_BLAKE2_ROUNDS>(
                    src_ptr.as_ref_unchecked(),
                    BLAKE2S_BLOCK_SIZE_U32_WORDS,
                    false,
                );
            src_ptr = src_ptr.add(1);
        }

        // last round unrolled padding, and here we will copy to temporary buffer
        {
            // NOTE: here we have to "touch" full buffer
            let mut buffer: AlignedArray64<u32, BLAKE2S_BLOCK_SIZE_U32_WORDS> =
                MaybeUninit::uninit().assume_init();
            blake2s_u32::spec_memzero_u32(
                buffer.as_mut_ptr_range().start,
                buffer.as_mut_ptr_range().end,
            );
            let src_ptr = src_ptr.cast::<u32>();
            let dst_ptr = buffer.as_mut_ptr().cast::<u32>();
            blake2s_u32::spec_memcopy_u32_nonoverlapping(src_ptr, dst_ptr, last_round_len);
            self.hasher
                .run_round_function_with_input::<USE_REDUCED_BLAKE2_ROUNDS>(
                    &buffer,
                    last_round_len,
                    true,
                );
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

        // our round function invoker has leaf hash now into the state,
        // so what we need to do is just write witness and invoke compression

        for _ in 0..depth {
            let input_is_right = index & 1 == 1;
            let dst = self.hasher.get_witness_buffer();
            for i in 0..8 {
                // BLAKE2S_DIGEST_SIZE_U32_WORDS
                dst[i] = I::read_word();
            }
            self.hasher
                .compress_node::<USE_REDUCED_BLAKE2_ROUNDS>(input_is_right);
            index >>= 1;
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
