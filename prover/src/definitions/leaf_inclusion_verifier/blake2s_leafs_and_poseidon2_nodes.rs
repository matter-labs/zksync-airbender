use super::*;
use crate::definitions::DIGEST_SIZE_U32_WORDS;
use blake2s_u32::BLAKE2S_BLOCK_SIZE_U32_WORDS;

#[derive(Debug)]
pub struct Blake2sForLeafsPoseidon2ForNodesVerifier {
    hasher: blake2s_u32::Blake2sState,
    poseidon2_hasher: poseidon2::m31::Poseidon2Compressor,
}

impl LeafInclusionVerifier for Blake2sForLeafsPoseidon2ForNodesVerifier {
    #[inline(always)]
    fn new() -> Self {
        Self {
            hasher: blake2s_u32::Blake2sState::new(),
            poseidon2_hasher: poseidon2::m31::Poseidon2Compressor::new(),
        }
    }

    #[inline(always)]
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
        // - but when we output the leaf hash, we will put it into the input buffer of Poseidon2 and keep it there
        self.hasher.reset();

        let input_len_words = leaf_encoding.len();
        let mut num_full_rounds = input_len_words / BLAKE2S_BLOCK_SIZE_U32_WORDS;
        let mut last_round_len = input_len_words % BLAKE2S_BLOCK_SIZE_U32_WORDS;
        if last_round_len == 0 {
            if num_full_rounds > 1 {
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
                // DIGEST_SIZE_U32_WORDS
                equal &= output_hash[i] == cap[i];
            }

            return equal;
        }

        {
            let input_is_right = index & 1 == 1;
            index >>= 1;
            let current_state = self.hasher.read_state_for_output_ref();
            blake2s_u32::spec_memcopy_u32_nonoverlapping(
                current_state.as_ptr().cast::<u32>(),
                self.poseidon2_hasher.input.as_mut_ptr().cast::<u32>(),
                poseidon2::m31::HASH_SIZE_U32_WORDS,
            );
            self.poseidon2_hasher
                .provide_witness_and_compress::<I>(input_is_right);
        }

        for _ in 1..depth {
            let input_is_right = index & 1 == 1;
            index >>= 1;
            self.poseidon2_hasher
                .provide_witness_and_compress::<I>(input_is_right);
        }

        // this performs full reduction
        let output_hash: [u32; DIGEST_SIZE_U32_WORDS] =
            core::mem::transmute(self.poseidon2_hasher.get_output());

        // here we manually compare, otherwise it's compiled as memcmp that does by byte(!) comparison
        // output_hash == &merkle_cap[coset_index as usize].cap[index]

        let cap = merkle_cap
            .get_unchecked(coset_index as usize)
            .cap
            .get_unchecked(index);
        let mut equal = true;
        for i in 0..8 {
            // DIGEST_SIZE_U32_WORDS
            equal &= output_hash[i] == cap[i];
        }

        return equal;
    }
}
