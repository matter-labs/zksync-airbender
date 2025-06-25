macro_rules! field_size {
    ($t:ident :: $field:ident) => {{
        let m = core::mem::MaybeUninit::<$t>::uninit();
        #[allow(unused_unsafe)]
        let p = unsafe { core::ptr::addr_of!((*m.as_ptr()).$field) };

        const fn size_of_raw<T>(_: *const T) -> usize {
            core::mem::size_of::<T>()
        }
        size_of_raw(p)
    }};
}

use super::size_constants::*;
use crate::skeleton::*;
use core::mem::offset_of;
use field::Mersenne31Field;
use field::Mersenne31Quartic;
use field::PrimeField;
use verifier_common::non_determinism_source::NonDeterminismSource;
use verifier_common::prover::definitions::LeafInclusionVerifier;
use verifier_common::prover::definitions::MerkleTreeCap;

pub type ProofSkeletonInstance = ProofSkeleton<
    SKELETON_PADDING,
    TREE_CAP_SIZE,
    NUM_COSETS,
    NUM_PUBLIC_INPUTS_FROM_STATE_ELEMENTS,
    NUM_DELEGATION_CHALLENGES,
    NUM_AUX_BOUNDARY_VALUES,
    NUM_PUBLIC_INPUTS_FROM_STATE_ELEMENTS,
    NUM_OPENINGS_AT_Z,
    NUM_OPENINGS_AT_Z_OMEGA,
    NUM_FRI_STEPS_WITH_ORACLES,
    LAST_FRI_STEP_LEAFS_TOTAL_SIZE_PER_COSET,
    FRI_FINAL_DEGREE,
>;

pub(crate) const BASE_CIRCUIT_PROOF_SKELETON_NO_PADDING_AND_GAPS_START_U32_WORDS: usize = const {
    let total_size = offset_of!(ProofSkeletonInstance, circuit_sequence_idx);

    assert!(total_size % core::mem::size_of::<u32>() == 0);

    total_size / core::mem::size_of::<u32>()
};

pub(crate) const BASE_CIRCUIT_PROOF_SKELETON_NO_PADDING_AND_GAPS_U32_WORDS: usize = const {
    // check that no spacing exists in the skeleton main part
    let mut total_size = 0;

    total_size += field_size!(ProofSkeletonInstance::_padding);
    assert!(offset_of!(ProofSkeletonInstance, circuit_sequence_idx) == total_size,);

    total_size += field_size!(ProofSkeletonInstance::circuit_sequence_idx);
    assert!(offset_of!(ProofSkeletonInstance, delegation_type) == total_size,);

    total_size += field_size!(ProofSkeletonInstance::delegation_type);
    assert!(offset_of!(ProofSkeletonInstance, public_inputs) == total_size,);

    total_size += field_size!(ProofSkeletonInstance::public_inputs);
    assert!(offset_of!(ProofSkeletonInstance, setup_caps) == total_size,);

    assert!(offset_of!(ProofSkeletonInstance, setup_caps) % 16 == 0);

    total_size += field_size!(ProofSkeletonInstance::setup_caps);
    assert!(offset_of!(ProofSkeletonInstance, memory_argument_challenges) == total_size,);

    total_size += field_size!(ProofSkeletonInstance::memory_argument_challenges);
    assert!(offset_of!(ProofSkeletonInstance, delegation_argument_challenges) == total_size,);

    total_size += field_size!(ProofSkeletonInstance::delegation_argument_challenges);
    assert!(offset_of!(ProofSkeletonInstance, aux_boundary_values) == total_size,);

    total_size += field_size!(ProofSkeletonInstance::aux_boundary_values);
    assert!(offset_of!(ProofSkeletonInstance, witness_caps) == total_size,);

    total_size += field_size!(ProofSkeletonInstance::witness_caps);
    assert!(offset_of!(ProofSkeletonInstance, memory_caps) == total_size,);

    total_size += field_size!(ProofSkeletonInstance::memory_caps);
    assert!(offset_of!(ProofSkeletonInstance, stage_2_caps) == total_size,);

    total_size += field_size!(ProofSkeletonInstance::stage_2_caps);
    assert!(offset_of!(ProofSkeletonInstance, memory_grand_product_accumulator) == total_size,);

    total_size += field_size!(ProofSkeletonInstance::memory_grand_product_accumulator);
    assert!(offset_of!(ProofSkeletonInstance, delegation_argument_accumulator) == total_size,);

    total_size += field_size!(ProofSkeletonInstance::delegation_argument_accumulator);
    assert!(offset_of!(ProofSkeletonInstance, quotient_caps) == total_size,);

    total_size += field_size!(ProofSkeletonInstance::quotient_caps);
    assert!(offset_of!(ProofSkeletonInstance, openings_at_z) == total_size,);

    total_size += field_size!(ProofSkeletonInstance::openings_at_z);
    assert!(offset_of!(ProofSkeletonInstance, openings_at_z_omega) == total_size,);

    total_size += field_size!(ProofSkeletonInstance::openings_at_z_omega);
    assert!(offset_of!(ProofSkeletonInstance, fri_intermediate_oracles) == total_size,);

    total_size += field_size!(ProofSkeletonInstance::fri_intermediate_oracles);
    assert!(offset_of!(ProofSkeletonInstance, fri_final_step_leafs) == total_size,);

    total_size += field_size!(ProofSkeletonInstance::fri_final_step_leafs);
    assert!(offset_of!(ProofSkeletonInstance, monomial_coeffs) == total_size,);

    total_size += field_size!(ProofSkeletonInstance::monomial_coeffs);
    assert!(offset_of!(ProofSkeletonInstance, pow_nonce) == total_size,);

    total_size += field_size!(ProofSkeletonInstance::pow_nonce);

    assert!(total_size <= core::mem::size_of::<ProofSkeletonInstance>());

    assert!(total_size % core::mem::size_of::<u32>() == 0);

    total_size / core::mem::size_of::<u32>()
};

pub type QueryValuesInstance = QueryValues<
    BITS_FOR_QUERY_INDEX,
    DEFAULT_MERKLE_PATH_LENGTH,
    TOTAL_FRI_ORACLES_PATHS_LENGTH,
    LEAF_SIZE_SETUP,
    LEAF_SIZE_WITNESS_TREE,
    LEAF_SIZE_MEMORY_TREE,
    LEAF_SIZE_STAGE_2,
    LEAF_SIZE_QUOTIENT,
    TOTAL_FRI_LEAFS_SIZES,
    NUM_FRI_STEPS,
>;

pub const BASE_CIRCUIT_QUERY_VALUES_NO_PADDING_U32_WORDS: usize = const {
    // check that no spacing exists in the skeleton main part
    let mut total_size = 0;
    total_size += field_size!(QueryValuesInstance::query_index);
    assert!(offset_of!(QueryValuesInstance, setup_leaf) == total_size,);

    total_size += field_size!(QueryValuesInstance::setup_leaf);
    assert!(offset_of!(QueryValuesInstance, witness_leaf) == total_size,);

    total_size += field_size!(QueryValuesInstance::witness_leaf);
    assert!(offset_of!(QueryValuesInstance, memory_leaf) == total_size,);

    total_size += field_size!(QueryValuesInstance::memory_leaf);
    assert!(offset_of!(QueryValuesInstance, stage_2_leaf) == total_size,);

    total_size += field_size!(QueryValuesInstance::stage_2_leaf);
    assert!(offset_of!(QueryValuesInstance, quotient_leaf) == total_size,);

    total_size += field_size!(QueryValuesInstance::quotient_leaf);
    assert!(offset_of!(QueryValuesInstance, fri_oracles_leafs) == total_size,);

    total_size += field_size!(QueryValuesInstance::fri_oracles_leafs);

    assert!(total_size <= core::mem::size_of::<QueryValuesInstance>());
    assert!(total_size % core::mem::size_of::<u32>() == 0);

    total_size / core::mem::size_of::<u32>()
};

impl ProofSkeletonInstance {
    #[inline(never)]
    pub unsafe fn fill<I: NonDeterminismSource>(this: *mut Self) {
        let dst = this.cast::<u32>();
        let modulus = Mersenne31Field::CHARACTERISTICS as u32;
        // we need to make few stops here and switch between field elements and u32 unstructured values
        let mut i = BASE_CIRCUIT_PROOF_SKELETON_NO_PADDING_AND_GAPS_START_U32_WORDS;
        // circuit sequence and delegation types
        while i < offset_of!(ProofSkeletonInstance, public_inputs) / core::mem::size_of::<u32>() {
            // values are unstructured u32, and we will check the logic over them separately
            dst.add(i).write(I::read_word());
            i += 1;
        }
        // public inputs
        while i < offset_of!(ProofSkeletonInstance, setup_caps) / core::mem::size_of::<u32>() {
            // field elements mut be reduced in full
            dst.add(i).write(I::read_reduced_field_element(modulus));
            i += 1;
        }
        // setup tree
        while i < offset_of!(ProofSkeletonInstance, memory_argument_challenges)
            / core::mem::size_of::<u32>()
        {
            // hashes are unstructured u32
            dst.add(i).write(I::read_word());
            i += 1;
        }
        // various external challenges - field elements
        while i < offset_of!(ProofSkeletonInstance, witness_caps) / core::mem::size_of::<u32>() {
            // field elements mut be reduced in full
            dst.add(i).write(I::read_reduced_field_element(modulus));
            i += 1;
        }
        // witness, memory, stage 2 tree
        while i < offset_of!(ProofSkeletonInstance, memory_grand_product_accumulator)
            / core::mem::size_of::<u32>()
        {
            // hashes are unstructured u32
            dst.add(i).write(I::read_word());
            i += 1;
        }
        // memory grand product + delegation accumulators
        while i < offset_of!(ProofSkeletonInstance, quotient_caps) / core::mem::size_of::<u32>() {
            // field elements mut be reduced in full
            dst.add(i).write(I::read_reduced_field_element(modulus));
            i += 1;
        }
        // quotient tree
        while i < offset_of!(ProofSkeletonInstance, openings_at_z) / core::mem::size_of::<u32>() {
            // hashes are unstructured u32
            dst.add(i).write(I::read_word());
            i += 1;
        }
        // values at z and z*omega
        while i < offset_of!(ProofSkeletonInstance, fri_intermediate_oracles)
            / core::mem::size_of::<u32>()
        {
            // field elements mut be reduced in full
            dst.add(i).write(I::read_reduced_field_element(modulus));
            i += 1;
        }
        // fri intermediate oracles
        while i < offset_of!(ProofSkeletonInstance, monomial_coeffs) / core::mem::size_of::<u32>() {
            // hashes are unstructured u32
            dst.add(i).write(I::read_word());
            i += 1;
        }
        // monomial coeffs
        while i < offset_of!(ProofSkeletonInstance, pow_nonce) / core::mem::size_of::<u32>() {
            // field elements mut be reduced in full
            dst.add(i).write(I::read_reduced_field_element(modulus));
            i += 1;
        }
        // nonce for PoW
        while i < core::hint::black_box(BASE_CIRCUIT_PROOF_SKELETON_NO_PADDING_AND_GAPS_U32_WORDS) {
            dst.add(i).write(I::read_word());
            i += 1;
        }
        // NOTE: black boxes here are to avoid u16 abuse by compiler
        assert!(
            this.as_ref_unchecked().circuit_sequence_idx & core::hint::black_box(0xffff0000u32)
                == 0
        );
        assert!(
            this.as_ref_unchecked().delegation_type & core::hint::black_box(0xffff0000u32) == 0
        );
    }

    pub fn transcript_elements_before_stage2(&'_ self) -> &'_ [u32] {
        unsafe {
            let start = (self as *const Self).cast::<u32>().add(
                offset_of!(ProofSkeletonInstance, circuit_sequence_idx)
                    / core::mem::size_of::<u32>(),
            );
            let end = (self as *const Self)
                .cast::<u32>()
                .add(offset_of!(ProofSkeletonInstance, stage_2_caps) / core::mem::size_of::<u32>());
            core::slice::from_ptr_range(start..end)
        }
    }

    pub fn transcript_elements_stage2_to_stage3(&'_ self) -> &'_ [u32] {
        unsafe {
            let start = (self as *const Self)
                .cast::<u32>()
                .add(offset_of!(ProofSkeletonInstance, stage_2_caps) / core::mem::size_of::<u32>());
            let end = (self as *const Self).cast::<u32>().add(
                offset_of!(ProofSkeletonInstance, quotient_caps) / core::mem::size_of::<u32>(),
            );
            core::slice::from_ptr_range(start..end)
        }
    }

    pub fn transcript_elements_stage3_to_stage4(&'_ self) -> &'_ [u32] {
        unsafe {
            let start = (self as *const Self).cast::<u32>().add(
                offset_of!(ProofSkeletonInstance, quotient_caps) / core::mem::size_of::<u32>(),
            );
            let end = (self as *const Self).cast::<u32>().add(
                offset_of!(ProofSkeletonInstance, openings_at_z) / core::mem::size_of::<u32>(),
            );
            core::slice::from_ptr_range(start..end)
        }
    }

    pub fn transcript_elements_evaluations_at_z(&'_ self) -> &'_ [u32] {
        unsafe {
            let start = (self as *const Self).cast::<u32>().add(
                offset_of!(ProofSkeletonInstance, openings_at_z) / core::mem::size_of::<u32>(),
            );
            let end = (self as *const Self).cast::<u32>().add(
                offset_of!(ProofSkeletonInstance, fri_intermediate_oracles)
                    / core::mem::size_of::<u32>(),
            );
            core::slice::from_ptr_range(start..end)
        }
    }

    pub fn transcript_elements_fri_intermediate_oracles(
        &'_ self,
    ) -> [&'_ [u32]; NUM_FRI_STEPS_WITH_ORACLES] {
        unsafe {
            let start_of_oracles = (self as *const Self).cast::<u32>().add(
                offset_of!(ProofSkeletonInstance, fri_intermediate_oracles)
                    / core::mem::size_of::<u32>(),
            );
            let cap_size_u32_words =
                core::mem::size_of::<[MerkleTreeCap<TREE_CAP_SIZE>; NUM_COSETS]>()
                    / core::mem::size_of::<u32>();

            core::array::from_fn(|i| {
                let start = start_of_oracles.add(i * cap_size_u32_words);
                let end = start.add(cap_size_u32_words);
                core::slice::from_ptr_range(start..end)
            })
        }
    }

    pub fn transcript_elements_last_fri_step_leaf_values(&'_ self) -> &'_ [u32] {
        unsafe {
            let start_of_oracles = (self as *const Self).cast::<u32>().add(
                offset_of!(ProofSkeletonInstance, fri_final_step_leafs)
                    / core::mem::size_of::<u32>(),
            );
            let set_size_u32_words = core::mem::size_of::<
                [[Mersenne31Quartic; LAST_FRI_STEP_LEAFS_TOTAL_SIZE_PER_COSET]; NUM_COSETS],
            >() / core::mem::size_of::<u32>();

            let start = start_of_oracles;
            let end = start.add(set_size_u32_words);
            // those are reduced when we read them
            core::slice::from_ptr_range(start..end)
        }
    }

    pub fn transcript_elements_monomial_coefficients(&'_ self) -> &'_ [u32] {
        unsafe {
            let start = (self as *const Self).cast::<u32>().add(
                offset_of!(ProofSkeletonInstance, monomial_coeffs) / core::mem::size_of::<u32>(),
            );
            let len =
                field_size!(ProofSkeletonInstance::monomial_coeffs) / core::mem::size_of::<u32>();
            core::slice::from_raw_parts(start, len)
        }
    }
}

impl QueryValuesInstance {
    #[inline(never)]
    pub unsafe fn fill<I: NonDeterminismSource, V: LeafInclusionVerifier>(
        this: *mut Self,
        proof_skeleton: &ProofSkeletonInstance,
        hasher: &mut V,
    ) {
        let dst = this.cast::<u32>();
        let modulus = Mersenne31Field::CHARACTERISTICS as u32;
        // query index
        let query_index = I::read_word();
        assert!(
            query_index < (1u32 << BITS_FOR_QUERY_INDEX),
            "query index 0x{:08x} must be smaller than 0x{:08x}",
            query_index,
            1u32 << BITS_FOR_QUERY_INDEX
        );
        dst.write(query_index);
        let mut i = 1;
        // leaf values are field elements
        while i < BASE_CIRCUIT_QUERY_VALUES_NO_PADDING_U32_WORDS {
            // field elements mut be reduced in full
            dst.add(i).write(I::read_reduced_field_element(modulus));
            i += 1;
        }

        // for all except FRI the following is valid
        let tree_index = query_index & TREE_INDEX_MASK;
        let coset_index = query_index >> TRACE_LEN_LOG2;
        // and now we should optimistically verify each leaf over the corresponding merkle cap

        let setup_included = hasher.verify_leaf_inclusion::<I, TREE_CAP_SIZE, NUM_COSETS>(
            coset_index,
            tree_index,
            DEFAULT_MERKLE_PATH_LENGTH,
            core::slice::from_raw_parts(
                this.as_ref_unchecked().setup_leaf.as_ptr().cast::<u32>(),
                LEAF_SIZE_SETUP,
            ),
            &proof_skeleton.setup_caps,
        );
        assert!(setup_included);

        let witness_included = hasher.verify_leaf_inclusion::<I, TREE_CAP_SIZE, NUM_COSETS>(
            coset_index,
            tree_index,
            DEFAULT_MERKLE_PATH_LENGTH,
            core::slice::from_raw_parts(
                this.as_ref_unchecked().witness_leaf.as_ptr().cast::<u32>(),
                LEAF_SIZE_WITNESS_TREE,
            ),
            &proof_skeleton.witness_caps,
        );
        assert!(witness_included);

        let memory_included = hasher.verify_leaf_inclusion::<I, TREE_CAP_SIZE, NUM_COSETS>(
            coset_index,
            tree_index,
            DEFAULT_MERKLE_PATH_LENGTH,
            core::slice::from_raw_parts(
                this.as_ref_unchecked().memory_leaf.as_ptr().cast::<u32>(),
                LEAF_SIZE_MEMORY_TREE,
            ),
            &proof_skeleton.memory_caps,
        );
        assert!(memory_included);

        let stage_2_included = hasher.verify_leaf_inclusion::<I, TREE_CAP_SIZE, NUM_COSETS>(
            coset_index,
            tree_index,
            DEFAULT_MERKLE_PATH_LENGTH,
            core::slice::from_raw_parts(
                this.as_ref_unchecked().stage_2_leaf.as_ptr().cast::<u32>(),
                LEAF_SIZE_STAGE_2,
            ),
            &proof_skeleton.stage_2_caps,
        );
        assert!(stage_2_included);

        let quotient_included = hasher.verify_leaf_inclusion::<I, TREE_CAP_SIZE, NUM_COSETS>(
            coset_index,
            tree_index,
            DEFAULT_MERKLE_PATH_LENGTH,
            core::slice::from_raw_parts(
                this.as_ref_unchecked().quotient_leaf.as_ptr().cast::<u32>(),
                LEAF_SIZE_QUOTIENT,
            ),
            &proof_skeleton.quotient_caps,
        );
        assert!(quotient_included);

        let mut fri_tree_index = tree_index;
        let mut fri_path_length = DEFAULT_MERKLE_PATH_LENGTH;
        let mut fri_leaf_start = this.as_ref_unchecked().fri_oracles_leafs.as_ptr();
        for fri_step in 0..NUM_FRI_STEPS_WITH_ORACLES {
            let caps = &proof_skeleton.fri_intermediate_oracles[fri_step];
            fri_tree_index >>= FRI_FOLDING_SCHEDULE[fri_step];
            fri_path_length -= FRI_FOLDING_SCHEDULE[fri_step];
            let leaf_size = 4 * (1 << FRI_FOLDING_SCHEDULE[fri_step]);
            let fri_oracle_included = hasher.verify_leaf_inclusion::<I, TREE_CAP_SIZE, NUM_COSETS>(
                coset_index,
                fri_tree_index,
                fri_path_length,
                core::slice::from_raw_parts(fri_leaf_start.cast::<u32>(), leaf_size),
                caps,
            );
            assert!(fri_oracle_included);

            fri_leaf_start = fri_leaf_start.add(leaf_size);
        }
    }

    pub unsafe fn fill_array<I: NonDeterminismSource, V: LeafInclusionVerifier, const N: usize>(
        dst: *mut [Self; N],
        proof_skeleton: &ProofSkeletonInstance,
        hasher: &mut V,
    ) {
        let dst = dst.cast::<Self>();
        let mut i = 0;
        while i < N {
            Self::fill::<I, V>(dst.add(i), proof_skeleton, hasher);
            i += 1;
        }
    }
}
