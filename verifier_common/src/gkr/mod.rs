use crate::lazy_vec::LazyVec;
use crate::structs::TranscriptState;
use blake2s_u32::{AlignedArray64, BLAKE2S_BLOCK_SIZE_U32_WORDS, BLAKE2S_DIGEST_SIZE_U32_WORDS};
use cs::definitions::GKRAddress;
use field::{Field, FieldExtension, PrimeField};
use non_determinism_source::NonDeterminismSource;
use prover::definitions::GKRExternalChallenges;
use transcript::Blake2sTranscript;

#[repr(usize)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SimpleGateType {
    Copy = 0,
    Product = 1, // InitialGrandProductFromCaches, TrivialProduct
    MaskToIdentity = 2,
    UnbalancedProduct = 3,
    LookupInitialPair = 4,
    LookupWithSetup = 5,
    LookupUnbalanced = 6,
    LookupAggregatePair = 7,
    LookupInitialWithCachedDenominators = 8,
}

#[cfg(any(test, feature = "proof_utils"))]
impl quote::ToTokens for SimpleGateType {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        use quote::quote;

        let quote = match self {
            SimpleGateType::Copy => {
                quote! { SimpleGateType::Copy }
            }
            SimpleGateType::Product => {
                quote! { SimpleGateType::Product }
            }
            SimpleGateType::MaskToIdentity => {
                quote! { SimpleGateType::MaskToIdentity }
            }
            SimpleGateType::UnbalancedProduct => {
                quote! { SimpleGateType::UnbalancedProduct }
            }
            SimpleGateType::LookupInitialPair => {
                quote! { SimpleGateType::LookupInitialPair }
            }
            SimpleGateType::LookupWithSetup => {
                quote! { SimpleGateType::LookupWithSetup }
            }
            SimpleGateType::LookupUnbalanced => {
                quote! { SimpleGateType::LookupUnbalanced }
            }
            SimpleGateType::LookupAggregatePair => {
                quote! { SimpleGateType::LookupAggregatePair }
            }
            SimpleGateType::LookupInitialWithCachedDenominators => {
                quote! { SimpleGateType::LookupInitialWithCachedDenominators }
            }
        };

        tokens.extend(quote);
    }
}

#[cfg(any(test, feature = "proof_utils"))]
pub mod flatten;

#[derive(Clone, Debug)]
pub struct LayerState<E: Field, const ROUNDS: usize, const ADDRS: usize> {
    pub prev_point: [E; ROUNDS],
    pub prev_point_len: usize,
    pub prev_claims: LazyVec<E, ADDRS>,
    pub batching_challenge: E,
}

// assigned sufficiently for precompile friendliness
#[derive(Debug)]
#[repr(C, align(64))]
pub struct InitialGKRTranscript<
    E: Field,
    const INIT_AND_TEARDOWN_SETS: usize,
    const EXTERNAL_CHALLENGES_FLATTENED_SIZE: usize,
    const CAP_SIZE: usize,
    const NUM_MEMORY_COMMITS: usize,
    const NUM_WITNESS_COMMITS: usize,
    const NUM_SETUP_COMMITS: usize,
    const PADDING_WORDS: usize,
> {
    pub inits_and_teardowns_top_bits: [u32; INIT_AND_TEARDOWN_SETS],
    pub external_challenges_flattened: [u32; EXTERNAL_CHALLENGES_FLATTENED_SIZE],
    pub setup_caps: [[[u32; BLAKE2S_DIGEST_SIZE_U32_WORDS]; CAP_SIZE]; NUM_SETUP_COMMITS],
    pub memory_caps: [[[u32; BLAKE2S_DIGEST_SIZE_U32_WORDS]; CAP_SIZE]; NUM_MEMORY_COMMITS],
    pub witness_caps: [[[u32; BLAKE2S_DIGEST_SIZE_U32_WORDS]; CAP_SIZE]; NUM_WITNESS_COMMITS],
    pub padding: [u32; PADDING_WORDS],
    pub _marker: core::marker::PhantomData<E>,
}

impl<
        E: Field,
        const INIT_AND_TEARDOWN_SETS: usize,
        const EXTERNAL_CHALLENGES_FLATTENED_SIZE: usize,
        const CAP_SIZE: usize,
        const NUM_MEMORY_COMMITS: usize,
        const NUM_WITNESS_COMMITS: usize,
        const NUM_SETUP_COMMITS: usize,
        const PADDING_WORDS: usize,
    >
    InitialGKRTranscript<
        E,
        INIT_AND_TEARDOWN_SETS,
        EXTERNAL_CHALLENGES_FLATTENED_SIZE,
        CAP_SIZE,
        NUM_MEMORY_COMMITS,
        NUM_WITNESS_COMMITS,
        NUM_SETUP_COMMITS,
        PADDING_WORDS,
    >
{
    pub fn as_aligned_chunks<'a>(
        &'a self,
    ) -> &'a [AlignedArray64<u32, BLAKE2S_BLOCK_SIZE_U32_WORDS>] {
        assert_eq!(
            core::mem::size_of::<Self>()
                % core::mem::size_of::<AlignedArray64<u32, BLAKE2S_BLOCK_SIZE_U32_WORDS>>(),
            0
        );
        assert_eq!(
                core::mem::offset_of!(Self,_marker)
                % core::mem::size_of::<AlignedArray64<u32, BLAKE2S_BLOCK_SIZE_U32_WORDS>>(),
            0
        );
        assert_eq!(
            core::mem::align_of::<Self>(),
            core::mem::align_of::<AlignedArray64<u32, BLAKE2S_BLOCK_SIZE_U32_WORDS>>()
        );
        unsafe {
            let len = core::mem::size_of::<Self>()
                / core::mem::size_of::<AlignedArray64<u32, BLAKE2S_BLOCK_SIZE_U32_WORDS>>();
            core::slice::from_raw_parts((self as *const Self).cast(), len)
        }
    }

    pub fn memory_caps_slice<'a>(&'a self) -> &'a [u32] {
        unsafe {
            let len = BLAKE2S_DIGEST_SIZE_U32_WORDS * CAP_SIZE * NUM_MEMORY_COMMITS;
            core::slice::from_raw_parts(core::ptr::addr_of!(self.memory_caps).cast(), len)
        }
    }

    pub fn witness_caps_slice<'a>(&'a self) -> &'a [u32] {
        unsafe {
            let len = BLAKE2S_DIGEST_SIZE_U32_WORDS * CAP_SIZE * NUM_WITNESS_COMMITS;
            core::slice::from_raw_parts(core::ptr::addr_of!(self.witness_caps).cast(), len)
        }
    }

    pub fn setup_caps_slice<'a>(&'a self) -> &'a [u32] {
        unsafe {
            let len = BLAKE2S_DIGEST_SIZE_U32_WORDS * CAP_SIZE * NUM_SETUP_COMMITS;
            core::slice::from_raw_parts(core::ptr::addr_of!(self.setup_caps).cast(), len)
        }
    }
}

#[inline(always)]
pub fn make_initial_transcript<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    I: NonDeterminismSource,
    const INIT_AND_TEARDOWN_SETS: usize,
    const EXTERNAL_CHALLENGES_FLATTENED_SIZE: usize,
    const CAP_SIZE: usize,
    const NUM_MEMORY_COMMITS: usize,
    const NUM_WITNESS_COMMITS: usize,
    const NUM_SETUP_COMMITS: usize,
    const PADDING_WORDS: usize,
>(
    external_challenges: &GKRExternalChallenges<F, E>,
) -> (
    InitialGKRTranscript<
        E,
        INIT_AND_TEARDOWN_SETS,
        EXTERNAL_CHALLENGES_FLATTENED_SIZE,
        CAP_SIZE,
        NUM_MEMORY_COMMITS,
        NUM_WITNESS_COMMITS,
        NUM_SETUP_COMMITS,
        PADDING_WORDS,
    >,
    TranscriptState,
)
where
    [(); E::DEGREE]:,
{
    assert!(NUM_MEMORY_COMMITS == 0 || NUM_MEMORY_COMMITS == 1);
    assert!(NUM_WITNESS_COMMITS == 0 || NUM_WITNESS_COMMITS == 1);
    assert!(NUM_SETUP_COMMITS == 0 || NUM_SETUP_COMMITS == 1);
    debug_assert_eq!(
        core::mem::size_of::<
            InitialGKRTranscript<
                E,
                INIT_AND_TEARDOWN_SETS,
                EXTERNAL_CHALLENGES_FLATTENED_SIZE,
                CAP_SIZE,
                NUM_MEMORY_COMMITS,
                NUM_WITNESS_COMMITS,
                NUM_SETUP_COMMITS,
                PADDING_WORDS,
            >,
        >() % (core::mem::size_of::<u32>() * BLAKE2S_BLOCK_SIZE_U32_WORDS),
        0
    );
    debug_assert_eq!(
        core::mem::align_of::<
            InitialGKRTranscript<
                E,
                INIT_AND_TEARDOWN_SETS,
                EXTERNAL_CHALLENGES_FLATTENED_SIZE,
                CAP_SIZE,
                NUM_MEMORY_COMMITS,
                NUM_WITNESS_COMMITS,
                NUM_SETUP_COMMITS,
                PADDING_WORDS,
            >,
        >() % 64,
        0
    );

    unsafe {
        let initial_transcript_state = InitialGKRTranscript {
            inits_and_teardowns_top_bits: core::array::from_fn(|_| I::read_word()),
            external_challenges_flattened: external_challenges.flatten_into_fixed_size_buffer(),
            setup_caps: core::array::from_fn(|_| {
                core::array::from_fn(|_| core::array::from_fn(|_| I::read_word()))
            }),
            memory_caps: core::array::from_fn(|_| {
                core::array::from_fn(|_| core::array::from_fn(|_| I::read_word()))
            }),
            witness_caps: core::array::from_fn(|_| {
                core::array::from_fn(|_| core::array::from_fn(|_| I::read_word()))
            }),
            padding: [0u32; PADDING_WORDS],
            _marker: core::marker::PhantomData,
        };
        let mut hasher = blake2s_u32::DelegatedBlake2sState::new();
        let state_as_flattened_buffers = initial_transcript_state.as_aligned_chunks();
        let meaningful_part_len = core::mem::offset_of!(
                InitialGKRTranscript<
                    E,
                    INIT_AND_TEARDOWN_SETS,
                    EXTERNAL_CHALLENGES_FLATTENED_SIZE,
                    CAP_SIZE,
                    NUM_MEMORY_COMMITS,
                    NUM_WITNESS_COMMITS,
                    NUM_SETUP_COMMITS,
                    PADDING_WORDS,
                >, padding);
        assert_eq!(meaningful_part_len % core::mem::size_of::<u32>(), 0);
        let total_words = meaningful_part_len / core::mem::size_of::<u32>();
        let seed = Blake2sTranscript::commit_initial_using_hasher_and_aligned_buffer(
            &mut hasher,
            state_as_flattened_buffers,
            total_words,
        );
        hasher.reset();
        let ts = TranscriptState::from_hasher_and_seed(hasher, seed);

        (initial_transcript_state, ts)
    }
}

pub struct GKRVerifierOutput<'a, E: Field, const ROUNDS: usize, const ADDRS: usize> {
    pub base_layer_addrs: &'a [GKRAddress],
    pub evaluation_point: [E; ROUNDS],
    pub evaluation_point_len: usize,
    pub permutation_read_product: E,
    pub permutation_write_product: E,
    pub additional_base_layer_openings: &'a [GKRAddress],
    pub whir_batching_challenge: E,
    pub base_layer_claims: LazyVec<E, ADDRS>,
}
