use crate::lazy_vec::LazyVec;
use crate::structs::TranscriptState;
use blake2s_u32::{AlignedArray64, BLAKE2S_BLOCK_SIZE_U32_WORDS, BLAKE2S_DIGEST_SIZE_U32_WORDS};
use field::{Field, FieldExtension, PrimeField};
use non_determinism_source::U32WordNonDeterminismSource;
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
    pub fn as_aligned_chunks(&self) -> &[AlignedArray64<u32, BLAKE2S_BLOCK_SIZE_U32_WORDS>] {
        assert_eq!(
            core::mem::size_of::<Self>()
                % core::mem::size_of::<AlignedArray64<u32, BLAKE2S_BLOCK_SIZE_U32_WORDS>>(),
            0
        );
        assert_eq!(
            core::mem::offset_of!(Self, _marker)
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

    pub fn memory_caps_slice(&self) -> &[u32] {
        unsafe {
            let len = BLAKE2S_DIGEST_SIZE_U32_WORDS * CAP_SIZE * NUM_MEMORY_COMMITS;
            core::slice::from_raw_parts(core::ptr::addr_of!(self.memory_caps).cast(), len)
        }
    }

    pub fn witness_caps_slice(&self) -> &[u32] {
        unsafe {
            let len = BLAKE2S_DIGEST_SIZE_U32_WORDS * CAP_SIZE * NUM_WITNESS_COMMITS;
            core::slice::from_raw_parts(core::ptr::addr_of!(self.witness_caps).cast(), len)
        }
    }

    pub fn setup_caps_slice(&self) -> &[u32] {
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
    I: U32WordNonDeterminismSource,
    const INIT_AND_TEARDOWN_SETS: usize,
    const EXTERNAL_CHALLENGES_FLATTENED_SIZE: usize,
    const CAP_SIZE: usize,
    const NUM_MEMORY_COMMITS: usize,
    const NUM_WITNESS_COMMITS: usize,
    const NUM_SETUP_COMMITS: usize,
    const PADDING_WORDS: usize,
>(
    external_challenges: &prover::definitions::GKRExternalChallenges<F, E>,
    nd_source: &mut I,
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
) {
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
            inits_and_teardowns_top_bits: core::array::from_fn(|_| nd_source.read_word()),
            external_challenges_flattened: external_challenges.flatten_into_fixed_size_buffer(),
            setup_caps: core::array::from_fn(|_| {
                core::array::from_fn(|_| core::array::from_fn(|_| nd_source.read_word()))
            }),
            memory_caps: core::array::from_fn(|_| {
                core::array::from_fn(|_| core::array::from_fn(|_| nd_source.read_word()))
            }),
            witness_caps: core::array::from_fn(|_| {
                core::array::from_fn(|_| core::array::from_fn(|_| nd_source.read_word()))
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
        let seed = Blake2sTranscript::<{ ::prover::definitions::USE_REDUCED_BLAKE2_ROUNDS }>::commit_initial_using_hasher_and_aligned_buffer(
            &mut hasher,
            state_as_flattened_buffers,
            total_words,
        );
        hasher.reset();
        let ts = TranscriptState::from_hasher_and_seed(hasher, seed);

        (initial_transcript_state, ts)
    }
}

pub struct GKRVerifierOutput<E: Field, const ROUNDS: usize, const ADDRS: usize> {
    pub evaluation_point: [E; ROUNDS],
    pub evaluation_point_len: usize,
    pub permutation_read_product: E,
    pub permutation_write_product: E,
    pub inits_and_teardowns_read_product: E,
    pub inits_and_teardowns_write_product: E,
    pub whir_batching_challenge: E,
    pub base_layer_claims: LazyVec<E, ADDRS>,
}

/// Merge the base-layer claims of a PACKED base commitment, in place.
///
/// Mirrors the prover's `merge_claims` (`prover::gkr::prover`): the base
/// columns of every committed set are packed by `2^pack_log2` consecutive
/// columns into one committed column (block `y` of the packed poly is
/// sub-poly `y`; a short tail group is zero-padded), so every group of
/// `2^pack_log2` consecutive claims collapses to ONE claim by binding the
/// `pack_log2 = extra_coordinates.len()` extra claim-point coordinates
/// forward: adjacent claims `(a, b)` — differing in pack-index bit 0 — become
/// `a + (b - a) * r_0`, the results pair up under `r_1`, and so on.
///
/// `set_lens` are the UNPACKED column counts of the committed sets in
/// commitment order ([memory, witness, setup]; the witness set is empty in the
/// merged modes), laid out contiguously at the front of `claims`. The merged
/// sets are written contiguously at the front of `claims` (each set is
/// `ceil(len / 2^pack_log2)` long) and their total length is returned.
/// Entries past the input sets are left untouched. With no extra coordinates
/// (`pack_log2 = 0`) the claims are unchanged.
#[inline(always)]
pub fn merge_packed_claims<E: Field>(
    claims: &mut [E],
    set_lens: &[usize],
    extra_coordinates: &[E],
) -> usize {
    let pack = 1usize << extra_coordinates.len();
    let mut in_off = 0usize;
    let mut out_off = 0usize;
    for &len in set_lens {
        let mut chunk_start = in_off;
        let mut remaining = len;
        while remaining > 0 {
            let chunk_len = if remaining < pack { remaining } else { pack };
            // Fold the group in place: level `i` halves the live prefix, reading
            // past it as zero (the prover's zero padding of a short tail group).
            let mut live = chunk_len;
            for r in extra_coordinates.iter() {
                let half = live.div_ceil(2);
                let mut i = 0;
                while i < half {
                    let a = claims[chunk_start + 2 * i];
                    let mut t = if 2 * i + 1 < live {
                        claims[chunk_start + 2 * i + 1]
                    } else {
                        E::ZERO
                    };
                    t.sub_assign(&a);
                    t.mul_assign(r);
                    t.add_assign(&a);
                    claims[chunk_start + i] = t;
                    i += 1;
                }
                live = half;
            }
            debug_assert_eq!(live, 1);
            // `out_off <= chunk_start`: outputs never overtake unread input.
            claims[out_off] = claims[chunk_start];
            out_off += 1;
            remaining -= chunk_len;
            chunk_start += pack;
        }
        in_off += len;
    }
    out_off
}

#[cfg(test)]
mod merge_packed_claims_tests {
    use super::merge_packed_claims;
    use field::baby_bear::base::BabyBearField;
    use field::baby_bear::ext4::BabyBearExt4;
    use field::{Field, FieldExtension, PrimeField};

    /// Reference: the prover's `merge_claims` (allocating, per set).
    fn reference_merge<F: Field>(input: &[F], extra_coordinates: &[F]) -> Vec<F> {
        let pack_log2 = extra_coordinates.len();
        let mut result = vec![];
        for chunk in input.chunks(1 << pack_log2) {
            let mut input = chunk.to_vec();
            input.resize(1 << pack_log2, F::ZERO);
            let mut buffer = vec![];
            for merge_point in extra_coordinates.iter() {
                for pair in input.chunks(2) {
                    let (a, b) = (pair[0], pair[1]);
                    let mut t = b;
                    t.sub_assign(&a);
                    t.mul_assign(merge_point);
                    t.add_assign(&a);
                    buffer.push(t);
                }
                core::mem::swap(&mut input, &mut buffer);
                buffer.clear();
            }
            assert_eq!(input.len(), 1);
            result.push(input[0]);
        }
        result
    }

    fn pseudo_random_el(state: &mut u64) -> BabyBearExt4 {
        let mut coeffs = [BabyBearField::ZERO; 4];
        for c in coeffs.iter_mut() {
            // xorshift64*
            *state ^= *state >> 12;
            *state ^= *state << 25;
            *state ^= *state >> 27;
            let word = (state.wrapping_mul(0x2545F4914F6CDD1D) >> 32) as u32;
            *c = BabyBearField::from_raw_repr_with_reduction(word);
        }
        <BabyBearExt4 as FieldExtension<BabyBearField>>::from_coeffs(coeffs)
    }

    #[test]
    fn matches_prover_merge_claims_per_set() {
        let mut state = 0x9E3779B97F4A7C15u64;
        for pack_log2 in 0..4usize {
            let pack = 1usize << pack_log2;
            for set_lens in [
                [0usize, 0, 0],
                [1, 0, 0],
                [pack, pack, pack],
                [pack + 1, 0, 1],
                [3 * pack - 1, pack - 1 + 1, 2],
                [7, 0, 5],
                [13, 11, 4],
                [40, 0, 17],
            ] {
                let extra: Vec<BabyBearExt4> = (0..pack_log2)
                    .map(|_| pseudo_random_el(&mut state))
                    .collect();
                let total: usize = set_lens.iter().sum();
                // trailing entries (virtual setup etc.) must survive untouched
                let tail = 3;
                let input: Vec<BabyBearExt4> = (0..total + tail)
                    .map(|_| pseudo_random_el(&mut state))
                    .collect();

                let mut expected = Vec::new();
                let mut off = 0;
                for &len in &set_lens {
                    let set = &input[off..off + len];
                    // the prover's own merge is the source of truth
                    let from_prover = prover::gkr::prover::merge_claims(set, &extra);
                    assert_eq!(from_prover, reference_merge(set, &extra));
                    expected.extend(from_prover);
                    off += len;
                }

                let mut claims = input.clone();
                let merged = merge_packed_claims(&mut claims, &set_lens, &extra);
                assert_eq!(
                    merged,
                    set_lens.iter().map(|l| l.div_ceil(pack)).sum::<usize>()
                );
                assert_eq!(
                    &claims[..merged],
                    &expected[..],
                    "pack_log2 {pack_log2}, sets {set_lens:?}"
                );
                assert_eq!(&claims[total..], &input[total..]);
            }
        }
    }
}
