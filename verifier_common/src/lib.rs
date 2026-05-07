#![cfg_attr(not(any(test, feature = "replace_csr")), no_std)]
#![cfg_attr(any(test, feature = "proof_utils"), allow(incomplete_features))]
#![cfg_attr(any(test, feature = "proof_utils"), feature(generic_const_exprs))]

#[macro_export]
macro_rules! gkr_circuits {
    ($callback:ident) => {
        $callback! {
            add_sub_lui_auipc_mop; 24 ; "_preprocessed_layout",
            jump_branch_slt; 24 ; "_preprocessed_layout",
            shift_binop; 24 ; "_preprocessed_layout",
            mem_word_only; 24 ; "_preprocessed_layout",
            mem_subword_only; 24 ; "_preprocessed_layout",
            bigint_with_extended_control; 22 ; "_layout",
            blake2_with_extended_control; 20 ; "_layout",
            keccak_special5; 22 ; "_layout",
            inits_and_teardowns; 24 ; "_preprocessed_layout",
        }
    };
}

/// GKR sumcheck polynomial is cubic
pub const SUMCHECK_POLY_COEFFS: usize = 4;
/// Dim-reducing layers use 4 evaluation points per address
pub const DIM_REDUCE_EVAL_POINTS: usize = 4;
/// Standard layers use 2 evaluation points per address (f(0) and f(1)).
pub const STANDARD_EVAL_POINTS: usize = 2;
/// One extra challenge for batching is drawn beyond the evaluation point challenges.
pub const BATCHING_CHALLENGE_EXTRA: usize = 1;

pub const fn transcript_challenge_array_size(num_elements: usize, pow_bits: usize) -> usize {
    if pow_bits > 0 {
        (num_elements + 1).next_multiple_of(blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS)
    } else {
        num_elements.next_multiple_of(blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS)
    }
}

// Stable reimpl of standard library
#[inline(always)]
pub const unsafe fn slice_from_ptr_range<'a, T>(range: core::ops::Range<*const T>) -> &'a [T] {
    unsafe { core::slice::from_raw_parts(range.start, range.end.offset_from(range.start) as usize) }
}

#[cfg(any(test, feature = "replace_csr", feature = "proof_utils"))]
extern crate alloc;

use crate::errors::ErrorCreator;
use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
use field::{Field, FieldExtension, PrimeField};
use non_determinism_source::NonDeterminismSource;

pub use blake2s_u32;
pub use cs;
pub use field;
pub use non_determinism_source;
pub use prover;
pub use transcript;
pub mod errors;
pub mod gkr;
pub mod structs;
#[cfg(feature = "proof_utils")]
pub mod test_circuits;
pub mod whir;

pub mod inline_ops;
pub mod lazy_vec;
pub mod no_inline_ops;

pub use self::gkr::{GKRVerifierOutput, InitialGKRTranscript};
pub use ::prover::definitions::{GKRExternalChallenges, USE_REDUCED_BLAKE2_ROUNDS};

/// Wrappers for common field operations used by the verifier.
/// We use inline operations when compiling to RISC-V to maximize performance,
/// but using inline operations on x86_64 causes the compile time to explode and requires
/// additional handling (e.g. creating profiles for certain packages) without providing
/// too much benefits, so on host platform we disable inlining.
pub mod field_ops {
    #[cfg(target_arch = "riscv32")]
    pub use crate::inline_ops::*;

    #[cfg(not(target_arch = "riscv32"))]
    pub use crate::no_inline_ops::*;
}

#[cfg(all(not(target_arch = "riscv32"), feature = "replace_csr"))]
pub type DefaultNonDeterminismSource = ::prover::nd_source_std::ThreadLocalBasedSource;

#[cfg(all(not(target_arch = "riscv32"), not(feature = "replace_csr")))]
pub type DefaultNonDeterminismSource = ();

#[cfg(target_arch = "riscv32")]
pub type DefaultNonDeterminismSource = non_determinism_source::CSRBasedSource;

#[cfg(not(all(
    target_arch = "riscv32",
    any(feature = "blake2_with_compression", feature = "blake2_g_function")
)))]
pub type DefaultLeafInclusionVerifier = ::prover::definitions::Blake2sForEverythingVerifier;

#[cfg(all(
    target_arch = "riscv32",
    any(feature = "blake2_with_compression", feature = "blake2_g_function")
))]
pub type DefaultLeafInclusionVerifier =
    ::prover::definitions::Blake2sForEverythingVerifierWithAlternativeCompression;

pub fn parse_field_els_as_u32_from_u16_limbs_checked(
    input: [::field::baby_bear::base::BabyBearField; 2],
) -> u32 {
    let [low, high] = input;
    let low = low.as_u32_reduced();
    let high = high.as_u32_reduced();
    assert!(low & core::hint::black_box(0xffff0000u32) == 0);
    assert!(high & core::hint::black_box(0xffff0000u32) == 0);

    low | (high << 16)
}

pub struct VerifierOutput<
    E: Field,
    const INIT_AND_TEARDOWN_SETS: usize,
    const CAP_SIZE: usize,
    const NUM_MEMORY_COMMITS: usize,
    const NUM_SETUP_COMMITS: usize,
> {
    pub inits_and_teardowns_top_bits: [u32; INIT_AND_TEARDOWN_SETS],
    pub memory_caps: [[[u32; BLAKE2S_DIGEST_SIZE_U32_WORDS]; CAP_SIZE]; NUM_MEMORY_COMMITS],
    pub grand_product_read_set_accumulator: E,
    pub grand_product_write_set_accumulator: E,
}

pub trait ConcreteVerifierImpl<
    F: PrimeField,
    EE: FieldExtension<F> + Field,
    const INIT_AND_TEARDOWN_SETS: usize,
    const EXTERNAL_CHALLENGES_FLATTENED_SIZE: usize,
    const CAP_SIZE: usize,
    const NUM_MEMORY_COMMITS: usize,
    const NUM_WITNESS_COMMITS: usize,
    const NUM_SETUP_COMMITS: usize,
    const PADDING_WORDS: usize,
    const ROUNDS: usize,
    const ADDRS: usize,
>: 'static
{
    fn verify_gkr<I: NonDeterminismSource, E: ErrorCreator>(
        external_challenges: &::prover::definitions::GKRExternalChallenges<F, EE>,
        initial_transcript: &InitialGKRTranscript<
            EE,
            INIT_AND_TEARDOWN_SETS,
            EXTERNAL_CHALLENGES_FLATTENED_SIZE,
            CAP_SIZE,
            NUM_MEMORY_COMMITS,
            NUM_WITNESS_COMMITS,
            NUM_SETUP_COMMITS,
            PADDING_WORDS,
        >,
        transcript_state: &mut ::transcript::TranscriptState,
    ) -> Result<GKRVerifierOutput<'static, EE, ROUNDS, ADDRS>, E::Error>;
    fn verify_whir<I: NonDeterminismSource, E: ErrorCreator>(
        initial_transcript: &InitialGKRTranscript<
            EE,
            INIT_AND_TEARDOWN_SETS,
            EXTERNAL_CHALLENGES_FLATTENED_SIZE,
            CAP_SIZE,
            NUM_MEMORY_COMMITS,
            NUM_WITNESS_COMMITS,
            NUM_SETUP_COMMITS,
            PADDING_WORDS,
        >,
        transcript_state: &mut transcript::TranscriptState,
        whir_batching_challenge: EE,
        base_layer_claims: &[EE],
        initial_claim_point: &[EE],
    ) -> Result<(), E::Error>;
}

pub fn verify_impl<
    I: NonDeterminismSource,
    E: ErrorCreator,
    F: PrimeField,
    EE: FieldExtension<F> + Field,
    const INIT_AND_TEARDOWN_SETS: usize,
    const EXTERNAL_CHALLENGES_FLATTENED_SIZE: usize,
    const CAP_SIZE: usize,
    const NUM_MEMORY_COMMITS: usize,
    const NUM_WITNESS_COMMITS: usize,
    const NUM_SETUP_COMMITS: usize,
    const PADDING_WORDS: usize,
    const ROUNDS: usize,
    const ADDRS: usize,
    V: ConcreteVerifierImpl<
        F,
        EE,
        INIT_AND_TEARDOWN_SETS,
        EXTERNAL_CHALLENGES_FLATTENED_SIZE,
        CAP_SIZE,
        NUM_MEMORY_COMMITS,
        NUM_WITNESS_COMMITS,
        NUM_SETUP_COMMITS,
        PADDING_WORDS,
        ROUNDS,
        ADDRS,
    >,
>(
    external_challenges: &prover::definitions::GKRExternalChallenges<F, EE>,
) -> Result<
    VerifierOutput<EE, INIT_AND_TEARDOWN_SETS, CAP_SIZE, NUM_MEMORY_COMMITS, NUM_SETUP_COMMITS>,
    E::Error,
> {
    use crate::gkr::make_initial_transcript;
    let (initial_transcript_values, mut ts) = make_initial_transcript::<
        F,
        EE,
        I,
        INIT_AND_TEARDOWN_SETS,
        EXTERNAL_CHALLENGES_FLATTENED_SIZE,
        CAP_SIZE,
        NUM_MEMORY_COMMITS,
        NUM_WITNESS_COMMITS,
        NUM_SETUP_COMMITS,
        PADDING_WORDS,
    >(external_challenges);
    let gkr_output =
        V::verify_gkr::<I, E>(external_challenges, &initial_transcript_values, &mut ts)?;
    let _ = V::verify_whir::<I, E>(
        &initial_transcript_values,
        &mut ts,
        gkr_output.whir_batching_challenge,
        gkr_output.base_layer_claims.as_slice(),
        &gkr_output.evaluation_point[..gkr_output.evaluation_point_len],
    )?;

    Ok(VerifierOutput {
        inits_and_teardowns_top_bits: initial_transcript_values.inits_and_teardowns_top_bits,
        memory_caps: initial_transcript_values.memory_caps,
        grand_product_read_set_accumulator: gkr_output.permutation_read_product,
        grand_product_write_set_accumulator: gkr_output.permutation_write_product,
    })
}

pub fn read_external_challenges<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    I: NonDeterminismSource,
>() -> prover::definitions::GKRExternalChallenges<F, E> {
    use crate::structs::ext_from_nds;
    use cs::definitions::NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES;

    let permutation_argument_linearization_challenges: [E;
        NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES] =
        core::array::from_fn(|_| ext_from_nds::<F, E, I>());
    let permutation_argument_additive_part: E = ext_from_nds::<F, E, I>();

    prover::definitions::GKRExternalChallenges {
        permutation_argument_linearization_challenges,
        permutation_argument_additive_part,
        _marker: core::marker::PhantomData,
    }
}
