#![cfg_attr(not(any(test, feature = "replace_csr")), no_std)]
#![cfg_attr(any(test, feature = "proof_utils"), allow(incomplete_features))]
#![cfg_attr(any(test, feature = "proof_utils"), feature(generic_const_exprs))]

#[macro_export]
macro_rules! gkr_circuits {
    ($callback:ident) => {
        $callback! {
            add_sub_lui_auipc_mop; 24 ; "_layout",
            jump_branch_slt; 24 ; "_layout",
            shift_binop; 24 ; "_layout",
            unsigned_mul_div; 24 ; "_layout",
            mem_word_only; 24 ; "_layout",
            mem_subword_only; 24 ; "_layout",
            bigint_with_extended_control; 22 ; "_layout",
            blake2_with_extended_control; 20 ; "_layout",
            keccak_special5; 22 ; "_layout",
            blake2_g_function; 22 ; "_layout",
            inits_and_teardowns; 24 ; "_layout",
            unified_reduced_machine; 24 ; "_layout",
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

/// log2 of `BabyBearExt4` field size.
/// `|F| = ORDER^4` with `ORDER = 0x7800_0001 = 2^31 - 2^27 + 1 ≈ 2^30.907`, so
/// `log2 |F| ≈ 123.63`. We floor it: using a *lower* bound on `|F|` gives an *upper*
/// bound on the Schwartz–Zippel collision probability `degree / |F|`, i.e. the
/// soundness-conservative rounding direction.
pub const BABYBEAR_EXT4_SIZE_LOG2: usize = 123;

/// Permutation elements contributed per cycle: 1 machine-state + 3 memory accesses = 4 = `2^2`.
const PERMUTATION_ELEMENTS_PER_CYCLE_LOG2: usize = 2;

/// Delegation-capacity headroom. These `+2` bits set the ceiling to 4x the main-circuit worst
/// case (`2^38 -> 2^40`) — this is the *ceiling* multiplier, NOT 4x headroom for delegations
/// (the net room above a maxed main circuit is ~3x). The number of delegation circuit instances
/// is bounded at runtime ONLY by [`MAX_PERMUTATION_ELEMENTS_LOG2`] (no compile-time cap); since
/// each delegation circuit contributes only ~`2^25`–`2^26` permutation terms, this is far above
/// any realistic program (delegations are negligible next to the `2^38` main worst case). A
/// *policy* choice, deliberately conservative: it bites ONLY at security_100 (it inflates the
/// auto-derived PoW by 1 bit per extra bit here); at security_80 the base soundness already
/// exceeds 80 for any ceiling `<= 2^41`, so this value is behaviourally moot there.
const DELEGATION_HEADROOM_LOG2: usize = 2;

/// log2 ceiling on the total number of permutation-argument elements that share the
/// memory/delegation external (linearization) challenges. The shared argument is ONE global
/// multiset/grand-product equality over the union of all circuits' accesses, so its
/// Schwartz–Zippel degree is this total element count.
///
/// Derived (not a magic number): main circuits contribute at most `MAX_NUMBER_OF_CYCLES * 4`
/// elements, where `MAX_NUMBER_OF_CYCLES = 2^36` comes from the RAM timestamp layout exactly as
/// `full_statement_verifier::MAX_CYCLES` computes it; the delegation headroom adds the policy
/// margin. Currently `36 + 2 + 2 = 40`.
///
/// The coupling is structural, not by convention: BOTH the runtime assert in
/// `full_statement_verifier::unrolled_proof_statement` AND the PoW derivation
/// ([`memory_delegation_pow_bits`]) read this one constant, so they cannot drift — changing the
/// cycle layout re-derives the PoW automatically. The `derivation_matches_expected_values`
/// self-check pins the resulting value/base soundness as a tripwire: a layout change that moves
/// it fails the test and forces a deliberate PoW-soundness re-review.
pub const MAX_PERMUTATION_ELEMENTS_LOG2: usize = {
    // Mirror full_statement_verifier::MAX_CYCLES: MAX_NUMBER_OF_CYCLES is
    // `1 << (TIMESTAMP_COLUMNS_NUM_BITS * NUM_TIMESTAMP_COLUMNS_FOR_RAM - NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP)`.
    let max_cycles_log2 = (cs::definitions::TIMESTAMP_COLUMNS_NUM_BITS as usize
        * cs::definitions::NUM_TIMESTAMP_COLUMNS_FOR_RAM)
        - cs::definitions::NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP as usize;
    max_cycles_log2 + PERMUTATION_ELEMENTS_PER_CYCLE_LOG2 + DELEGATION_HEADROOM_LOG2
};

/// Schwartz–Zippel base soundness (in bits) of the shared memory/delegation permutation
/// argument *before* any proof-of-work. The `- 2` (factor 4) is a conservative
/// cushion for the linearization coupling multiple key components plus the read/write
/// two-sidedness of the grand product.
const fn permutation_argument_base_security_bits(
    field_size_log2: usize,
    max_elements_log2: usize,
) -> usize {
    field_size_log2 - max_elements_log2 - 2
}

/// Generic PoW derivation: grinding bits required to lift the permutation-argument base
/// soundness up to `security_bits`: `max(0, security_bits - base)`
const fn pow_bits_for_target_security(
    security_bits: usize,
    field_size_log2: usize,
    max_elements_log2: usize,
) -> usize {
    let base = permutation_argument_base_security_bits(field_size_log2, max_elements_log2);
    // == max(0, security_bits - base)
    security_bits.saturating_sub(base)
}

pub const fn memory_delegation_pow_bits(level: ::prover::definitions::SecurityLevel) -> usize {
    use ::prover::definitions::SecurityLevel;
    let security_bits = match level {
        SecurityLevel::Sec80 => 80,
        SecurityLevel::Sec100 => 100,
    };
    pow_bits_for_target_security(
        security_bits,
        BABYBEAR_EXT4_SIZE_LOG2,
        MAX_PERMUTATION_ELEMENTS_LOG2,
    )
}

#[cfg(feature = "security_100")]
pub const MEMORY_DELEGATION_POW_BITS: usize =
    memory_delegation_pow_bits(::prover::definitions::SecurityLevel::Sec100);
#[cfg(not(feature = "security_100"))]
pub const MEMORY_DELEGATION_POW_BITS: usize =
    memory_delegation_pow_bits(::prover::definitions::SecurityLevel::Sec80);

#[cfg(test)]
mod memory_delegation_pow_tests {
    use super::*;
    use ::prover::definitions::SecurityLevel;

    #[test]
    fn derivation_matches_expected_values() {
        // Tripwire: the derived ceiling is currently 40 (cycles 2^36 * 4 + 4x delegation
        // headroom). If the RAM timestamp layout changes this, re-review the PoW soundness
        // before updating these expectations.
        assert_eq!(MAX_PERMUTATION_ELEMENTS_LOG2, 40);
        // base = 123 - 40 - 2 = 81
        assert_eq!(
            permutation_argument_base_security_bits(
                BABYBEAR_EXT4_SIZE_LOG2,
                MAX_PERMUTATION_ELEMENTS_LOG2
            ),
            81
        );
        // 80-bit target is already met without PoW; 100-bit needs 19.
        assert_eq!(memory_delegation_pow_bits(SecurityLevel::Sec80), 0);
        assert_eq!(memory_delegation_pow_bits(SecurityLevel::Sec100), 19);
    }

    #[test]
    fn active_constant_matches_selected_security_level() {
        #[cfg(feature = "security_100")]
        assert_eq!(MEMORY_DELEGATION_POW_BITS, 19);
        #[cfg(not(feature = "security_100"))]
        assert_eq!(MEMORY_DELEGATION_POW_BITS, 0);
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
use prover::definitions::MerkleTreeCap;

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
#[cfg(feature = "verifier_stats")]
pub mod stats;

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
    pub setup_caps: [[[u32; BLAKE2S_DIGEST_SIZE_U32_WORDS]; CAP_SIZE]; NUM_SETUP_COMMITS],
    pub grand_product_read_set_accumulator: E,
    pub grand_product_write_set_accumulator: E,
}

impl<
        E: Field,
        const INIT_AND_TEARDOWN_SETS: usize,
        const CAP_SIZE: usize,
        const NUM_SETUP_COMMITS: usize,
    > VerifierOutput<E, INIT_AND_TEARDOWN_SETS, CAP_SIZE, 1, NUM_SETUP_COMMITS>
{
    pub fn memory_caps_flattened(&'_ self) -> &'_ [u32] {
        unsafe {
            slice_from_ptr_range(
                self.memory_caps.as_ptr_range().start.cast::<u32>()
                    ..self.memory_caps.as_ptr_range().end.cast::<u32>(),
            )
        }
    }
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
        nd_source: &mut I,
    ) -> Result<GKRVerifierOutput<EE, ROUNDS, ADDRS>, E::Error>;
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
        nd_source: &mut I,
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
    nd_source: &mut I,
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
    >(external_challenges, nd_source);
    let gkr_output = V::verify_gkr::<I, E>(
        external_challenges,
        &initial_transcript_values,
        &mut ts,
        nd_source,
    )?;
    V::verify_whir::<I, E>(
        &initial_transcript_values,
        &mut ts,
        gkr_output.whir_batching_challenge,
        gkr_output.base_layer_claims.as_slice(),
        &gkr_output.evaluation_point[..gkr_output.evaluation_point_len],
        nd_source,
    )?;

    Ok(VerifierOutput {
        inits_and_teardowns_top_bits: initial_transcript_values.inits_and_teardowns_top_bits,
        memory_caps: initial_transcript_values.memory_caps,
        setup_caps: initial_transcript_values.setup_caps,
        grand_product_read_set_accumulator: gkr_output.permutation_read_product,
        grand_product_write_set_accumulator: gkr_output.permutation_write_product,
    })
}

pub fn read_external_challenges<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    I: NonDeterminismSource,
>(
    nd_source: &mut I,
) -> prover::definitions::GKRExternalChallenges<F, E> {
    use crate::structs::ext_from_nds;
    use cs::definitions::NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES;

    let permutation_argument_linearization_challenges: [E;
        NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES] =
        core::array::from_fn(|_| ext_from_nds::<F, E, I>(nd_source));
    let permutation_argument_additive_part: E = ext_from_nds::<F, E, I>(nd_source);

    prover::definitions::GKRExternalChallenges {
        permutation_argument_linearization_challenges,
        permutation_argument_additive_part,
        _marker: core::marker::PhantomData,
    }
}

pub struct DelegationCircuitSetupData<const N: usize> {
    pub delegation_type: u32,
    pub num_permutation_terms_per_circuit: u32,
    pub setup_cap: MerkleTreeCap<N>,
}

#[cfg(feature = "proof_utils")]
impl<const N: usize> quote::ToTokens for DelegationCircuitSetupData<N> {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        use quote::quote;

        let DelegationCircuitSetupData {
            delegation_type,
            num_permutation_terms_per_circuit,
            setup_cap,
        } = self;

        let t = quote! {
            DelegationCircuitSetupData {
                delegation_type: #delegation_type,
                num_permutation_terms_per_circuit: #num_permutation_terms_per_circuit,
                setup_cap: #setup_cap,
            }
        };

        tokens.extend(t);
    }
}
