use ::cs::definitions::*;
use ::field::*;
use transcript::Blake2sTranscript;

// pub const USE_REDUCED_BLAKE2_ROUNDS: bool = false;
pub const USE_REDUCED_BLAKE2_ROUNDS: bool = true;

fn split_u32_into_pair_u16(num: u32) -> (u32, u32) {
    let high_word = num >> 16;
    let low_word = num & core::hint::black_box(0x0000ffff);
    (low_word, high_word)
}

mod hash_like_holder;
mod leaf_inclusion_verifier;
mod optimal_folding;
pub mod sumcheck_kernel;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct FinalRegisterValue {
    pub value: u32,
    pub last_access_timestamp: TimestampScalar,
}

pub const DEFAULT_LDE_FACTOR: usize = 2;
pub const DEFAULT_CAP_SIZE: usize = 16;
pub const DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2: usize = 4;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
#[repr(usize)]
pub enum SecurityLevel {
    Sec100 = 0,
}

impl SecurityLevel {
    pub const ALL: &'static [SecurityLevel] = &[SecurityLevel::Sec100];

    pub fn dir_suffix(self) -> &'static str {
        match self {
            SecurityLevel::Sec100 => "sec_100",
        }
    }

    pub const fn security_bits(self) -> usize {
        match self {
            SecurityLevel::Sec100 => 100,
        }
    }
}

/// Which soundness accounting a default prover configuration is computed under
/// (`prover_config::example_configs`). Lives next to [`SecurityLevel`] so that
/// `no_std` verifier crates can name it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum SoundnessMode {
    /// The in-house capacity-conjecture accounting
    /// ([`PessimisticConjectureMode`](crate::gkr::whir::proximity_testing_modes::PessimisticConjectureMode):
    /// one query at rate `ρ` is worth `log2(1/ρ)` bits, plus 20 % extra
    /// queries; no folding-challenge or OOD proof of work): the production
    /// ladders of `example_configs::pessimistic_conjecture`.
    PessimisticConjecture,
    /// Schedules certified at the security level by `ethereum/soundcalc`
    /// (commit `2af5e7d`, 2026-09-21): a unique-decoding base round, Johnson
    /// bound later rounds with an explicit multiplicity, a proof of work on
    /// every folding challenge and on the single OOD sample of every oracle.
    /// See `example_configs::ethproofs_soundcalc`.
    EthproofsSoundnessCalc,
}

impl SoundnessMode {
    pub const ALL: &'static [SoundnessMode] = &[
        SoundnessMode::PessimisticConjecture,
        SoundnessMode::EthproofsSoundnessCalc,
    ];

    /// The mode of the configs proved and verified by default (every tracked
    /// proof / verifier fixture).
    pub const DEFAULT: SoundnessMode = SoundnessMode::PessimisticConjecture;

    /// Suffix of the serialized config files
    /// (`generated/prover_config_<level>_<suffix>.json`).
    pub fn file_suffix(self) -> &'static str {
        match self {
            SoundnessMode::PessimisticConjecture => "pessimistic_conjecture",
            SoundnessMode::EthproofsSoundnessCalc => "ethproofs_soundcalc",
        }
    }
}

/// The blake2s implementation a verifier program is built with: what a
/// Merkle compression costs it, and so which proof layouts pay off. Lives
/// here so the prover-side config (`WhirSchedule`), the verifier generator
/// and the proof flattener agree on one policy; `verifier_common::BLAKE_MODE`
/// is the mode of the build at hand.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum BlakeMode {
    /// The whole compression is one delegation call
    /// (`blake2_with_compression`): a Merkle level costs the main machine
    /// little more than reading its sibling.
    Compression,
    /// The mixing function is delegated (`blake2_g_function`): one call per
    /// G function, the rest of the compression on the main machine.
    GFunction,
    /// The compression runs on the main machine with the special blake
    /// opcodes (`special_opcodes_extension`): hundreds of cycles each.
    BlakeSpecialOpcodes,
    /// The plain software compression: a RISC-V build without any blake
    /// feature (`mop_extension`), or every native (host) build.
    Software,
}

impl BlakeMode {
    pub const ALL: &'static [BlakeMode] = &[
        BlakeMode::Compression,
        BlakeMode::GFunction,
        BlakeMode::BlakeSpecialOpcodes,
        BlakeMode::Software,
    ];

    #[must_use]
    pub const fn tag(self) -> &'static str {
        match self {
            Self::Compression => "blake2_with_compression",
            Self::GFunction => "blake2_g_function",
            Self::BlakeSpecialOpcodes => "special_opcodes_extension",
            Self::Software => "software",
        }
    }

    #[must_use]
    pub fn parse(s: &str) -> Option<Self> {
        match s {
            "blake2_with_compression" | "compression" | "round" => Some(Self::Compression),
            "blake2_g_function" | "g_function" => Some(Self::GFunction),
            "special_opcodes_extension" | "special_opcodes" | "spec" => {
                Some(Self::BlakeSpecialOpcodes)
            }
            "software" | "mop_extension" | "baseline" => Some(Self::Software),
            _ => None,
        }
    }

    /// Whether a compression is expensive enough on the main machine that
    /// hashing fewer Merkle nodes beats the bookkeeping of a pruned
    /// multiproof (measured on add/sub: a wash with the delegated
    /// compression, -10% of the verifier with the special opcodes).
    #[must_use]
    pub const fn merkle_compressions_are_expensive(self) -> bool {
        match self {
            Self::Compression => false,
            Self::GFunction | Self::BlakeSpecialOpcodes | Self::Software => true,
        }
    }

    /// Whether a WHIR round that opens `num_queries` leaves of trees capped
    /// at `cap_size` nodes is proved and verified as a pruned Merkle
    /// multiproof under this blake implementation: only when the
    /// compressions are expensive, and only when the round draws at least
    /// twice as many queries as the cap has nodes (below that the shared
    /// ancestors are too few to pay for the walk's bookkeeping). The one
    /// policy `WhirSchedule::merkle_multiproof_for_round`, the generated
    /// verifiers (at compile time, for `verifier_common::BLAKE_MODE`) and
    /// the proof flattener follow.
    #[must_use]
    pub const fn merkle_multiproofs(self, num_queries: usize, cap_size: usize) -> bool {
        self.merkle_compressions_are_expensive() && num_queries >= 2 * cap_size
    }
}

use cs::definitions::gkr::AddressSpaceType;

pub use self::hash_like_holder::*;
pub use self::leaf_inclusion_verifier::*;
pub use self::optimal_folding::*;

#[derive(
    Clone, Copy, Debug, Hash, Default, serde::Serialize, serde::Deserialize, PartialEq, Eq,
)]
#[repr(C)]
pub struct GKRExternalChallenges<F: PrimeField, E: FieldExtension<F> + Field> {
    pub permutation_argument_linearization_challenges:
        [E; NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES],
    pub permutation_argument_additive_part: E,
    pub _marker: core::marker::PhantomData<F>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> GKRExternalChallenges<F, E> {
    pub const TOTAL_CHALLENGES: usize = NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES + 1;

    #[cfg(feature = "prover")]
    pub fn from_slice(challenges: &[E]) -> Self {
        assert_eq!(
            challenges.len(),
            NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES + 1
        );
        let (permutation_argument_linearization_challenges, permutation_argument_additive_part) =
            challenges.as_chunks::<NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES>();
        let permutation_argument_linearization_challenges =
            permutation_argument_linearization_challenges[0];
        let permutation_argument_additive_part = permutation_argument_additive_part[0];

        Self {
            permutation_argument_linearization_challenges,
            permutation_argument_additive_part,
            _marker: core::marker::PhantomData,
        }
    }

    #[cfg(feature = "prover")]
    pub fn flatten_into_buffer(&self, dst: &mut Vec<u32>) {
        use crate::gkr::prover::transcript_utils::flatten_field_els_into;
        flatten_field_els_into(&self.permutation_argument_linearization_challenges, dst);
        flatten_field_els_into(&[self.permutation_argument_additive_part], dst);
    }

    #[cfg(feature = "prover")]
    #[inline(always)]
    pub fn flatten_into_fixed_size_buffer_dst<const N: usize>(&self, dst: &mut [u32; N]) {
        assert_eq!(
            N,
            E::DEGREE * (NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES + 1)
        );
        let mut it = dst.chunks_exact_mut(E::DEGREE);
        for src in self
            .permutation_argument_linearization_challenges
            .iter()
            .chain(core::iter::once(&self.permutation_argument_additive_part))
        {
            let chunk = it.next().unwrap();
            for (dst, el) in chunk.iter_mut().zip(E::into_coeffs(*src).as_ref()) {
                *dst = el.as_u32_raw_repr_reduced();
            }
        }
    }

    #[inline(always)]
    pub fn flatten_into_fixed_size_buffer<const N: usize>(&self) -> [u32; N] {
        assert_eq!(
            N,
            E::DEGREE * (NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES + 1)
        );

        unsafe {
            let mut dst = [const { MaybeUninit::uninit() }; N];
            let mut i = 0;
            use core::mem::MaybeUninit;
            for src in self.permutation_argument_linearization_challenges.iter() {
                for src in src.into_coeffs().as_ref() {
                    dst[i].write(src.as_u32_raw_repr_reduced());
                    i += 1;
                }
            }
            for src in self
                .permutation_argument_additive_part
                .into_coeffs()
                .as_ref()
            {
                dst[i].write(src.as_u32_raw_repr_reduced());
                i += 1;
            }

            debug_assert_eq!(i, N);

            dst.map(|el| el.assume_init())
        }
    }

    pub fn draw_from_blake_transcript_seed(
        mut seed: transcript::Seed,
        pow_bits: usize,
        pow_challenge: u64,
    ) -> Self {
        let mut hasher = blake2s_u32::DelegatedBlake2sState::new();

        if pow_bits > 0 {
            Blake2sTranscript::<USE_REDUCED_BLAKE2_ROUNDS>::verify_pow_using_hasher(
                &mut hasher,
                &mut seed,
                pow_challenge,
                pow_bits as u32,
            );
        }
        hasher.reset();
        let mut transcript_state =
            transcript::TranscriptState::<USE_REDUCED_BLAKE2_ROUNDS>::from_hasher_and_seed(
                hasher, seed,
            );

        let mut it = transcript_state.iterator();
        if pow_bits > 0 {
            let _ = it.next().expect("PoW word");
        }

        let mut placeholder = E::ZERO.into_coeffs();

        let permutation_argument_linearization_challenges: [E;
            NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES] = core::array::from_fn(|_| {
            for i in 0..E::DEGREE {
                placeholder[i] =
                    F::from_raw_repr_with_reduction(it.next().expect("transcript word"));
            }
            E::from_coeffs_ref(&placeholder)
        });

        let permutation_argument_additive_part: E = {
            for i in 0..E::DEGREE {
                placeholder[i] =
                    F::from_raw_repr_with_reduction(it.next().expect("transcript word"));
            }
            E::from_coeffs(placeholder)
        };

        Self {
            permutation_argument_linearization_challenges,
            permutation_argument_additive_part,
            _marker: core::marker::PhantomData,
        }
    }
}

/// (value, timestamp) for registers
pub fn produce_initial_permutation_product_separate_contributions<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    register_final_data: &[(u32, (u32, u32)); NUM_REGISTERS],
    initial_pc: u32,
    initial_timestamp: (u32, u32),
    final_pc: u32,
    final_timestamp: (u32, u32),
    external_challenges: &GKRExternalChallenges<F, E>,
) -> (E, E) {
    let mut write_set_contribution = E::ONE;
    // all registers are write 0 at timestamp 0
    for reg_idx in 0..NUM_REGISTERS {
        let mut contribution =
            E::from_base(F::from_u32_unchecked(AddressSpaceType::Register as u32)); // without challenge
        let mut t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        t.mul_assign_by_base(&F::from_u32_unchecked(reg_idx as u32));
        contribution.add_assign(&t);
        contribution.add_assign(&external_challenges.permutation_argument_additive_part);
        write_set_contribution.mul_assign(&contribution);
    }

    let mut read_set_contribution = E::ONE;
    // all registers are write 0 at timestamp 0
    for (reg_idx, (value, timestamp)) in register_final_data.iter().enumerate() {
        let (value_low, value_high) = split_u32_into_pair_u16(*value);
        let (timestamp_low, timestamp_high) = *timestamp;

        let mut contribution =
            E::from_base(F::from_u32_unchecked(AddressSpaceType::Register as u32)); // without challenge
        let mut t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        t.mul_assign_by_base(&F::from_u32_unchecked(reg_idx as u32));
        contribution.add_assign(&t);

        let mut t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        t.mul_assign_by_base(&F::from_u32_with_reduction(timestamp_low));
        contribution.add_assign(&t);

        let mut t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        t.mul_assign_by_base(&F::from_u32_with_reduction(timestamp_high));
        contribution.add_assign(&t);

        let mut t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        t.mul_assign_by_base(&F::from_u32_unchecked(value_low));
        contribution.add_assign(&t);

        let mut t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        t.mul_assign_by_base(&F::from_u32_unchecked(value_high));
        contribution.add_assign(&t);

        contribution.add_assign(&external_challenges.permutation_argument_additive_part);
        read_set_contribution.mul_assign(&contribution);
    }

    for (dst, (pc, (ts_low, ts_high))) in [&mut write_set_contribution, &mut read_set_contribution]
        .into_iter()
        .zip([(initial_pc, initial_timestamp), (final_pc, final_timestamp)])
    {
        let (pc_low, pc_high) = split_u32_into_pair_u16(pc);

        // address space - PC
        let mut contribution = E::from_base(F::from_u32_unchecked(AddressSpaceType::PC as u32)); // without challenge

        // PC low
        let mut t = external_challenges.permutation_argument_linearization_challenges
            [MACHINE_STATE_CHALLENGE_POWERS_PC_LOW_IDX];
        t.mul_assign_by_base(&F::from_u32_unchecked(pc_low));
        contribution.add_assign(&t);
        // PC high
        let mut t = external_challenges.permutation_argument_linearization_challenges
            [MACHINE_STATE_CHALLENGE_POWERS_PC_HIGH_IDX];
        t.mul_assign_by_base(&F::from_u32_unchecked(pc_high));
        contribution.add_assign(&t);
        // timestamp low
        let mut t = external_challenges.permutation_argument_linearization_challenges
            [MACHINE_STATE_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        t.mul_assign_by_base(&F::from_u32_with_reduction(ts_low));
        contribution.add_assign(&t);
        // timestamp high
        let mut t = external_challenges.permutation_argument_linearization_challenges
            [MACHINE_STATE_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        t.mul_assign_by_base(&F::from_u32_with_reduction(ts_high));
        contribution.add_assign(&t);
        // additive term
        contribution.add_assign(&external_challenges.permutation_argument_additive_part);
        dst.mul_assign(&contribution);
    }

    (read_set_contribution, write_set_contribution)
}

/// (value, timestamp) for registers
pub fn produce_initial_permutation_product_contribution<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    register_final_data: &[(u32, (u32, u32)); NUM_REGISTERS],
    initial_pc: u32,
    initial_timestamp: (u32, u32),
    final_pc: u32,
    final_timestamp: (u32, u32),
    external_challenges: &GKRExternalChallenges<F, E>,
) -> E {
    let (read_set_contribution, write_set_contribution) =
        produce_initial_permutation_product_separate_contributions(
            register_final_data,
            initial_pc,
            initial_timestamp,
            final_pc,
            final_timestamp,
            external_challenges,
        );

    let mut result = write_set_contribution;
    result.mul_assign(&read_set_contribution.inverse().unwrap());

    result
}
