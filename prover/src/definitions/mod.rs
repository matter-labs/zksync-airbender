use ::cs::definitions::*;
use ::field::*;
use transcript::Blake2sTranscript;

fn split_u32_into_pair_u16(num: u32) -> (u32, u32) {
    let high_word = num >> 16;
    let low_word = num & core::hint::black_box(0x0000ffff);
    (low_word, high_word)
}

mod hash_like_holder;
mod leaf_inclusion_verifier;
mod optimal_folding;
pub mod sumcheck_kernel;

pub const DEFAULT_LDE_FACTOR: usize = 2;
pub const DEFAULT_CAP_SIZE: usize = 16;
pub const DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2: usize = 4;

use cs::definitions::gkr::AddressSpaceType;

pub use self::hash_like_holder::*;
pub use self::leaf_inclusion_verifier::*;
pub use self::optimal_folding::*;

pub type Transcript = Blake2sTranscript;

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
    #[cfg(feature = "prover")]
    pub fn flatten_into_buffer(&self, dst: &mut Vec<u32>)
    where
        [(); E::DEGREE]: Sized,
    {
        use crate::gkr::prover::transcript_utils::flatten_field_els_into;
        flatten_field_els_into(&self.permutation_argument_linearization_challenges, dst);
        flatten_field_els_into(&[self.permutation_argument_additive_part], dst);
    }

    #[inline(always)]
    pub fn flatten_into_fixed_size_buffer_dst<const N: usize>(&self, dst: &mut [u32; N])
    where
        [(); E::DEGREE]: Sized,
    {
        assert_eq!(
            N,
            E::DEGREE * (NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES + 1)
        );
        unsafe {
            let mut it = dst.as_chunks_unchecked_mut::<{ E::DEGREE }>().iter_mut();
            for src in self.permutation_argument_linearization_challenges.iter() {
                *it.next().unwrap_unchecked() = E::into_coeffs(*src)
                    .into_array::<{ E::DEGREE }>()
                    .map(|el: F| el.as_u32_raw_repr_reduced());
            }
            *it.next().unwrap_unchecked() = E::into_coeffs(self.permutation_argument_additive_part)
                .into_array::<{ E::DEGREE }>()
                .map(|el: F| el.as_u32_raw_repr_reduced());
        }
    }

    #[inline(always)]
    pub fn flatten_into_fixed_size_buffer<const N: usize>(&self) -> [u32; N]
    where
        [(); E::DEGREE]: Sized,
    {
        unsafe {
            #[allow(invalid_value)]
            let mut dst = [const { MaybeUninit::uninit().assume_init() }; N];
            use core::mem::MaybeUninit;
            self.flatten_into_fixed_size_buffer_dst(&mut dst);
            dst
        }
    }

    pub fn draw_from_transcript_seed(
        mut seed: transcript::Seed,
        pow_bits: usize,
        pow_challenge: u64,
    ) -> Self
    where
        [(); ((NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES + 1) * E::DEGREE + 1)
            .next_multiple_of(blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS)]:,
        [(); ((NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES + 1) * E::DEGREE)
            .next_multiple_of(blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS)]:,
        [(); E::DEGREE]:,
    {
        if pow_bits > 0 {
            Transcript::verify_pow(&mut seed, pow_challenge, pow_bits as u32);
        }

        use crate::utils::*;
        use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;

        unsafe {
            if pow_bits > 0 {
                let mut transcript_challenges = [0u32;
                    ((NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES + 1) * E::DEGREE + 1)
                        .next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS)];
                Transcript::draw_randomness(&mut seed, &mut transcript_challenges);

                let mut it = transcript_challenges[1..]
                    .as_chunks::<{ E::DEGREE }>()
                    .0
                    .iter();
                let permutation_argument_linearization_challenges: [E;
                    NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES] =
                    core::array::from_fn(|_| {
                        extension_field_from_base_coeffs(
                            it.next()
                                .unwrap_unchecked()
                                .map(|el| F::from_raw_repr_with_reduction(el)),
                        )
                    });
                let permutation_argument_additive_part: E =
                    extension_field_from_base_coeffs::<F, E>({
                        let t = *it.next().unwrap_unchecked();
                        let t: [F; E::DEGREE] = t.map(|el| F::from_raw_repr_with_reduction(el));
                        t
                    });

                Self {
                    permutation_argument_linearization_challenges,
                    permutation_argument_additive_part,
                    _marker: core::marker::PhantomData,
                }
            } else {
                let mut transcript_challenges = [0u32;
                    ((NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES + 1) * E::DEGREE)
                        .next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS)];
                Transcript::draw_randomness(&mut seed, &mut transcript_challenges);

                let mut it = transcript_challenges[1..]
                    .as_chunks::<{ E::DEGREE }>()
                    .0
                    .iter();
                let permutation_argument_linearization_challenges: [E;
                    NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES] =
                    core::array::from_fn(|_| {
                        extension_field_from_base_coeffs(
                            it.next()
                                .unwrap_unchecked()
                                .map(|el| F::from_raw_repr_with_reduction(el)),
                        )
                    });
                let permutation_argument_additive_part: E =
                    extension_field_from_base_coeffs::<F, E>({
                        let t = *it.next().unwrap_unchecked();
                        let t: [F; E::DEGREE] = t.map(|el| F::from_raw_repr_with_reduction(el));
                        t
                    });

                Self {
                    permutation_argument_linearization_challenges,
                    permutation_argument_additive_part,
                    _marker: core::marker::PhantomData,
                }
            }
        }
    }
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
        t.mul_assign_by_base(&F::from_u32_unchecked(timestamp_low));
        contribution.add_assign(&t);

        let mut t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        t.mul_assign_by_base(&F::from_u32_unchecked(timestamp_high));
        contribution.add_assign(&t);

        let mut t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        t.mul_assign_by_base(&F::from_u32_unchecked(value_low as u32));
        contribution.add_assign(&t);

        let mut t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        t.mul_assign_by_base(&F::from_u32_unchecked(value_high as u32));
        contribution.add_assign(&t);

        contribution.add_assign(&external_challenges.permutation_argument_additive_part);
        read_set_contribution.mul_assign(&contribution);
    }

    for (dst, (pc, (ts_low, ts_high))) in [&mut write_set_contribution, &mut read_set_contribution]
        .into_iter()
        .zip([(initial_pc, initial_timestamp), (final_pc, final_timestamp)].into_iter())
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
        t.mul_assign_by_base(&F::from_u32_unchecked(ts_low));
        contribution.add_assign(&t);
        // timestamp high
        let mut t = external_challenges.permutation_argument_linearization_challenges
            [MACHINE_STATE_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        t.mul_assign_by_base(&F::from_u32_unchecked(ts_high));
        contribution.add_assign(&t);
        // additive term
        contribution.add_assign(&external_challenges.permutation_argument_additive_part);
        dst.mul_assign(&contribution);
    }

    let mut result = write_set_contribution;
    result.mul_assign(&read_set_contribution.inverse().unwrap());

    result
}
