use ::cs::definitions::*;
use ::field::*;
use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
use transcript::{Blake2sTranscript, Seed};

mod hash_like_holder;
mod leaf_inclusion_verifier;
mod optimal_folding;

pub use self::hash_like_holder::*;
pub use self::leaf_inclusion_verifier::*;
pub use self::optimal_folding::*;

pub type Transcript = Blake2sTranscript;

#[derive(
    Clone, Copy, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize, Hash,
)]
#[repr(C)]
pub struct ExternalMemoryArgumentChallenges {
    // we skip "is register" here
    // #[serde(bound(
    //     deserialize = "[Mersenne31Quartic; NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES]: serde::Deserialize<'de>"
    // ))]
    // #[serde(bound(
    //     serialize = "[Mersenne31Quartic; NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES]: serde::Serialize"
    // ))]
    pub memory_argument_linearization_challenges:
        [Mersenne31Quartic; NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES],
    pub memory_argument_gamma: Mersenne31Quartic,
}

impl ExternalMemoryArgumentChallenges {
    pub fn flatten(&self) -> [u32; NUM_MEM_ARGUMENT_KEY_PARTS * 4] {
        // we must normalize
        let mut result = [0u32; NUM_MEM_ARGUMENT_KEY_PARTS * 4];
        let mut it = result.iter_mut();

        for el in self.memory_argument_linearization_challenges.iter() {
            let flattened = el
                .into_coeffs_in_base()
                .map(|el: Mersenne31Field| el.to_reduced_u32());
            for src in flattened.into_iter() {
                *it.next().unwrap() = src;
            }
        }

        let flattened = self
            .memory_argument_gamma
            .into_coeffs_in_base()
            .map(|el: Mersenne31Field| el.to_reduced_u32());
        for src in flattened.into_iter() {
            *it.next().unwrap() = src;
        }

        assert!(it.next().is_none());

        result
    }
}

#[derive(
    Clone, Copy, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize, Hash,
)]
#[repr(C)]
pub struct ExternalDelegationArgumentChallenges {
    // #[serde(bound(
    //     deserialize = "[Mersenne31Quartic; NUM_DELEGATION_ARGUMENT_LINEARIZATION_CHALLENGES]: serde::Deserialize<'de>"
    // ))]
    // #[serde(bound(
    //     serialize = "[Mersenne31Quartic; NUM_DELEGATION_ARGUMENT_LINEARIZATION_CHALLENGES]: serde::Serialize"
    // ))]
    pub delegation_argument_linearization_challenges:
        [Mersenne31Quartic; NUM_DELEGATION_ARGUMENT_LINEARIZATION_CHALLENGES],
    pub delegation_argument_gamma: Mersenne31Quartic,
}

impl ExternalDelegationArgumentChallenges {
    pub fn flatten(&self) -> [u32; NUM_DELEGATION_ARGUMENT_KEY_PARTS * 4] {
        // we must normalize
        let mut result = [0u32; NUM_DELEGATION_ARGUMENT_KEY_PARTS * 4];
        let mut it = result.iter_mut();

        for el in self.delegation_argument_linearization_challenges.iter() {
            let flattened = el
                .into_coeffs_in_base()
                .map(|el: Mersenne31Field| el.to_reduced_u32());
            for src in flattened.into_iter() {
                *it.next().unwrap() = src;
            }
        }

        let flattened = self
            .delegation_argument_gamma
            .into_coeffs_in_base()
            .map(|el: Mersenne31Field| el.to_reduced_u32());
        for src in flattened.into_iter() {
            *it.next().unwrap() = src;
        }

        assert!(it.next().is_none());

        result
    }
}

#[derive(
    Clone, Copy, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize, Hash,
)]
#[repr(C)]
pub struct ExternalMachineStateArgumentChallenges {
    pub linearization_challenges: [Mersenne31Quartic; NUM_MACHINE_STATE_LINEARIZATION_CHALLENGES],
    pub additive_term: Mersenne31Quartic,
}

impl ExternalMachineStateArgumentChallenges {
    pub fn flatten(&self) -> [u32; (NUM_MACHINE_STATE_LINEARIZATION_CHALLENGES + 1) * 4] {
        // we must normalize
        let mut result = [0u32; (NUM_MACHINE_STATE_LINEARIZATION_CHALLENGES + 1) * 4];
        let mut it = result.iter_mut();

        for el in self.linearization_challenges.iter() {
            let flattened = el
                .into_coeffs_in_base()
                .map(|el: Mersenne31Field| el.to_reduced_u32());
            for src in flattened.into_iter() {
                *it.next().unwrap() = src;
            }
        }

        let flattened = self
            .additive_term
            .into_coeffs_in_base()
            .map(|el: Mersenne31Field| el.to_reduced_u32());
        for src in flattened.into_iter() {
            *it.next().unwrap() = src;
        }

        assert!(it.next().is_none());

        result
    }
}

#[derive(
    Clone, Copy, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize, Hash,
)]
#[repr(C)]
pub struct ExternalMachineIntermediateStateArgumentChallenges {
    pub linearization_challenges:
        [Mersenne31Quartic; NUM_INTERMEDIATE_MACHINE_STATE_LINEARIZATION_CHALLENGES],
    pub additive_term: Mersenne31Quartic,
}

impl ExternalMachineIntermediateStateArgumentChallenges {
    pub fn flatten(&self) -> [u32; NUM_INTERMEDIATE_MACHINE_STATE_LINEARIZATION_CHALLENGES * 4] {
        // we must normalize
        let mut result = [0u32; NUM_INTERMEDIATE_MACHINE_STATE_LINEARIZATION_CHALLENGES * 4];
        let mut it = result.iter_mut();

        for el in self.linearization_challenges.iter() {
            let flattened = el
                .into_coeffs_in_base()
                .map(|el: Mersenne31Field| el.to_reduced_u32());
            for src in flattened.into_iter() {
                *it.next().unwrap() = src;
            }
        }

        let flattened = self
            .additive_term
            .into_coeffs_in_base()
            .map(|el: Mersenne31Field| el.to_reduced_u32());
        for src in flattened.into_iter() {
            *it.next().unwrap() = src;
        }

        assert!(it.next().is_none());

        result
    }
}

#[derive(Clone, Copy, Debug, Hash, Default, serde::Serialize, serde::Deserialize, PartialEq)]
#[repr(C)]
pub struct ExternalChallenges {
    pub memory_argument: ExternalMemoryArgumentChallenges,
    pub delegation_argument: Option<ExternalDelegationArgumentChallenges>,
    pub machine_state_permutation_argument: Option<ExternalMachineStateArgumentChallenges>,
}

impl ExternalChallenges {
    pub fn draw_from_transcript_seed(mut seed: Seed, produce_delegation_challenge: bool) -> Self {
        unsafe {
            if produce_delegation_challenge == false {
                let mut transcript_challenges = [0u32;
                    ((NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES + 1) * 4)
                        .next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS)];
                Transcript::draw_randomness(&mut seed, &mut transcript_challenges);

                let mut it = transcript_challenges.as_chunks::<4>().0.into_iter();
                let memory_argument_linearization_challenges: [Mersenne31Quartic;
                    NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES] = core::array::from_fn(|_| {
                    Mersenne31Quartic::from_coeffs_in_base(
                        &it.next()
                            .unwrap_unchecked()
                            .map(|el| Mersenne31Field::from_nonreduced_u32(el)),
                    )
                });
                let memory_argument_gamma = Mersenne31Quartic::from_coeffs_in_base(
                    &it.next()
                        .unwrap_unchecked()
                        .map(|el| Mersenne31Field::from_nonreduced_u32(el)),
                );

                let memory_argument = ExternalMemoryArgumentChallenges {
                    memory_argument_linearization_challenges,
                    memory_argument_gamma,
                };

                Self {
                    memory_argument,
                    delegation_argument: None,
                    machine_state_permutation_argument: None,
                }
            } else {
                let mut transcript_challenges = [0u32;
                    ((NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES
                        + 1
                        + NUM_DELEGATION_ARGUMENT_LINEARIZATION_CHALLENGES
                        + 1)
                        * 4)
                    .next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS)];
                Transcript::draw_randomness(&mut seed, &mut transcript_challenges);

                let mut it = transcript_challenges.as_chunks::<4>().0.into_iter();
                let memory_argument_linearization_challenges: [Mersenne31Quartic;
                    NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES] = core::array::from_fn(|_| {
                    Mersenne31Quartic::from_coeffs_in_base(
                        &it.next()
                            .unwrap_unchecked()
                            .map(|el| Mersenne31Field::from_nonreduced_u32(el)),
                    )
                });
                let memory_argument_gamma = Mersenne31Quartic::from_coeffs_in_base(
                    &it.next()
                        .unwrap_unchecked()
                        .map(|el| Mersenne31Field::from_nonreduced_u32(el)),
                );

                let delegation_argument_linearization_challenges: [Mersenne31Quartic;
                    NUM_DELEGATION_ARGUMENT_LINEARIZATION_CHALLENGES] =
                    core::array::from_fn(|_| {
                        Mersenne31Quartic::from_coeffs_in_base(
                            &it.next()
                                .unwrap_unchecked()
                                .map(|el| Mersenne31Field::from_nonreduced_u32(el)),
                        )
                    });
                let delegation_argument_gamma = Mersenne31Quartic::from_coeffs_in_base(
                    &it.next()
                        .unwrap_unchecked()
                        .map(|el| Mersenne31Field::from_nonreduced_u32(el)),
                );

                let memory_argument = ExternalMemoryArgumentChallenges {
                    memory_argument_linearization_challenges,
                    memory_argument_gamma,
                };

                let delegation_argument = ExternalDelegationArgumentChallenges {
                    delegation_argument_linearization_challenges,
                    delegation_argument_gamma,
                };

                Self {
                    memory_argument,
                    delegation_argument: Some(delegation_argument),
                    machine_state_permutation_argument: None,
                }
            }
        }
    }
}

#[derive(
    Clone, Copy, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize, Hash,
)]
#[repr(C)]
pub struct AuxArgumentsBoundaryValues {
    // #[serde(bound(deserialize = "[Mersenne31Field; REGISTER_SIZE]: serde::Deserialize<'de>"))]
    // #[serde(bound(serialize = "[Mersenne31Field; REGISTER_SIZE]: serde::Serialize"))]
    pub lazy_init_first_row: [Mersenne31Field; REGISTER_SIZE],
    pub teardown_value_first_row: [Mersenne31Field; REGISTER_SIZE],
    pub teardown_timestamp_first_row: [Mersenne31Field; REGISTER_SIZE],
    pub lazy_init_one_before_last_row: [Mersenne31Field; REGISTER_SIZE],
    pub teardown_value_one_before_last_row: [Mersenne31Field; REGISTER_SIZE],
    pub teardown_timestamp_one_before_last_row: [Mersenne31Field; REGISTER_SIZE],
}

impl AuxArgumentsBoundaryValues {
    pub fn flatten(&self) -> [u32; REGISTER_SIZE * 2 * 3] {
        // we must normalize
        let mut result = [0u32; REGISTER_SIZE * 2 * 3];
        let mut it = result.iter_mut();

        let flattened = self
            .lazy_init_first_row
            .map(|el: Mersenne31Field| el.to_reduced_u32());
        for src in flattened.into_iter() {
            *it.next().unwrap() = src;
        }

        let flattened = self
            .teardown_value_first_row
            .map(|el: Mersenne31Field| el.to_reduced_u32());
        for src in flattened.into_iter() {
            *it.next().unwrap() = src;
        }

        let flattened = self
            .teardown_timestamp_first_row
            .map(|el: Mersenne31Field| el.to_reduced_u32());
        for src in flattened.into_iter() {
            *it.next().unwrap() = src;
        }

        let flattened = self
            .lazy_init_one_before_last_row
            .map(|el: Mersenne31Field| el.to_reduced_u32());
        for src in flattened.into_iter() {
            *it.next().unwrap() = src;
        }

        let flattened = self
            .teardown_value_one_before_last_row
            .map(|el: Mersenne31Field| el.to_reduced_u32());
        for src in flattened.into_iter() {
            *it.next().unwrap() = src;
        }

        let flattened = self
            .teardown_timestamp_one_before_last_row
            .map(|el: Mersenne31Field| el.to_reduced_u32());
        for src in flattened.into_iter() {
            *it.next().unwrap() = src;
        }

        assert!(it.next().is_none());

        result
    }
}

#[derive(Clone, Copy, Debug, Hash, serde::Serialize, serde::Deserialize)]
#[repr(C)]
pub struct ExternalValues {
    // #[serde(bound(deserialize = "ExternalChallenges: serde::Deserialize<'de>"))]
    // #[serde(bound(serialize = "ExternalChallenges: serde::Serialize"))]
    pub challenges: ExternalChallenges,
    // #[serde(bound(deserialize = "AuxArgumentsBoundaryValues: serde::Deserialize<'de>"))]
    // #[serde(bound(serialize = "AuxArgumentsBoundaryValues: serde::Serialize"))]
    pub aux_boundary_values: AuxArgumentsBoundaryValues,
}

#[derive(Clone, Copy, Debug, serde::Serialize, serde::Deserialize)]
pub struct ProofAuxValues {
    pub grand_product_accumulator_final_value: Mersenne31Quartic,
    pub delegation_argument_accumulator_sum: Mersenne31Quartic,
}

/// (value, timestamp)
pub fn produce_register_contribution_into_memory_accumulator_raw(
    register_final_data: &[(u32, (u32, u32)); NUM_REGISTERS],
    memory_argument_linearization_challenges: [Mersenne31Quartic;
        NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES],
    memory_argument_gamma: Mersenne31Quartic,
) -> Mersenne31Quartic {
    let mut write_set_contribution = Mersenne31Quartic::ONE;
    // all registers are write 0 at timestamp 0
    for reg_idx in 0..NUM_REGISTERS {
        let mut contribution = Mersenne31Quartic::ONE; // is_register == 1, without challenge
        let mut t =
            memory_argument_linearization_challenges[MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        t.mul_assign_by_base(&Mersenne31Field(reg_idx as u32));
        contribution.add_assign(&t);
        contribution.add_assign(&memory_argument_gamma);
        write_set_contribution.mul_assign(&contribution);
    }

    let mut read_set_contribution = Mersenne31Quartic::ONE;
    // all registers are write 0 at timestamp 0
    for (reg_idx, (value, timestamp)) in register_final_data.iter().enumerate() {
        let (value_low, value_high) = split_u32_into_pair_u16(*value);
        let (timestamp_low, timestamp_high) = *timestamp;

        let mut contribution = Mersenne31Quartic::ONE; // is_register == 1, without challenge
        let mut t =
            memory_argument_linearization_challenges[MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        t.mul_assign_by_base(&Mersenne31Field(reg_idx as u32));
        contribution.add_assign(&t);

        let mut t = memory_argument_linearization_challenges
            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        t.mul_assign_by_base(&Mersenne31Field(timestamp_low));
        contribution.add_assign(&t);

        let mut t = memory_argument_linearization_challenges
            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        t.mul_assign_by_base(&Mersenne31Field(timestamp_high));
        contribution.add_assign(&t);

        let mut t =
            memory_argument_linearization_challenges[MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        t.mul_assign_by_base(&Mersenne31Field(value_low as u32));
        contribution.add_assign(&t);

        let mut t =
            memory_argument_linearization_challenges[MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        t.mul_assign_by_base(&Mersenne31Field(value_high as u32));
        contribution.add_assign(&t);

        contribution.add_assign(&memory_argument_gamma);
        read_set_contribution.mul_assign(&contribution);
    }

    let mut result = write_set_contribution;
    result.mul_assign(&read_set_contribution.inverse().unwrap());

    result
}

fn split_u32_into_pair_u16(num: u32) -> (u32, u32) {
    let high_word = num >> 16;
    let low_word = num & core::hint::black_box(0x0000ffff);
    (low_word, high_word)
}

/// (PC, timestamp)
pub fn produce_pc_into_permutation_accumulator_raw(
    initial_pc: u32,
    initial_timestamp: (u32, u32),
    final_pc: u32,
    final_timestamp: (u32, u32),
    state_permutation_argument_linearization_challenges: &[Mersenne31Quartic;
        NUM_MACHINE_STATE_LINEARIZATION_CHALLENGES],
    state_permutation_argument_gamma: &Mersenne31Quartic,
) -> Mersenne31Quartic {
    let mut write_set_contribution = Mersenne31Quartic::ONE;
    let mut read_set_contribution = Mersenne31Quartic::ONE;

    for (dst, (pc, (ts_low, ts_high))) in [&mut write_set_contribution, &mut read_set_contribution]
        .into_iter()
        .zip([(initial_pc, initial_timestamp), (final_pc, final_timestamp)].into_iter())
    {
        let (pc_low, pc_high) = split_u32_into_pair_u16(pc);
        // PC low without challenge
        let mut contribution = Mersenne31Quartic::from_base(Mersenne31Field(pc_low));
        // PC high
        let mut t = state_permutation_argument_linearization_challenges
            [MACHINE_STATE_CHALLENGE_POWERS_PC_HIGH_IDX];
        t.mul_assign_by_base(&Mersenne31Field(pc_high));
        contribution.add_assign(&t);
        // timestamp low
        let mut t = state_permutation_argument_linearization_challenges
            [MACHINE_STATE_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        t.mul_assign_by_base(&Mersenne31Field(ts_low));
        contribution.add_assign(&t);
        // timestamp high
        let mut t = state_permutation_argument_linearization_challenges
            [MACHINE_STATE_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        t.mul_assign_by_base(&Mersenne31Field(ts_high));
        contribution.add_assign(&t);
        // additive term
        contribution.add_assign(state_permutation_argument_gamma);
        dst.mul_assign(&contribution);
    }

    let mut result = write_set_contribution;
    result.mul_assign(&read_set_contribution.inverse().unwrap());

    result
}

// Joint structure for RAM init/teardown
#[derive(
    Clone, Copy, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize, Hash,
)]
#[repr(C)]
pub struct LazyInitAndTeardown {
    pub address: u32,
    pub teardown_value: u32,
    pub teardown_timestamp: TimestampData,
}
