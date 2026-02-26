use std::alloc::Global;
use std::collections::HashMap;

use prover::common_constants::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER;
use prover::common_constants::BLAKE2S_DELEGATION_CSR_REGISTER;
use prover::common_constants::KECCAK_SPECIAL5_CSR_REGISTER;
use prover::cs::cs::oracle::ExecutorFamilyDecoderData;
use prover::cs::definitions::NUM_DELEGATION_ARGUMENT_KEY_PARTS;
use prover::cs::definitions::NUM_MACHINE_STATE_LINEARIZATION_CHALLENGES;
use prover::cs::definitions::NUM_MEM_ARGUMENT_KEY_PARTS;
use prover::cs::machine::ops::unrolled::opcodes_for_full_machine_with_mem_word_access_specialization;
use prover::cs::machine::ops::unrolled::opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization;
use prover::cs::machine::ops::unrolled::process_binary_into_separate_tables_ext;
use prover::cs::machine::ops::unrolled::DecoderTableEntry;
use prover::cs::machine::NON_DETERMINISM_CSR;
use prover::definitions::ExternalChallenges;
use prover::definitions::ExternalDelegationArgumentChallenges;
use prover::definitions::ExternalMachineStateArgumentChallenges;
use prover::definitions::ExternalMemoryArgumentChallenges;
use prover::fft::materialize_powers_serial_starting_with_elem;
use prover::field::Mersenne31Field;
use prover::field::Mersenne31Quartic;

use crate::rv32im::prover::SUPPORT_SIGNED;

pub fn make_external_challenges() -> ExternalChallenges {
    let memory_argument_alpha = Mersenne31Quartic::from_array_of_base([
        Mersenne31Field(2),
        Mersenne31Field(5),
        Mersenne31Field(42),
        Mersenne31Field(123),
    ]);
    let memory_argument_gamma = Mersenne31Quartic::from_array_of_base([
        Mersenne31Field(11),
        Mersenne31Field(7),
        Mersenne31Field(1024),
        Mersenne31Field(8000),
    ]);

    let memory_argument_linearization_challenges_powers: [Mersenne31Quartic;
        NUM_MEM_ARGUMENT_KEY_PARTS - 1] =
        materialize_powers_serial_starting_with_elem::<_, Global>(
            memory_argument_alpha,
            NUM_MEM_ARGUMENT_KEY_PARTS - 1,
        )
        .try_into()
        .unwrap();

    let delegation_argument_alpha = Mersenne31Quartic::from_array_of_base([
        Mersenne31Field(5),
        Mersenne31Field(8),
        Mersenne31Field(32),
        Mersenne31Field(16),
    ]);
    let delegation_argument_gamma = Mersenne31Quartic::from_array_of_base([
        Mersenne31Field(200),
        Mersenne31Field(100),
        Mersenne31Field(300),
        Mersenne31Field(400),
    ]);

    let state_permutation_argument_alpha = Mersenne31Quartic::from_array_of_base([
        Mersenne31Field(41),
        Mersenne31Field(42),
        Mersenne31Field(43),
        Mersenne31Field(44),
    ]);
    let state_permutation_argument_gamma = Mersenne31Quartic::from_array_of_base([
        Mersenne31Field(80),
        Mersenne31Field(90),
        Mersenne31Field(100),
        Mersenne31Field(110),
    ]);

    let delegation_argument_linearization_challenges: [Mersenne31Quartic;
        NUM_DELEGATION_ARGUMENT_KEY_PARTS - 1] =
        materialize_powers_serial_starting_with_elem::<_, Global>(
            delegation_argument_alpha,
            NUM_DELEGATION_ARGUMENT_KEY_PARTS - 1,
        )
        .try_into()
        .unwrap();

    let linearization_challenges: [Mersenne31Quartic; NUM_MACHINE_STATE_LINEARIZATION_CHALLENGES] =
        materialize_powers_serial_starting_with_elem::<_, Global>(
            state_permutation_argument_alpha,
            NUM_MACHINE_STATE_LINEARIZATION_CHALLENGES,
        )
        .try_into()
        .unwrap();

    ExternalChallenges {
        memory_argument: ExternalMemoryArgumentChallenges {
            memory_argument_linearization_challenges:
                memory_argument_linearization_challenges_powers,
            memory_argument_gamma,
        },
        delegation_argument: Some(ExternalDelegationArgumentChallenges {
            delegation_argument_linearization_challenges,
            delegation_argument_gamma,
        }),
        machine_state_permutation_argument: Some(ExternalMachineStateArgumentChallenges {
            linearization_challenges,
            additive_term: state_permutation_argument_gamma,
        }),
    }
}

pub type PreprocessingData = HashMap<
    u8,
    (
        Vec<Option<DecoderTableEntry<Mersenne31Field>>>,
        Vec<ExecutorFamilyDecoderData>,
    ),
>;

pub fn make_preprocessing_data(text_section: &[u32]) -> PreprocessingData {
    let opcodes = if SUPPORT_SIGNED {
        opcodes_for_full_machine_with_mem_word_access_specialization()
    } else {
        opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization()
    };

    process_binary_into_separate_tables_ext::<Mersenne31Field, true, Global>(
        text_section,
        &opcodes,
        1 << 20,
        &[
            NON_DETERMINISM_CSR,
            BLAKE2S_DELEGATION_CSR_REGISTER as u16,
            BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16,
            KECCAK_SPECIAL5_CSR_REGISTER as u16,
        ],
    )
}
