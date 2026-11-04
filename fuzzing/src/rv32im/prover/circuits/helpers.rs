use prover::definitions::AuxArgumentsBoundaryValues;
use prover::definitions::ExternalDelegationArgumentChallenges;
use prover::definitions::ExternalMachineStateArgumentChallenges;
use prover::definitions::ExternalMemoryArgumentChallenges;
use prover::definitions::MerkleTreeCap;
use prover::field::Field as _;
use prover::field::Mersenne31Field;
use prover::field::Mersenne31Quartic;
use prover::nd_source_std::set_iterator;
use verifier_common::ProofOutput;
use verifier_common::ProofPublicInputs;

pub type ValidatorOutput<
    const CAP_SIZE: usize,
    const NUM_COSETS: usize,
    const NUM_DELEGATION_CHALLENGES: usize,
    const NUM_AUX_BOUNDARY_VALUES: usize,
    const NUM_MACHINE_STATE_CHALLENGES: usize,
    const N: usize,
> = (
    ProofOutput<
        CAP_SIZE,
        NUM_COSETS,
        NUM_DELEGATION_CHALLENGES,
        NUM_AUX_BOUNDARY_VALUES,
        NUM_MACHINE_STATE_CHALLENGES,
    >,
    ProofPublicInputs<N>,
);

/// Creates empty validator output to avoid using assume init stuff.
pub const fn validator_outputs<
    const CAP_SIZE: usize,
    const NUM_COSETS: usize,
    const NUM_DELEGATION_CHALLENGES: usize,
    const NUM_AUX_BOUNDARY_VALUES: usize,
    const NUM_MACHINE_STATE_CHALLENGES: usize,
    const N: usize,
>() -> ValidatorOutput<
    CAP_SIZE,
    NUM_COSETS,
    NUM_DELEGATION_CHALLENGES,
    NUM_AUX_BOUNDARY_VALUES,
    NUM_MACHINE_STATE_CHALLENGES,
    N,
> {
    (
        ProofOutput {
            setup_caps: [MerkleTreeCap { cap: [[0; _]; _] }; _],
            memory_caps: [MerkleTreeCap { cap: [[0; _]; _] }; _],
            memory_challenges: ExternalMemoryArgumentChallenges {
                memory_argument_linearization_challenges: [Mersenne31Quartic::ZERO; _],
                memory_argument_gamma: Mersenne31Quartic::ZERO,
            },
            delegation_challenges: [ExternalDelegationArgumentChallenges {
                delegation_argument_linearization_challenges: [Mersenne31Quartic::ZERO; _],
                delegation_argument_gamma: Mersenne31Quartic::ZERO,
            }; _],
            machine_state_permutation_challenges: [ExternalMachineStateArgumentChallenges {
                linearization_challenges: [Mersenne31Quartic::ZERO; _],
                additive_term: Mersenne31Quartic::ZERO,
            }; _],
            lazy_init_boundary_values: [AuxArgumentsBoundaryValues {
                lazy_init_first_row: [Mersenne31Field::ZERO; _],
                teardown_value_first_row: [Mersenne31Field::ZERO; _],
                teardown_timestamp_first_row: [Mersenne31Field::ZERO; _],
                lazy_init_one_before_last_row: [Mersenne31Field::ZERO; _],
                teardown_value_one_before_last_row: [Mersenne31Field::ZERO; _],
                teardown_timestamp_one_before_last_row: [Mersenne31Field::ZERO; _],
            }; _],
            grand_product_accumulator: Mersenne31Quartic::ZERO,
            delegation_argument_accumulator: [Mersenne31Quartic::ZERO; _],
            circuit_sequence: 0,
            delegation_type: 0,
        },
        ProofPublicInputs {
            input_state_variables: [Mersenne31Field::ZERO; _],
            output_state_variables: [Mersenne31Field::ZERO; _],
        },
    )
}

pub fn run_verifier_in_thread(
    thread_name: &str,
    oracle_data: Vec<u32>,
    verify: impl FnOnce() + Send + 'static,
) -> Result<(), ()> {
    std::thread::Builder::new()
        .name(thread_name.to_owned())
        .stack_size(1 << 27)
        .spawn(move || {
            set_iterator(oracle_data.into_iter());
            verify();
        })
        .expect("must spawn verifier thread")
        .join()
        .map_err(|_| ())
}
