use prover::common_constants::INITIAL_TIMESTAMP;
use prover::cs::utils::split_timestamp;
use prover::definitions::produce_pc_into_permutation_accumulator_raw;
use prover::definitions::ExternalChallenges;
use prover::field::Field as _;
use prover::field::Mersenne31Quartic;
use prover::mem_utils::produce_register_contribution_into_memory_accumulator;
use prover::RamShuffleMemStateRecord;
use riscv_transpiler::vm::State;

use crate::rv32im::prover::INITIAL_PC;
use crate::rv32im::types::CountersT;

pub struct Accumulators {
    delegation_argument: Mersenne31Quartic,
    permutation_argument: Mersenne31Quartic,
}

impl Accumulators {
    pub fn new(state: State<CountersT>, external_challenges: &ExternalChallenges) -> Self {
        let final_pc = state.pc;
        let final_timestamp = state.timestamp;
        let register_final_state = state.registers.map(|el| RamShuffleMemStateRecord {
            last_access_timestamp: el.timestamp,
            current_value: el.value,
        });
        let mut permutation_argument = produce_pc_into_permutation_accumulator_raw(
            INITIAL_PC,
            split_timestamp(INITIAL_TIMESTAMP),
            final_pc,
            split_timestamp(final_timestamp),
            &external_challenges
                .machine_state_permutation_argument
                .as_ref()
                .unwrap()
                .linearization_challenges,
            &external_challenges
                .machine_state_permutation_argument
                .as_ref()
                .unwrap()
                .additive_term,
        );
        let t = produce_register_contribution_into_memory_accumulator(
            &register_final_state,
            external_challenges
                .memory_argument
                .memory_argument_linearization_challenges,
            external_challenges.memory_argument.memory_argument_gamma,
        );
        permutation_argument.mul_assign(&t);
        Self {
            delegation_argument: Mersenne31Quartic::ZERO,
            permutation_argument,
        }
    }

    pub fn delegation_argument(&self) -> Mersenne31Quartic {
        self.delegation_argument
    }

    pub fn delegation_argument_mut(&mut self) -> &mut Mersenne31Quartic {
        &mut self.delegation_argument
    }

    pub fn permutation_argument(&self) -> Mersenne31Quartic {
        self.permutation_argument
    }

    pub fn permutation_argument_mut(&mut self) -> &mut Mersenne31Quartic {
        &mut self.permutation_argument
    }
}
