use prover::risc_v_simulator::machine_mode_only_unrolled::MemoryOpcodeTracingDataWithTimestamp;
use prover::risc_v_simulator::machine_mode_only_unrolled::NonMemoryOpcodeTracingDataWithTimestamp;
use rand::rngs::StdRng;

use crate::prover::mutations::choose_row_mut;
use crate::prover::mutations::mutate_u32;
use crate::prover::mutations::Mutator;
use crate::rv32im::prover::circuits::ProofInputs;

pub struct InitialPcMutator;

impl Mutator for InitialPcMutator {
    fn name(&self) -> &'static str {
        "initial pc mutator"
    }

    fn mutate_non_mem_inputs(
        &self,
        input: &mut ProofInputs<NonMemoryOpcodeTracingDataWithTimestamp>,
        rng: &mut StdRng,
    ) {
        if let Some(row) = choose_row_mut(input.buffer.as_mut_slice(), rng) {
            mutate_u32(&mut row.opcode_data.initial_pc, rng);
        }
    }

    fn mutate_mem_inputs(
        &self,
        input: &mut ProofInputs<MemoryOpcodeTracingDataWithTimestamp>,
        rng: &mut StdRng,
    ) {
        if let Some(row) = choose_row_mut(input.buffer.as_mut_slice(), rng) {
            mutate_u32(&mut row.opcode_data.initial_pc, rng);
        }
    }
}
