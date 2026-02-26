use prover::risc_v_simulator::machine_mode_only_unrolled::MemoryOpcodeTracingDataWithTimestamp;
use prover::risc_v_simulator::machine_mode_only_unrolled::NonMemoryOpcodeTracingDataWithTimestamp;
use rand::rngs::StdRng;

use crate::prover::mutations::choose_row_mut;
use crate::prover::mutations::flip_mem_discr;
use crate::prover::mutations::Mutator;
use crate::rv32im::prover::circuits::ProofInputs;

pub struct MemDiscrFlipMutator;

impl Mutator for MemDiscrFlipMutator {
    fn name(&self) -> &'static str {
        "memory discriminator flip mutator"
    }

    fn mutate_non_mem_inputs(
        &self,
        _: &mut ProofInputs<NonMemoryOpcodeTracingDataWithTimestamp>,
        _: &mut StdRng,
    ) {
    }

    fn mutate_mem_inputs(
        &self,
        input: &mut ProofInputs<MemoryOpcodeTracingDataWithTimestamp>,
        rng: &mut StdRng,
    ) {
        if let Some(row) = choose_row_mut(input.buffer.as_mut_slice(), rng) {
            flip_mem_discr(row);
        }
    }
}
