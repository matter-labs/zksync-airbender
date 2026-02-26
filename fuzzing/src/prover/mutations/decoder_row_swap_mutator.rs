use prover::risc_v_simulator::machine_mode_only_unrolled::MemoryOpcodeTracingDataWithTimestamp;
use prover::risc_v_simulator::machine_mode_only_unrolled::NonMemoryOpcodeTracingDataWithTimestamp;
use rand::rngs::StdRng;

use crate::prover::mutations::choose_distinct_indices;
use crate::prover::mutations::Mutator;
use crate::rv32im::prover::circuits::ProofInputs;

pub struct DecoderRowSwapMutator;

impl Mutator for DecoderRowSwapMutator {
    fn name(&self) -> &'static str {
        "decoder row swap mutator"
    }

    fn mutate_non_mem_inputs(
        &self,
        input: &mut ProofInputs<NonMemoryOpcodeTracingDataWithTimestamp>,
        rng: &mut StdRng,
    ) {
        if let Some((a, b)) = choose_distinct_indices(input.witness_gen_data.len(), rng) {
            input.witness_gen_data.swap(a, b);
        }
    }

    fn mutate_mem_inputs(
        &self,
        input: &mut ProofInputs<MemoryOpcodeTracingDataWithTimestamp>,
        rng: &mut StdRng,
    ) {
        if let Some((a, b)) = choose_distinct_indices(input.witness_gen_data.len(), rng) {
            input.witness_gen_data.swap(a, b);
        }
    }
}
