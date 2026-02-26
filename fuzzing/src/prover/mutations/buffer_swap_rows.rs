use prover::risc_v_simulator::machine_mode_only_unrolled::MemoryOpcodeTracingDataWithTimestamp;
use prover::risc_v_simulator::machine_mode_only_unrolled::NonMemoryOpcodeTracingDataWithTimestamp;
use rand::rngs::StdRng;

use crate::prover::mutations::choose_distinct_indices;
use crate::prover::mutations::Mutator;
use crate::rv32im::prover::circuits::ProofInputs;

fn swap_rows<T>(v: &mut [T], rng: &mut StdRng) {
    if let Some((a, b)) = choose_distinct_indices(v.len(), rng) {
        v.swap(a, b);
    }
}

pub struct BufferSwapRowsMutator;

impl Mutator for BufferSwapRowsMutator {
    fn name(&self) -> &'static str {
        "buffer swap rows mutator"
    }

    fn mutate_non_mem_inputs(
        &self,
        input: &mut ProofInputs<NonMemoryOpcodeTracingDataWithTimestamp>,
        rng: &mut StdRng,
    ) {
        swap_rows(&mut input.buffer, rng);
    }

    fn mutate_mem_inputs(
        &self,
        input: &mut ProofInputs<MemoryOpcodeTracingDataWithTimestamp>,
        rng: &mut StdRng,
    ) {
        swap_rows(&mut input.buffer, rng);
    }
}
