use prover::risc_v_simulator::machine_mode_only_unrolled::MemoryOpcodeTracingDataWithTimestamp;
use prover::risc_v_simulator::machine_mode_only_unrolled::NonMemoryOpcodeTracingDataWithTimestamp;
use rand::rngs::StdRng;

use crate::prover::mutations::choose_row_mut;
use crate::prover::mutations::mutate_mem_trace_row;
use crate::prover::mutations::mutate_non_mem_trace_row;
use crate::prover::mutations::Mutator;
use crate::rv32im::prover::circuits::ProofInputs;

pub struct TraceValueMutator;

impl Mutator for TraceValueMutator {
    fn name(&self) -> &'static str {
        "trace value mutator"
    }

    fn mutate_non_mem_inputs(
        &self,
        input: &mut ProofInputs<NonMemoryOpcodeTracingDataWithTimestamp>,
        rng: &mut StdRng,
    ) {
        if let Some(row) = choose_row_mut(input.buffer.as_mut_slice(), rng) {
            mutate_non_mem_trace_row(row, rng);
        }
    }

    fn mutate_mem_inputs(
        &self,
        input: &mut ProofInputs<MemoryOpcodeTracingDataWithTimestamp>,
        rng: &mut StdRng,
    ) {
        if let Some(row) = choose_row_mut(input.buffer.as_mut_slice(), rng) {
            mutate_mem_trace_row(row, rng);
        }
    }
}
