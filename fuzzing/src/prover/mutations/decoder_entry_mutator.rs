use riscv_transpiler::machine_mode_only_unrolled::MemoryOpcodeTracingDataWithTimestamp;
use riscv_transpiler::machine_mode_only_unrolled::NonMemoryOpcodeTracingDataWithTimestamp;
use rand::rngs::StdRng;

use crate::prover::mutations::mutate_decoder_row;
use crate::prover::mutations::Mutator;
use crate::rv32im::prover::circuits::ProofInputs;

pub struct DecoderEntryMutator;

impl Mutator for DecoderEntryMutator {
    fn name(&self) -> &'static str {
        "decoder entry mutator"
    }

    fn mutate_non_mem_inputs(
        &self,
        input: &mut ProofInputs<NonMemoryOpcodeTracingDataWithTimestamp>,
        rng: &mut StdRng,
    ) {
        mutate_decoder_row(&mut input.witness_gen_data, rng);
    }

    fn mutate_mem_inputs(
        &self,
        input: &mut ProofInputs<MemoryOpcodeTracingDataWithTimestamp>,
        rng: &mut StdRng,
    ) {
        mutate_decoder_row(&mut input.witness_gen_data, rng);
    }
}
