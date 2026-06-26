use rand::rngs::StdRng;
use rand::RngExt;
use riscv_transpiler::machine_mode_only_unrolled::MemoryOpcodeTracingDataWithTimestamp;
use riscv_transpiler::machine_mode_only_unrolled::NonMemoryOpcodeTracingDataWithTimestamp;

use crate::prover::mutations::choose_row_mut;
use crate::prover::mutations::mutate_timestamp;
use crate::prover::mutations::Mutator;
use crate::rv32im::prover::circuits::ProofInputs;

pub struct ReadTimestampMutator;

impl Mutator for ReadTimestampMutator {
    fn name(&self) -> &'static str {
        "read timestamp mutator"
    }

    fn mutate_non_mem_inputs(
        &self,
        input: &mut ProofInputs<NonMemoryOpcodeTracingDataWithTimestamp>,
        rng: &mut StdRng,
    ) {
        let Some(row) = choose_row_mut(input.buffer.as_mut_slice(), rng) else {
            return;
        };

        match rng.random_range(0..3) {
            0 => mutate_timestamp(&mut row.rs1_read_timestamp, rng),
            1 => mutate_timestamp(&mut row.rs2_read_timestamp, rng),
            2 => mutate_timestamp(&mut row.rd_read_timestamp, rng),
            _ => unreachable!(),
        }
    }

    fn mutate_mem_inputs(
        &self,
        input: &mut ProofInputs<MemoryOpcodeTracingDataWithTimestamp>,
        rng: &mut StdRng,
    ) {
        let Some(row) = choose_row_mut(input.buffer.as_mut_slice(), rng) else {
            return;
        };

        match rng.random_range(0..3) {
            0 => mutate_timestamp(&mut row.rs1_read_timestamp, rng),
            1 => mutate_timestamp(&mut row.rs2_or_ram_read_timestamp, rng),
            2 => mutate_timestamp(&mut row.rd_or_ram_read_timestamp, rng),
            _ => unreachable!(),
        }
    }
}
