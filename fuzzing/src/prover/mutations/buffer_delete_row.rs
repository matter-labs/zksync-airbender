use riscv_transpiler::machine_mode_only_unrolled::MemoryOpcodeTracingDataWithTimestamp;
use riscv_transpiler::machine_mode_only_unrolled::NonMemoryOpcodeTracingDataWithTimestamp;
use rand::rngs::StdRng;
use rand::RngExt;

use crate::prover::mutations::Mutator;
use crate::rv32im::prover::circuits::ProofInputs;

pub struct BufferDeleteRowMutator;

/// Removes a random row of the given Vec.
///
/// Does not touch the last row, so if the Vec is empty or has only one
/// element this mutation is a no-op.
fn remove_random_row<T>(v: &mut Vec<T>, rng: &mut StdRng) {
    if v.len() < 2 {
        return;
    }

    let idx = rng.random_range(0..(v.len() - 1));
    v.remove(idx);
}

impl Mutator for BufferDeleteRowMutator {
    fn name(&self) -> &'static str {
        "buffer delete row mutator"
    }

    fn mutate_non_mem_inputs(
        &self,
        input: &mut ProofInputs<NonMemoryOpcodeTracingDataWithTimestamp>,
        rng: &mut StdRng,
    ) {
        remove_random_row(&mut input.buffer, rng)
    }

    fn mutate_mem_inputs(
        &self,
        input: &mut ProofInputs<MemoryOpcodeTracingDataWithTimestamp>,
        rng: &mut StdRng,
    ) {
        remove_random_row(&mut input.buffer, rng)
    }
}
