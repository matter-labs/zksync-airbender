use prover::risc_v_simulator::machine_mode_only_unrolled::MemoryOpcodeTracingDataWithTimestamp;
use prover::risc_v_simulator::machine_mode_only_unrolled::NonMemoryOpcodeTracingDataWithTimestamp;
use rand::rngs::StdRng;
use rand::RngExt;

use crate::prover::mutations::Mutator;
use crate::rv32im::prover::circuits::ProofInputs;

fn insert_clone<T: Copy>(v: &mut Vec<T>, rng: &mut StdRng) {
    if v.is_empty() {
        return;
    }

    let src = rng.random_range(0..v.len());
    let dst = rng.random_range(0..=v.len());
    let row = v[src];
    v.insert(dst, row);
}

pub struct BufferInsertCloneRowMutator;

impl Mutator for BufferInsertCloneRowMutator {
    fn name(&self) -> &'static str {
        "buffer insert clone row mutator"
    }

    fn mutate_non_mem_inputs(
        &self,
        input: &mut ProofInputs<NonMemoryOpcodeTracingDataWithTimestamp>,
        rng: &mut StdRng,
    ) {
        insert_clone(&mut input.buffer, rng);
    }

    fn mutate_mem_inputs(
        &self,
        input: &mut ProofInputs<MemoryOpcodeTracingDataWithTimestamp>,
        rng: &mut StdRng,
    ) {
        insert_clone(&mut input.buffer, rng);
    }
}
