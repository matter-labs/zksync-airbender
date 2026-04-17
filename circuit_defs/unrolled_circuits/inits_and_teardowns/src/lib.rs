#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

use crate::gkr_compiler::compile_inits_and_teardowns_circuit;
use common_constants::circuit_families::INITS_AND_TEARDOWNS_FORMAL_CIRCUIT_FAMILY_IDX;
use prover::cs::gkr_compiler::GKRCircuitArtifact;
use prover::cs::*;
use prover::field::baby_bear::base::BabyBearField;
use prover::field::PrimeField;
use prover::*;

pub const FAMILY_IDX: u8 = INITS_AND_TEARDOWNS_FORMAL_CIRCUIT_FAMILY_IDX;
pub const TRACE_LEN_LOG2: u32 = 24;
pub const NUM_INIT_AND_TEARDOWN_SETS: usize = 16;

fn serialize_to_file<T: serde::Serialize>(el: &T, filename: &str) {
    let mut dst = std::fs::File::create(filename).unwrap();
    serde_json::to_writer_pretty(&mut dst, el).unwrap();
}

pub fn get_inits_and_teardowns_circuit<F: PrimeField>() -> GKRCircuitArtifact<F> {
    compile_inits_and_teardowns_circuit::<F, 2>(NUM_INIT_AND_TEARDOWN_SETS, TRACE_LEN_LOG2 as usize)
}

pub fn get_table_driver<F: PrimeField>() -> prover::cs::tables::TableDriver<F> {
    prover::cs::tables::TableDriver::new()
}

/// This function will generate layout and quotient files for verifier
pub fn generate_artifacts() {
    let compiled_machine = get_inits_and_teardowns_circuit::<BabyBearField>();
    serialize_to_file(&compiled_machine, "generated/layout.json");
}

#[cfg(test)]
mod test {
    use test_utils::skip_if_ci;

    use super::*;

    #[cfg(test)]
    #[test]
    fn generate() {
        skip_if_ci!();
        generate_artifacts();
    }
}
