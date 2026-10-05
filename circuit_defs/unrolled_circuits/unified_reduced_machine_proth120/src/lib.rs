#![allow(incomplete_features)]
#![feature(generic_const_exprs)]
#![feature(allocator_api)]

//! The unified reduced-machine circuit over Proth120: the L1 wrap circuit.
//!
//! The layout is the compiled JSON the EVM verifier contracts are generated
//! from; the witness-eval fn is generated from the matching SSA.

use prover::cs::gkr_circuits::decoder_trait::{
    process_binary_into_separate_tables_ext, ExecutorFamilyDecoderData, OpcodeFamilyDecoder,
};
use prover::cs::gkr_circuits::unified_reduced_machine::UnifiedReducedMachineDecoder;
use prover::cs::gkr_compiler::GKRCircuitArtifact;
use prover::cs::tables::TableDriver;
use prover::cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;
use prover::field::baby_bear::base::BabyBearField;
use prover::field::Proth120;
use prover::gkr::prover::setup::GKRSetup;
use prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
use prover::gkr::witness_gen::family_circuits::build_unified_table_driver;
use prover::gkr::witness_gen::oracles::UnifiedRiscvCircuitOracle;
use riscv_transpiler::ir::ReducedMachineDecoderConfig;
use std::alloc::Global;

pub const TRACE_LEN_LOG2: usize =
    prover::gkr::prover_config::example_configs::EVM_PRODUCTION_TRACE_LEN_LOG2;
pub const NUM_INIT_AND_TEARDOWN_SETS: usize = 2;

pub const LAYOUT_JSON: &str = include_str!(
    "../../../../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json"
);

pub fn circuit_artifact() -> GKRCircuitArtifact<Proth120> {
    serde_json::from_str(LAYOUT_JSON).expect("embedded Proth120 unified layout")
}

mod sealed {
    use prover::cs::oracle::Placeholder;
    use prover::cs::witness_placer::*;
    use prover::field::Proth120;
    use prover::gkr::witness_gen::witness_proxy::*;

    include!(
        "../../../../prover/compiled_circuits/unified_reduced_machine_generated_gkr_proth120.rs"
    );
}

pub fn witness_eval_fn(
    proxy: &'_ mut ColumnMajorWitnessProxy<'_, UnifiedRiscvCircuitOracle<'_>, Proth120>,
) {
    let fn_ptr = sealed::evaluate_witness_fn::<
        ScalarWitnessTypeSet<Proth120, true>,
        ColumnMajorWitnessProxy<'_, UnifiedRiscvCircuitOracle<'_>, Proth120>,
    >;
    (fn_ptr)(proxy);
}

pub struct L1WrapSetup {
    pub circuit: GKRCircuitArtifact<Proth120>,
    pub table_driver: TableDriver<Proth120>,
    pub decoder_table: Vec<Option<ExecutorFamilyDecoderData>>,
    pub setup: GKRSetup<Proth120>,
    pub trace_len: usize,
}

pub fn l1_wrap_setup(binary: &[u32], text: &[u32]) -> L1WrapSetup {
    let circuit = circuit_artifact();
    assert_eq!(
        circuit.memory_layout.teardown_sets.len(),
        NUM_INIT_AND_TEARDOWN_SETS
    );
    let decoders: Vec<Box<dyn OpcodeFamilyDecoder>> = vec![Box::new(UnifiedReducedMachineDecoder)];
    let mut preprocessing = process_binary_into_separate_tables_ext::<
        BabyBearField,
        ReducedMachineDecoderConfig,
        true,
        Global,
    >(
        text,
        &decoders,
        common_constants::ROM_WORD_SIZE,
        &[common_constants::NON_DETERMINISM_CSR as u16],
    );
    let decoder_table = preprocessing
        .remove(&common_constants::circuit_families::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX)
        .expect("UnifiedReducedMachineDecoder must produce the unified family entry");
    let table_driver = build_unified_table_driver::<Proth120>(binary);
    let trace_len = 1 << TRACE_LEN_LOG2;
    let setup = GKRSetup::construct(&table_driver, &decoder_table, trace_len, &circuit);
    L1WrapSetup {
        circuit,
        table_driver,
        decoder_table,
        setup,
        trace_len,
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    #[ignore = "compiles the Proth120 unified circuit"]
    fn embedded_layout_matches_the_compiler() {
        let compiled = prover::cs::gkr_circuits::unified_reduced_machine::build_unified_artifact::<
            Proth120,
        >(true, TRACE_LEN_LOG2, 1);
        assert!(
            serde_json::to_string(&compiled).unwrap()
                == serde_json::to_string(&circuit_artifact()).unwrap(),
            "embedded Proth120 layout drifted from the compiler"
        );
    }
}
