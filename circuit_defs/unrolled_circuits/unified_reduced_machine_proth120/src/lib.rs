#![feature(allocator_api)]

//! The unified reduced-machine circuit over Proth120: the 2^21 L1 wrap circuit.
//!
//! The layout is the compiled JSON the L1 wrap verifiers are generated
//! from; the witness-eval fn is generated from the matching SSA.

use common_constants::rom::{RomGeometry, L1_WRAP_ROM};
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
use prover::gkr::witness_gen::family_circuits::build_unified_table_driver_with_rom;
use prover::gkr::witness_gen::oracles::UnifiedRiscvCircuitOracle;
use riscv_transpiler::ir::ReducedMachineDecoderConfig;
use std::alloc::Global;

pub const NUM_INIT_AND_TEARDOWN_SETS: usize = 2;

/// The 2^21 wrap circuit over the 512 KiB wrap ROM.
pub mod l1_wrap_2p21 {
    use super::*;

    pub const TRACE_LEN_LOG2: usize = 21;
    pub const ROM: RomGeometry = L1_WRAP_ROM;

    pub const LAYOUT_JSON: &str = include_str!(
        "../../../../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120_2p21.json"
    );

    pub fn circuit_artifact() -> GKRCircuitArtifact<Proth120> {
        serde_json::from_str(LAYOUT_JSON).expect("embedded 2^21 Proth120 unified layout")
    }

    mod sealed {
        use prover::cs::oracle::Placeholder;
        use prover::cs::witness_placer::*;
        use prover::field::Proth120;
        use prover::gkr::witness_gen::witness_proxy::*;

        include!(
            "../../../../prover/compiled_circuits/unified_reduced_machine_generated_gkr_proth120_2p21.rs"
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

    pub fn l1_wrap_setup(binary: &[u32], text: &[u32]) -> L1WrapSetup {
        let circuit = circuit_artifact();
        assert!(
            binary.len() <= ROM.word_size() && text.len() <= ROM.word_size(),
            "the wrap image ({} binary / {} text words) exceeds the 2^{}-word ROM",
            binary.len(),
            text.len(),
            ROM.word_size().trailing_zeros()
        );
        assert_eq!(circuit.trace_len, 1 << TRACE_LEN_LOG2);
        assert_eq!(
            circuit.memory_layout.teardown_sets.len(),
            NUM_INIT_AND_TEARDOWN_SETS
        );
        let decoders: Vec<Box<dyn OpcodeFamilyDecoder>> =
            vec![Box::new(UnifiedReducedMachineDecoder)];
        let mut preprocessing = process_binary_into_separate_tables_ext::<
            BabyBearField,
            ReducedMachineDecoderConfig,
            true,
            Global,
        >(
            text,
            &decoders,
            ROM.word_size(),
            &[common_constants::NON_DETERMINISM_CSR as u16],
        );
        let decoder_table = preprocessing
            .remove(&common_constants::circuit_families::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX)
            .expect("UnifiedReducedMachineDecoder must produce the unified family entry");
        let table_driver = build_unified_table_driver_with_rom::<
            Proth120,
            { L1_WRAP_ROM.second_word_bits() },
        >(binary);
        let trace_len = 1 << TRACE_LEN_LOG2;
        let setup = GKRSetup::construct(&table_driver, &decoder_table, trace_len, &circuit);
        L1WrapSetup {
            circuit,
            table_driver,
            decoder_table,
            setup,
            trace_len,
            rom: ROM,
        }
    }
}

pub struct L1WrapSetup {
    pub circuit: GKRCircuitArtifact<Proth120>,
    pub table_driver: TableDriver<Proth120>,
    pub decoder_table: Vec<Option<ExecutorFamilyDecoderData>>,
    pub setup: GKRSetup<Proth120>,
    pub trace_len: usize,
    pub rom: RomGeometry,
}
