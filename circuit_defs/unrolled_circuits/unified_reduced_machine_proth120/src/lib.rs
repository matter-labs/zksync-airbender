#![feature(allocator_api)]

//! The unified reduced-machine circuits over Proth120 for L1 wrapping.
//!
//! `generated/layout.json` is the compiled circuit the L1 wrap verifiers are generated from,
//! and `generated/witness_generation_fn.rs` is the witness-eval fn derived from its SSA; the
//! `generate` test writes both.

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

/// The wrap circuit over the 512 KiB wrap ROM.
pub mod l1_wrap {
    use super::*;

    pub const LAYOUT_TRACE_LEN_LOG2: usize = 21;
    pub const ROM: RomGeometry = L1_WRAP_ROM;

    pub const LAYOUT_JSON: &str = include_str!("../generated/layout.json");

    pub fn circuit_artifact() -> GKRCircuitArtifact<Proth120> {
        serde_json::from_str(LAYOUT_JSON).expect("embedded 2^21 Proth120 unified layout")
    }

    /// The compiled gate and witness layout is shared by the two trace sizes.
    pub fn circuit_artifact_for_trace(trace_len_log2: usize) -> GKRCircuitArtifact<Proth120> {
        assert!(
            matches!(trace_len_log2, LAYOUT_TRACE_LEN_LOG2 | 22),
            "the wrap layout has no 2^{trace_len_log2}-row trace"
        );
        let mut circuit = circuit_artifact();
        assert_eq!(circuit.trace_len, 1 << LAYOUT_TRACE_LEN_LOG2);
        circuit.trace_len = 1 << trace_len_log2;
        circuit
    }

    mod sealed {
        use prover::cs::oracle::Placeholder;
        use prover::cs::witness_placer::*;
        use prover::field::Proth120;
        use prover::gkr::witness_gen::witness_proxy::*;

        include!("../generated/witness_generation_fn.rs");
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

    pub fn l1_wrap_setup_for_2_21(
        binary: &[u32],
        text: &[u32],
        worker: &prover::worker::Worker,
    ) -> L1WrapSetup {
        l1_wrap_setup_for_trace(LAYOUT_TRACE_LEN_LOG2, binary, text, worker)
    }

    pub fn l1_wrap_setup_for_trace(
        trace_len_log2: usize,
        binary: &[u32],
        text: &[u32],
        worker: &prover::worker::Worker,
    ) -> L1WrapSetup {
        let circuit = circuit_artifact_for_trace(trace_len_log2);
        assert!(
            binary.len() <= ROM.word_size() && text.len() <= ROM.word_size(),
            "the wrap image ({} binary / {} text words) exceeds the 2^{}-word ROM",
            binary.len(),
            text.len(),
            ROM.word_size().trailing_zeros()
        );
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
        let trace_len = circuit.trace_len;
        let setup = GKRSetup::construct(&table_driver, &decoder_table, trace_len, &circuit, worker);
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

#[cfg(test)]
mod test {
    use super::*;
    use prover::cs::gkr_circuits::unified_reduced_machine::{
        build_unified_artifact_core,
        unified_reduced_machine_circuit_with_preprocessed_bytecode_for_gkr_core,
        unified_register_all_tables,
    };
    use prover::cs::gkr_compiler::dump_ssa_witness_eval_form;
    use std::io::Write;
    use test_utils::skip_if_ci;

    #[test]
    fn trace_2_22_shares_the_compiled_layout() {
        let compiled =
            build_unified_artifact_core::<Proth120, BabyBearField>(true, 22, 1, L1_WRAP_ROM);
        let wrap = l1_wrap::circuit_artifact_for_trace(22);
        assert!(
            compiled == wrap,
            "the shared wrap layout must match the compiler at the 2^22 trace length"
        );
    }

    /// Writes `generated/layout.json` and `generated/witness_generation_fn.rs`.
    #[test]
    fn generate() {
        skip_if_ci!();

        let layout = build_unified_artifact_core::<Proth120, BabyBearField>(
            true,
            l1_wrap::LAYOUT_TRACE_LEN_LOG2,
            1,
            L1_WRAP_ROM,
        );
        let ssa = dump_ssa_witness_eval_form::<Proth120>(
            &|cs| unified_register_all_tables(cs, L1_WRAP_ROM),
            &|cs| {
                unified_reduced_machine_circuit_with_preprocessed_bytecode_for_gkr_core::<
                    Proth120,
                    BabyBearField,
                    _,
                >(cs, L1_WRAP_ROM)
            },
        );
        let mut dst = std::fs::File::create("generated/layout.json").unwrap();
        serde_json::to_writer_pretty(&mut dst, &layout).unwrap();
        let witness = witness_eval_generator::derive_from_ssa::derive_from_gkr_ssa(
            &ssa, &layout, false, "Proth120",
        );
        std::fs::File::create("generated/witness_generation_fn.rs")
            .unwrap()
            .write_all(witness.to_string().as_bytes())
            .unwrap();
    }
}
