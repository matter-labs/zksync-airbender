#![feature(allocator_api)]

//! The unified reduced-machine circuit over Proth120: the 2^21 L1 wrap circuit.
//!
//! The layout is the compiled JSON the EVM verifier contracts are generated
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

    pub const TRACE_LEN_LOG2: usize =
        prover::gkr::prover_config::example_configs::l1_wrap_2p21::TRACE_LEN_LOG2;
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
        build_l1_wrap_setup(
            circuit_artifact(),
            TRACE_LEN_LOG2,
            ROM,
            build_unified_table_driver_with_rom::<Proth120, { L1_WRAP_ROM.second_word_bits() }>,
            binary,
            text,
        )
    }

    #[cfg(test)]
    mod test {
        use super::*;
        use prover::definitions::SecurityLevel;
        use prover::gkr::prover_config::example_configs::l1_wrap_2p21::{
            packed_prover_config, EXTERNAL_CHALLENGES_POW_BITS, PACK_LOG2,
        };
        use prover::gkr::prover_config::pow_bits::{
            batched_proximity_check_pow_bits, lookup_challenges_pow_bits, lookup_identity_degree,
            total_base_oracle_columns,
        };

        #[test]
        #[ignore = "compiles the Proth120 unified circuit"]
        fn embedded_layout_matches_the_compiler() {
            assert_embedded_layout_matches_the_compiler(&circuit_artifact(), TRACE_LEN_LOG2, ROM);
        }

        #[test]
        fn l1_wrap_2p21_artifact_geometry() {
            let circuit = circuit_artifact();
            assert_eq!(circuit.trace_len, 1 << 21);
            assert_eq!(circuit.total_tables_size, 1_311_105);
            assert!(circuit.total_tables_size <= circuit.trace_len);
            assert_eq!(circuit.offset_for_decoder_table, 1_180_033);
            assert_eq!(circuit.layers.len(), 5);
            assert_eq!(circuit.memory_layout.total_width, 38);
            assert_eq!(circuit.witness_layout.total_width, 66);
            assert_eq!(circuit.generic_lookup_tables_width, 10);
            assert_eq!(circuit.memory_layout.inits_and_teardowns_word_bits, Some(2));
            assert_eq!(
                circuit.memory_layout.teardown_sets.len(),
                NUM_INIT_AND_TEARDOWN_SETS
            );

            let config = packed_prover_config(SecurityLevel::Sec100);
            let lookup_pow = lookup_challenges_pow_bits::<Proth120, Proth120>(
                100,
                lookup_identity_degree(&circuit),
            );
            assert_eq!(lookup_pow, 8);
            assert_eq!(lookup_pow.max(EXTERNAL_CHALLENGES_POW_BITS), 20);
            let batching_pow = batched_proximity_check_pow_bits::<Proth120, Proth120>(
                100,
                TRACE_LEN_LOG2 + PACK_LOG2,
                config.lde_factor.trailing_zeros() as usize,
                total_base_oracle_columns(&circuit),
            );
            assert_eq!(batching_pow, 16);
        }

        #[test]
        #[should_panic(expected = "exceeds the 2^17-word ROM")]
        fn l1_wrap_2p21_setup_rejects_an_oversize_image() {
            l1_wrap_setup(&vec![0u32; ROM.word_size() + 1], &[]);
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

fn build_l1_wrap_setup(
    circuit: GKRCircuitArtifact<Proth120>,
    trace_len_log2: usize,
    rom: RomGeometry,
    table_driver_fn: fn(&[u32]) -> TableDriver<Proth120>,
    binary: &[u32],
    text: &[u32],
) -> L1WrapSetup {
    assert!(
        binary.len() <= rom.word_size() && text.len() <= rom.word_size(),
        "the wrap image ({} binary / {} text words) exceeds the 2^{}-word ROM",
        binary.len(),
        text.len(),
        rom.word_size().trailing_zeros()
    );
    assert_eq!(circuit.trace_len, 1 << trace_len_log2);
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
        rom.word_size(),
        &[common_constants::NON_DETERMINISM_CSR as u16],
    );
    let decoder_table = preprocessing
        .remove(&common_constants::circuit_families::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX)
        .expect("UnifiedReducedMachineDecoder must produce the unified family entry");
    let table_driver = table_driver_fn(binary);
    let trace_len = 1 << trace_len_log2;
    let setup = GKRSetup::construct(&table_driver, &decoder_table, trace_len, &circuit);
    L1WrapSetup {
        circuit,
        table_driver,
        decoder_table,
        setup,
        trace_len,
        rom,
    }
}

#[cfg(test)]
fn assert_embedded_layout_matches_the_compiler(
    embedded: &GKRCircuitArtifact<Proth120>,
    trace_len_log2: usize,
    rom: RomGeometry,
) {
    let compiled = prover::cs::gkr_circuits::unified_reduced_machine::build_unified_artifact_core::<
        Proth120,
        BabyBearField,
    >(true, trace_len_log2, 1, rom);
    assert!(
        serde_json::to_string(&compiled).unwrap() == serde_json::to_string(embedded).unwrap(),
        "embedded Proth120 layout drifted from the compiler"
    );
}
