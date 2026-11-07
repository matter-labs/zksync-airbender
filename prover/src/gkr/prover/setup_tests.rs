use super::*;
use cs::gkr_circuits::{AddSubLuiAuipcMopDecoder, OpcodeFamilyDecoder};
use cs::tables::TableType;
use field::{baby_bear::base::BabyBearField as F, Field};
use riscv_transpiler::ir::FullUnsignedMachineDecoderConfig;

// Keep the real cached/no-cache decoder shapes, but use a small public program
// and setup domain for the export roundtrip test. No artifact is
// regenerated or written by the tests.
fn artifact(cached: bool, tagged: bool, trace_len: usize) -> GKRCircuitArtifact<F> {
    let suffix = if cached { "" } else { "_no_caches" };
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(format!(
        "../cs/compiled_circuits/add_sub_lui_auipc_mop_layout{suffix}_gkr.json"
    ));
    let mut circuit: GKRCircuitArtifact<F> =
        serde_json::from_reader(std::fs::File::open(path).unwrap()).unwrap();
    assert!(circuit.has_decoder_lookup);
    assert!(!circuit.tables_ids_in_generic_lookups);
    assert_eq!(circuit.offset_for_decoder_table, 0);
    circuit.trace_len = trace_len;
    circuit.offset_for_decoder_table = usize::from(tagged);
    circuit.total_tables_size = circuit.offset_for_decoder_table + 4;
    circuit.tables_ids_in_generic_lookups = tagged;
    circuit.generic_lookup_tables_width += usize::from(tagged);
    // The current compiler carries the committed tail explicitly. Tagged
    // tables use their discriminator; decoder-only tables use all-minus-one.
    circuit.generic_lookup_padding = if tagged { None } else { Some(F::MINUS_ONE) };
    circuit
}

#[test]
fn setup_json_roundtrip_preserves_materialized_columns_and_program() {
    use crate::gkr::prover::setup_artifact::{ColumnBlock, SetupArtifact, SetupProgram};
    let trace_len = 1 << 19;
    let mut circuit = artifact(false, true, trace_len);
    let mut driver = TableDriver::<F>::new();
    driver.materialize_table::<9>(TableType::ZeroEntry);
    driver.materialize_table::<9>(TableType::RangeCheck13);
    circuit.table_offsets = driver
        .table_starts_offsets()
        .map(|offset| offset as u32)
        .to_vec();
    circuit.offset_for_decoder_table = driver.total_tables_len;
    circuit.total_tables_size = driver.total_tables_len + 4;
    let binary = [0x0000_0013, 0x0040_8093, 0x0000_006f, 0x0071_81b3];
    let family: Box<dyn OpcodeFamilyDecoder> = Box::new(AddSubLuiAuipcMopDecoder);
    let decoder = cs::gkr_circuits::decoder_trait::preprocess_bytecode::<
        F,
        FullUnsignedMachineDecoderConfig,
        Global,
    >(&binary, binary.len(), &family, &[]);
    let setup = GKRSetup::construct(&driver, &decoder, trace_len, &circuit);
    // Compare the export input with the production table driver, including
    // every zero and discriminator column.
    for (row, expected) in driver
        .dump_tables(circuit.generic_lookup_tables_width)
        .iter()
        .enumerate()
    {
        for (column, value) in expected.iter().enumerate() {
            assert_eq!(setup.hypercube_evals[column][row], *value);
        }
    }
    let artifact = setup
        .artifact(&circuit, &driver, Some(SetupProgram::new(&binary, &binary)))
        .unwrap();
    let source = serde_json::to_string(&artifact).unwrap();
    let parsed: SetupArtifact = serde_json::from_str(&source).unwrap();
    assert_eq!(parsed, artifact);
    parsed.validate().unwrap();
    let parsed_circuit: GKRCircuitArtifact<F> =
        serde_json::from_value(parsed.circuit.clone()).unwrap();
    assert_eq!(parsed_circuit, circuit);
    for (encoded, actual) in parsed.columns.iter().zip(&setup.hypercube_evals) {
        let mut row = 0;
        for block in &encoded.blocks {
            for index in 0..block.len() {
                assert_eq!(block.value_at(index), Some(actual[row].as_u32_reduced()));
                row += 1;
            }
        }
        assert_eq!(row, trace_len);
    }
    assert_eq!(
        parsed.range16.blocks,
        vec![
            ColumnBlock::Affine {
                length: 65536,
                first: 0,
                step: 1
            },
            ColumnBlock::Affine {
                length: trace_len - 65536,
                first: 0,
                step: 0
            },
        ]
    );
    assert_eq!(
        parsed.timestamp_range.blocks,
        vec![ColumnBlock::Affine {
            length: trace_len,
            first: 0,
            step: 1
        }]
    );
    assert_eq!(
        parsed
            .tables
            .iter()
            .map(|table| (table.id, table.offset, table.length))
            .collect::<Vec<_>>(),
        vec![(0, 0, 1), (26, 1, 8192)]
    );
    let program = parsed.program.as_ref().unwrap();
    for (i, word) in binary.into_iter().enumerate() {
        assert_eq!(program.image.value_at(i), Some(word));
        assert_eq!(program.text.value_at(i), Some(word));
    }
    let mut malformed = parsed.clone();
    malformed.columns[0].blocks.push(ColumnBlock::Affine {
        length: 1,
        first: 0,
        step: 0,
    });
    assert!(malformed.validate().is_err());
    let mut malformed = parsed.clone();
    malformed.columns[0].blocks[0] = ColumnBlock::Affine {
        length: trace_len,
        first: F::CHARACTERISTICS_U32,
        step: 0,
    };
    assert!(malformed.validate().is_err());
    let mut malformed = parsed.clone();
    malformed.tables[1].offset += 1;
    assert!(malformed.validate().is_err());
    // Explicit fixture generation only; ordinary test runs never write the repository.
    if let Some(path) = std::env::var_os("AIRBENDER_SETUP_JSON_FIXTURE") {
        std::fs::write(path, source).unwrap();
    }
}
