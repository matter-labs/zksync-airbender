use super::*;
use crate::allocation_pool::GenericAllocationPool;
use crate::gkr::prover::forward_loop::utils::materialize_vector_lookup_input;
use crate::gkr::prover::forward_loop::vector_lookup::materialize_decoder_lookup_minus_setup;
use cs::definitions::gkr::{LinearRelation, VectorLookupRelation, DECODER_LOOKUP_FORMAL_SET_INDEX};
use cs::gkr_circuits::{AddSubLuiAuipcMopDecoder, OpcodeFamilyDecoder};
use field::baby_bear::{base::BabyBearField as F, ext4::BabyBearExt4 as E};
use riscv_transpiler::ir::FullUnsignedMachineDecoderConfig;

// Keep the real cached/no-cache decoder shapes, but use a small public program
// and setup domain for these setup/forward-relation regressions. No artifact is
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

fn check_decoder_padding(cached: bool, tagged: bool, supports_pc_zero: bool) {
    // Also crosses the accelerated forward path's minimum size on AVX-512 hosts.
    let trace_len = 1 << 12;
    let circuit = artifact(cached, tagged, trace_len);
    // Use the real bytecode preprocessor, including its NOP/default distinction:
    // a valid PC-zero instruction still has an actual decoded operation flag.
    let family: Box<dyn OpcodeFamilyDecoder> = Box::new(AddSubLuiAuipcMopDecoder);
    let binary = [
        if supports_pc_zero {
            0x0000_0013
        } else {
            0x0000_006f
        },
        0x0040_8093, // ADDI x1, x1, 4
        0x0000_006f, // JAL x0, 0 belongs to another family
        0x0071_81b3, // ADD x3, x3, x7
    ];
    let decoder = cs::gkr_circuits::decoder_trait::preprocess_bytecode::<
        F,
        FullUnsignedMachineDecoderConfig,
        Global,
    >(&binary, 4, &family, &[]);
    assert_eq!(decoder[0].is_some(), supports_pc_zero);
    assert!(decoder[1].is_some() && decoder[2].is_none() && decoder[3].is_some());
    let mut driver = TableDriver::<F>::new();
    if tagged {
        driver.materialize_table::<9>(TableType::ZeroEntry);
    }
    let setup = GKRSetup::construct(&driver, &decoder, trace_len, &circuit);
    let expected = materialize_flattened_decoder_table_with_bitmask::<F>(
        &decoder,
        &circuit.decode_table_columns_mask,
    );
    let offset = circuit.offset_for_decoder_table;
    let width = circuit.generic_lookup_tables_width;
    for (i, row) in expected.iter().enumerate() {
        for (column, value) in row.iter().enumerate() {
            assert_eq!(setup.hypercube_evals[column][offset + i], *value);
        }
    }
    assert!(F::MINUS_ONE.as_u32_reduced() as u64 > u16::MAX as u64);
    for row in circuit.total_tables_size..trace_len {
        if tagged {
            // Preserve the generic zero-entry table and its disabled queries;
            // the decoder discriminator excludes this tail from active queries.
            assert!(setup
                .hypercube_evals
                .iter()
                .all(|column| column[row].is_zero()));
            assert_ne!(
                setup.hypercube_evals[width - 1][row],
                F::from_u32_unchecked(TableType::Decoder as u32)
            );
        } else {
            assert!(setup
                .hypercube_evals
                .iter()
                .all(|column| column[row] == F::MINUS_ONE));
        }
    }
    // A default all-zero query has no real decoded operation flag, even when
    // the program contains a valid instruction at PC zero.
    let decoder_zero_query_matches = (0..trace_len)
        .filter(|&row| {
            setup
                .hypercube_evals
                .iter()
                .enumerate()
                .all(|(column, values)| {
                    let query = if tagged && column == width - 1 {
                        F::from_u32_unchecked(TableType::Decoder as u32)
                    } else {
                        F::ZERO
                    };
                    values[row] == query
                })
        })
        .count();
    assert_eq!(decoder_zero_query_matches, 0);

    let worker = Worker::new_with_num_threads(1);
    let pool = GenericAllocationPool::<F, E>::new();
    let alpha = E::from_array_of_base([
        F::from_u32_unchecked(3),
        F::from_u32_unchecked(5),
        F::from_u32_unchecked(7),
        F::from_u32_unchecked(11),
    ]);
    let gamma = E::from_array_of_base([
        F::from_u32_unchecked(13),
        F::from_u32_unchecked(17),
        F::from_u32_unchecked(19),
        F::from_u32_unchecked(23),
    ]);
    let mut storage = GKRStorage { layers: vec![] };
    let (preprocessed, inactive_fill) =
        setup.preprocess_generic_lookups(&circuit, alpha, trace_len, &mut storage, &worker);
    assert_eq!(preprocessed.len(), circuit.total_tables_size);
    let powers = materialize_powers_serial_starting_with_one::<E, Global>(alpha, width);
    let compressed: Vec<E> = (0..trace_len)
        .map(|row| {
            let mut value = E::ZERO;
            for (power, column) in powers.iter().zip(&setup.hypercube_evals) {
                let mut term = *power;
                term.mul_assign_by_base(&column[row]);
                value.add_assign(&term);
            }
            value
        })
        .collect();
    assert_eq!(&*preprocessed, &compressed[..circuit.total_tables_size]);
    assert_eq!(
        inactive_fill,
        if tagged {
            let mut value = powers[width - 1];
            value.mul_assign_by_base(&F::from_u32_unchecked(TableType::Decoder as u32));
            value
        } else {
            E::ZERO
        }
    );
    if !tagged {
        let mut expected_tail = E::ZERO;
        for power in &powers {
            let mut term = *power;
            term.mul_assign_by_base(&F::MINUS_ONE);
            expected_tail.add_assign(&term);
        }
        assert!(compressed[circuit.total_tables_size..]
            .iter()
            .all(|value| *value == expected_tail));
    }

    let selected = [offset + usize::from(!supports_pc_zero), offset + 3];
    let predicate_address = GKRAddress::BaseLayerWitness(width);
    let multiplicity_address = GKRAddress::BaseLayerWitness(width + 1);
    for column in 0..width {
        let mut values = vec![F::ZERO; trace_len];
        for (row, table_row) in selected.into_iter().enumerate() {
            values[row] = setup.hypercube_evals[column][table_row];
        }
        if tagged {
            // Inactive decoder tuples still have their table discriminator.
            if column == width - 1 {
                values[2..].fill(F::from_u32_unchecked(TableType::Decoder as u32));
            }
        }
        storage.insert_base_field_at_layer(
            0,
            GKRAddress::BaseLayerWitness(column),
            BaseFieldPoly::new(values.into_boxed_slice()),
        );
    }
    let mut predicate = vec![F::ZERO; trace_len];
    predicate[..2].fill(F::ONE);
    let mut multiplicity = vec![F::ZERO; trace_len];
    for table_row in selected {
        multiplicity[table_row] = F::ONE;
    }
    storage.insert_base_field_at_layer(
        0,
        predicate_address,
        BaseFieldPoly::new(predicate.into_boxed_slice()),
    );
    storage.insert_base_field_at_layer(
        0,
        multiplicity_address,
        BaseFieldPoly::new(multiplicity.into_boxed_slice()),
    );
    let relation = VectorLookupRelation {
        columns: (0..width)
            .map(|column| LinearRelation::from_single_input(GKRAddress::BaseLayerWitness(column)))
            .collect(),
        lookup_set_index: DECODER_LOOKUP_FORMAL_SET_INDEX,
    };
    let mut witness = GKRFullWitnessTrace::new(trace_len, 0, 0, 0, 1, 0, 0, Global, Global);
    witness.generic_lookup_mapping[0].resize(trace_len, 0);
    for (row, table_row) in selected.into_iter().enumerate() {
        witness.generic_lookup_mapping[0][row] = table_row as u32;
    }
    let input = materialize_vector_lookup_input(
        &relation,
        &storage,
        &mut witness,
        trace_len,
        &preprocessed,
        alpha,
        inactive_fill,
        offset as u32,
        predicate_address,
        &pool,
        &worker,
    );
    assert_eq!(input[0], compressed[selected[0]]);
    assert_eq!(input[1], compressed[selected[1]]);
    assert!(input[2..].iter().all(|value| *value == inactive_fill));

    let outputs = [
        GKRAddress::InnerLayer {
            layer: 1,
            offset: 0,
        },
        GKRAddress::InnerLayer {
            layer: 1,
            offset: 1,
        },
    ];
    materialize_decoder_lookup_minus_setup(
        predicate_address,
        &relation,
        multiplicity_address,
        outputs,
        &mut storage,
        &mut witness,
        trace_len,
        &preprocessed,
        alpha,
        gamma,
        inactive_fill,
        compressed[trace_len - 1],
        offset as u32,
        &pool,
        &worker,
    );
    let numerator = storage.get_ext_poly(outputs[0]);
    let denominator = storage.get_ext_poly(outputs[1]);
    let mut sum = E::ZERO;
    for row in 0..trace_len {
        let mut query = if row < 2 {
            compressed[selected[row]]
        } else {
            inactive_fill
        };
        query.add_assign(&gamma);
        let mut table = compressed[row];
        table.add_assign(&gamma);
        let mut expected_num = if row < 2 { table } else { E::ZERO };
        if selected.contains(&row) {
            expected_num.sub_assign(&query);
        }
        let mut expected_den = query;
        expected_den.mul_assign(&table);
        assert_eq!(numerator[row], expected_num, "numerator row {row}");
        assert_eq!(denominator[row], expected_den, "denominator row {row}");
        let mut fraction = numerator[row];
        fraction.mul_assign(&denominator[row].inverse().unwrap());
        sum.add_assign(&fraction);
    }
    assert_eq!(
        sum,
        E::ZERO,
        "valid decoder lookups must cancel actual setup multiplicities"
    );
}

#[test]
fn decoder_padding_matches_committed_setup_in_forward_relations() {
    for cached in [false, true] {
        for tagged in [false, true] {
            for supports_pc_zero in [false, true] {
                check_decoder_padding(cached, tagged, supports_pc_zero);
            }
        }
    }
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
    // Independently retain the previous padded-row assembly as the reference
    // for direct stored-row materialization, including every zero/tag column.
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
