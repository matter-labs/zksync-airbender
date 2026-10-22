use cs::definitions::GKRAddress;
use cs::gkr_compiler::GKRCircuitArtifact;
use field::Proth120;
use serde::Deserialize;
use std::ops::Range;

use super::fixture::Reference;

#[derive(Deserialize)]
pub(super) struct WitnessDigests {
    pub(super) memory: Vec<String>,
    pub(super) witness: Vec<String>,
    pub(super) setup: Vec<String>,
    pub(super) trace_len_log2: u32,
    pub(super) scratch: Vec<String>,
    pub(super) generic_lookup_mapping_u32le: Vec<String>,
    pub(super) range_check_16_lookup_mapping_u16le: Vec<String>,
    pub(super) timestamp_range_check_lookup_mapping_u32le: Vec<String>,
}

#[derive(Deserialize)]
pub(super) struct ColumnEdges {
    pub(super) first: Vec<String>,
    pub(super) last: Vec<String>,
}

#[derive(Deserialize)]
pub(super) struct WitnessEdges {
    pub(super) trace_len_log2: u32,
    pub(super) edge_rows: usize,
    pub(super) memory: Vec<ColumnEdges>,
    pub(super) witness: Vec<ColumnEdges>,
    pub(super) setup: Vec<ColumnEdges>,
    pub(super) scratch: Vec<ColumnEdges>,
}

#[derive(Deserialize)]
pub(super) struct PerSet<T> {
    pub(super) memory: Vec<T>,
    pub(super) witness: Vec<T>,
    pub(super) setup: Vec<T>,
    pub(super) scratch: Vec<T>,
    pub(super) generic_lookup_mapping: Vec<T>,
    pub(super) range_check_16_lookup_mapping: Vec<T>,
    pub(super) timestamp_range_check_lookup_mapping: Vec<T>,
}

#[derive(Deserialize)]
pub(super) struct SelectorCoverage {
    pub(super) address: GKRAddress,
    pub(super) active_rows: u64,
}

#[derive(Deserialize)]
pub(super) struct MultiplicityColumns {
    pub(super) range_check_16: Range<usize>,
    pub(super) timestamp_range_check: Range<usize>,
    pub(super) generic_lookup: Range<usize>,
}

#[derive(Deserialize)]
pub(super) struct WitnessCoverage {
    pub(super) trace_len_log2: u32,
    pub(super) execute_column: usize,
    pub(super) rows_traced: u64,
    pub(super) nonzero_rows: PerSet<u64>,
    pub(super) all_zero_columns: PerSet<usize>,
    pub(super) circuit_family_mask_bits: Vec<SelectorCoverage>,
    pub(super) zero_count_selectors: Vec<GKRAddress>,
    pub(super) multiplicity_columns: MultiplicityColumns,
    pub(super) teardown_sets: Vec<([GKRAddress; 2], [GKRAddress; 2])>,
}

pub(super) const SYNTHETIC_RAM_VALUE: u32 = 0x12345678;
pub(super) const SYNTHETIC_TIMESTAMP: u64 = (1 << 19) + 4;
pub(super) const SYNTHETIC_ADDMOD_X: u32 = u32::MAX;
pub(super) const SYNTHETIC_ADDMOD_Y: u32 = u32::MAX;
pub(super) const SYNTHETIC_DELEGATION_FAMILY: u32 = 1 << 7;

pub(super) fn validate_metadata(reference: &Reference, circuit: &GKRCircuitArtifact<Proth120>) {
    let rows = circuit.trace_len;
    assert_eq!(rows, 1 << 21, "Proth120 witness fixture production rows");
    assert_eq!(
        reference.digests.trace_len_log2, 21,
        "Proth120 witness digest trace length"
    );
    assert_eq!(
        reference.edges.trace_len_log2, 21,
        "Proth120 witness edges trace length"
    );
    assert_eq!(
        reference.coverage.trace_len_log2, 21,
        "Proth120 witness coverage trace length"
    );
    assert_eq!(reference.edges.edge_rows, 64, "Proth120 witness edge count");
    for (set, actual, expected) in [
        (
            "memory",
            reference.digests.memory.len(),
            circuit.memory_layout.total_width,
        ),
        (
            "witness",
            reference.digests.witness.len(),
            circuit.witness_layout.total_width,
        ),
        (
            "setup",
            reference.digests.setup.len(),
            circuit.generic_lookup_tables_width,
        ),
        (
            "scratch",
            reference.digests.scratch.len(),
            circuit.scratch_space_size,
        ),
        (
            "generic mapping",
            reference.digests.generic_lookup_mapping_u32le.len(),
            circuit.generic_lookups.len() + usize::from(circuit.has_decoder_lookup),
        ),
        (
            "RC16 mapping",
            reference.digests.range_check_16_lookup_mapping_u16le.len(),
            circuit.range_check_16_lookup_expressions.len(),
        ),
        (
            "timestamp mapping",
            reference
                .digests
                .timestamp_range_check_lookup_mapping_u32le
                .len(),
            circuit.timestamp_range_check_lookup_expressions.len(),
        ),
    ] {
        assert_eq!(actual, expected, "Proth120 witness fixture columns {set}");
    }
    for (set, edges, expected) in [
        (
            "memory",
            &reference.edges.memory,
            circuit.memory_layout.total_width,
        ),
        (
            "witness",
            &reference.edges.witness,
            circuit.witness_layout.total_width,
        ),
        (
            "setup",
            &reference.edges.setup,
            circuit.generic_lookup_tables_width,
        ),
        (
            "scratch",
            &reference.edges.scratch,
            circuit.scratch_space_size,
        ),
    ] {
        assert_eq!(
            edges.len(),
            expected,
            "Proth120 witness fixture edge columns {set}"
        );
        for column in edges {
            assert_eq!(
                column.first.len(),
                64,
                "Proth120 witness fixture first edges {set}"
            );
            assert_eq!(
                column.last.len(),
                64,
                "Proth120 witness fixture last edges {set}"
            );
            for value in column.first.iter().chain(&column.last) {
                assert_eq!(value.len(), 34, "Proth120 witness natural edge width");
                let value = u128::from_str_radix(
                    value
                        .strip_prefix("0x")
                        .expect("Proth120 witness natural edge prefix"),
                    16,
                )
                .expect("Proth120 witness natural edge encoding");
                assert!(
                    value < Proth120::ORDER,
                    "Proth120 witness natural edge field range"
                );
            }
        }
    }
    for (set, counts, zeros, expected) in [
        (
            "memory",
            &reference.coverage.nonzero_rows.memory,
            &reference.coverage.all_zero_columns.memory,
            circuit.memory_layout.total_width,
        ),
        (
            "witness",
            &reference.coverage.nonzero_rows.witness,
            &reference.coverage.all_zero_columns.witness,
            circuit.witness_layout.total_width,
        ),
        (
            "setup",
            &reference.coverage.nonzero_rows.setup,
            &reference.coverage.all_zero_columns.setup,
            circuit.generic_lookup_tables_width,
        ),
        (
            "scratch",
            &reference.coverage.nonzero_rows.scratch,
            &reference.coverage.all_zero_columns.scratch,
            circuit.scratch_space_size,
        ),
        (
            "generic mapping",
            &reference.coverage.nonzero_rows.generic_lookup_mapping,
            &reference.coverage.all_zero_columns.generic_lookup_mapping,
            circuit.generic_lookups.len() + usize::from(circuit.has_decoder_lookup),
        ),
        (
            "RC16 mapping",
            &reference
                .coverage
                .nonzero_rows
                .range_check_16_lookup_mapping,
            &reference
                .coverage
                .all_zero_columns
                .range_check_16_lookup_mapping,
            circuit.range_check_16_lookup_expressions.len(),
        ),
        (
            "timestamp mapping",
            &reference
                .coverage
                .nonzero_rows
                .timestamp_range_check_lookup_mapping,
            &reference
                .coverage
                .all_zero_columns
                .timestamp_range_check_lookup_mapping,
            circuit.timestamp_range_check_lookup_expressions.len(),
        ),
    ] {
        assert_eq!(
            counts.len(),
            expected,
            "Proth120 witness coverage columns {set}"
        );
        assert!(
            counts.iter().all(|&count| count <= rows as u64),
            "Proth120 witness coverage row bounds {set}"
        );
        let actual_zeros: Vec<_> = counts
            .iter()
            .enumerate()
            .filter_map(|(column, &count)| (count == 0).then_some(column))
            .collect();
        assert_eq!(
            &actual_zeros, zeros,
            "Proth120 witness coverage zero columns {set}"
        );
    }
    assert!(
        reference.coverage.rows_traced <= rows as u64,
        "Proth120 witness fixture traced rows"
    );
    assert_eq!(
        reference.coverage.teardown_sets, circuit.memory_layout.teardown_sets,
        "Proth120 witness fixture teardown columns"
    );
    assert_eq!(
        reference.coverage.multiplicity_columns.range_check_16,
        circuit
            .witness_layout
            .multiplicities_columns_for_range_check_16,
        "Proth120 witness fixture RC16 multiplicity columns"
    );
    assert_eq!(
        reference
            .coverage
            .multiplicity_columns
            .timestamp_range_check,
        circuit
            .witness_layout
            .multiplicities_columns_for_timestamp_range_check,
        "Proth120 witness fixture timestamp multiplicity columns"
    );
    assert_eq!(
        reference.coverage.multiplicity_columns.generic_lookup,
        circuit
            .witness_layout
            .multiplicities_columns_for_generic_lookup,
        "Proth120 witness fixture generic multiplicity columns"
    );
    for (name, mapping_columns, active_counts_len) in [
        (
            "generic",
            circuit.generic_lookups.len() + usize::from(circuit.has_decoder_lookup),
            circuit.total_tables_size,
        ),
        (
            "RC16",
            circuit.range_check_16_lookup_expressions.len(),
            1 << 16,
        ),
        (
            "timestamp",
            circuit.timestamp_range_check_lookup_expressions.len(),
            1 << common_constants::TIMESTAMP_COLUMNS_NUM_BITS,
        ),
    ] {
        assert!(
            mapping_columns * rows < u32::MAX as usize,
            "Proth120 witness fixture counter sum {name}"
        );
        assert!(
            active_counts_len * 8 <= u32::MAX as usize,
            "Proth120 witness fixture counter shards {name}"
        );
        assert!(
            active_counts_len <= rows,
            "Proth120 witness fixture counter output {name}"
        );
    }
    assert_eq!(
        SYNTHETIC_RAM_VALUE & 0xffff,
        0x5678,
        "Proth120 synthetic teardown low"
    );
    assert_eq!(
        SYNTHETIC_RAM_VALUE >> 16,
        0x1234,
        "Proth120 synthetic teardown high"
    );
    assert_eq!(
        SYNTHETIC_TIMESTAMP >> 19,
        1,
        "Proth120 synthetic timestamp high"
    );
    assert_eq!(
        (SYNTHETIC_ADDMOD_X as u64 + SYNTHETIC_ADDMOD_Y as u64)
            / field::baby_bear::base::BabyBearField::ORDER as u64,
        4,
        "Proth120 synthetic ADDMOD quotient"
    );
    assert_eq!(
        (SYNTHETIC_ADDMOD_X as u64 + SYNTHETIC_ADDMOD_Y as u64)
            % field::baby_bear::base::BabyBearField::ORDER as u64,
        536870906,
        "Proth120 synthetic ADDMOD output"
    );
    assert_eq!(
        SYNTHETIC_DELEGATION_FAMILY, 128,
        "Proth120 synthetic delegation selector"
    );
}

pub(super) fn validate_selectors(reference: &Reference, circuit: &GKRCircuitArtifact<Proth120>) {
    let decoder = circuit
        .memory_layout
        .decoder_input
        .as_ref()
        .expect("Proth120 selector decoder");
    assert_eq!(
        reference.coverage.execute_column,
        circuit
            .memory_layout
            .machine_state
            .as_ref()
            .expect("Proth120 selector machine state")
            .execute,
        "Proth120 selector execute column"
    );
    assert_eq!(
        reference.coverage.circuit_family_mask_bits.len(),
        decoder.circuit_family_mask_bits.len(),
        "Proth120 selector count"
    );
    for (selector, &address) in reference
        .coverage
        .circuit_family_mask_bits
        .iter()
        .zip(decoder.circuit_family_mask_bits.iter())
    {
        assert_eq!(selector.address, address, "Proth120 selector address");
        assert!(
            selector.active_rows <= reference.coverage.rows_traced,
            "Proth120 selector active rows"
        );
    }
    let zeros: Vec<_> = reference
        .coverage
        .circuit_family_mask_bits
        .iter()
        .filter(|selector| selector.active_rows == 0)
        .map(|selector| selector.address)
        .collect();
    assert_eq!(
        zeros, reference.coverage.zero_count_selectors,
        "Proth120 zero-count selectors"
    );
    assert!(
        zeros.contains(&GKRAddress::BaseLayerWitness(12)),
        "Proth120 synthetic delegation reference-zero selector"
    );
}

pub(super) fn synthetic_rows() -> (
    Vec<riscv_transpiler::witness::UnifiedOpcodeTracingDataWithTimestamp>,
    Vec<Option<cs::gkr_circuits::decoder_trait::ExecutorFamilyDecoderData>>,
    execution_prover_model::trace::InitsAndTeardownsTraceHost<
        execution_prover_model::allocator::CpuTraceAllocator,
    >,
) {
    use common_constants::TimestampData;
    use cs::gkr_circuits::decoder_trait::ExecutorFamilyDecoderData;
    use execution_prover_model::allocator::CpuTraceAllocator;
    use execution_prover_model::trace::{
        ChunkedTraceHolder, InitsAndTeardownsTraceHost, PAGE_SIZE_LOG2,
    };
    use riscv_transpiler::witness::{
        NonMemoryOpcodeTracingData, NonMemoryOpcodeTracingDataWithTimestamp,
        UnifiedOpcodeTracingDataWithTimestamp,
    };
    use std::sync::Arc;
    fn chunk<T: Copy>(values: &[T]) -> ChunkedTraceHolder<T, CpuTraceAllocator> {
        let mut data = Vec::with_capacity_in(
            values.len(),
            CpuTraceAllocator::new(std::mem::size_of_val(values)),
        );
        data.extend_from_slice(values);
        ChunkedTraceHolder {
            chunks: vec![Arc::new(data)],
        }
    }
    let rows = vec![
        UnifiedOpcodeTracingDataWithTimestamp::NonMem(NonMemoryOpcodeTracingDataWithTimestamp {
            opcode_data: NonMemoryOpcodeTracingData {
                initial_pc: 0,
                new_pc: 4,
                rs1_value: SYNTHETIC_ADDMOD_X,
                rs2_value: SYNTHETIC_ADDMOD_Y,
                rd_value: 536870906,
                ..Default::default()
            },
            cycle_timestamp: TimestampData::from_scalar(4),
            ..Default::default()
        }),
        UnifiedOpcodeTracingDataWithTimestamp::NonMem(NonMemoryOpcodeTracingDataWithTimestamp {
            opcode_data: NonMemoryOpcodeTracingData {
                initial_pc: 4,
                new_pc: 8,
                ..Default::default()
            },
            cycle_timestamp: TimestampData::from_scalar(8),
            ..Default::default()
        }),
    ];
    let decoder = vec![
        Some(ExecutorFamilyDecoderData {
            rs1_index: 1,
            rs2_index: 2,
            rd_index: 3,
            opcode_family_bits: 1 << 3,
            funct3: Some(0),
            ..Default::default()
        }),
        Some(ExecutorFamilyDecoderData {
            rs1_index: 1,
            opcode_family_bits: SYNTHETIC_DELEGATION_FAMILY,
            funct3: Some(0),
            ..Default::default()
        }),
    ];
    let page_rows = 1 << PAGE_SIZE_LOG2;
    let inits = InitsAndTeardownsTraceHost {
        page_indices: chunk(&[0]),
        values_packed: chunk(&vec![SYNTHETIC_RAM_VALUE; page_rows]),
        timestamps_packed: chunk(&vec![SYNTHETIC_TIMESTAMP; page_rows]),
        top_bits: vec![0, 1],
    };
    (rows, decoder, inits)
}

pub(super) fn standalone_columns(
    circuit: &GKRCircuitArtifact<Proth120>,
) -> (Vec<usize>, Vec<usize>) {
    use std::collections::BTreeSet;
    let decoder = circuit
        .memory_layout
        .decoder_input
        .as_ref()
        .expect("Proth120 standalone decoder");
    let mut fixed = BTreeSet::new();
    for address in [decoder.rs2_index, decoder.rd_index]
        .into_iter()
        .chain(decoder.circuit_family_mask_bits.iter().copied())
        .chain(
            circuit
                .aux_layout_data
                .shuffle_ram_timestamp_comparison_aux_vars
                .iter()
                .flatten()
                .map(|set| set.intermediate_borrow),
        )
    {
        if let GKRAddress::BaseLayerWitness(column) = address {
            fixed.insert(column);
        }
    }
    if !decoder.decoder_witness_is_in_memory {
        fixed.extend(decoder.imm);
        fixed.extend(decoder.funct3);
    }
    let source = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../circuit_defs/unrolled_circuits/unified_reduced_machine_proth120/generated/witness_generation_fn.cuh"));
    let mut generated = BTreeSet::new();
    for line in source.lines().filter(|line| {
        line.starts_with("SET_WITNESS_PLACE(") || line.starts_with("SET_WITNESS_PLACE_OR_ZERO(")
    }) {
        let column = line
            .split_once('(')
            .unwrap()
            .1
            .split_once(',')
            .unwrap()
            .0
            .parse::<usize>()
            .expect("Proth120 standalone SSA target");
        assert!(
            column
                < circuit
                    .witness_layout
                    .multiplicities_columns_for_range_check_16
                    .start,
            "Proth120 standalone SSA multiplicity target"
        );
        generated.insert(column);
    }
    assert!(!generated.is_empty(), "Proth120 standalone SSA targets");
    assert!(
        fixed.is_disjoint(&generated),
        "Proth120 standalone fixed inputs are not SSA targets"
    );
    (fixed.into_iter().collect(), generated.into_iter().collect())
}
