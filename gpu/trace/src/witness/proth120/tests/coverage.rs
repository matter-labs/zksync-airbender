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
    assert_eq!(rows, 1 << 22, "Proth120 witness fixture production rows");
    assert_eq!(
        reference.digests.trace_len_log2, 22,
        "Proth120 witness digest trace length"
    );
    assert_eq!(
        reference.edges.trace_len_log2, 22,
        "Proth120 witness edges trace length"
    );
    assert_eq!(
        reference.coverage.trace_len_log2, 22,
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
