mod coverage;
mod fixture;

use super::prepare_lookup_relations;
use cpu_execution_prover::test_support::with_l1_wrap_fixture;
use execution_prover_model::allocator::CpuTraceAllocator;
use execution_prover_model::trace::{
    ChunkedTraceHolder, InitsAndTeardownsTraceHost, PAGE_SIZE_LOG2,
};
use field::Proth120;
use gpu_core::primitives::device_structures::{DeviceMatrix, DeviceMatrixImpl};
use std::time::Instant;

#[test]
fn cpu_fixture_contract() {
    let reference = fixture::manifest_and_identities();
    let circuit = unified_reduced_machine_proth120::circuit_artifact();
    coverage::validate_metadata(&reference, &circuit);
    let (bin, text, nd_words) = fixture::wrap_inputs(&reference);
    assert!(
        !bin.is_empty() && !text.is_empty() && !nd_words.is_empty(),
        "Proth120 witness fixture wrap inputs"
    );
    let value = Proth120::new(1);
    assert!(
        value.raw_u128_value() > u64::MAX as u128,
        "Proth120 fixture typed u128 exercise"
    );
    let json = serde_json::to_string(&value).expect("Proth120 fixture typed u128 encoding");
    let decoded: Proth120 =
        serde_json::from_str(&json).expect("Proth120 fixture typed u128 decoding");
    assert_eq!(
        value.raw_u128_value(),
        decoded.raw_u128_value(),
        "Proth120 fixture typed u128 bytes"
    );

    let empty: InitsAndTeardownsTraceHost<CpuTraceAllocator> = InitsAndTeardownsTraceHost {
        page_indices: ChunkedTraceHolder { chunks: Vec::new() },
        values_packed: ChunkedTraceHolder { chunks: Vec::new() },
        timestamps_packed: ChunkedTraceHolder { chunks: Vec::new() },
        top_bits: vec![0, 1],
    };
    let teardown_sets =
        cpu_execution_prover::test_support::expand_inits_and_teardowns(&empty, 2, PAGE_SIZE_LOG2);
    assert_eq!(teardown_sets.len(), 2, "Proth120 fixture CPU teardown sets");
    for (timestamps, values) in teardown_sets {
        for column in timestamps.into_iter().chain(values) {
            assert_eq!(
                column.len(),
                1 << PAGE_SIZE_LOG2,
                "Proth120 fixture CPU teardown rows"
            );
            assert!(
                column.iter().all(|&value| value == Proth120::new(0)),
                "Proth120 fixture CPU empty teardown"
            );
        }
    }

    let actual = [Proth120::new(0), Proth120::new(1), Proth120::new(2)];
    let mut copied_cpu_column = actual.to_vec();
    copied_cpu_column[1] = Proth120::new(0);
    let mismatch = copied_cpu_column
        .iter()
        .copied()
        .zip(actual)
        .enumerate()
        .find_map(|(row, (expected, actual))| {
            fixture::field_cell("memory", 7, row, expected, actual.raw_u128_value()).err()
        })
        .expect("Proth120 witness comparator detects flipped CPU cell");
    assert_eq!(
        (mismatch.set.as_str(), mismatch.column, mismatch.row),
        ("memory", 7, 1),
        "Proth120 witness comparator negative-control location"
    );
    assert_eq!(
        mismatch.expected,
        format!("raw 0x{:032x}", copied_cpu_column[1].raw_u128_value())
    );
    assert_eq!(
        mismatch.actual,
        format!("raw 0x{:032x}", actual[1].raw_u128_value())
    );
}

fn vm_hwm_kib() -> u64 {
    std::fs::read_to_string("/proc/self/status")
        .expect("Proth120 witness parity /proc/self/status")
        .lines()
        .find_map(|line| line.strip_prefix("VmHWM:"))
        .and_then(|value| value.trim().strip_suffix("kB"))
        .and_then(|value| value.trim().parse().ok())
        .expect("Proth120 witness parity VmHWM")
}

fn assert_report(
    set: &str,
    column: usize,
    report: &fixture::ColumnReport,
    digest: &str,
    nonzero_rows: u64,
    edges: Option<&coverage::ColumnEdges>,
) {
    assert_eq!(
        report.digest, digest,
        "Proth120 witness committed digest {set} {column}"
    );
    assert_eq!(
        report.nonzero_rows, nonzero_rows,
        "Proth120 witness committed nonzero rows {set} {column}"
    );
    if let Some(edges) = edges {
        assert_eq!(
            report.edges.first, edges.first,
            "Proth120 witness committed first edges {set} {column}"
        );
        assert_eq!(
            report.edges.last, edges.last,
            "Proth120 witness committed last edges {set} {column}"
        );
    }
}

#[test]
#[ignore]
fn l1_wrap_witness_cpu_parity() {
    let start = Instant::now();
    let reference = fixture::manifest_and_identities();
    let circuit = unified_reduced_machine_proth120::circuit_artifact();
    coverage::validate_metadata(&reference, &circuit);
    drop(circuit);
    let (bin, text, nd_words) = fixture::wrap_inputs(&reference);
    let fixture::Reference {
        checkpoint,
        bundle,
        digests,
        edges,
        coverage,
        ..
    } = reference;
    drop(checkpoint);
    let commitment_mode = bundle.commitment_mode;
    let top_bits = bundle.proof.inits_and_teardowns_top_bits.clone();
    drop(bundle);
    let t_reference = start.elapsed();
    let call = Instant::now();
    let summary = with_l1_wrap_fixture(
        fixture::configuration(),
        bin,
        text,
        nd_words,
        None,
        move |fixture| {
            let t_capture = call.elapsed();
            assert_eq!(
                fixture.commitment_mode, commitment_mode,
                "Proth120 witness parity commitment mode"
            );
            assert_eq!(
                fixture.inits_and_teardowns.top_bits, top_bits,
                "Proth120 witness parity inits/teardowns windows"
            );
            let circuit = &fixture.setup.circuit;
            let rows = circuit.trace_len;

            let gpu_start = Instant::now();
            let context = fixture::context().unwrap();
            let relations = prepare_lookup_relations(circuit, &context).unwrap();
            let mut buffers = fixture::DeviceBuffers::new(circuit, &context).unwrap();
            let (inputs, transfer) = fixture::upload(&fixture, &context).unwrap();
            fixture::run_witness(&inputs, &relations, &mut buffers, &context).unwrap();
            let t_gpu = gpu_start.elapsed();
            drop(transfer);
            drop(relations);

            let cpu_start = Instant::now();
            let cpu = fixture.evaluate_witness();
            let t_cpu = cpu_start.elapsed();

            let compare_start = Instant::now();
            let mut comparator = fixture::Comparator::new();
            let field_sets = [
                (
                    "memory",
                    &buffers.memory,
                    &cpu.column_major_memory_trace,
                    &digests.memory,
                    &coverage.nonzero_rows.memory,
                    &edges.memory,
                ),
                (
                    "witness",
                    &buffers.witness,
                    &cpu.column_major_witness_trace,
                    &digests.witness,
                    &coverage.nonzero_rows.witness,
                    &edges.witness,
                ),
                (
                    "scratch",
                    &buffers.scratch,
                    &cpu.column_major_scratch_space_trace,
                    &digests.scratch,
                    &coverage.nonzero_rows.scratch,
                    &edges.scratch,
                ),
            ];
            for (set, device, expected, digests, nonzero_rows, edges) in field_sets {
                let device = DeviceMatrix::new(device, rows);
                assert_eq!(
                    device.cols(),
                    expected.len(),
                    "Proth120 witness parity columns {set}"
                );
                for (column, expected) in expected.iter().enumerate() {
                    let report = comparator
                        .fields(
                            set,
                            column,
                            fixture::column(&device, column),
                            expected,
                            &context,
                        )
                        .unwrap();
                    assert_report(
                        set,
                        column,
                        &report,
                        &digests[column],
                        nonzero_rows[column],
                        Some(&edges[column]),
                    );
                }
            }
            let tables = DeviceMatrix::new(&inputs.tables, rows);
            for (column, expected) in fixture.setup.setup.hypercube_evals.iter().enumerate() {
                let report = comparator
                    .fields(
                        "setup",
                        column,
                        fixture::column(&tables, column),
                        expected.as_slice(),
                        &context,
                    )
                    .unwrap();
                assert_report(
                    "setup",
                    column,
                    &report,
                    &digests.setup[column],
                    coverage.nonzero_rows.setup[column],
                    Some(&edges.setup[column]),
                );
            }
            let generic = DeviceMatrix::new(&buffers.generic, rows);
            assert_eq!(generic.cols(), cpu.generic_lookup_mapping.len());
            for (column, expected) in cpu.generic_lookup_mapping.iter().enumerate() {
                let report = comparator
                    .mappings(
                        "generic",
                        column,
                        fixture::column(&generic, column),
                        expected,
                        false,
                        &context,
                    )
                    .unwrap();
                assert_report(
                    "generic",
                    column,
                    &report,
                    &digests.generic_lookup_mapping_u32le[column],
                    coverage.nonzero_rows.generic_lookup_mapping[column],
                    None,
                );
            }
            let range_check_16 = DeviceMatrix::new(&buffers.range_check_16, rows);
            assert_eq!(
                range_check_16.cols(),
                cpu.range_check_16_lookup_mapping.len()
            );
            for (column, expected) in cpu.range_check_16_lookup_mapping.iter().enumerate() {
                let report = comparator
                    .mappings(
                        "range_check_16",
                        column,
                        fixture::column(&range_check_16, column),
                        expected,
                        true,
                        &context,
                    )
                    .unwrap();
                assert_report(
                    "range_check_16",
                    column,
                    &report,
                    &digests.range_check_16_lookup_mapping_u16le[column],
                    coverage.nonzero_rows.range_check_16_lookup_mapping[column],
                    None,
                );
            }
            let timestamp = DeviceMatrix::new(&buffers.timestamp, rows);
            assert_eq!(
                timestamp.cols(),
                cpu.timestamp_range_check_lookup_mapping.len()
            );
            for (column, expected) in cpu.timestamp_range_check_lookup_mapping.iter().enumerate() {
                let report = comparator
                    .mappings(
                        "timestamp",
                        column,
                        fixture::column(&timestamp, column),
                        expected,
                        false,
                        &context,
                    )
                    .unwrap();
                assert_report(
                    "timestamp",
                    column,
                    &report,
                    &digests.timestamp_range_check_lookup_mapping_u32le[column],
                    coverage.nonzero_rows.timestamp_range_check_lookup_mapping[column],
                    None,
                );
            }
            let t_compare = compare_start.elapsed();
            let allocator_peak = context.get_used_mem_peak();
            drop(cpu);
            drop(buffers);
            drop(inputs);
            drop(context);
            (t_capture, t_gpu, t_cpu, t_compare, allocator_peak)
        },
    );
    let (t_capture, t_gpu, t_cpu, t_compare, allocator_peak) = summary;
    println!(
        "Proth120 witness parity: reference {t_reference:?}, capture {t_capture:?}, gpu {t_gpu:?}, \
         cpu {t_cpu:?}, compare {t_compare:?}, total {:?}, VmHWM {} KiB, allocator peak {allocator_peak} B",
        start.elapsed(),
        vm_hwm_kib(),
    );
}
