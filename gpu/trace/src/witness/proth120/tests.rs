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

use super::fused::pr_witness_probe;
use super::relations::{Proth120LinearRelation, Proth120LinearTerm, Proth120LookupExpressions};
use crate::witness::Address;
use cs::definitions::gkr::{LinearRelation, SingleColumnLookupRelation};
use cs::definitions::GKRAddress;
use cs::tables::{LookupWrapper, TableType};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart_sys::CudaError;
use field::Field;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_structures::DeviceMatrixMut;
use gpu_core::primitives::static_host::alloc_static_pinned_box_from_slice;
use gpu_prover_context::{ProverContext, ProverContextConfig};
use std::mem::{align_of, size_of};

fn runtime_context() -> ProverContext {
    ProverContext::new(&ProverContextConfig {
        allocator_block_log_size: 20,
        device_allocation_blocks_count: Some(64),
        host_allocator_block_log_size: 13,
        host_allocator_blocks_count: 64,
        ..Default::default()
    })
    .unwrap()
}

fn upload_slice<T: Copy>(values: &[T], context: &ProverContext) -> DeviceAllocation<T> {
    let mut device = context
        .alloc(values.len(), AllocationPlacement::BestFit)
        .unwrap();
    if !values.is_empty() {
        let pinned = alloc_static_pinned_box_from_slice(values).unwrap();
        memory_copy_async(&mut device, pinned.as_ref(), context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
    }
    device
}

fn read_slice<T: Copy + Default + Send + Sync + 'static>(
    device: &DeviceSlice<T>,
    context: &ProverContext,
) -> Vec<T> {
    assert!(
        size_of::<T>() * device.len() <= 64 << 20,
        "Proth120 runtime bounded host copy"
    );
    if device.is_empty() {
        return Vec::new();
    }
    let mut staging = unsafe { context.alloc_host_uninit_slice::<T>(device.len()) };
    memory_copy_async(&mut staging, device, context.get_exec_stream()).unwrap();
    let accessor = staging.get_accessor();
    let owned = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
    let output = std::sync::Arc::clone(&owned);
    let mut callbacks = gpu_core::primitives::callbacks::Callbacks::new();
    callbacks
        .schedule(
            move || {
                output
                    .lock()
                    .unwrap()
                    .extend_from_slice(unsafe { accessor.get() });
            },
            context.get_exec_stream(),
        )
        .unwrap();
    drop(staging);
    context.get_exec_stream().synchronize().unwrap();
    drop(callbacks);
    std::sync::Arc::try_unwrap(owned)
        .unwrap_or_else(|_| panic!("Proth120 runtime callback ownership"))
        .into_inner()
        .unwrap()
}

fn probe(
    op: u32,
    input: &[Proth120],
    words: &[u32],
    table_type: u32,
    relation: Proth120LookupExpressions,
    count: usize,
    output_len: usize,
    context: &ProverContext,
) -> CudaResult<(Vec<Proth120>, Vec<u32>)> {
    let input = upload_slice(input, context);
    let words = upload_slice(words, context);
    let mut output = upload_slice(&vec![Proth120::new(17); output_len], context);
    let mut output_words = upload_slice(&vec![0xabababab; count], context);
    pr_witness_probe(
        op,
        &input,
        &words,
        table_type,
        relation,
        &mut output,
        &mut output_words,
        count as u32,
        context.get_exec_stream(),
    )?;
    context.get_exec_stream().synchronize()?;
    Ok((
        read_slice(&output, context),
        read_slice(&output_words, context),
    ))
}

fn random_word(state: &mut u64) -> u32 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    (*state >> 16) as u32
}

fn relation_circuit(
    relation: LinearRelation<Proth120>,
) -> cs::gkr_compiler::GKRCircuitArtifact<Proth120> {
    let mut circuit = unified_reduced_machine_proth120::circuit_artifact();
    circuit.range_check_16_lookup_expressions = vec![SingleColumnLookupRelation {
        input: relation,
        lookup_set_index: 0,
    }];
    circuit.timestamp_range_check_lookup_expressions.clear();
    circuit
}

#[test]
fn cpu_relations_abi_pins() {
    assert_eq!((size_of::<Address>(), align_of::<Address>()), (12, 4));
    assert_eq!(
        (
            size_of::<Proth120LinearTerm>(),
            align_of::<Proth120LinearTerm>()
        ),
        (32, 16)
    );
    assert_eq!(
        (
            size_of::<Proth120LinearRelation>(),
            align_of::<Proth120LinearRelation>()
        ),
        (160, 16)
    );
    assert_eq!(
        (
            size_of::<Proth120LookupExpressions>(),
            align_of::<Proth120LookupExpressions>()
        ),
        (16, 8)
    );
    let address = Address::InnerLayer {
        offset: 0x12345678,
        layer: 0x87654321,
    };
    let words =
        unsafe { std::slice::from_raw_parts((&address as *const Address).cast::<u32>(), 3) };
    assert_eq!(
        words,
        &[2, 0x12345678, 0x87654321],
        "Proth120 Address tag/offset/layer at 0/4/8"
    );
    for (address, tag) in [
        (Address::BaseLayerWitness(0), 0),
        (Address::BaseLayerMemory(0), 1),
        (
            Address::InnerLayer {
                offset: 0,
                layer: 0,
            },
            2,
        ),
        (Address::Setup(0), 3),
        (Address::ScratchSpace(0), 4),
        (
            Address::Cached {
                offset: 0,
                layer: 0,
            },
            5,
        ),
    ] {
        assert_eq!(
            unsafe { *(&address as *const Address).cast::<u32>() },
            tag,
            "Proth120 Address discriminant"
        );
    }
}

#[test]
fn cpu_counter_bounds() {
    let circuit = unified_reduced_machine_proth120::circuit_artifact();
    for (name, columns, expected) in [
        (
            "generic",
            circuit.generic_lookups.len() + usize::from(circuit.has_decoder_lookup),
            25_165_824,
        ),
        (
            "RC16",
            circuit.range_check_16_lookup_expressions.len(),
            62_914_560,
        ),
        (
            "timestamp",
            circuit.timestamp_range_check_lookup_expressions.len(),
            33_554_432,
        ),
    ] {
        let product = circuit
            .trace_len
            .checked_mul(columns)
            .expect("Proth120 counter product");
        assert_eq!(product, expected, "Proth120 counter bound {name}");
        assert!(
            product < u32::MAX as usize,
            "Proth120 counter u32 bound {name}"
        );
    }
    coverage::validate_selectors(&fixture::manifest_and_identities(), &circuit);
    let (fixed, generated) = coverage::standalone_columns(&circuit);
    assert!(
        fixed.contains(&12) && generated.contains(&26),
        "Proth120 standalone delegation input and ADDMOD output"
    );
}

#[test]
#[cfg(not(no_cuda))]
fn runtime_contract() {
    let context = runtime_context();
    let mut circuit = unified_reduced_machine_proth120::circuit_artifact();
    circuit.range_check_16_lookup_expressions.clear();
    circuit.timestamp_range_check_lookup_expressions.clear();
    let empty = prepare_lookup_relations(&circuit, &context).unwrap();
    let relation = empty.expressions().0;
    let mut state = 0x1205_0006_0001u64;
    let mut naturals = vec![
        0,
        1,
        u32::MAX as u128,
        1u128 << 32,
        (1u128 << 32) + 7,
        Proth120::ORDER - 1,
    ];
    for _ in 0..256 {
        naturals.push(random_word(&mut state) as u128);
        let wide = ((random_word(&mut state) as u128) << 64) | random_word(&mut state) as u128;
        naturals.push(wide);
    }
    let values: Vec<_> = naturals.iter().copied().map(Proth120::new).collect();
    let narrow: Vec<_> = naturals
        .iter()
        .copied()
        .filter(|&x| x <= u32::MAX as u128)
        .map(|x| x as u32)
        .collect();
    let (actual, _) = probe(
        0,
        &[],
        &narrow,
        0,
        relation,
        narrow.len(),
        narrow.len(),
        &context,
    )
    .unwrap();
    assert_eq!(
        actual,
        narrow
            .iter()
            .map(|&x| Proth120::new(x as u128))
            .collect::<Vec<_>>(),
        "Proth120 from u32"
    );
    let (_, actual) = probe(
        1,
        &values,
        &[],
        0,
        relation,
        values.len(),
        values.len(),
        &context,
    )
    .unwrap();
    assert_eq!(
        actual,
        naturals
            .iter()
            .map(|&x| if x <= u32::MAX as u128 { x as u32 } else { 0 })
            .collect::<Vec<_>>(),
        "Proth120 computational conversion"
    );
    let bounded: Vec<_> = narrow.iter().map(|&x| Proth120::new(x as u128)).collect();
    let (_, actual) = probe(
        2,
        &bounded,
        &[],
        0,
        relation,
        narrow.len(),
        narrow.len(),
        &context,
    )
    .unwrap();
    assert_eq!(actual, narrow, "Proth120 bounded conversion");
    let (_, actual) = probe(
        3,
        &values,
        &[],
        0,
        relation,
        values.len(),
        values.len(),
        &context,
    )
    .unwrap();
    assert_eq!(
        actual,
        naturals
            .iter()
            .map(|&x| u32::from(x == 1))
            .collect::<Vec<_>>(),
        "Proth120 exact one mask"
    );
    let pairs: Vec<_> = values
        .iter()
        .enumerate()
        .flat_map(|(i, &x)| [x, if i % 2 == 0 { x } else { Proth120::new(0) }])
        .collect();
    let (_, actual) = probe(
        4,
        &pairs,
        &[],
        0,
        relation,
        values.len(),
        values.len(),
        &context,
    )
    .unwrap();
    assert_eq!(
        actual,
        pairs
            .as_chunks::<2>()
            .0
            .iter()
            .map(|pair| u32::from(pair[0] == pair[1]))
            .collect::<Vec<_>>(),
        "Proth120 equality"
    );
    let (actual, _) = probe(
        6,
        &[],
        &narrow,
        0,
        relation,
        narrow.len(),
        2 * narrow.len(),
        &context,
    )
    .unwrap();
    assert_eq!(
        actual,
        narrow
            .iter()
            .flat_map(|&x| [
                Proth120::new((x & 0xffff) as u128),
                Proth120::new((x >> 16) as u128)
            ])
            .collect::<Vec<_>>(),
        "Proth120 u32 writer"
    );
    let timestamps: Vec<_> = [
        0,
        1,
        (1u64 << 19) - 1,
        1 << 19,
        (1 << 19) + 4,
        (1 << 38) - 1,
    ]
    .into_iter()
    .chain((0..256).map(|_| ((random_word(&mut state) as u64) << 6) & ((1 << 38) - 1)))
    .collect();
    let words: Vec<_> = timestamps
        .iter()
        .flat_map(|&x| [x as u32, (x >> 32) as u32])
        .collect();
    let (actual, _) = probe(
        7,
        &[],
        &words,
        0,
        relation,
        timestamps.len(),
        2 * timestamps.len(),
        &context,
    )
    .unwrap();
    assert_eq!(
        actual,
        timestamps
            .iter()
            .flat_map(|&x| [
                Proth120::new((x & ((1 << 19) - 1)) as u128),
                Proth120::new((x >> 19) as u128)
            ])
            .collect::<Vec<_>>(),
        "Proth120 timestamp writer"
    );
    let (actual, _) = probe(
        8,
        &[],
        &narrow,
        0,
        relation,
        narrow.len(),
        narrow.len(),
        &context,
    )
    .unwrap();
    assert_eq!(
        actual,
        narrow
            .iter()
            .map(|&x| Proth120::new(u128::from(x != 0)))
            .collect::<Vec<_>>(),
        "Proth120 bool writer"
    );
    for tag in 0..3 {
        let (actual, _) = probe(
            9,
            &[],
            &narrow,
            tag,
            relation,
            narrow.len(),
            4 * narrow.len(),
            &context,
        )
        .unwrap();
        let expected: Vec<_> = narrow
            .iter()
            .flat_map(|&x| match tag {
                0 => [Proth120::new(17); 4],
                1 => [
                    Proth120::new((x & 0xffff) as u128),
                    Proth120::new((x >> 16) as u128),
                    Proth120::new(17),
                    Proth120::new(17),
                ],
                _ => std::array::from_fn(|i| Proth120::new(((x >> (8 * i)) & 255) as u128)),
            })
            .collect();
        assert_eq!(actual, expected, "Proth120 RAM writer tag {tag}");
    }
    for table_type in [
        TableType::RegIsZero,
        TableType::GetSignExtensionByte,
        TableType::Xor3,
        TableType::Xor4,
        TableType::Xor7,
        TableType::RangeCheck8x8,
        TableType::And,
        TableType::Or,
        TableType::KeccakThetaRhoDIndices,
        TableType::KeccakColumnParityIndices,
        TableType::KeccakThetaRhoControl,
        TableType::KeccakColumnParityControl,
        TableType::KeccakChi5Control,
    ] {
        let LookupWrapper::Initialized(table) = table_type.generate_table::<Proth120, 8>() else {
            panic!("Proth120 CPU table initialized");
        };
        let mut keys = Vec::new();
        let mut expected = Vec::new();
        for i in 0..128 {
            let row = &table.data[if i == 0 {
                0
            } else if i == 1 {
                table.data.len() - 1
            } else {
                random_word(&mut state) as usize % table.data.len()
            }];
            let mut key = [Proth120::new(0); 5];
            key[..table.num_key_columns].copy_from_slice(&row[..table.num_key_columns]);
            expected.push(table.lookup_values_and_get_index::<15>(&key).0 as u32);
            keys.extend(key);
        }
        let (_, actual) = probe(
            5,
            &keys,
            &[],
            table_type as u32,
            relation,
            expected.len(),
            expected.len(),
            &context,
        )
        .unwrap();
        assert_eq!(actual, expected, "Proth120 CPU table index {table_type:?}");
    }
    let rom = cs::tables::create_table_for_word_aligned_rom_image::<Proth120, 1>(
        &[0x12345678, u32::MAX],
        TableType::RomRead as u32,
    );
    let mut keys = Vec::new();
    let mut expected = Vec::new();
    for i in 0..128 {
        let pc = if i == 0 {
            0
        } else if i == 1 {
            (1 << 17) - 4
        } else {
            random_word(&mut state) & ((1 << 17) - 4)
        };
        let key = [
            Proth120::new(pc as u128),
            Proth120::new(0),
            Proth120::new(0),
            Proth120::new(0),
            Proth120::new(0),
        ];
        expected.push(rom.lookup_values_and_get_index::<15>(&key).0 as u32);
        keys.extend(key);
    }
    for table_type in [TableType::RomRead, TableType::AlignedRomRead] {
        let (_, actual) = probe(
            5,
            &keys,
            &[],
            table_type as u32,
            relation,
            expected.len(),
            expected.len(),
            &context,
        )
        .unwrap();
        assert_eq!(actual, expected, "Proth120 CPU ROM index {table_type:?}");
    }
    let input: Vec<_> = (0..128 * 12)
        .map(|_| {
            Proth120::new(
                ((random_word(&mut state) as u128) << 64) | random_word(&mut state) as u128,
            )
        })
        .collect();
    let addresses = [
        GKRAddress::BaseLayerMemory(0),
        GKRAddress::BaseLayerWitness(1),
        GKRAddress::ScratchSpace(2),
        GKRAddress::BaseLayerMemory(3),
    ];
    for terms in 0..=4 {
        let linear = LinearRelation {
            linear_terms: addresses[..terms]
                .iter()
                .enumerate()
                .map(|(i, &address)| (Proth120::new((1u128 << (32 * i)) + 7), address))
                .collect(),
            constant: Proth120::new(Proth120::ORDER - 1),
        };
        let circuit = relation_circuit(linear.clone());
        let owner = prepare_lookup_relations(&circuit, &context).unwrap();
        let (actual, _) = probe(
            10,
            &input,
            &[],
            0,
            owner.expressions().0,
            128,
            128,
            &context,
        )
        .unwrap();
        let expected: Vec<_> = input
            .as_chunks::<12>()
            .0
            .iter()
            .map(|row| {
                let mut result = linear.constant;
                for &(coefficient, address) in &linear.linear_terms {
                    let offset = match address {
                        GKRAddress::BaseLayerMemory(i) => i,
                        GKRAddress::BaseLayerWitness(i) => 4 + i,
                        GKRAddress::ScratchSpace(i) => 8 + i,
                        _ => unreachable!(),
                    };
                    let mut product = coefficient;
                    product.mul_assign(&row[offset]);
                    result.add_assign(&product);
                }
                result
            })
            .collect();
        assert_eq!(
            actual, expected,
            "Proth120 full-field relation {terms} terms"
        );
    }
    let circuit = relation_circuit(LinearRelation::from_single_input(
        GKRAddress::BaseLayerMemory(0),
    ));
    let owner = prepare_lookup_relations(&circuit, &context).unwrap();
    let input: Vec<_> = narrow
        .iter()
        .flat_map(|&x| {
            let mut row = [Proth120::new(0); 12];
            row[0] = Proth120::new(x as u128);
            row
        })
        .collect();
    let (_, actual) = probe(
        11,
        &input,
        &[],
        0,
        owner.expressions().0,
        narrow.len(),
        narrow.len(),
        &context,
    )
    .unwrap();
    assert_eq!(actual, narrow, "Proth120 bounded relation");
}

fn assert_trap(result: CudaResult<()>, name: &str) {
    assert!(
        matches!(
            result,
            Err(CudaError::ErrorAssert | CudaError::ErrorLaunchFailure)
        ),
        "Proth120 {name} trap: {result:?}"
    );
}

#[test]
#[cfg(not(no_cuda))]
fn runtime_bounded_key_traps() {
    let context = runtime_context();
    let mut circuit = unified_reduced_machine_proth120::circuit_artifact();
    circuit.range_check_16_lookup_expressions.clear();
    circuit.timestamp_range_check_lookup_expressions.clear();
    let owner = prepare_lookup_relations(&circuit, &context).unwrap();
    let mut input = [Proth120::new(0); 5];
    input[0] = Proth120::new((1u128 << 32) + 7);
    assert_trap(
        probe(
            5,
            &input,
            &[],
            TableType::RegIsZero as u32,
            owner.expressions().0,
            1,
            1,
            &context,
        )
        .map(|_| ()),
        "bounded table key",
    );
}

#[test]
#[cfg(not(no_cuda))]
fn runtime_bounded_relation_traps() {
    let context = runtime_context();
    let circuit = relation_circuit(LinearRelation::from_single_input(
        GKRAddress::BaseLayerMemory(0),
    ));
    let owner = prepare_lookup_relations(&circuit, &context).unwrap();
    let mut input = [Proth120::new(0); 12];
    input[0] = Proth120::new(1u128 << 32);
    assert_trap(
        probe(11, &input, &[], 0, owner.expressions().0, 1, 1, &context).map(|_| ()),
        "bounded relation",
    );
}

#[test]
#[cfg(not(no_cuda))]
fn multiplicity_contract() {
    let context = runtime_context();
    let rows = 2048;
    let active = 257;
    let mut state = 0x1205_0006_0002u64;
    let random: Vec<_> = (0..3 * rows)
        .map(|i| {
            if i % 7 == 0 {
                u32::MAX
            } else {
                random_word(&mut state) % active as u32
            }
        })
        .collect();
    let mut boundaries = vec![u32::MAX; 3 * rows];
    for i in [
        0,
        31,
        32,
        63,
        64,
        127,
        128,
        rows - 1,
        rows,
        2 * rows - 1,
        2 * rows,
        3 * rows - 1,
    ] {
        boundaries[i] = (active - 1) as u32;
    }
    for (name, values) in [
        ("random holes", random),
        ("all equal", vec![7; 3 * rows]),
        ("shard boundaries", boundaries),
        ("empty", Vec::new()),
    ] {
        let mut mapping = upload_slice(&values, &context);
        let mut counts = upload_slice(&vec![Proth120::new(17); rows], &context);
        super::generate_lookup_multiplicities(
            &mut DeviceMatrixMut::new(&mut mapping, rows),
            &mut DeviceMatrixMut::new(&mut counts, rows),
            active,
            &context,
        )
        .unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let mut histogram = vec![0u32; rows];
        for &index in &values {
            if index != u32::MAX {
                histogram[index as usize] += 1;
            }
        }
        assert_eq!(
            read_slice(&counts, &context),
            histogram
                .into_iter()
                .map(|count| Proth120::new(count as u128))
                .collect::<Vec<_>>(),
            "Proth120 multiplicities {name}"
        );
        assert_eq!(
            read_slice(&mapping, &context),
            values
                .into_iter()
                .map(|index| if index == u32::MAX { 0 } else { index })
                .collect::<Vec<_>>(),
            "Proth120 normalized holes {name}"
        );
    }
}

#[test]
#[cfg(not(no_cuda))]
fn multiplicity_invalid_index_traps() {
    let context = runtime_context();
    let mut values = vec![u32::MAX; 128];
    values[64] = 17;
    let mut mapping = upload_slice(&values, &context);
    let mut counts = upload_slice(&vec![Proth120::new(0); 128], &context);
    let launch = super::generate_lookup_multiplicities(
        &mut DeviceMatrixMut::new(&mut mapping, 128),
        &mut DeviceMatrixMut::new(&mut counts, 128),
        17,
        &context,
    );
    assert_trap(
        launch.and_then(|_| context.get_exec_stream().synchronize()),
        "invalid multiplicity index",
    );
}

#[test]
#[ignore]
#[cfg(not(no_cuda))]
fn synthetic_rows_cpu_parity() {
    use super::fused::generate_witness_values;
    use super::{
        generate_fused_values, generate_inits_and_teardowns, generate_lookup_multiplicities,
    };
    use crate::witness::trace_unrolled::{
        ExecutorFamilyDecoderData, InitsAndTeardownsTraceDevice, UnrolledUnifiedTraceDevice,
    };
    use gpu_ops::simple::{set_by_val, set_to_ones, set_to_zero};
    use prover::gkr::witness_gen::family_circuits::evaluate_gkr_witness_for_executor_family;
    use prover::gkr::witness_gen::oracles::UnifiedRiscvCircuitOracle;
    use std::alloc::Global;

    let start = Instant::now();
    let reference = fixture::manifest_and_identities();
    let (bin, text, _) = fixture::wrap_inputs(&reference);
    let setup = unified_reduced_machine_proth120::l1_wrap_setup(&bin, &text);
    coverage::validate_selectors(&reference, &setup.circuit);
    drop(reference);
    let circuit = &setup.circuit;
    let rows = circuit.trace_len;
    assert_eq!(rows, 1 << 22, "Proth120 synthetic production rows");
    let (tracing, decoder, inits) = coverage::synthetic_rows();
    let expanded = cpu_execution_prover::test_support::expand_inits_and_teardowns(
        &inits,
        circuit.memory_layout.teardown_sets.len(),
        rows.trailing_zeros(),
    );
    let worker = worker::Worker::new_with_num_threads(8);
    let oracle = UnifiedRiscvCircuitOracle {
        inner: &tracing,
        decoder_table: &decoder,
    };
    let cpu_start = Instant::now();
    let cpu = evaluate_gkr_witness_for_executor_family::<Proth120, _, _, _>(
        circuit,
        unified_reduced_machine_proth120::witness_eval_fn,
        rows,
        &oracle,
        &setup.table_driver,
        &worker,
        Some(expanded),
        Global,
        Global,
    );
    let cpu_time = cpu_start.elapsed();
    for (name, expected, column) in [
        (
            "memory 30 teardown low",
            Proth120::new(0x5678),
            &cpu.column_major_memory_trace[30],
        ),
        (
            "memory 31 teardown high",
            Proth120::new(0x1234),
            &cpu.column_major_memory_trace[31],
        ),
        (
            "memory 33 teardown timestamp high",
            Proth120::new(1),
            &cpu.column_major_memory_trace[33],
        ),
        (
            "witness 12 delegation",
            Proth120::new(1),
            &cpu.column_major_witness_trace[12],
        ),
        (
            "witness 26 ADDMOD",
            Proth120::new(1),
            &cpu.column_major_witness_trace[26],
        ),
    ] {
        assert!(
            column.iter().any(|&value| value != Proth120::new(0)),
            "Proth120 synthetic CPU event missing: {name}"
        );
        assert!(
            column.contains(&expected),
            "Proth120 synthetic CPU event value: {name}"
        );
    }
    assert_eq!(
        cpu.column_major_witness_trace[12][1],
        Proth120::new(1),
        "Proth120 synthetic delegation row"
    );
    assert_eq!(
        cpu.column_major_witness_trace[26][0],
        Proth120::new(1),
        "Proth120 synthetic ADDMOD k_add bit 2"
    );
    println!("Proth120 synthetic evaluator-only CPU events: memory 30/31/33, witness 12/26; ADDMOD x=y=u32::MAX, output=536870906, k_add=4; delegation unreachable in L1Wrap");

    let context = fixture::context().unwrap();
    let stream = context.get_exec_stream();
    let decoder: Vec<ExecutorFamilyDecoderData> = decoder
        .into_iter()
        .map(|row| row.unwrap_or_default().into())
        .collect();
    let trace = UnrolledUnifiedTraceDevice {
        tracing_data: upload_slice(&tracing, &context),
    };
    let device_decoder = upload_slice(&decoder, &context);
    let device_inits = InitsAndTeardownsTraceDevice {
        page_indices: upload_slice(inits.page_indices.chunks[0].as_slice(), &context),
        values_packed: upload_slice(inits.values_packed.chunks[0].as_slice(), &context),
        timestamps_packed: upload_slice(inits.timestamps_packed.chunks[0].as_slice(), &context),
    };
    let mut tables = context
        .alloc(
            rows * circuit.generic_lookup_tables_width,
            AllocationPlacement::Top,
        )
        .unwrap();
    for (column, source) in setup.setup.hypercube_evals.iter().enumerate() {
        let pinned = alloc_static_pinned_box_from_slice(source.as_slice()).unwrap();
        memory_copy_async(
            &mut tables[column * rows..(column + 1) * rows],
            pinned.as_ref(),
            stream,
        )
        .unwrap();
        stream.synchronize().unwrap();
    }
    let owner = prepare_lookup_relations(circuit, &context).unwrap();
    let mut buffers = fixture::DeviceBuffers::new(circuit, &context).unwrap();
    let gpu_start = Instant::now();
    for allocation in [
        &mut buffers.memory,
        &mut buffers.witness,
        &mut buffers.scratch,
    ] {
        set_by_val(
            Proth120::new(17),
            &mut DeviceMatrixMut::new(allocation, rows),
            stream,
        )
        .unwrap();
    }
    for allocation in [
        &mut buffers.generic,
        &mut buffers.range_check_16,
        &mut buffers.timestamp,
    ] {
        set_by_val(
            0xabababab,
            &mut DeviceMatrixMut::new(allocation, rows),
            stream,
        )
        .unwrap();
    }
    generate_inits_and_teardowns(
        &circuit.memory_layout,
        rows.trailing_zeros(),
        PAGE_SIZE_LOG2,
        &device_inits,
        &mut DeviceMatrixMut::new(&mut buffers.memory, rows),
        stream,
    )
    .unwrap();
    generate_fused_values(
        circuit,
        &device_decoder,
        &trace,
        &DeviceMatrix::new(&tables, rows),
        &owner,
        &mut buffers.outputs(),
        stream,
    )
    .unwrap();
    stream.synchronize().unwrap();
    let fused_generic: Vec<Vec<u32>> = (0..circuit.generic_lookups.len())
        .map(|column| {
            read_slice(
                &buffers.generic[column * rows..(column + 1) * rows],
                &context,
            )
        })
        .collect();
    for (mapping, columns, active) in [
        (
            &mut buffers.generic,
            circuit
                .witness_layout
                .multiplicities_columns_for_generic_lookup
                .clone(),
            circuit.total_tables_size,
        ),
        (
            &mut buffers.range_check_16,
            circuit
                .witness_layout
                .multiplicities_columns_for_range_check_16
                .clone(),
            1 << 16,
        ),
        (
            &mut buffers.timestamp,
            circuit
                .witness_layout
                .multiplicities_columns_for_timestamp_range_check
                .clone(),
            1 << common_constants::TIMESTAMP_COLUMNS_NUM_BITS,
        ),
    ] {
        generate_lookup_multiplicities(
            &mut DeviceMatrixMut::new(mapping, rows),
            &mut DeviceMatrixMut::new(
                &mut buffers.witness[columns.start * rows..columns.end * rows],
                rows,
            ),
            active,
            &context,
        )
        .unwrap();
    }
    stream.synchronize().unwrap();
    let gpu_time = gpu_start.elapsed();
    let compare_start = Instant::now();
    let mut comparator = fixture::Comparator::new();
    for (name, device, expected) in [
        (
            "synthetic memory",
            &buffers.memory,
            &cpu.column_major_memory_trace,
        ),
        (
            "synthetic witness",
            &buffers.witness,
            &cpu.column_major_witness_trace,
        ),
        (
            "synthetic scratch",
            &buffers.scratch,
            &cpu.column_major_scratch_space_trace,
        ),
    ] {
        let device = DeviceMatrix::new(device, rows);
        assert_eq!(
            device.cols(),
            expected.len(),
            "Proth120 synthetic column count {name}"
        );
        for (column, expected) in expected.iter().enumerate() {
            comparator
                .fields(
                    name,
                    column,
                    fixture::column(&device, column),
                    expected,
                    &context,
                )
                .unwrap();
        }
    }
    for (column, expected) in setup.setup.hypercube_evals.iter().enumerate() {
        comparator
            .fields(
                "synthetic setup",
                column,
                &tables[column * rows..(column + 1) * rows],
                expected.as_slice(),
                &context,
            )
            .unwrap();
    }
    for (name, device, expected, u16_encoding) in [
        (
            "synthetic generic",
            &buffers.generic,
            &cpu.generic_lookup_mapping,
            false,
        ),
        (
            "synthetic timestamp",
            &buffers.timestamp,
            &cpu.timestamp_range_check_lookup_mapping,
            false,
        ),
    ] {
        let device = DeviceMatrix::new(device, rows);
        assert_eq!(
            device.cols(),
            expected.len(),
            "Proth120 synthetic mapping count {name}"
        );
        for (column, expected) in expected.iter().enumerate() {
            comparator
                .mappings(
                    name,
                    column,
                    fixture::column(&device, column),
                    expected,
                    u16_encoding,
                    &context,
                )
                .unwrap();
        }
    }
    for (column, expected) in cpu.range_check_16_lookup_mapping.iter().enumerate() {
        comparator
            .mappings(
                "synthetic RC16",
                column,
                &buffers.range_check_16[column * rows..(column + 1) * rows],
                expected,
                true,
                &context,
            )
            .unwrap();
    }
    let compare_time = compare_start.elapsed();
    println!("Proth120 synthetic fused CPU parity: 38 memory, 66 witness incl. 63..65, 41 scratch, 10 setup, 6 generic+decoder, 15 RC16, 8 timestamp columns equal");

    let standalone_start = Instant::now();
    let (fixed, generated) = coverage::standalone_columns(circuit);
    let mut standalone = context
        .alloc(buffers.witness.len(), AllocationPlacement::BestFit)
        .unwrap();
    set_to_zero(&mut standalone, stream).unwrap();
    for &column in &fixed {
        memory_copy_async(
            &mut standalone[column * rows..(column + 1) * rows],
            &buffers.witness[column * rows..(column + 1) * rows],
            stream,
        )
        .unwrap();
    }
    for &column in &generated {
        set_by_val(
            Proth120::new(17),
            &mut DeviceMatrixMut::new(&mut standalone[column * rows..(column + 1) * rows], rows),
            stream,
        )
        .unwrap();
    }
    set_to_zero(&mut buffers.scratch, stream).unwrap();
    set_to_ones(
        &mut buffers.generic[..rows * circuit.generic_lookups.len()],
        stream,
    )
    .unwrap();
    generate_witness_values(
        circuit,
        &device_decoder,
        &trace,
        &DeviceMatrix::new(&tables, rows),
        &DeviceMatrix::new(&buffers.memory, rows),
        &mut DeviceMatrixMut::new(&mut standalone, rows),
        &mut DeviceMatrixMut::new(&mut buffers.scratch, rows),
        &mut DeviceMatrixMut::new(
            &mut buffers.generic[..rows * circuit.generic_lookups.len()],
            rows,
        ),
        stream,
    )
    .unwrap();
    stream.synchronize().unwrap();
    for (column, expected) in cpu.column_major_witness_trace.iter().enumerate().take(63) {
        comparator
            .fields(
                "standalone self-consistency witness",
                column,
                &standalone[column * rows..(column + 1) * rows],
                expected,
                &context,
            )
            .unwrap();
    }
    for (column, expected) in cpu.column_major_scratch_space_trace.iter().enumerate() {
        comparator
            .fields(
                "standalone self-consistency scratch",
                column,
                &buffers.scratch[column * rows..(column + 1) * rows],
                expected,
                &context,
            )
            .unwrap();
    }
    for (column, expected) in fused_generic.iter().enumerate() {
        comparator
            .mappings(
                "standalone self-consistency pre-count generic",
                column,
                &buffers.generic[column * rows..(column + 1) * rows],
                expected,
                false,
                &context,
            )
            .unwrap();
    }
    let standalone_time = standalone_start.elapsed();
    println!("Proth120 standalone self-consistency: {} fixed inputs copied from fused, {} SSA targets poisoned, scratch cleared; witness 0..63, all scratch and pre-count generic mappings equal fused (field columns use the CPU copy already matched cell-for-cell); multiplicity 63..65 excluded", fixed.len(), generated.len());
    println!("Proth120 synthetic evaluator-only: cpu {cpu_time:?}, gpu {gpu_time:?}, compare {compare_time:?}, standalone {standalone_time:?}, total {:?}, VmHWM {} KiB, allocator peak {} B", start.elapsed(), vm_hwm_kib(), context.get_used_mem_peak());
}
