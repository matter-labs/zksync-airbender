use cpu_execution_prover::test_support::{with_l1_wrap_fixture_for, L1WrapFixture};
use cpu_execution_prover::CpuExecutionProverConfiguration;
use cs::definitions::GKRAddress;
use cs::gkr_compiler::GKRCircuitArtifact;
use execution_prover::ExecutionKind;
use field::Proth120;
use full_statement_verifier::host_utils::{build_unified_stream, load_fsv_program};
use full_statement_verifier::program_proof::ProgramProof;
use prover::gkr::prover::{CommitmentMode, GKRProof};
use prover::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};
use setups::Setups;
use sha3::{Digest, Keccak256};
use std::fs::{self, File};
use std::io::{BufReader, BufWriter, Write};
use std::ops::Range;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;
use std::time::{Duration, Instant};
use unified_reduced_machine_proth120::l1_wrap_2p21::{LAYOUT_JSON, TRACE_LEN_LOG2};
use verifier_common::fsv_binaries::{BlakeMode, FsvProgram};

const REGENERATE: &str = "RUST_MIN_STACK=1073741824 cargo test -p cpu_execution_prover --release --test l1_reference generate_l1_witness_reference -- --exact --ignored --nocapture --test-threads=1";
const EDGE_ROWS: usize = 64;
const DIGESTS: &str = "witness_digests.json";
const EDGES: &str = "witness_edges.json";
const COVERAGE: &str = "witness_coverage.json";
const MANIFEST: &str = "witness_manifest.json";

fn fixture_dir() -> PathBuf {
    std::env::var_os("AB_PROTH120_REFERENCE_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../prover_pipeline/fixtures/l1_reference_2p21")
        })
}

fn fsv_dir() -> PathBuf {
    std::env::var_os("FSV_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| Path::new(env!("CARGO_MANIFEST_DIR")).join("../tools/gkr_verifier"))
}

fn disposable_dir(purpose: &str) -> PathBuf {
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("L1 witness reference staging clock")
        .as_nanos();
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../target/l1_reference_staging")
        .join(format!("{purpose}-{}-{nonce}", std::process::id()))
}

#[derive(Deserialize)]
struct FeederCheckpoint {
    schema_version: u32,
    target: String,
    security_level: String,
    batch_id: u64,
    proof: ProgramProof,
    setups: Setups,
}

#[derive(Serialize, Deserialize)]
struct ReferenceBundle {
    proof: GKRProof<Proth120, Proth120, Keccak256MerkleTreeWithCap>,
    commitment_mode: CommitmentMode,
    wrap: String,
}

#[derive(Deserialize)]
struct FsvIdentity {
    role: String,
    stem: String,
    bin_keccak256: String,
    text_keccak256: String,
}

#[derive(Deserialize)]
struct ProofManifest {
    fsv: Vec<FsvIdentity>,
}

#[derive(Serialize, Deserialize)]
struct WitnessDigests {
    memory: Vec<String>,
    witness: Vec<String>,
    setup: Vec<String>,
    trace_len_log2: u32,
    scratch: Vec<String>,
    generic_lookup_mapping_u32le: Vec<String>,
    range_check_16_lookup_mapping_u16le: Vec<String>,
    timestamp_range_check_lookup_mapping_u32le: Vec<String>,
}

#[derive(Serialize, Deserialize)]
struct ColumnEdges {
    first: Vec<String>,
    last: Vec<String>,
}

#[derive(Serialize, Deserialize)]
struct WitnessEdges {
    trace_len_log2: u32,
    edge_rows: usize,
    memory: Vec<ColumnEdges>,
    witness: Vec<ColumnEdges>,
    setup: Vec<ColumnEdges>,
    scratch: Vec<ColumnEdges>,
}

#[derive(Serialize, Deserialize, Default)]
struct PerSet<T> {
    memory: Vec<T>,
    witness: Vec<T>,
    setup: Vec<T>,
    scratch: Vec<T>,
    generic_lookup_mapping: Vec<T>,
    range_check_16_lookup_mapping: Vec<T>,
    timestamp_range_check_lookup_mapping: Vec<T>,
}

#[derive(Serialize, Deserialize)]
struct SelectorCoverage {
    address: GKRAddress,
    active_rows: u64,
}

#[derive(Serialize, Deserialize)]
struct MultiplicityColumns {
    range_check_16: Range<usize>,
    timestamp_range_check: Range<usize>,
    generic_lookup: Range<usize>,
}

#[derive(Serialize, Deserialize)]
struct WitnessCoverage {
    trace_len_log2: u32,
    execute_column: usize,
    rows_traced: u64,
    nonzero_rows: PerSet<u64>,
    all_zero_columns: PerSet<usize>,
    circuit_family_mask_bits: Vec<SelectorCoverage>,
    zero_count_selectors: Vec<GKRAddress>,
    multiplicity_columns: MultiplicityColumns,
    teardown_sets: Vec<([GKRAddress; 2], [GKRAddress; 2])>,
}

#[derive(Serialize, Deserialize)]
struct FileIdentity {
    name: String,
    bytes: u64,
    keccak256: String,
}

#[derive(Serialize, Deserialize)]
struct WitnessManifest {
    format_version: u32,
    l1_feeder_keccak256: String,
    l1_bundle_keccak256: String,
    layout_keccak256: String,
    files: Vec<FileIdentity>,
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn keccak_hex(bytes: &[u8]) -> String {
    hex(&Keccak256::digest(bytes))
}

fn read_bytes(path: &Path) -> Vec<u8> {
    fs::read(path)
        .unwrap_or_else(|error| panic!("L1 witness reference read {}: {error}", path.display()))
}

fn read_typed<T: DeserializeOwned>(path: &Path) -> T {
    let file = File::open(path)
        .unwrap_or_else(|error| panic!("L1 witness reference open {}: {error}", path.display()));
    serde_json::from_reader(BufReader::new(file)).unwrap_or_else(|error| {
        panic!(
            "L1 witness reference deserialize {}: {error}",
            path.display()
        )
    })
}

fn write_compact<T: Serialize>(path: &Path, value: &T) {
    let temporary = path.with_extension("json.part");
    let mut writer = BufWriter::new(File::create(&temporary).unwrap_or_else(|error| {
        panic!(
            "L1 witness reference create {}: {error}",
            temporary.display()
        )
    }));
    serde_json::to_writer(&mut writer, value).expect("L1 witness reference serializes");
    writer.flush().expect("L1 witness reference flushes");
    drop(writer);
    fs::rename(&temporary, path)
        .unwrap_or_else(|error| panic!("L1 witness reference rename {}: {error}", path.display()));
}

fn vmhwm_kib() -> u64 {
    fs::read_to_string("/proc/self/status")
        .expect("L1 witness reference reads /proc/self/status")
        .lines()
        .find_map(|line| {
            line.strip_prefix("VmHWM:")?
                .split_whitespace()
                .next()?
                .parse()
                .ok()
        })
        .expect("L1 witness reference finds VmHWM")
}

fn natural_hex(value: &Proth120) -> String {
    format!("0x{:032x}", value.to_u128())
}

fn column_edges(column: &[Proth120]) -> ColumnEdges {
    ColumnEdges {
        first: column[..EDGE_ROWS].iter().map(natural_hex).collect(),
        last: column[column.len() - EDGE_ROWS..]
            .iter()
            .map(natural_hex)
            .collect(),
    }
}

trait DigestValue: Sync {
    const WIDTH: usize;
    fn encode(&self, out: &mut Vec<u8>);
    fn is_zero(&self) -> bool;
}

impl DigestValue for Proth120 {
    const WIDTH: usize = 16;
    fn encode(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.to_u128().to_be_bytes());
    }
    fn is_zero(&self) -> bool {
        self.to_u128() == 0
    }
}

impl DigestValue for u32 {
    const WIDTH: usize = 4;
    fn encode(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.to_le_bytes());
    }
    fn is_zero(&self) -> bool {
        *self == 0
    }
}

impl DigestValue for u16 {
    const WIDTH: usize = 2;
    fn encode(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.to_le_bytes());
    }
    fn is_zero(&self) -> bool {
        *self == 0
    }
}

struct ColumnSummary {
    digest: String,
    nonzero_rows: u64,
}

fn summarize<T: DigestValue>(column: &[T]) -> ColumnSummary {
    const BLOCK: usize = 1 << 12;
    let mut hasher = Keccak256::new();
    let mut buffer = Vec::with_capacity(BLOCK * T::WIDTH);
    let mut nonzero_rows = 0;
    for block in column.chunks(BLOCK) {
        buffer.clear();
        for value in block {
            value.encode(&mut buffer);
            nonzero_rows += u64::from(!value.is_zero());
        }
        hasher.update(&buffer);
    }
    ColumnSummary {
        digest: hex(&hasher.finalize()),
        nonzero_rows,
    }
}

fn summarize_set<T: DigestValue, C: AsRef<[T]> + Sync>(
    columns: &[C],
    trace_len: usize,
    threads: usize,
    set: &str,
) -> Vec<ColumnSummary> {
    for (index, column) in columns.iter().enumerate() {
        assert_eq!(
            column.as_ref().len(),
            trace_len,
            "L1 witness reference {set} column {index} length"
        );
    }
    let next = AtomicUsize::new(0);
    let results: Mutex<Vec<Option<ColumnSummary>>> =
        Mutex::new((0..columns.len()).map(|_| None).collect());
    std::thread::scope(|scope| {
        for _ in 0..threads.min(columns.len()) {
            scope.spawn(|| loop {
                let index = next.fetch_add(1, Ordering::Relaxed);
                let Some(column) = columns.get(index) else {
                    break;
                };
                let summary = summarize(column.as_ref());
                results.lock().unwrap()[index] = Some(summary);
            });
        }
    });
    results
        .into_inner()
        .unwrap()
        .into_iter()
        .map(|summary| summary.expect("L1 witness reference summarized every column"))
        .collect()
}

fn digests_of(summaries: &[ColumnSummary]) -> Vec<String> {
    summaries
        .iter()
        .map(|summary| summary.digest.clone())
        .collect()
}

fn nonzero_of(summaries: &[ColumnSummary]) -> Vec<u64> {
    summaries
        .iter()
        .map(|summary| summary.nonzero_rows)
        .collect()
}

fn all_zero_of(summaries: &[ColumnSummary]) -> Vec<usize> {
    summaries
        .iter()
        .enumerate()
        .filter(|(_, summary)| summary.nonzero_rows == 0)
        .map(|(index, _)| index)
        .collect()
}

fn boolean_rows(column: &[Proth120], name: &str) -> Vec<bool> {
    column
        .iter()
        .enumerate()
        .map(|(row, value)| match value.to_u128() {
            0 => false,
            1 => true,
            other => panic!("L1 witness reference {name} row {row} is {other}, not boolean"),
        })
        .collect()
}

fn independent_digest(column: &[Proth120]) -> String {
    let mut bytes = Vec::with_capacity(column.len() * 16);
    for value in column {
        let encoded = natural_hex(value);
        let decoded = u128::from_str_radix(&encoded[2..], 16)
            .expect("L1 witness reference natural hex decodes");
        bytes.extend_from_slice(&decoded.to_be_bytes());
    }
    keccak_hex(&bytes)
}

struct WitnessOutputs {
    digests: WitnessDigests,
    edges: WitnessEdges,
    coverage: WitnessCoverage,
}

fn compute(fixture: &L1WrapFixture<'_>) -> (WitnessOutputs, Duration) {
    let eval_start = Instant::now();
    let trace = fixture.evaluate_witness();
    let t_eval = eval_start.elapsed();
    let trace_len = 1usize << TRACE_LEN_LOG2;
    let circuit: &GKRCircuitArtifact<Proth120> = &fixture.setup.circuit;
    let threads = fixture.worker.num_cores;
    let setup_columns: Vec<&[Proth120]> = fixture
        .setup
        .setup
        .hypercube_evals
        .iter()
        .map(|column| &column[..])
        .collect();
    let memory = summarize_set(
        &trace.column_major_memory_trace,
        trace_len,
        threads,
        "memory",
    );
    let witness = summarize_set(
        &trace.column_major_witness_trace,
        trace_len,
        threads,
        "witness",
    );
    let setup = summarize_set(&setup_columns, trace_len, threads, "setup");
    let scratch = summarize_set(
        &trace.column_major_scratch_space_trace,
        trace_len,
        threads,
        "scratch",
    );
    let generic = summarize_set(
        &trace.generic_lookup_mapping,
        trace_len,
        threads,
        "generic_lookup_mapping",
    );
    let range_check_16 = summarize_set(
        &trace.range_check_16_lookup_mapping,
        trace_len,
        threads,
        "range_check_16_lookup_mapping",
    );
    let timestamp_range_check = summarize_set(
        &trace.timestamp_range_check_lookup_mapping,
        trace_len,
        threads,
        "timestamp_range_check_lookup_mapping",
    );
    assert_eq!(memory.len(), circuit.memory_layout.total_width);
    assert_eq!(witness.len(), circuit.witness_layout.total_width);

    let execute_column = circuit
        .memory_layout
        .machine_state
        .as_ref()
        .expect("L1 witness reference layout has a machine state")
        .execute;
    let execute_values = &trace.column_major_memory_trace[execute_column];
    assert_eq!(
        independent_digest(execute_values),
        memory[execute_column].digest,
        "L1 witness reference independent encoding of memory column {execute_column}"
    );
    let active = boolean_rows(execute_values, "machine_state.execute");
    let rows_traced = active.iter().filter(|&&row| row).count() as u64;
    let circuit_family_mask_bits: Vec<SelectorCoverage> = circuit
        .memory_layout
        .decoder_input
        .as_ref()
        .expect("L1 witness reference layout has a decoder input")
        .circuit_family_mask_bits
        .iter()
        .map(|&address| {
            let column = match address {
                GKRAddress::BaseLayerMemory(index) => &trace.column_major_memory_trace[index],
                GKRAddress::BaseLayerWitness(index) => &trace.column_major_witness_trace[index],
                other => panic!("L1 witness reference selector at unsupported address {other:?}"),
            };
            let values = boolean_rows(column, &format!("selector {address:?}"));
            let active_rows = values
                .iter()
                .zip(&active)
                .filter(|(&value, &active)| value && active)
                .count() as u64;
            SelectorCoverage {
                address,
                active_rows,
            }
        })
        .collect();
    let zero_count_selectors = circuit_family_mask_bits
        .iter()
        .filter(|selector| selector.active_rows == 0)
        .map(|selector| selector.address)
        .collect();

    let digests = WitnessDigests {
        memory: digests_of(&memory),
        witness: digests_of(&witness),
        setup: digests_of(&setup),
        trace_len_log2: TRACE_LEN_LOG2 as u32,
        scratch: digests_of(&scratch),
        generic_lookup_mapping_u32le: digests_of(&generic),
        range_check_16_lookup_mapping_u16le: digests_of(&range_check_16),
        timestamp_range_check_lookup_mapping_u32le: digests_of(&timestamp_range_check),
    };
    let edges = WitnessEdges {
        trace_len_log2: TRACE_LEN_LOG2 as u32,
        edge_rows: EDGE_ROWS,
        memory: trace
            .column_major_memory_trace
            .iter()
            .map(|column| column_edges(column))
            .collect(),
        witness: trace
            .column_major_witness_trace
            .iter()
            .map(|column| column_edges(column))
            .collect(),
        setup: setup_columns
            .iter()
            .map(|column| column_edges(column))
            .collect(),
        scratch: trace
            .column_major_scratch_space_trace
            .iter()
            .map(|column| column_edges(column))
            .collect(),
    };
    let coverage = WitnessCoverage {
        trace_len_log2: TRACE_LEN_LOG2 as u32,
        execute_column,
        rows_traced,
        nonzero_rows: PerSet {
            memory: nonzero_of(&memory),
            witness: nonzero_of(&witness),
            setup: nonzero_of(&setup),
            scratch: nonzero_of(&scratch),
            generic_lookup_mapping: nonzero_of(&generic),
            range_check_16_lookup_mapping: nonzero_of(&range_check_16),
            timestamp_range_check_lookup_mapping: nonzero_of(&timestamp_range_check),
        },
        all_zero_columns: PerSet {
            memory: all_zero_of(&memory),
            witness: all_zero_of(&witness),
            setup: all_zero_of(&setup),
            scratch: all_zero_of(&scratch),
            generic_lookup_mapping: all_zero_of(&generic),
            range_check_16_lookup_mapping: all_zero_of(&range_check_16),
            timestamp_range_check_lookup_mapping: all_zero_of(&timestamp_range_check),
        },
        circuit_family_mask_bits,
        zero_count_selectors,
        multiplicity_columns: MultiplicityColumns {
            range_check_16: circuit
                .witness_layout
                .multiplicities_columns_for_range_check_16
                .clone(),
            timestamp_range_check: circuit
                .witness_layout
                .multiplicities_columns_for_timestamp_range_check
                .clone(),
            generic_lookup: circuit
                .witness_layout
                .multiplicities_columns_for_generic_lookup
                .clone(),
        },
        teardown_sets: circuit.memory_layout.teardown_sets.clone(),
    };
    (
        WitnessOutputs {
            digests,
            edges,
            coverage,
        },
        t_eval,
    )
}

fn produce(sink: &Path) {
    let start = Instant::now();
    let reference = fixture_dir();
    let feeder_path = reference.join("l1_feeder.json");
    let bundle_path = reference.join("l1_bundle.json");
    let checkpoint: FeederCheckpoint = read_typed(&feeder_path);
    assert!(
        checkpoint.schema_version == 5
            && checkpoint.target == "L1Feeder"
            && checkpoint.security_level == "Sec100"
            && checkpoint.batch_id == 0,
        "L1 witness reference requires the schema-5 Sec100 L1Feeder checkpoint at batch_id 0"
    );
    assert!(
        checkpoint.proof.riscv_proofs.len() == 1
            && checkpoint
                .proof
                .riscv_proofs
                .values()
                .all(|proofs| proofs.len() == 1)
            && checkpoint
                .proof
                .delegation_proofs
                .values()
                .all(|proofs| proofs.is_empty()),
        "L1 witness reference requires one unified feeder proof and no delegation proofs"
    );
    let bundle: ReferenceBundle = read_typed(&bundle_path);
    assert_eq!(
        bundle.wrap, "2p21",
        "L1 witness reference requires the 2^21 wrap bundle"
    );
    let manifest: ProofManifest = read_typed(&reference.join("manifest.json"));

    let program = FsvProgram::UnifiedRecursionLayerL1FeederWrap;
    let blake = BlakeMode::BlakeSpecialOpcodes;
    let stem = program.file_stem(blake);
    let dir = fsv_dir();
    let wrap_program = manifest
        .fsv
        .iter()
        .find(|identity| identity.role == "feeder_wrap")
        .expect("L1 witness reference proof manifest names the wrap fsv binary");
    assert!(
        wrap_program.stem == stem
            && wrap_program.bin_keccak256
                == keccak_hex(&read_bytes(&dir.join(format!("{stem}.bin"))))
            && wrap_program.text_keccak256
                == keccak_hex(&read_bytes(&dir.join(format!("{stem}.text")))),
        "L1 witness reference wrap fsv binary differs from the proof manifest"
    );
    let (bin, text) = load_fsv_program(&dir, program, blake);
    let nd_words = build_unified_stream(&checkpoint.setups, &checkpoint.proof);
    drop(checkpoint);

    let commitment_mode = bundle.commitment_mode;
    let top_bits = bundle.proof.inits_and_teardowns_top_bits.clone();
    drop(bundle);
    let call = Instant::now();
    let (outputs, t_capture, t_eval, t_hash, threads) = with_l1_wrap_fixture_for(
        ExecutionKind::L1Wrap21,
        CpuExecutionProverConfiguration::default(),
        bin,
        text,
        nd_words,
        None,
        move |fixture| {
            let t_capture = call.elapsed();
            assert_eq!(
                fixture.commitment_mode, commitment_mode,
                "L1 witness reference boundary state differs from the committed bundle"
            );
            assert_eq!(
                fixture.inits_and_teardowns.top_bits, top_bits,
                "L1 witness reference inits/teardowns windows differ from the committed bundle"
            );
            let (outputs, t_eval) = compute(&fixture);
            (
                outputs,
                t_capture,
                t_eval,
                call.elapsed() - t_capture - t_eval,
                fixture.worker.num_cores,
            )
        },
    );

    fs::create_dir_all(sink).expect("L1 witness reference sink");
    write_compact(&sink.join(DIGESTS), &outputs.digests);
    write_compact(&sink.join(EDGES), &outputs.edges);
    write_compact(&sink.join(COVERAGE), &outputs.coverage);
    let files = [DIGESTS, EDGES, COVERAGE]
        .into_iter()
        .map(|name| {
            let bytes = read_bytes(&sink.join(name));
            FileIdentity {
                name: name.into(),
                bytes: bytes.len() as u64,
                keccak256: keccak_hex(&bytes),
            }
        })
        .collect();
    write_compact(
        &sink.join(MANIFEST),
        &WitnessManifest {
            format_version: 1,
            l1_feeder_keccak256: keccak_hex(&read_bytes(&feeder_path)),
            l1_bundle_keccak256: keccak_hex(&read_bytes(&bundle_path)),
            layout_keccak256: keccak_hex(LAYOUT_JSON.as_bytes()),
            files,
        },
    );
    for name in [DIGESTS, EDGES, COVERAGE, MANIFEST] {
        println!(
            "witness_fixture={name} bytes={}",
            read_bytes(&sink.join(name)).len()
        );
    }
    println!(
        "producer.env t_capture_ms={} t_eval_ms={} t_hash_ms={} total_ms={} vmhwm_kib={} worker_threads={threads} binding_digests={} additive_digests={} rows_traced={}",
        t_capture.as_millis(),
        t_eval.as_millis(),
        t_hash.as_millis(),
        start.elapsed().as_millis(),
        vmhwm_kib(),
        outputs.digests.memory.len() + outputs.digests.witness.len() + outputs.digests.setup.len(),
        outputs.digests.scratch.len()
            + outputs.digests.generic_lookup_mapping_u32le.len()
            + outputs.digests.range_check_16_lookup_mapping_u16le.len()
            + outputs.digests.timestamp_range_check_lookup_mapping_u32le.len(),
        outputs.coverage.rows_traced,
    );
}

fn first_difference(name: &str, expected: &[u8], actual: &[u8]) -> String {
    fn columns(set: &str, expected: &[String], actual: &[String]) -> Option<String> {
        if expected.len() != actual.len() {
            return Some(format!("{set} column count"));
        }
        expected
            .iter()
            .zip(actual)
            .position(|(a, b)| a != b)
            .map(|index| format!("{set} column {index}"))
    }
    let located = match name {
        DIGESTS => serde_json::from_slice::<WitnessDigests>(expected)
            .ok()
            .zip(serde_json::from_slice::<WitnessDigests>(actual).ok())
            .and_then(|(e, a)| {
                columns("memory", &e.memory, &a.memory)
                    .or_else(|| columns("witness", &e.witness, &a.witness))
                    .or_else(|| columns("setup", &e.setup, &a.setup))
                    .or_else(|| columns("scratch", &e.scratch, &a.scratch))
                    .or_else(|| {
                        columns(
                            "generic_lookup_mapping_u32le",
                            &e.generic_lookup_mapping_u32le,
                            &a.generic_lookup_mapping_u32le,
                        )
                    })
                    .or_else(|| {
                        columns(
                            "range_check_16_lookup_mapping_u16le",
                            &e.range_check_16_lookup_mapping_u16le,
                            &a.range_check_16_lookup_mapping_u16le,
                        )
                    })
                    .or_else(|| {
                        columns(
                            "timestamp_range_check_lookup_mapping_u32le",
                            &e.timestamp_range_check_lookup_mapping_u32le,
                            &a.timestamp_range_check_lookup_mapping_u32le,
                        )
                    })
            }),
        _ => None,
    };
    let offset = expected
        .iter()
        .zip(actual)
        .position(|(a, b)| a != b)
        .unwrap_or(expected.len().min(actual.len()));
    let context = |bytes: &[u8]| {
        let start = offset.saturating_sub(40).min(bytes.len());
        String::from_utf8_lossy(&bytes[start..(start + 80).min(bytes.len())]).into_owned()
    };
    format!(
        "L1 witness reference mismatch {name} at byte {offset} ({}); expected {:?}, actual {:?}; regenerate: {REGENERATE}",
        located.unwrap_or_else(|| "see context".into()),
        context(expected),
        context(actual)
    )
}

#[test]
#[ignore = "replays the committed L1 feeder checkpoint through the L1 wrap simulator and witness evaluator"]
fn generate_l1_witness_reference() {
    let sink = disposable_dir("witness-generate");
    produce(&sink);
    let reference = fixture_dir();
    for name in [DIGESTS, EDGES, COVERAGE, MANIFEST] {
        fs::rename(sink.join(name), reference.join(name))
            .expect("L1 witness reference promotes the complete set");
    }
    fs::remove_dir_all(sink).expect("L1 witness reference removes staging directory");
}

#[test]
#[ignore = "replays the committed L1 feeder checkpoint and compares the committed witness reference"]
fn committed_l1_witness_reference_is_current() {
    let sink = disposable_dir("witness-guard");
    produce(&sink);
    let reference = fixture_dir();
    for name in [DIGESTS, EDGES, COVERAGE, MANIFEST] {
        let expected = read_bytes(&reference.join(name));
        let actual = read_bytes(&sink.join(name));
        assert!(
            expected == actual,
            "{}",
            first_difference(name, &expected, &actual)
        );
    }
    fs::remove_dir_all(sink).expect("L1 witness reference guard removes disposable sink");
}
