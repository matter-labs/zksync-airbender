use super::super::{
    generate_fused_values, generate_inits_and_teardowns, generate_lookup_multiplicities,
    Proth120LookupRelations, Proth120WitnessBuffers,
};
use super::coverage::{ColumnEdges, WitnessCoverage, WitnessDigests, WitnessEdges};
use crate::witness::trace_unrolled::{
    ExecutorFamilyDecoderData, InitsAndTeardownsTraceDevice, UnrolledUnifiedTraceDevice,
    PAGE_SIZE_LOG2,
};
use cpu_execution_prover::test_support::L1WrapFixture;
use cpu_execution_prover::CpuExecutionProverConfiguration;
use cs::gkr_compiler::GKRCircuitArtifact;
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use field::Proth120;
use full_statement_verifier::host_utils::{build_unified_stream, load_fsv_program};
use full_statement_verifier::program_proof::ProgramProof;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_structures::{DeviceMatrix, DeviceMatrixImpl, DeviceMatrixMut};
use gpu_core::primitives::static_host::alloc_static_pinned_box_from_slice;
use gpu_prover_context::transfer::Transfer;
use gpu_prover_context::{ProverContext, ProverContextConfig};
use prover::gkr::prover::{GKRProof, OperationMode};
use prover::gkr::prover_config::example_configs::l1_wrap_2p21::EXTERNAL_CHALLENGES_POW_BITS;
use prover::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
use serde::de::DeserializeOwned;
use serde::Deserialize;
use setups::Setups;
use sha3::{Digest, Keccak256};
use std::collections::BTreeSet;
use std::fs::File;
use std::io::{BufReader, Read};
use std::mem::size_of;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use unified_reduced_machine_proth120::l1_wrap_2p21::LAYOUT_JSON;
use verifier_common::fsv_binaries::{BlakeMode, FsvProgram};

#[derive(Deserialize)]
pub(super) struct Checkpoint {
    pub(super) schema_version: u32,
    pub(super) target: String,
    pub(super) security_level: String,
    pub(super) batch_id: u64,
    pub(super) proof: ProgramProof,
    pub(super) setups: Setups,
}

#[derive(Deserialize)]
pub(super) struct ReferenceBundle {
    pub(super) proof: GKRProof<Proth120, Proth120, Keccak256MerkleTreeWithCap>,
    pub(super) operation_mode: OperationMode,
}

#[derive(Deserialize)]
pub(super) struct FileIdentity {
    pub(super) name: String,
    pub(super) bytes: u64,
    pub(super) keccak256: String,
}

#[derive(Deserialize)]
struct FsvIdentity {
    role: String,
    stem: String,
    bin_keccak256: String,
    text_keccak256: String,
}

#[derive(Deserialize)]
struct ReferenceConfiguration {
    security_level: String,
    backend: String,
    batch_id: u64,
}

#[derive(Deserialize)]
pub(super) struct ProofManifest {
    format_version: u32,
    configuration: ReferenceConfiguration,
    fsv: Vec<FsvIdentity>,
    files: Vec<FileIdentity>,
}

#[derive(Deserialize)]
struct WitnessManifest {
    format_version: u32,
    l1_feeder_keccak256: String,
    l1_bundle_keccak256: String,
    layout_keccak256: String,
    files: Vec<FileIdentity>,
}

pub(super) struct Reference {
    pub(super) checkpoint: Checkpoint,
    pub(super) bundle: ReferenceBundle,
    pub(super) digests: WitnessDigests,
    pub(super) edges: WitnessEdges,
    pub(super) coverage: WitnessCoverage,
    fsv_directory: PathBuf,
}

fn reference_dir() -> PathBuf {
    std::env::var_os("AB_PROTH120_REFERENCE_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../prover_pipeline/fixtures/l1_reference_2p21")
        })
}

fn fsv_dir() -> PathBuf {
    std::env::var_os("FSV_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tools/gkr_verifier"))
}

fn read_typed<T: DeserializeOwned>(path: &Path) -> T {
    let file = File::open(path).unwrap_or_else(|error| {
        panic!("Proth120 witness fixture open {}: {error}", path.display())
    });
    serde_json::from_reader(BufReader::new(file)).unwrap_or_else(|error| {
        panic!(
            "Proth120 witness fixture decode {}: {error}",
            path.display()
        )
    })
}

pub(super) fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn file_identity(path: &Path) -> (u64, String) {
    let mut reader = BufReader::new(File::open(path).unwrap_or_else(|error| {
        panic!(
            "Proth120 witness fixture identity open {}: {error}",
            path.display()
        )
    }));
    let mut hasher = Keccak256::new();
    let mut buffer = [0u8; 1 << 16];
    let mut bytes = 0u64;
    loop {
        let len = reader.read(&mut buffer).unwrap_or_else(|error| {
            panic!(
                "Proth120 witness fixture identity read {}: {error}",
                path.display()
            )
        });
        if len == 0 {
            break;
        }
        bytes += len as u64;
        hasher.update(&buffer[..len]);
    }
    (bytes, hex(&hasher.finalize()))
}

fn check_files(directory: &Path, files: &[FileIdentity], required: &[&str]) {
    let names: BTreeSet<_> = files.iter().map(|file| file.name.as_str()).collect();
    assert_eq!(
        names.len(),
        files.len(),
        "Proth120 witness fixture duplicate file identity"
    );
    for name in required {
        assert!(
            names.contains(name),
            "Proth120 witness fixture missing identity {name}"
        );
    }
    for file in files {
        let (bytes, digest) = file_identity(&directory.join(&file.name));
        assert_eq!(
            bytes, file.bytes,
            "Proth120 witness fixture size {}",
            file.name
        );
        assert_eq!(
            digest, file.keccak256,
            "Proth120 witness fixture identity {}",
            file.name
        );
    }
}

pub(super) fn manifest_and_identities() -> Reference {
    let directory = reference_dir();
    let manifest: ProofManifest = read_typed(&directory.join("manifest.json"));
    assert_eq!(
        manifest.format_version, 1,
        "Proth120 witness proof manifest version"
    );
    assert_eq!(
        manifest.configuration.security_level, "Sec100",
        "Proth120 witness fixture security"
    );
    assert_eq!(
        manifest.configuration.backend, "Cpu",
        "Proth120 witness fixture backend"
    );
    assert_eq!(
        manifest.configuration.batch_id, 0,
        "Proth120 witness fixture batch"
    );
    check_files(
        &directory,
        &manifest.files,
        &[
            "recursion_unified.json",
            "feeder_layer_0.json",
            "l1_feeder.json",
            "l1_bundle.json",
        ],
    );

    let witness: WitnessManifest = read_typed(&directory.join("witness_manifest.json"));
    assert_eq!(
        witness.format_version, 1,
        "Proth120 witness manifest version"
    );
    check_files(
        &directory,
        &witness.files,
        &[
            "witness_digests.json",
            "witness_edges.json",
            "witness_coverage.json",
        ],
    );
    assert_eq!(
        file_identity(&directory.join("l1_feeder.json")).1,
        witness.l1_feeder_keccak256,
        "Proth120 witness feeder identity"
    );
    assert_eq!(
        file_identity(&directory.join("l1_bundle.json")).1,
        witness.l1_bundle_keccak256,
        "Proth120 witness bundle identity"
    );
    assert_eq!(
        hex(&Keccak256::digest(LAYOUT_JSON.as_bytes())),
        witness.layout_keccak256,
        "Proth120 witness layout identity"
    );

    let fsv_directory = fsv_dir();
    let program = FsvProgram::UnifiedRecursionLayerL1FeederWrap;
    let stem = program.file_stem(BlakeMode::BlakeSpecialOpcodes);
    let feeders: Vec<_> = manifest
        .fsv
        .iter()
        .filter(|identity| identity.role == "feeder_wrap")
        .collect();
    assert_eq!(
        feeders.len(),
        1,
        "Proth120 witness fixture feeder identity count"
    );
    let feeder = feeders[0];
    assert_eq!(feeder.stem, stem, "Proth120 witness fixture feeder stem");
    assert_eq!(
        file_identity(&fsv_directory.join(format!("{stem}.bin"))).1,
        feeder.bin_keccak256,
        "Proth120 witness feeder binary identity"
    );
    assert_eq!(
        file_identity(&fsv_directory.join(format!("{stem}.text"))).1,
        feeder.text_keccak256,
        "Proth120 witness feeder text identity"
    );

    let checkpoint: Checkpoint = read_typed(&directory.join("l1_feeder.json"));
    assert_eq!(
        checkpoint.schema_version, 5,
        "Proth120 witness checkpoint schema"
    );
    assert_eq!(
        checkpoint.target, "L1Feeder",
        "Proth120 witness checkpoint target"
    );
    assert_eq!(
        checkpoint.security_level, "Sec100",
        "Proth120 witness checkpoint security"
    );
    assert_eq!(checkpoint.batch_id, 0, "Proth120 witness checkpoint batch");
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
        "Proth120 witness checkpoint requires one unified proof and no delegation proofs"
    );
    let bundle: ReferenceBundle = read_typed(&directory.join("l1_bundle.json"));
    assert!(
        matches!(
            bundle.operation_mode,
            OperationMode::SingleChunk {
                external_challenges_pow_bits: EXTERNAL_CHALLENGES_POW_BITS,
                ..
            }
        ),
        "Proth120 witness fixture operation mode"
    );
    Reference {
        checkpoint,
        bundle,
        digests: read_typed(&directory.join("witness_digests.json")),
        edges: read_typed(&directory.join("witness_edges.json")),
        coverage: read_typed(&directory.join("witness_coverage.json")),
        fsv_directory,
    }
}

pub(super) fn wrap_inputs(reference: &Reference) -> (Vec<u32>, Vec<u32>, Vec<u32>) {
    let (bin, text) = load_fsv_program(
        &reference.fsv_directory,
        FsvProgram::UnifiedRecursionLayerL1FeederWrap,
        BlakeMode::BlakeSpecialOpcodes,
    );
    let nd_words = build_unified_stream(&reference.checkpoint.setups, &reference.checkpoint.proof);
    (bin, text, nd_words)
}

pub(super) fn configuration() -> CpuExecutionProverConfiguration {
    CpuExecutionProverConfiguration {
        max_thread_pool_threads: Some(8),
        replay_worker_threads_count: 1,
        expected_concurrent_jobs: 1,
        ..Default::default()
    }
}

pub(super) fn context() -> CudaResult<ProverContext> {
    ProverContext::new(&ProverContextConfig {
        allocator_block_log_size: 20,
        device_allocation_blocks_count: Some(16384),
        host_allocator_block_log_size: 13,
        host_allocator_blocks_count: 16384,
        ..Default::default()
    })
}

pub(super) struct DeviceInputs {
    pub(super) trace: UnrolledUnifiedTraceDevice,
    pub(super) inits: InitsAndTeardownsTraceDevice,
    pub(super) decoder: DeviceAllocation<ExecutorFamilyDecoderData>,
    pub(super) tables: DeviceAllocation<Proth120>,
}

fn alloc_input<T>(
    len: usize,
    capacity: usize,
    context: &ProverContext,
) -> CudaResult<DeviceAllocation<T>> {
    assert!(len <= capacity, "Proth120 witness fixture input capacity");
    let mut allocation = context.alloc(capacity, AllocationPlacement::Top)?;
    allocation.shrink_len_to(len);
    Ok(allocation)
}

pub(super) fn upload(
    fixture: &L1WrapFixture<'_>,
    context: &ProverContext,
) -> CudaResult<(DeviceInputs, Transfer<'static>)> {
    let setup = fixture.setup;
    let trace_len = setup.trace_len;
    let teardown_capacity = setup.circuit.memory_layout.teardown_sets.len() * trace_len;
    let mut inputs = DeviceInputs {
        trace: UnrolledUnifiedTraceDevice {
            tracing_data: alloc_input(fixture.tracing_data.len(), trace_len, context)?,
        },
        inits: InitsAndTeardownsTraceDevice {
            page_indices: alloc_input(
                fixture.inits_and_teardowns.page_indices.len(),
                teardown_capacity >> PAGE_SIZE_LOG2,
                context,
            )?,
            values_packed: alloc_input(
                fixture.inits_and_teardowns.values_packed.len(),
                teardown_capacity,
                context,
            )?,
            timestamps_packed: alloc_input(
                fixture.inits_and_teardowns.timestamps_packed.len(),
                teardown_capacity,
                context,
            )?,
        },
        decoder: context.alloc(setup.decoder_table.len(), AllocationPlacement::Top)?,
        tables: context.alloc(
            trace_len * setup.circuit.generic_lookup_tables_width,
            AllocationPlacement::Top,
        )?,
    };
    let mut transfer = Transfer::new()?;
    transfer.record_allocated(context)?;
    transfer.schedule_multiple(
        &fixture.tracing_data.chunks,
        &mut inputs.trace.tracing_data,
        context,
    )?;
    transfer.schedule_multiple(
        &fixture.inits_and_teardowns.page_indices.chunks,
        &mut inputs.inits.page_indices,
        context,
    )?;
    transfer.schedule_multiple(
        &fixture.inits_and_teardowns.values_packed.chunks,
        &mut inputs.inits.values_packed,
        context,
    )?;
    transfer.schedule_multiple(
        &fixture.inits_and_teardowns.timestamps_packed.chunks,
        &mut inputs.inits.timestamps_packed,
        context,
    )?;
    let decoder: Vec<ExecutorFamilyDecoderData> = setup
        .decoder_table
        .iter()
        .copied()
        .map(|row| row.unwrap_or_default().into())
        .collect();
    let decoder = Arc::new(alloc_static_pinned_box_from_slice(&decoder)?);
    transfer.schedule(decoder, &mut inputs.decoder, context)?;
    assert_eq!(
        setup.setup.hypercube_evals.len(),
        setup.circuit.generic_lookup_tables_width,
        "Proth120 witness fixture table columns"
    );
    for (column, source) in setup.setup.hypercube_evals.iter().enumerate() {
        assert_eq!(
            source.len(),
            trace_len,
            "Proth120 witness fixture table rows"
        );
        memory_copy_async(
            &mut inputs.tables[column * trace_len..(column + 1) * trace_len],
            source.as_slice(),
            context.get_exec_stream(),
        )?;
    }
    transfer.record_transferred(context)?;
    transfer.ensure_transferred(context)?;
    Ok((inputs, transfer))
}

pub(super) struct DeviceBuffers<'a> {
    pub(super) circuit: &'a GKRCircuitArtifact<Proth120>,
    pub(super) memory: DeviceAllocation<Proth120>,
    pub(super) witness: DeviceAllocation<Proth120>,
    pub(super) scratch: DeviceAllocation<Proth120>,
    pub(super) generic: DeviceAllocation<u32>,
    pub(super) range_check_16: DeviceAllocation<u32>,
    pub(super) timestamp: DeviceAllocation<u32>,
}

impl<'a> DeviceBuffers<'a> {
    pub(super) fn new(
        circuit: &'a GKRCircuitArtifact<Proth120>,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let rows = circuit.trace_len;
        Ok(Self {
            circuit,
            memory: context.alloc(
                rows * circuit.memory_layout.total_width,
                AllocationPlacement::BestFit,
            )?,
            witness: context.alloc(
                rows * circuit.witness_layout.total_width,
                AllocationPlacement::BestFit,
            )?,
            scratch: context.alloc(
                rows * circuit.scratch_space_size,
                AllocationPlacement::BestFit,
            )?,
            generic: context.alloc(
                rows * (circuit.generic_lookups.len() + usize::from(circuit.has_decoder_lookup)),
                AllocationPlacement::BestFit,
            )?,
            range_check_16: context.alloc(
                rows * circuit.range_check_16_lookup_expressions.len(),
                AllocationPlacement::BestFit,
            )?,
            timestamp: context.alloc(
                rows * circuit.timestamp_range_check_lookup_expressions.len(),
                AllocationPlacement::BestFit,
            )?,
        })
    }

    pub(super) fn outputs(&mut self) -> Proth120WitnessBuffers<'_> {
        let rows = self.circuit.trace_len;
        let (generic, decoder) = self
            .generic
            .split_at_mut(rows * self.circuit.generic_lookups.len());
        Proth120WitnessBuffers {
            memory: DeviceMatrixMut::new(&mut self.memory, rows),
            witness: DeviceMatrixMut::new(&mut self.witness, rows),
            scratch: DeviceMatrixMut::new(&mut self.scratch, rows),
            generic_lookup_mapping: DeviceMatrixMut::new(generic, rows),
            range_check_16_lookup_mapping: DeviceMatrixMut::new(&mut self.range_check_16, rows),
            range_check_timestamp_lookup_mapping: DeviceMatrixMut::new(&mut self.timestamp, rows),
            decoder_lookup_mapping: decoder,
        }
    }
}

pub(super) fn run_witness(
    inputs: &DeviceInputs,
    relations: &Proth120LookupRelations,
    buffers: &mut DeviceBuffers<'_>,
    context: &ProverContext,
) -> CudaResult<()> {
    let circuit = buffers.circuit;
    let rows = circuit.trace_len;
    let stream = context.get_exec_stream();
    generate_inits_and_teardowns(
        &circuit.memory_layout,
        rows.trailing_zeros(),
        PAGE_SIZE_LOG2,
        &inputs.inits,
        &mut DeviceMatrixMut::new(&mut buffers.memory, rows),
        stream,
    )?;
    generate_fused_values(
        circuit,
        &inputs.decoder,
        &inputs.trace,
        &DeviceMatrix::new(&inputs.tables, rows),
        relations,
        &mut buffers.outputs(),
        stream,
    )?;
    for (mapping, columns, active_counts_len) in [
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
        let mut mapping = DeviceMatrixMut::new(mapping, rows);
        let mut counts = DeviceMatrixMut::new(
            &mut buffers.witness[columns.start * rows..columns.end * rows],
            rows,
        );
        generate_lookup_multiplicities(&mut mapping, &mut counts, active_counts_len, context)?;
    }
    stream.synchronize()
}

pub(super) fn column<T>(matrix: &impl DeviceMatrixImpl<T>, column: usize) -> &DeviceSlice<T> {
    let rows = matrix.stride();
    assert!(
        column < matrix.cols(),
        "Proth120 witness comparator column bounds"
    );
    &matrix.slice()[column * rows..(column + 1) * rows]
}

const CHUNK_BYTES: usize = 64 << 20;
const EDGE_ROWS: usize = 64;

trait ReadbackValue: Copy + Send + Sync + 'static {
    fn copy_bytes(self, output: &mut Vec<u8>);
}

impl ReadbackValue for Proth120 {
    fn copy_bytes(self, output: &mut Vec<u8>) {
        output.extend_from_slice(&self.raw_u128_value().to_ne_bytes());
    }
}

impl ReadbackValue for u32 {
    fn copy_bytes(self, output: &mut Vec<u8>) {
        output.extend_from_slice(&self.to_ne_bytes());
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(super) struct Mismatch {
    pub(super) set: String,
    pub(super) column: usize,
    pub(super) row: usize,
    pub(super) expected: String,
    pub(super) actual: String,
}

impl std::fmt::Display for Mismatch {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Proth120 witness mismatch ({}, {}, {}, {}, {})",
            self.set, self.column, self.row, self.expected, self.actual
        )
    }
}

pub(super) fn field_cell(
    set: &str,
    column: usize,
    row: usize,
    expected: Proth120,
    raw: u128,
) -> Result<Proth120, Mismatch> {
    if raw >= Proth120::ORDER || raw != expected.raw_u128_value() {
        return Err(Mismatch {
            set: set.into(),
            column,
            row,
            expected: format!("raw 0x{:032x}", expected.raw_u128_value()),
            actual: format!(
                "raw 0x{raw:032x}{}",
                if raw >= Proth120::ORDER {
                    " noncanonical"
                } else {
                    ""
                }
            ),
        });
    }
    Ok(Proth120::from_raw_u128(raw))
}

pub(super) struct ColumnReport {
    pub(super) digest: String,
    pub(super) nonzero_rows: u64,
    pub(super) edges: ColumnEdges,
}

pub(super) struct Comparator {
    owned: Arc<Mutex<Vec<u8>>>,
}

impl Comparator {
    pub(super) fn new() -> Self {
        Self {
            owned: Arc::new(Mutex::new(Vec::with_capacity(CHUNK_BYTES))),
        }
    }

    fn read_chunk<T: ReadbackValue>(
        &mut self,
        source: &DeviceSlice<T>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        assert!(
            source.len() * size_of::<T>() <= CHUNK_BYTES,
            "Proth120 witness comparator chunk bound"
        );
        let stream = context.get_exec_stream();
        let mut staging = unsafe { context.alloc_host_uninit_slice::<T>(source.len()) };
        memory_copy_async(&mut staging, source, stream)?;
        let accessor = staging.get_accessor();
        let owned = Arc::clone(&self.owned);
        let mut callbacks = Callbacks::new();
        callbacks.schedule(
            move || {
                let source = unsafe { accessor.get() };
                let mut output = owned
                    .lock()
                    .expect("Proth120 witness comparator buffer lock");
                output.clear();
                for value in source.iter().copied() {
                    value.copy_bytes(&mut output);
                }
            },
            stream,
        )?;
        drop(staging);
        stream.synchronize()?;
        drop(callbacks);
        Ok(())
    }

    pub(super) fn fields(
        &mut self,
        set: &str,
        column: usize,
        source: &DeviceSlice<Proth120>,
        expected: &[Proth120],
        context: &ProverContext,
    ) -> CudaResult<ColumnReport> {
        assert_eq!(
            source.len(),
            expected.len(),
            "Proth120 witness comparator field length {set} {column}"
        );
        let mut hasher = Keccak256::new();
        let mut nonzero_rows = 0;
        let mut edges = ColumnEdges {
            first: Vec::new(),
            last: Vec::new(),
        };
        let edge_rows = EDGE_ROWS.min(expected.len());
        for start in (0..expected.len()).step_by(CHUNK_BYTES / size_of::<Proth120>()) {
            let end = (start + CHUNK_BYTES / size_of::<Proth120>()).min(expected.len());
            self.read_chunk(&source[start..end], context)?;
            let mut owned = self
                .owned
                .lock()
                .expect("Proth120 witness comparator buffer lock");
            assert_eq!(
                owned.len(),
                (end - start) * 16,
                "Proth120 witness comparator field readback length"
            );
            for (offset, raw_bytes) in owned.as_chunks_mut::<16>().0.iter_mut().enumerate() {
                let row = start + offset;
                let raw = u128::from_ne_bytes(*raw_bytes);
                let actual = field_cell(set, column, row, expected[row], raw)
                    .unwrap_or_else(|mismatch| panic!("{mismatch}"));
                let natural = actual.to_u128();
                nonzero_rows += u64::from(natural != 0);
                if row < edge_rows {
                    edges.first.push(format!("0x{natural:032x}"));
                }
                if row >= expected.len() - edge_rows {
                    edges.last.push(format!("0x{natural:032x}"));
                }
                raw_bytes.copy_from_slice(&natural.to_be_bytes());
            }
            hasher.update(owned.as_slice());
        }
        Ok(ColumnReport {
            digest: hex(&hasher.finalize()),
            nonzero_rows,
            edges,
        })
    }

    pub(super) fn mappings<T: Copy + Into<u32>>(
        &mut self,
        set: &str,
        column: usize,
        source: &DeviceSlice<u32>,
        expected: &[T],
        u16_encoding: bool,
        context: &ProverContext,
    ) -> CudaResult<ColumnReport> {
        assert_eq!(
            source.len(),
            expected.len(),
            "Proth120 witness comparator mapping length {set} {column}"
        );
        let mut hasher = Keccak256::new();
        let mut nonzero_rows = 0;
        for start in (0..expected.len()).step_by(CHUNK_BYTES / size_of::<u32>()) {
            let end = (start + CHUNK_BYTES / size_of::<u32>()).min(expected.len());
            self.read_chunk(&source[start..end], context)?;
            let mut owned = self
                .owned
                .lock()
                .expect("Proth120 witness comparator buffer lock");
            assert_eq!(
                owned.len(),
                (end - start) * 4,
                "Proth120 witness comparator mapping readback length"
            );
            for offset in 0..end - start {
                let row = start + offset;
                let actual =
                    u32::from_ne_bytes(owned[4 * offset..4 * offset + 4].try_into().unwrap());
                let expected = expected[row].into();
                if actual != expected || (u16_encoding && actual >= 1 << 16) {
                    panic!(
                        "{}",
                        Mismatch {
                            set: set.into(),
                            column,
                            row,
                            expected: expected.to_string(),
                            actual: actual.to_string()
                        }
                    );
                }
                nonzero_rows += u64::from(actual != 0);
                if u16_encoding {
                    owned[2 * offset..2 * offset + 2]
                        .copy_from_slice(&(actual as u16).to_le_bytes());
                } else {
                    owned[4 * offset..4 * offset + 4].copy_from_slice(&actual.to_le_bytes());
                }
            }
            let encoded_len = (end - start) * if u16_encoding { 2 } else { 4 };
            hasher.update(&owned[..encoded_len]);
        }
        Ok(ColumnReport {
            digest: hex(&hasher.finalize()),
            nonzero_rows,
            edges: ColumnEdges {
                first: Vec::new(),
                last: Vec::new(),
            },
        })
    }
}
