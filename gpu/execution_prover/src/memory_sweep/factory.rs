//! Synthetic proof and memory-commitment requests for the offline memory sweep.
//!
//! Inputs are production-shaped but arbitrary: precomputations come from the
//! production builders over a zero ROM image, tracing data is `2^N` filled
//! rows in pinned chunks, inits-and-teardowns hosts fill every page in every set, and external challenges are fixed. Proofs are not verified.
//!
//! Ordering contract for the runner: initialize every setup host on the sweep
//! context (`precomputations.setup_host.get_or_init`) and run one warm memory
//! commitment per circuit (`memory_commitment_request` -> `set_memory_caps`)
//! before building proof requests or reading `input_bytes`.

use crate::messages::{GpuWorkRequest, MemoryCommitmentRequest, ProofRequest};
use crate::precomputations::{
    build_unrolled_circuit_precomputation, config_logs_for_circuit,
    get_common_precomputations_for_all, CircuitPrecomputations,
};
use crate::upstream::{
    GKRExternalChallenges, MerkleTreeCapVarLength, SecurityLevel, ROM_WORD_SIZE,
};
use crate::A;
use common_constants::{TimestampData, TimestampScalar, INITIAL_TIMESTAMP};
use era_cudart::memory::{CudaHostAllocFlags, HostAllocation};
use era_cudart_sys::CudaError;
use gpu_core::primitives::field::{BF, E4};
use gpu_core::primitives::machine_type::MachineType;
use gpu_trace::trace::holder::PARTIAL_TREE_REDUCTION_LAYERS;
use gpu_trace::trace::tracing_data::{
    DelegationTracingDataHostSource, TracingDataHost, UnrolledTracingDataHost,
};
use gpu_trace::witness::circuit_type::{CircuitType, DelegationCircuitType, UnrolledCircuitType};
use gpu_trace::witness::trace::ChunkedTraceHolder;
use gpu_trace::witness::trace_unrolled::{
    ExecutorFamilyDecoderData, InitsAndTeardownsTraceHost, PAGE_SIZE_LOG2,
};
use riscv_transpiler::witness::data_structs::UnifiedOpcodeTracingDataWithTimestamp;
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_g_function::Blake2sGFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;
use riscv_transpiler::witness::{
    MemoryOpcodeTracingDataWithTimestamp, NonMemoryOpcodeTracingDataWithTimestamp,
};
use std::collections::BTreeMap;
use std::fmt::{Display, Formatter};
use std::mem::size_of;
use std::sync::Arc;
use worker::Worker;

/// Pinned chunk size for synthetic traces; one pool allocator per chunk.
const TRACE_CHUNK_BYTES: usize = 64 << 20;
const TRACE_CHUNK_LOG_SIZE: u32 = 26;

/// Production device-arena rounding (`ProverContextConfig` defaults): requests
/// up to `1 << (allocator_block_log_size - 2)` bytes go to the small
/// sub-allocator at 256-byte granularity; larger ones take whole 1 MiB blocks.
const SMALL_ALLOCATION_THRESHOLD_BYTES: usize = 1 << 18;
const SMALL_ALLOCATION_GRANULARITY_BYTES: usize = 256;
const BLOCK_BYTES: usize = 1 << 20;

/// Blake2s digest width. Kept local so the accounting needs no `gpu_hash`
/// dependency; checked against the setup host's cap element size.
const DIGEST_BYTES: usize = 8 * size_of::<u32>();

/// Stable external GKR challenges shared by every synthetic request. Any
/// nonzero deterministic values are acceptable: the sweep never verifies.
const CHALLENGE_SEED: [u32; 4] = [0x5359_4e54, 0x4845_5449, 0x435f_4d45, 0x4153_5552];

#[derive(Debug)]
pub(crate) enum SyntheticRequestError {
    Cuda(CudaError),
    InvalidShape,
    MemoryCapsNotCommitted,
}

impl Display for SyntheticRequestError {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Cuda(error) => write!(formatter, "synthetic pinned allocation failed: {error:?}"),
            Self::InvalidShape => formatter.write_str("synthetic request shape overflow"),
            Self::MemoryCapsNotCommitted => {
                formatter.write_str("memory caps must be supplied by a warm commit first")
            }
        }
    }
}

impl std::error::Error for SyntheticRequestError {}

impl From<CudaError> for SyntheticRequestError {
    fn from(error: CudaError) -> Self {
        Self::Cuda(error)
    }
}

#[derive(Clone)]
struct SyntheticInputs {
    inits_and_teardowns: Option<InitsAndTeardownsTraceHost>,
    tracing_data: Option<TracingDataHost<A>>,
    /// One entry per compiled teardown set: the full host's windows for i&t
    /// carriers, all zero otherwise (what the worker synthesizes without a host).
    top_bits: Vec<u32>,
}

#[derive(Clone, Copy)]
enum TraceRecipe {
    Absent,
    BigInt,
    Blake2WithCompression,
    Blake2GFunction,
    Keccak,
    Memory,
    NonMemory,
    Unified,
}

impl TraceRecipe {
    fn for_circuit(circuit: CircuitType) -> Self {
        match circuit {
            CircuitType::Delegation(DelegationCircuitType::BigIntWithControl) => Self::BigInt,
            CircuitType::Delegation(DelegationCircuitType::Blake2WithCompression) => {
                Self::Blake2WithCompression
            }
            CircuitType::Delegation(DelegationCircuitType::Blake2GFunction) => {
                Self::Blake2GFunction
            }
            CircuitType::Delegation(DelegationCircuitType::KeccakSpecial5) => Self::Keccak,
            CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns) => Self::Absent,
            CircuitType::Unrolled(UnrolledCircuitType::Memory(_)) => Self::Memory,
            CircuitType::Unrolled(UnrolledCircuitType::NonMemory(_)) => Self::NonMemory,
            CircuitType::Unrolled(UnrolledCircuitType::Unified) => Self::Unified,
        }
    }

    fn build(self, rows: usize) -> Result<Option<TracingDataHost<A>>, SyntheticRequestError> {
        fn delegation<W: Copy + DelegationTracingDataHostSource>(
            rows: usize,
            value: W,
        ) -> Result<Option<TracingDataHost<A>>, SyntheticRequestError> {
            Ok(Some(TracingDataHost::Delegation(W::get(
                pinned_filled_trace(rows, value)?,
            ))))
        }
        match self {
            Self::Absent => Ok(None),
            Self::BigInt => delegation(rows, BigintDelegationWitness::empty()),
            Self::Blake2WithCompression => {
                delegation(rows, Blake2sRoundFunctionDelegationWitness::empty())
            }
            Self::Blake2GFunction => delegation(rows, Blake2sGFunctionDelegationWitness::empty()),
            Self::Keccak => delegation(rows, KeccakSpecial5DelegationWitness::empty()),
            Self::Memory => Ok(Some(TracingDataHost::Unrolled(
                UnrolledTracingDataHost::Memory(pinned_filled_trace(
                    rows,
                    MemoryOpcodeTracingDataWithTimestamp {
                        cycle_timestamp: TimestampData::from_scalar(INITIAL_TIMESTAMP),
                        ..Default::default()
                    },
                )?),
            ))),
            Self::NonMemory => Ok(Some(TracingDataHost::Unrolled(
                UnrolledTracingDataHost::NonMemory(pinned_filled_trace(
                    rows,
                    NonMemoryOpcodeTracingDataWithTimestamp {
                        cycle_timestamp: TimestampData::from_scalar(INITIAL_TIMESTAMP),
                        ..Default::default()
                    },
                )?),
            ))),
            Self::Unified => Ok(Some(TracingDataHost::Unrolled(
                UnrolledTracingDataHost::Unified(pinned_filled_trace(
                    rows,
                    UnifiedOpcodeTracingDataWithTimestamp::NonMem(
                        NonMemoryOpcodeTracingDataWithTimestamp {
                            cycle_timestamp: TimestampData::from_scalar(INITIAL_TIMESTAMP),
                            ..Default::default()
                        },
                    ),
                )?),
            ))),
        }
    }

    /// Device bytes `TracingDataTransfer::new` reserves for `rows` elements
    /// (one allocation of the host's total length).
    fn device_bytes(self, rows: usize) -> Result<usize, SyntheticRequestError> {
        match self {
            Self::Absent => Ok(0),
            Self::BigInt => allocation_bytes::<BigintDelegationWitness>(rows),
            Self::Blake2WithCompression => {
                allocation_bytes::<Blake2sRoundFunctionDelegationWitness>(rows)
            }
            Self::Blake2GFunction => allocation_bytes::<Blake2sGFunctionDelegationWitness>(rows),
            Self::Keccak => allocation_bytes::<KeccakSpecial5DelegationWitness>(rows),
            Self::Memory => allocation_bytes::<MemoryOpcodeTracingDataWithTimestamp>(rows),
            Self::NonMemory => allocation_bytes::<NonMemoryOpcodeTracingDataWithTimestamp>(rows),
            Self::Unified => allocation_bytes::<UnifiedOpcodeTracingDataWithTimestamp>(rows),
        }
    }
}

/// One circuit's reusable synthetic inputs. `memory_caps` stays `None` until
/// the runner has fed back the warm GPU memory commitment for this circuit.
pub(crate) struct PreparedCircuit {
    pub(crate) circuit: CircuitType,
    pub(crate) precomputations: CircuitPrecomputations,
    security_level: SecurityLevel,
    inputs: SyntheticInputs,
    memory_caps: Option<Vec<MerkleTreeCapVarLength>>,
}

impl PreparedCircuit {
    /// The warm memory commitment request. Feed its result's per-coset
    /// `merkle_tree_caps` back through `set_memory_caps`.
    pub(crate) fn memory_commitment_request(&self, sequence_id: usize) -> GpuWorkRequest<A> {
        GpuWorkRequest::MemoryCommitment(MemoryCommitmentRequest {
            batch_id: 0,
            circuit_type: self.circuit,
            sequence_id,
            precomputations: self.precomputations.clone(),
            inits_and_teardowns: self.inputs.inits_and_teardowns.clone(),
            tracing_data: self.inputs.tracing_data.clone(),
            security_level: self.security_level,
        })
    }

    pub(crate) fn set_memory_caps(&mut self, memory_caps: Vec<MerkleTreeCapVarLength>) {
        self.memory_caps = Some(memory_caps);
    }

    pub(crate) fn proof_request(
        &self,
        sequence_id: usize,
    ) -> Result<GpuWorkRequest<A>, SyntheticRequestError> {
        let memory_caps = self
            .memory_caps
            .clone()
            .ok_or(SyntheticRequestError::MemoryCapsNotCommitted)?;
        Ok(GpuWorkRequest::Proof(ProofRequest {
            batch_id: 0,
            circuit_type: self.circuit,
            sequence_id,
            precomputations: self.precomputations.clone(),
            inits_and_teardowns: self.inputs.inits_and_teardowns.clone(),
            tracing_data: self.inputs.tracing_data.clone(),
            external_challenges: stable_external_challenges(),
            memory_caps,
            security_level: self.security_level,
        }))
    }

    /// Device bytes proof phase one reserves for this circuit's inputs, with
    /// production arena rounding. The setup host must already be initialized
    /// (`get_initialized` panics otherwise, as it does in production).
    pub(crate) fn input_bytes(&self) -> Result<usize, SyntheticRequestError> {
        input_bytes(
            self.circuit,
            self.security_level,
            &self.precomputations,
            &self.inputs,
        )
    }
}

pub(crate) struct SyntheticRequestFactory {
    worker: Worker,
    security_level: SecurityLevel,
    /// Zero ROM image and text section at `ROM_WORD_SIZE` words, the padded
    /// size `add_binary` hands to the per-binary precomputation builder.
    binary_image: Vec<u32>,
    text_section: Vec<u32>,
    common: BTreeMap<CircuitType, CircuitPrecomputations>,
}

impl SyntheticRequestFactory {
    pub(crate) fn new(security_level: SecurityLevel) -> Self {
        let worker = Worker::new();
        let common = get_common_precomputations_for_all(&worker, security_level);
        Self {
            worker,
            security_level,
            binary_image: vec![0; ROM_WORD_SIZE],
            text_section: vec![0; ROM_WORD_SIZE],
            common,
        }
    }

    /// Production precomputations for `circuit`: delegations and i&t from the
    /// binary-independent map, unrolled families and the unified circuit from
    /// the per-binary builder over the zero image.
    pub(crate) fn precomputations(&self, circuit: CircuitType) -> CircuitPrecomputations {
        match circuit {
            CircuitType::Delegation(_)
            | CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns) => {
                self.common[&circuit].clone()
            }
            CircuitType::Unrolled(unrolled) => {
                let machine_type = match unrolled {
                    UnrolledCircuitType::Unified => MachineType::Reduced,
                    _ => MachineType::FullUnsigned,
                };
                build_unrolled_circuit_precomputation(
                    machine_type,
                    unrolled,
                    &self.binary_image,
                    &self.text_section,
                    &self.worker,
                    self.security_level,
                )
            }
        }
    }

    pub(crate) fn prepare(
        &self,
        circuit: CircuitType,
        precomputations: CircuitPrecomputations,
    ) -> Result<PreparedCircuit, SyntheticRequestError> {
        let inputs = build_inputs(circuit, &precomputations)?;
        Ok(PreparedCircuit {
            circuit,
            precomputations,
            security_level: self.security_level,
            inputs,
            memory_caps: None,
        })
    }
}

fn build_inputs(
    circuit: CircuitType,
    precomputations: &CircuitPrecomputations,
) -> Result<SyntheticInputs, SyntheticRequestError> {
    let compiled = precomputations.gkr_programs.compiled_circuit();
    let tracing_data = TraceRecipe::for_circuit(circuit).build(circuit.get_domain_size())?;
    let num_sets = compiled.memory_layout.teardown_sets.len();
    let (inits_and_teardowns, top_bits) = if carries_inits_and_teardowns(circuit) {
        let host = full_inits_and_teardowns(circuit.get_domain_size_log2(), num_sets)?;
        let top_bits = host.top_bits.clone();
        (Some(host), top_bits)
    } else {
        (None, vec![0u32; num_sets])
    };
    Ok(SyntheticInputs {
        inits_and_teardowns,
        tracing_data,
        top_bits,
    })
}

fn carries_inits_and_teardowns(circuit: CircuitType) -> bool {
    matches!(
        circuit,
        CircuitType::Unrolled(
            UnrolledCircuitType::InitsAndTeardowns | UnrolledCircuitType::Unified
        )
    )
}

/// Maximum-capacity page payload, matching the v2 factory's full init/teardown
/// input. Local page indices enumerate every page in every set window.
fn full_inits_and_teardowns(
    trace_len_log2: u32,
    num_sets: usize,
) -> Result<InitsAndTeardownsTraceHost, SyntheticRequestError> {
    assert!(trace_len_log2 >= PAGE_SIZE_LOG2);
    assert!(
        num_sets > 0,
        "i&t carriers declare at least one teardown set"
    );
    let pages_per_set_log2 = trace_len_log2 - PAGE_SIZE_LOG2;
    let words = num_sets
        .checked_shl(trace_len_log2)
        .ok_or(SyntheticRequestError::InvalidShape)?;
    let page_count = num_sets
        .checked_shl(pages_per_set_log2)
        .ok_or(SyntheticRequestError::InvalidShape)?;
    let page_count: u32 = page_count
        .try_into()
        .map_err(|_| SyntheticRequestError::InvalidShape)?;
    let page_indices: Vec<u32> = (0..page_count).collect();
    Ok(InitsAndTeardownsTraceHost {
        page_indices: pinned_chunks_from_slice(&page_indices)?,
        values_packed: pinned_filled_trace(words, 0u32)?,
        timestamps_packed: pinned_filled_trace(words, TimestampScalar::default())?,
        top_bits: (0..num_sets as u32).collect(),
    })
}

fn stable_external_challenges() -> GKRExternalChallenges<BF, E4> {
    let total = GKRExternalChallenges::<BF, E4>::TOTAL_CHALLENGES;
    let challenges: Vec<E4> = (0..total as u32)
        .map(|index| {
            E4::from_array_of_base(CHALLENGE_SEED.map(|word| {
                // Distinct nonzero base elements far below any supported field order.
                BF::new((word.wrapping_mul(index + 1) % 1_000_000) + 1)
            }))
        })
        .collect();
    GKRExternalChallenges::from_slice(&challenges)
}

/// Device bytes reserved by proof phase one (`workers/gpu.rs`) for one
/// circuit, rounded per allocation as the production arena rounds:
/// setup transfer (raw evals, one cached partial-tree buffer, unified cap),
/// decoder, inits-and-teardowns (three buffers), tracing data, memory cap,
/// top bits, external challenges.
fn input_bytes(
    circuit: CircuitType,
    security_level: SecurityLevel,
    precomputations: &CircuitPrecomputations,
    inputs: &SyntheticInputs,
) -> Result<usize, SyntheticRequestError> {
    let mut total = 0usize;
    let mut add = |bytes: usize| -> Result<(), SyntheticRequestError> {
        total = total
            .checked_add(bytes)
            .ok_or(SyntheticRequestError::InvalidShape)?;
        Ok(())
    };
    let (log_lde_factor, log_rows_per_leaf, log_tree_cap_size) =
        config_logs_for_circuit(circuit, security_level);
    let cap_bytes = round_allocation((1usize << log_tree_cap_size) * DIGEST_BYTES);

    // Setup (`GpuGKRSetupTransfer::new` -> `TraceHolder::new_without_cosets`
    // with `CachePartial`): raw evals, one buffer holding every coset's
    // partial tree, and the unified cap. Setup-less circuits reserve nothing.
    if let Some(host) = precomputations.setup_host.get_initialized() {
        debug_assert_eq!(
            std::mem::size_of_val(host.unified_tree_cap()),
            (1usize << host.log_tree_cap_size) * DIGEST_BYTES
        );
        debug_assert_eq!(host.log_lde_factor, log_lde_factor);
        debug_assert_eq!(host.log_rows_per_leaf, log_rows_per_leaf);
        debug_assert_eq!(host.log_tree_cap_size, log_tree_cap_size);
        let raw_elements = host
            .columns_count
            .checked_shl(host.log_domain_size)
            .ok_or(SyntheticRequestError::InvalidShape)?;
        add(allocation_bytes::<BF>(raw_elements)?)?;
        let per_coset_tree_len = 1usize
            << (host.log_domain_size - PARTIAL_TREE_REDUCTION_LAYERS + 1 - host.log_rows_per_leaf);
        let tree_digests = per_coset_tree_len
            .checked_shl(host.log_lde_factor)
            .ok_or(SyntheticRequestError::InvalidShape)?;
        add(round_allocation(
            tree_digests
                .checked_mul(DIGEST_BYTES)
                .ok_or(SyntheticRequestError::InvalidShape)?,
        ))?;
        add(cap_bytes)?;
    }

    if let Some(decoder) = &precomputations.decoder_host {
        add(allocation_bytes::<ExecutorFamilyDecoderData>(
            decoder.len(),
        )?)?;
    }
    if let Some(host) = &inputs.inits_and_teardowns {
        add(allocation_bytes::<u32>(host.page_indices.len())?)?;
        add(allocation_bytes::<u32>(host.values_packed.len())?)?;
        add(allocation_bytes::<TimestampScalar>(
            host.timestamps_packed.len(),
        )?)?;
    }
    add(TraceRecipe::for_circuit(circuit).device_bytes(circuit.get_domain_size())?)?;
    // `GpuGKRMemoryTransfer::new`: one unified cap of the proof's geometry.
    add(cap_bytes)?;
    if !inputs.top_bits.is_empty() {
        add(allocation_bytes::<u32>(inputs.top_bits.len())?)?;
    }
    // `ExternalChallengesTransfer::new`: linearization challenges + additive part.
    add(allocation_bytes::<E4>(
        GKRExternalChallenges::<BF, E4>::TOTAL_CHALLENGES,
    )?)?;
    Ok(total)
}

pub(crate) fn allocation_bytes<T>(len: usize) -> Result<usize, SyntheticRequestError> {
    let bytes = len
        .checked_mul(size_of::<T>())
        .ok_or(SyntheticRequestError::InvalidShape)?;
    Ok(round_allocation(bytes))
}

fn round_allocation(bytes: usize) -> usize {
    if bytes == 0 {
        0
    } else if bytes <= SMALL_ALLOCATION_THRESHOLD_BYTES {
        bytes.next_multiple_of(SMALL_ALLOCATION_GRANULARITY_BYTES)
    } else {
        bytes.next_multiple_of(BLOCK_BYTES)
    }
}

/// `total_elements` copies of `value` in 64 MiB pinned chunks, each on its own
/// pool allocator; the pinned memory is released when the last request clone
/// drops its `Arc`.
fn pinned_filled_trace<T: Copy>(
    total_elements: usize,
    value: T,
) -> Result<ChunkedTraceHolder<T, A>, SyntheticRequestError> {
    assert_ne!(size_of::<T>(), 0);
    let elements_per_chunk = (TRACE_CHUNK_BYTES / size_of::<T>()).max(1);
    let mut remaining = total_elements;
    let mut chunks = Vec::new();
    while remaining != 0 {
        let elements = remaining.min(elements_per_chunk);
        let mut chunk = Vec::with_capacity_in(elements, pinned_chunk_allocator()?);
        chunk.extend(std::iter::repeat_n(value, elements));
        chunks.push(Arc::new(chunk));
        remaining -= elements;
    }
    Ok(ChunkedTraceHolder { chunks })
}

fn pinned_chunks_from_slice<T: Copy>(
    values: &[T],
) -> Result<ChunkedTraceHolder<T, A>, SyntheticRequestError> {
    assert_ne!(size_of::<T>(), 0);
    let elements_per_chunk = (TRACE_CHUNK_BYTES / size_of::<T>()).max(1);
    let mut chunks = Vec::new();
    for piece in values.chunks(elements_per_chunk) {
        let mut chunk = Vec::with_capacity_in(piece.len(), pinned_chunk_allocator()?);
        chunk.extend_from_slice(piece);
        chunks.push(Arc::new(chunk));
    }
    Ok(ChunkedTraceHolder { chunks })
}

fn pinned_chunk_allocator() -> Result<A, SyntheticRequestError> {
    let backing = HostAllocation::alloc(TRACE_CHUNK_BYTES, CudaHostAllocFlags::DEFAULT)?;
    Ok(A::new([backing], TRACE_CHUNK_LOG_SIZE))
}
