//! Synthetic proof and memory-commitment requests for the offline memory sweep.
//!
//! Inputs are production-shaped but arbitrary: precomputations come from the
//! production builders over a zero ROM image, tracing data is `2^N` filled
//! rows in pinned chunks, inits-and-teardowns hosts fill every page in every set, and external challenges are fixed. Proofs are not verified.
//!
//! Ordering contract for the runner: initialize every setup host on the sweep
//! context (`precomputations.setup_host.get_or_init`) and run one warm memory
//! commitment per circuit (`memory_commitment_request` -> `set_memory_caps`)
//! before building proof requests.

use crate::messages::{GpuWorkRequest, MemoryCommitmentRequest, ProofRequest};
use crate::precomputations::{
    build_unrolled_circuit_precomputation, get_common_precomputations_for_all,
    CircuitPrecomputations,
};
use crate::upstream::{
    GKRExternalChallenges, MerkleTreeCapVarLength, SecurityLevel, ROM_WORD_SIZE,
};
use crate::A;
use common_constants::{TimestampData, TimestampScalar, INITIAL_TIMESTAMP};
use era_cudart::memory::{CudaHostAllocFlags, HostAllocation};
use era_cudart::result::CudaResult;
use gpu_core::primitives::field::{BF, E4};
use gpu_core::primitives::machine_type::MachineType;
use gpu_trace::trace::tracing_data::{
    DelegationTracingDataHostSource, TracingDataHost, UnrolledTracingDataHost,
};
use gpu_trace::witness::circuit_type::{CircuitType, DelegationCircuitType, UnrolledCircuitType};
use gpu_trace::witness::trace::ChunkedTraceHolder;
use gpu_trace::witness::trace_unrolled::{InitsAndTeardownsTraceHost, PAGE_SIZE_LOG2};
use riscv_transpiler::witness::data_structs::UnifiedOpcodeTracingDataWithTimestamp;
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_g_function::Blake2sGFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;
use riscv_transpiler::witness::{
    MemoryOpcodeTracingDataWithTimestamp, NonMemoryOpcodeTracingDataWithTimestamp,
};
use std::collections::BTreeMap;
use std::mem::size_of;
use std::sync::Arc;
use worker::Worker;

/// Pinned chunk size for synthetic traces; one pool allocator per chunk.
const TRACE_CHUNK_BYTES: usize = 64 << 20;
const TRACE_CHUNK_LOG_SIZE: u32 = 26;

/// Stable external GKR challenges shared by every synthetic request. Any
/// nonzero deterministic values are acceptable: the sweep never verifies.
const CHALLENGE_SEED: [u32; 4] = [0x5359_4e54, 0x4845_5449, 0x435f_4d45, 0x4153_5552];

#[derive(Clone)]
struct SyntheticInputs {
    inits_and_teardowns: Option<InitsAndTeardownsTraceHost>,
    tracing_data: Option<TracingDataHost<A>>,
}

fn build_tracing_data(circuit: CircuitType, rows: usize) -> CudaResult<Option<TracingDataHost<A>>> {
    fn delegation<W: Copy + DelegationTracingDataHostSource>(
        rows: usize,
        value: W,
    ) -> CudaResult<Option<TracingDataHost<A>>> {
        Ok(Some(TracingDataHost::Delegation(W::get(
            pinned_filled_trace(rows, value)?,
        ))))
    }
    match circuit {
        CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns) => Ok(None),
        CircuitType::Delegation(DelegationCircuitType::BigIntWithControl) => {
            delegation(rows, BigintDelegationWitness::empty())
        }
        CircuitType::Delegation(DelegationCircuitType::Blake2WithCompression) => {
            delegation(rows, Blake2sRoundFunctionDelegationWitness::empty())
        }
        CircuitType::Delegation(DelegationCircuitType::Blake2GFunction) => {
            delegation(rows, Blake2sGFunctionDelegationWitness::empty())
        }
        CircuitType::Delegation(DelegationCircuitType::KeccakSpecial5) => {
            delegation(rows, KeccakSpecial5DelegationWitness::empty())
        }
        CircuitType::Unrolled(UnrolledCircuitType::Memory(_)) => Ok(Some(
            TracingDataHost::Unrolled(UnrolledTracingDataHost::Memory(pinned_filled_trace(
                rows,
                MemoryOpcodeTracingDataWithTimestamp {
                    cycle_timestamp: TimestampData::from_scalar(INITIAL_TIMESTAMP),
                    ..Default::default()
                },
            )?)),
        )),
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(_)) => Ok(Some(
            TracingDataHost::Unrolled(UnrolledTracingDataHost::NonMemory(pinned_filled_trace(
                rows,
                NonMemoryOpcodeTracingDataWithTimestamp {
                    cycle_timestamp: TimestampData::from_scalar(INITIAL_TIMESTAMP),
                    ..Default::default()
                },
            )?)),
        )),
        CircuitType::Unrolled(UnrolledCircuitType::Unified) => Ok(Some(TracingDataHost::Unrolled(
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

    pub(crate) fn proof_request(&self, sequence_id: usize) -> GpuWorkRequest<A> {
        let memory_caps = self
            .memory_caps
            .clone()
            .expect("memory caps must be supplied by a warm commit first");
        GpuWorkRequest::Proof(ProofRequest {
            batch_id: 0,
            circuit_type: self.circuit,
            sequence_id,
            precomputations: self.precomputations.clone(),
            inits_and_teardowns: self.inputs.inits_and_teardowns.clone(),
            tracing_data: self.inputs.tracing_data.clone(),
            external_challenges: stable_external_challenges(),
            memory_caps,
            security_level: self.security_level,
        })
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
    fn precomputations(&self, circuit: CircuitType) -> CircuitPrecomputations {
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

    pub(crate) fn prepare(&self, circuit: CircuitType) -> CudaResult<PreparedCircuit> {
        let precomputations = self.precomputations(circuit);
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
) -> CudaResult<SyntheticInputs> {
    let compiled = precomputations.gkr_programs.compiled_circuit();
    let tracing_data = build_tracing_data(circuit, circuit.get_domain_size())?;
    let num_sets = compiled.memory_layout.teardown_sets.len();
    let inits_and_teardowns = if carries_inits_and_teardowns(circuit) {
        Some(full_inits_and_teardowns(
            circuit.get_domain_size_log2(),
            num_sets,
        )?)
    } else {
        None
    };
    Ok(SyntheticInputs {
        inits_and_teardowns,
        tracing_data,
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
) -> CudaResult<InitsAndTeardownsTraceHost> {
    assert!(trace_len_log2 >= PAGE_SIZE_LOG2);
    assert!(
        num_sets > 0,
        "i&t carriers declare at least one teardown set"
    );
    let pages_per_set_log2 = trace_len_log2 - PAGE_SIZE_LOG2;
    let words = num_sets
        .checked_shl(trace_len_log2)
        .expect("synthetic request shape overflow");
    let page_count = num_sets
        .checked_shl(pages_per_set_log2)
        .expect("synthetic request shape overflow");
    let page_count: u32 = page_count
        .try_into()
        .expect("synthetic page count exceeds u32");
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

/// `total_elements` copies of `value` in 64 MiB pinned chunks, each on its own
/// pool allocator; the pinned memory is released when the last request clone
/// drops its `Arc`.
fn pinned_filled_trace<T: Copy>(
    total_elements: usize,
    value: T,
) -> CudaResult<ChunkedTraceHolder<T, A>> {
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

fn pinned_chunks_from_slice<T: Copy>(values: &[T]) -> CudaResult<ChunkedTraceHolder<T, A>> {
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

fn pinned_chunk_allocator() -> CudaResult<A> {
    let backing = HostAllocation::alloc(TRACE_CHUNK_BYTES, CudaHostAllocFlags::DEFAULT)?;
    Ok(A::new([backing], TRACE_CHUNK_LOG_SIZE))
}
