use crate::allocator::host::ConcurrentStaticHostAllocator;
use crate::blake2s::Digest;
use crate::circuit_type::{CircuitType, DelegationCircuitType, UnrolledCircuitType};
use crate::execution::messages::{GpuWorkRequest, ProofRequest};
use crate::execution::precomputations::CircuitPrecomputations;
use crate::execution::A;
use crate::prover::tracing_data::{
    DelegationTracingDataHost, TracingDataHost, UnrolledTracingDataHost,
};
use crate::witness::trace_unrolled::ShuffleRamInitsAndTeardownsHost;
use field::Mersenne31Field;
use prover::definitions::LazyInitAndTeardown;
use std::fmt::{Display, Formatter};
use std::mem::size_of;
use std::sync::Arc;
use worker::Worker;

const TRACE_CHUNK_BYTES: usize = 64 << 20;
const CHALLENGE_SEED: [u32; 8] = [
    0x5359_4e54,
    0x4845_5449,
    0x435f_4d45,
    0x4153_5552,
    0x454d_454e,
    0x545f_5631,
    0x0123_4567,
    0x89ab_cdef,
];

#[derive(Debug)]
pub(crate) enum SyntheticRequestError {
    Cuda(crate::cudart_sys::CudaError),
    InvalidShape,
    SetupNotWarmed,
}

impl Display for SyntheticRequestError {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Cuda(error) => write!(formatter, "synthetic pinned allocation failed: {error:?}"),
            Self::InvalidShape => formatter.write_str("synthetic request shape overflow"),
            Self::SetupNotWarmed => formatter.write_str("setup cache must be warmed first"),
        }
    }
}

impl std::error::Error for SyntheticRequestError {}

impl From<crate::cudart_sys::CudaError> for SyntheticRequestError {
    fn from(error: crate::cudart_sys::CudaError) -> Self {
        Self::Cuda(error)
    }
}

#[derive(Clone)]
struct SyntheticInputs {
    inits_and_teardowns: Option<ShuffleRamInitsAndTeardownsHost<ConcurrentStaticHostAllocator>>,
    tracing_data: Option<TracingDataHost<ConcurrentStaticHostAllocator>>,
}

#[derive(Clone, Copy)]
enum TraceRecipe {
    Absent,
    BigInt,
    Blake2,
    Keccak,
    Memory,
    NonMemory,
    Unified,
}

impl TraceRecipe {
    fn for_circuit(circuit: CircuitType) -> Self {
        match circuit {
            CircuitType::Delegation(DelegationCircuitType::BigIntWithControl) => Self::BigInt,
            CircuitType::Delegation(DelegationCircuitType::Blake2WithCompression) => Self::Blake2,
            CircuitType::Delegation(DelegationCircuitType::KeccakSpecial5) => Self::Keccak,
            CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns) => Self::Absent,
            CircuitType::Unrolled(UnrolledCircuitType::Memory(_)) => Self::Memory,
            CircuitType::Unrolled(UnrolledCircuitType::NonMemory(_)) => Self::NonMemory,
            CircuitType::Unrolled(UnrolledCircuitType::Unified) => Self::Unified,
        }
    }

    fn build(
        self,
        elements: usize,
    ) -> Result<Option<TracingDataHost<ConcurrentStaticHostAllocator>>, SyntheticRequestError> {
        use riscv_transpiler::machine_mode_only_unrolled::{
            MemoryOpcodeTracingDataWithTimestamp, NonMemoryOpcodeTracingDataWithTimestamp,
            UnifiedOpcodeTracingDataWithTimestamp,
        };
        use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
        use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
        use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;

        Ok(match self {
            Self::Absent => None,
            Self::BigInt => Some(TracingDataHost::Delegation(
                DelegationTracingDataHost::BigIntWithControl(pinned_filled_trace(
                    elements,
                    BigintDelegationWitness::empty(),
                )?),
            )),
            Self::Blake2 => Some(TracingDataHost::Delegation(
                DelegationTracingDataHost::Blake2WithCompression(pinned_filled_trace(
                    elements,
                    Blake2sRoundFunctionDelegationWitness::empty(),
                )?),
            )),
            Self::Keccak => Some(TracingDataHost::Delegation(
                DelegationTracingDataHost::KeccakSpecial5(pinned_filled_trace(
                    elements,
                    KeccakSpecial5DelegationWitness::empty(),
                )?),
            )),
            Self::Memory => Some(TracingDataHost::Unrolled(UnrolledTracingDataHost::Memory(
                pinned_filled_trace(elements, MemoryOpcodeTracingDataWithTimestamp::default())?,
            ))),
            Self::NonMemory => Some(TracingDataHost::Unrolled(
                UnrolledTracingDataHost::NonMemory(pinned_filled_trace(
                    elements,
                    NonMemoryOpcodeTracingDataWithTimestamp::default(),
                )?),
            )),
            Self::Unified => Some(TracingDataHost::Unrolled(UnrolledTracingDataHost::Unified(
                pinned_filled_trace(elements, UnifiedOpcodeTracingDataWithTimestamp::default())?,
            ))),
        })
    }

    fn bytes(self, elements: usize) -> Result<usize, SyntheticRequestError> {
        use riscv_transpiler::machine_mode_only_unrolled::{
            MemoryOpcodeTracingDataWithTimestamp, NonMemoryOpcodeTracingDataWithTimestamp,
            UnifiedOpcodeTracingDataWithTimestamp,
        };
        use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
        use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
        use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;

        match self {
            Self::Absent => Ok(0),
            Self::BigInt => allocation_bytes::<BigintDelegationWitness>(elements),
            Self::Blake2 => allocation_bytes::<Blake2sRoundFunctionDelegationWitness>(elements),
            Self::Keccak => allocation_bytes::<KeccakSpecial5DelegationWitness>(elements),
            Self::Memory => allocation_bytes::<MemoryOpcodeTracingDataWithTimestamp>(elements),
            Self::NonMemory => {
                allocation_bytes::<NonMemoryOpcodeTracingDataWithTimestamp>(elements)
            }
            Self::Unified => allocation_bytes::<UnifiedOpcodeTracingDataWithTimestamp>(elements),
        }
    }
}

pub(crate) struct PreparedCircuit {
    pub(crate) circuit: CircuitType,
    pub(crate) precomputations: CircuitPrecomputations,
    pub(crate) input_bytes: usize,
    inputs: SyntheticInputs,
}

impl PreparedCircuit {
    pub(crate) fn request(&self, sequence_id: usize) -> GpuWorkRequest<A> {
        GpuWorkRequest::Proof(ProofRequest {
            batch_id: 0,
            circuit_type: self.circuit,
            sequence_id,
            precomputations: self.precomputations.clone(),
            inits_and_teardowns: self.inputs.inits_and_teardowns.clone(),
            tracing_data: self.inputs.tracing_data.clone(),
            external_challenges:
                prover::definitions::ExternalChallenges::draw_from_transcript_seed_with_delegation_and_state_permutation(
                    prover::transcript::Seed(CHALLENGE_SEED),
                    0,
                    0,
                ),
        })
    }
}

pub(crate) struct SyntheticRequestFactory {
    worker: Worker,
    rom: Vec<u32>,
    bytecode: Vec<u32>,
}

impl SyntheticRequestFactory {
    pub(crate) fn new() -> Self {
        Self {
            worker: Worker::new(),
            rom: vec![0; prover::common_constants::ROM_WORD_SIZE],
            bytecode: vec![0; prover::common_constants::ROM_WORD_SIZE],
        }
    }

    pub(crate) fn precomputations(&self, circuit: CircuitType) -> CircuitPrecomputations {
        CircuitPrecomputations::new(circuit, &self.rom, &self.bytecode, &self.worker)
    }

    pub(crate) fn request(
        &self,
        circuit: CircuitType,
        sequence_id: usize,
        precomputations: CircuitPrecomputations,
    ) -> Result<GpuWorkRequest<A>, SyntheticRequestError> {
        let inputs = self.build_inputs(circuit, &precomputations)?;
        Ok(PreparedCircuit {
            circuit,
            precomputations,
            input_bytes: 0,
            inputs,
        }
        .request(sequence_id))
    }

    pub(crate) fn prepare(
        &self,
        circuit: CircuitType,
        precomputations: CircuitPrecomputations,
    ) -> Result<PreparedCircuit, SyntheticRequestError> {
        let inputs = self.build_inputs(circuit, &precomputations)?;
        let input_bytes = input_bytes(circuit, &precomputations)?;
        Ok(PreparedCircuit {
            circuit,
            precomputations,
            input_bytes,
            inputs,
        })
    }

    fn build_inputs(
        &self,
        circuit: CircuitType,
        precomputations: &CircuitPrecomputations,
    ) -> Result<SyntheticInputs, SyntheticRequestError> {
        let trace_recipe = TraceRecipe::for_circuit(circuit);
        let tracing_data = trace_recipe.build(circuit.get_num_cycles())?;
        let inits_and_teardowns = if matches!(
            circuit,
            CircuitType::Unrolled(
                UnrolledCircuitType::InitsAndTeardowns | UnrolledCircuitType::Unified
            )
        ) {
            let elements = init_teardown_elements(precomputations)?;
            Some(pinned_filled_trace(elements, LazyInitAndTeardown::EMPTY)?)
        } else {
            None
        };
        Ok(SyntheticInputs {
            inits_and_teardowns,
            tracing_data,
        })
    }
}

fn input_bytes(
    circuit: CircuitType,
    precomputations: &CircuitPrecomputations,
) -> Result<usize, SyntheticRequestError> {
    let compiled = &precomputations.compiled_circuit;
    let setup_elements = compiled
        .setup_layout
        .total_width
        .next_multiple_of(2)
        .checked_mul(compiled.trace_len)
        .ok_or(SyntheticRequestError::InvalidShape)?;
    let mut total = allocation_bytes::<Mersenne31Field>(setup_elements)?;

    let trees = precomputations
        .setup_trees_and_caps
        .get()
        .ok_or(SyntheticRequestError::SetupNotWarmed)?;
    for tree in trees.partial_trees.iter() {
        total = total
            .checked_add(allocation_bytes::<Digest>(tree.len())?)
            .ok_or(SyntheticRequestError::InvalidShape)?;
    }
    if let Some(decoder) = &precomputations.decoder_data {
        total = total
            .checked_add(allocation_bytes::<
                crate::witness::trace_unrolled::ExecutorFamilyDecoderData,
            >(decoder.len())?)
            .ok_or(SyntheticRequestError::InvalidShape)?;
    }
    if matches!(
        circuit,
        CircuitType::Unrolled(
            UnrolledCircuitType::InitsAndTeardowns | UnrolledCircuitType::Unified
        )
    ) {
        total = total
            .checked_add(allocation_bytes::<LazyInitAndTeardown>(
                init_teardown_elements(precomputations)?,
            )?)
            .ok_or(SyntheticRequestError::InvalidShape)?;
    }
    total
        .checked_add(TraceRecipe::for_circuit(circuit).bytes(circuit.get_num_cycles())?)
        .ok_or(SyntheticRequestError::InvalidShape)
}

fn init_teardown_elements(
    precomputations: &CircuitPrecomputations,
) -> Result<usize, SyntheticRequestError> {
    precomputations
        .compiled_circuit
        .trace_len
        .checked_sub(1)
        .and_then(|rows| {
            rows.checked_mul(
                precomputations
                    .compiled_circuit
                    .memory_layout
                    .shuffle_ram_inits_and_teardowns
                    .len(),
            )
        })
        .ok_or(SyntheticRequestError::InvalidShape)
}

pub(crate) fn allocation_bytes<T>(len: usize) -> Result<usize, SyntheticRequestError> {
    let bytes = len
        .checked_mul(size_of::<T>())
        .ok_or(SyntheticRequestError::InvalidShape)?;
    Ok(if bytes == 0 {
        0
    } else if bytes <= 256 << 10 {
        bytes.next_multiple_of(256)
    } else {
        bytes.next_multiple_of(1 << 20)
    })
}

fn pinned_filled_trace<T: Copy>(
    total_elements: usize,
    value: T,
) -> Result<
    crate::witness::trace::ChunkedTraceHolder<T, ConcurrentStaticHostAllocator>,
    SyntheticRequestError,
> {
    use crate::witness::trace::ChunkedTraceHolder;
    use era_cudart::memory::{CudaHostAllocFlags, HostAllocation};

    assert_ne!(size_of::<T>(), 0);
    let elements_per_chunk = (TRACE_CHUNK_BYTES / size_of::<T>()).max(1);
    let mut remaining = total_elements;
    let mut chunks = Vec::new();
    while remaining != 0 {
        let elements = remaining.min(elements_per_chunk);
        let backing = HostAllocation::alloc(TRACE_CHUNK_BYTES, CudaHostAllocFlags::DEFAULT)?;
        let allocator = ConcurrentStaticHostAllocator::new([backing], 26);
        let mut chunk = Vec::with_capacity_in(elements, allocator);
        chunk.extend(std::iter::repeat_n(value, elements));
        chunks.push(Arc::new(chunk));
        remaining -= elements;
    }
    Ok(ChunkedTraceHolder { chunks })
}
