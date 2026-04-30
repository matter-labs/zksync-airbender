use crate::ops::blake2s::Digest;
use crate::primitives::callbacks::Callbacks;
use crate::primitives::circuit_type::{CircuitType, UnrolledCircuitType};
use crate::primitives::context::{ProverContext, UnsafeMutAccessor};
use crate::primitives::device_structures::DeviceMatrixMut;
use crate::primitives::device_tracing::Range;
use crate::primitives::field::BF;
use crate::prover::trace_holder::{bitreverse_index, TraceHolder, TreesCacheMode};
use crate::prover::tracing_data::{
    DelegationTracingDataDevice, TracingDataDevice, UnrolledTracingDataDevice,
};
use crate::witness::memory_delegation::generate_memory_values_delegation;
use crate::witness::memory_unrolled::{
    generate_memory_values_unrolled_memory, generate_memory_values_unrolled_non_memory,
};
use crate::witness::trace_unrolled::ExecutorFamilyDecoderData;
use cs::gkr_compiler::GKRCircuitArtifact;
use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use prover::merkle_trees::MerkleTreeCapVarLength;

pub(crate) struct MemoryCommitmentJob<'a> {
    is_finished_event: CudaEvent,
    callbacks: Callbacks<'a>,
    tree_caps: Box<Option<Vec<MerkleTreeCapVarLength>>>,
    range: Range,
}

impl<'a> MemoryCommitmentJob<'a> {
    pub(crate) fn is_finished(&self) -> CudaResult<bool> {
        self.is_finished_event.query()
    }

    pub(crate) fn finish(self) -> CudaResult<(Vec<MerkleTreeCapVarLength>, f32)> {
        let Self {
            is_finished_event,
            callbacks,
            tree_caps,
            range,
        } = self;
        is_finished_event.synchronize()?;
        drop(callbacks);
        let tree_caps = tree_caps.unwrap();
        let commitment_time_ms = range.elapsed()?;
        Ok((tree_caps, commitment_time_ms))
    }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn commit_memory<'a>(
    circuit_type: CircuitType,
    compiled_circuit: &GKRCircuitArtifact<BF>,
    decoder_table: Option<&DeviceSlice<ExecutorFamilyDecoderData>>,
    tracing_data: &TracingDataDevice,
    log_lde_factor: u32,
    log_rows_per_leaf: u32,
    log_tree_cap_size: u32,
    context: &ProverContext,
) -> CudaResult<MemoryCommitmentJob<'a>> {
    let trace_len = compiled_circuit.trace_len;
    assert!(trace_len.is_power_of_two());
    let log_domain_size = trace_len.trailing_zeros();
    let memory_columns_count = compiled_circuit.memory_layout.total_width;
    let mut memory_holder = TraceHolder::new(
        log_domain_size,
        log_lde_factor,
        log_rows_per_leaf,
        log_tree_cap_size,
        memory_columns_count,
        TreesCacheMode::CachePartial,
        context,
    )?;
    let mut callbacks = Callbacks::new();
    let range = Range::new("commit_memory")?;
    let stream = context.get_exec_stream();
    range.start(stream)?;
    let mut evaluations = memory_holder.get_uninit_hypercube_evals_mut();
    let memory = &mut DeviceMatrixMut::new(&mut evaluations, trace_len);
    match (circuit_type, tracing_data) {
        (
            CircuitType::Delegation(circuit_type),
            TracingDataDevice::Delegation(DelegationTracingDataDevice::BigIntWithControl(trace)),
        ) => {
            assert_eq!(
                circuit_type,
                crate::primitives::circuit_type::DelegationCircuitType::BigIntWithControl
            );
            generate_memory_values_delegation(compiled_circuit, trace, memory, stream)?;
        }
        (
            CircuitType::Delegation(circuit_type),
            TracingDataDevice::Delegation(DelegationTracingDataDevice::Blake2WithCompression(
                trace,
            )),
        ) => {
            assert_eq!(
                circuit_type,
                crate::primitives::circuit_type::DelegationCircuitType::Blake2WithCompression
            );
            generate_memory_values_delegation(compiled_circuit, trace, memory, stream)?;
        }
        (
            CircuitType::Delegation(circuit_type),
            TracingDataDevice::Delegation(DelegationTracingDataDevice::KeccakSpecial5(trace)),
        ) => {
            assert_eq!(
                circuit_type,
                crate::primitives::circuit_type::DelegationCircuitType::KeccakSpecial5
            );
            generate_memory_values_delegation(compiled_circuit, trace, memory, stream)?;
        }
        (
            CircuitType::Unrolled(UnrolledCircuitType::NonMemory(circuit_type)),
            TracingDataDevice::Unrolled(UnrolledTracingDataDevice::NonMemory(trace)),
        ) => {
            generate_memory_values_unrolled_non_memory(
                circuit_type,
                &compiled_circuit.memory_layout,
                decoder_table.expect("non-memory circuits require a decoder table"),
                trace,
                memory,
                stream,
            )?;
        }
        (
            CircuitType::Unrolled(UnrolledCircuitType::Memory(circuit_type)),
            TracingDataDevice::Unrolled(UnrolledTracingDataDevice::Memory(trace)),
        ) => {
            generate_memory_values_unrolled_memory(
                circuit_type,
                &compiled_circuit.memory_layout,
                decoder_table.expect("memory circuits require a decoder table"),
                trace,
                memory,
                stream,
            )?;
        }
        _ => unimplemented!(
            "commit_memory currently supports only delegation and unrolled non-memory/memory traces"
        ),
    }
    let _ = evaluations;
    memory_holder.commit_all(context)?;
    // Schedule a D2H of the unified device cap into a pinned host buffer; the
    // callback below slices that single contiguous cap into per-coset
    // `MerkleTreeCapVarLength` entries (canonical bit-reversed coset order).
    let log_lde = memory_holder.log_lde_factor;
    let lde_factor = 1usize << log_lde;
    let cap_size = 1usize << log_tree_cap_size;
    let mut cap_host = unsafe { context.alloc_host_uninit_slice::<Digest>(cap_size) };
    memory_copy_async(&mut cap_host, memory_holder.unified_device_cap(), stream)?;
    let cap_host_accessor = cap_host.get_accessor();
    let mut tree_caps = Box::new(None);
    let dst_tree_caps_accessor = UnsafeMutAccessor::new(tree_caps.as_mut());
    let transform_tree_caps_fn = move || unsafe {
        let unified = cap_host_accessor.get();
        debug_assert_eq!(unified.len() % lde_factor, 0);
        let per_coset = unified.len() / lde_factor;
        // Repack the unified cap (bit-reversed coset order) back into the
        // natural per-coset shape that `MemoryCommitmentJob`'s callers expect.
        let mut per_coset_caps: Vec<MerkleTreeCapVarLength> =
            (0..lde_factor).map(|_| MerkleTreeCapVarLength { cap: Vec::new() }).collect();
        for stage1_pos in 0..lde_factor {
            let natural_coset_index = bitreverse_index(stage1_pos, log_lde);
            per_coset_caps[natural_coset_index].cap =
                unified[stage1_pos * per_coset..(stage1_pos + 1) * per_coset].to_vec();
        }
        assert!(dst_tree_caps_accessor
            .get_mut()
            .replace(per_coset_caps)
            .is_none());
    };
    callbacks.schedule(transform_tree_caps_fn, stream)?;
    // `cap_host` (pool-backed pinned host buffer) drops at end of this function;
    // the callback above has already been scheduled, so the contract's
    // scheduled-not-completed lifetime rule is satisfied.
    drop(cap_host);
    range.end(stream)?;
    let is_finished_event = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
    is_finished_event.record(stream)?;
    let job = MemoryCommitmentJob {
        is_finished_event,
        callbacks,
        tree_caps,
        range,
    };
    Ok(job)
}
