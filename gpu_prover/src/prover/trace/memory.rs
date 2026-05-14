use crate::ops::blake2s::Digest;
use crate::primitives::callbacks::Callbacks;
use crate::primitives::circuit_type::{CircuitType, UnrolledCircuitType};
use crate::primitives::context::{ProverContext, UnsafeMutAccessor};
use crate::primitives::device_structures::DeviceMatrixMut;
use crate::primitives::device_tracing::Range;
use crate::primitives::field::BF;
use crate::prover::trace::decoder::DecoderTableTransfer;
use crate::prover::trace::holder::{bitreverse_index, TraceHolder, TreesCacheMode};
use crate::prover::trace::tracing_data::{
    DelegationTracingDataDevice, InitsAndTeardownsTransfer, TracingDataDevice, TracingDataTransfer,
    UnrolledTracingDataDevice,
};
use crate::witness::memory_delegation::generate_memory_values_delegation;
use crate::witness::memory_unrolled::{
    generate_memory_and_witness_values_unrolled_inits_and_teardowns,
    generate_memory_values_unrolled_memory, generate_memory_values_unrolled_non_memory,
};
use crate::witness::trace_unrolled::{ExecutorFamilyDecoderData, PAGE_SIZE_LOG2};

use crate::upstream::{GKRCircuitArtifact, MerkleTreeCapVarLength, ProverConfig};
use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use fft::GoodAllocator;

pub(crate) struct MemoryCommitmentJob<'a> {
    is_finished_event: CudaEvent,
    callbacks: Callbacks<'a>,
    tree_caps: Box<Option<Vec<MerkleTreeCapVarLength>>>,
    range: Range,
}

impl<'a> MemoryCommitmentJob<'a> {
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
fn commit_memory_inner<'a>(
    circuit_type: CircuitType,
    compiled_circuit: &GKRCircuitArtifact<BF>,
    decoder_table: Option<&DeviceSlice<ExecutorFamilyDecoderData>>,
    inits_and_teardowns: Option<&crate::witness::trace_unrolled::InitsAndTeardownsTraceDevice>,
    tracing_data: Option<&TracingDataDevice>,
    prover_config: &ProverConfig,
    mut callbacks: Callbacks<'a>,
    context: &ProverContext,
) -> CudaResult<MemoryCommitmentJob<'a>> {
    crate::prover::proof::assert_gpu_supported_pow_config(prover_config);
    assert_eq!(
        prover_config.base_oracles_values_per_leaf.trailing_zeros() as usize,
        prover_config.whir_schedule.whir_steps_schedule[0]
    );
    let log_lde_factor = prover_config.lde_factor.trailing_zeros();
    let log_rows_per_leaf = prover_config.base_oracles_values_per_leaf.trailing_zeros();
    let log_tree_cap_size = prover_config.cap_size.trailing_zeros();
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
    let range = Range::new("commit_memory")?;
    let stream = context.get_exec_stream();
    range.start(stream)?;
    let mut evaluations = memory_holder.get_uninit_hypercube_evals_mut();
    let memory = &mut DeviceMatrixMut::new(&mut evaluations, trace_len);
    match (circuit_type, tracing_data.as_ref()) {
        (
            CircuitType::Delegation(circuit_type),
            Some(TracingDataDevice::Delegation(DelegationTracingDataDevice::BigIntWithControl(
                trace,
            ))),
        ) => {
            assert_eq!(
                circuit_type,
                crate::primitives::circuit_type::DelegationCircuitType::BigIntWithControl
            );
            generate_memory_values_delegation(compiled_circuit, trace, memory, stream)?;
        }
        (
            CircuitType::Delegation(circuit_type),
            Some(TracingDataDevice::Delegation(
                DelegationTracingDataDevice::Blake2WithCompression(trace),
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
            Some(TracingDataDevice::Delegation(DelegationTracingDataDevice::Blake2GFunction(
                trace,
            ))),
        ) => {
            assert_eq!(
                circuit_type,
                crate::primitives::circuit_type::DelegationCircuitType::Blake2GFunction
            );
            generate_memory_values_delegation(compiled_circuit, trace, memory, stream)?;
        }
        (
            CircuitType::Delegation(circuit_type),
            Some(TracingDataDevice::Delegation(DelegationTracingDataDevice::KeccakSpecial5(trace))),
        ) => {
            assert_eq!(
                circuit_type,
                crate::primitives::circuit_type::DelegationCircuitType::KeccakSpecial5
            );
            generate_memory_values_delegation(compiled_circuit, trace, memory, stream)?;
        }
        (
            CircuitType::Unrolled(UnrolledCircuitType::NonMemory(circuit_type)),
            Some(TracingDataDevice::Unrolled(UnrolledTracingDataDevice::NonMemory(trace))),
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
            Some(TracingDataDevice::Unrolled(UnrolledTracingDataDevice::Memory(trace))),
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
        (CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns), None) => {
            let inits_and_teardowns = inits_and_teardowns
                .as_ref()
                .expect("standalone init/teardown circuit requires init/teardown data");
            generate_memory_and_witness_values_unrolled_inits_and_teardowns(
                &compiled_circuit.memory_layout,
                log_domain_size,
                PAGE_SIZE_LOG2,
                inits_and_teardowns,
                memory,
                stream,
            )?;
        }
        (
            CircuitType::Unrolled(UnrolledCircuitType::Unified),
            Some(TracingDataDevice::Unrolled(UnrolledTracingDataDevice::Unified(_))),
        ) => {
            unimplemented!("unified memory commitment is not implemented yet")
        }
        _ => unimplemented!(
            "commit_memory received an unsupported witness shape for circuit {circuit_type:?}"
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
        let mut per_coset_caps: Vec<MerkleTreeCapVarLength> = (0..lde_factor)
            .map(|_| MerkleTreeCapVarLength { cap: Vec::new() })
            .collect();
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

#[cfg(test)]
pub(crate) fn commit_memory<'a>(
    circuit_type: CircuitType,
    compiled_circuit: &GKRCircuitArtifact<BF>,
    decoder_table: Option<&DeviceSlice<ExecutorFamilyDecoderData>>,
    tracing_data: &TracingDataDevice,
    prover_config: &ProverConfig,
    context: &ProverContext,
) -> CudaResult<MemoryCommitmentJob<'a>> {
    commit_memory_inner(
        circuit_type,
        compiled_circuit,
        decoder_table,
        None,
        Some(tracing_data),
        prover_config,
        Callbacks::new(),
        context,
    )
}

pub(crate) fn commit_memory_from_transfers<'a, A: GoodAllocator + 'a>(
    circuit_type: CircuitType,
    compiled_circuit: &GKRCircuitArtifact<BF>,
    decoder_transfer: Option<DecoderTableTransfer<'a>>,
    inits_and_teardowns_transfer: Option<InitsAndTeardownsTransfer<'a>>,
    tracing_data_transfer: Option<TracingDataTransfer<'a, A>>,
    prover_config: &ProverConfig,
    context: &ProverContext,
) -> CudaResult<MemoryCommitmentJob<'a>> {
    let mut callbacks = Callbacks::new();
    let decoder_table = if let Some(decoder_transfer) = decoder_transfer {
        decoder_transfer.transfer.ensure_transferred(context)?;
        let DecoderTableTransfer {
            data_host: _,
            data_device,
            transfer,
        } = decoder_transfer;
        callbacks.extend(transfer.into_callbacks());
        Some(data_device)
    } else {
        None
    };
    let inits_and_teardowns =
        if let Some(inits_and_teardowns_transfer) = inits_and_teardowns_transfer {
            let InitsAndTeardownsTransfer {
                data_host: _,
                data_device,
                transfer,
            } = inits_and_teardowns_transfer;
            transfer.ensure_transferred(context)?;
            callbacks.extend(transfer.into_callbacks());
            Some(data_device)
        } else {
            None
        };
    let tracing_data = if let Some(tracing_data_transfer) = tracing_data_transfer {
        let TracingDataTransfer {
            data_host: _,
            data_device,
            transfer,
        } = tracing_data_transfer;
        transfer.ensure_transferred(context)?;
        callbacks.extend(transfer.into_callbacks());
        Some(data_device)
    } else {
        None
    };
    commit_memory_inner(
        circuit_type,
        compiled_circuit,
        decoder_table.as_ref().map(|t| &t[..]),
        inits_and_teardowns.as_ref(),
        tracing_data.as_ref(),
        prover_config,
        callbacks,
        context,
    )
}
