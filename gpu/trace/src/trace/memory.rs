use crate::trace::holder::{bitreverse_index, device_range, TraceHolder, TreesCacheMode};
use crate::trace::tracing_data::{
    DelegationTracingDataDevice, TracingDataDevice, UnrolledTracingDataDevice,
};
use crate::witness::circuit_type::{CircuitType, UnrolledCircuitType};
use crate::witness::memory_delegation::generate_memory_values_delegation;
use crate::witness::memory_unrolled::{
    generate_memory_and_witness_values_unrolled_inits_and_teardowns,
    generate_memory_values_unrolled_memory, generate_memory_values_unrolled_non_memory,
    generate_memory_values_unrolled_unified, InitsAndTeardownsPages,
};
use crate::witness::trace_unrolled::{ExecutorFamilyDecoderData, TraceCycles, PAGE_SIZE_LOG2};
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::context::UnsafeMutAccessor;
use gpu_core::primitives::device_structures::DeviceMatrixMut;
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::BF;
use gpu_hash::blake2s::Digest;
use gpu_prover_context::replay::{PhaseOutcome, ReplayInputs};
use gpu_prover_context::transfer::TransferKeepalive;
use gpu_prover_context::ProverContext;

use crate::upstream::{GKRCircuitArtifact, MerkleTreeCapVarLength, ProverConfig};
use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use fft::GoodAllocator;

pub struct MemoryCommitmentJob<'a> {
    is_finished_event: CudaEvent,
    callbacks: Callbacks<'a>,
    inputs: Option<TransferKeepalive<'a>>,
    tree_caps: Box<Option<Vec<MerkleTreeCapVarLength>>>,
    range: Range,
}

impl<'a> MemoryCommitmentJob<'a> {
    pub fn finish(self) -> CudaResult<(Vec<MerkleTreeCapVarLength>, f32)> {
        let Self {
            is_finished_event,
            callbacks,
            inputs,
            tree_caps,
            range,
        } = self;
        is_finished_event.synchronize()?;
        drop(callbacks);
        drop(inputs);
        let tree_caps = tree_caps.unwrap();
        let commitment_time_ms = range.elapsed()?;
        Ok((tree_caps, commitment_time_ms))
    }
}

fn commit_memory_inner<'a>(
    circuit_type: CircuitType,
    compiled_circuit: &GKRCircuitArtifact<BF>,
    decoder_table: Option<&DeviceSlice<ExecutorFamilyDecoderData>>,
    inits_and_teardowns: Option<&crate::witness::trace_unrolled::InitsAndTeardownsTraceDevice>,
    tracing_data: Option<&TracingDataDevice>,
    prover_config: &ProverConfig,
    inputs: Option<TransferKeepalive<'a>>,
    context: &ProverContext,
) -> CudaResult<MemoryCommitmentJob<'a>> {
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
    let key = format!("commit_memory|{circuit_type:?}|{prover_config:?}");
    let (replay_ranges, trace_cycles) = commit_replay_inputs(
        decoder_table,
        inits_and_teardowns,
        tracing_data,
        &memory_holder,
    );
    let mut replay_inputs = ReplayInputs::default();
    if let Some(cycles) = trace_cycles {
        replay_inputs.insert(TraceCycles(cycles));
    }
    if let Some(it) = inits_and_teardowns {
        replay_inputs.insert(InitsAndTeardownsPages(it.page_indices.len() as u32));
    }
    let cap_location = context.replay_phase(
        &key,
        &replay_ranges,
        &replay_inputs,
        || range.start(stream),
        || {
            let evaluations = memory_holder.get_uninit_hypercube_evals_mut();
            let memory = &mut DeviceMatrixMut::new(evaluations, trace_len);
            match (circuit_type, tracing_data.as_ref()) {
                (
                    CircuitType::Delegation(circuit_type),
                    Some(TracingDataDevice::Delegation(DelegationTracingDataDevice::BigIntWithControl(trace))),
                ) => {
                    assert_eq!(
                        circuit_type,
                        crate::witness::circuit_type::DelegationCircuitType::BigIntWithControl
                    );
                    generate_memory_values_delegation::<
                        _,
                        { crate::witness::circuit_type::DelegationCircuitType::BigIntWithControl as u16 },
                    >(compiled_circuit, trace, memory, stream)?;
                }
                (
                    CircuitType::Delegation(circuit_type),
                    Some(TracingDataDevice::Delegation(DelegationTracingDataDevice::Blake2WithCompression(trace))),
                ) => {
                    assert_eq!(
                        circuit_type,
                        crate::witness::circuit_type::DelegationCircuitType::Blake2WithCompression
                    );
                    generate_memory_values_delegation::<
                        _,
                        { crate::witness::circuit_type::DelegationCircuitType::Blake2WithCompression as u16 },
                    >(compiled_circuit, trace, memory, stream)?;
                }
                (
                    CircuitType::Delegation(circuit_type),
                    Some(TracingDataDevice::Delegation(DelegationTracingDataDevice::Blake2GFunction(trace))),
                ) => {
                    assert_eq!(
                        circuit_type,
                        crate::witness::circuit_type::DelegationCircuitType::Blake2GFunction
                    );
                    generate_memory_values_delegation::<
                        _,
                        { crate::witness::circuit_type::DelegationCircuitType::Blake2GFunction as u16 },
                    >(compiled_circuit, trace, memory, stream)?;
                }
                (
                    CircuitType::Delegation(circuit_type),
                    Some(TracingDataDevice::Delegation(DelegationTracingDataDevice::KeccakSpecial5(trace))),
                ) => {
                    assert_eq!(
                        circuit_type,
                        crate::witness::circuit_type::DelegationCircuitType::KeccakSpecial5
                    );
                    generate_memory_values_delegation::<
                        _,
                        { crate::witness::circuit_type::DelegationCircuitType::KeccakSpecial5 as u16 },
                    >(compiled_circuit, trace, memory, stream)?;
                }
                (
                    CircuitType::Delegation(circuit_type),
                    Some(TracingDataDevice::Delegation(DelegationTracingDataDevice::KeccakColumnParity(trace))),
                ) => {
                    assert_eq!(
                        circuit_type,
                        crate::witness::circuit_type::DelegationCircuitType::KeccakColumnParity
                    );
                    generate_memory_values_delegation::<
                        _,
                        { crate::witness::circuit_type::DelegationCircuitType::KeccakColumnParity as u16 },
                    >(compiled_circuit, trace, memory, stream)?;
                }
                (
                    CircuitType::Delegation(circuit_type),
                    Some(TracingDataDevice::Delegation(DelegationTracingDataDevice::KeccakThetaRho(trace))),
                ) => {
                    assert_eq!(
                        circuit_type,
                        crate::witness::circuit_type::DelegationCircuitType::KeccakThetaRho
                    );
                    generate_memory_values_delegation::<
                        _,
                        { crate::witness::circuit_type::DelegationCircuitType::KeccakThetaRho as u16 },
                    >(compiled_circuit, trace, memory, stream)?;
                }
                (
                    CircuitType::Delegation(circuit_type),
                    Some(TracingDataDevice::Delegation(DelegationTracingDataDevice::KeccakChi5(trace))),
                ) => {
                    assert_eq!(
                        circuit_type,
                        crate::witness::circuit_type::DelegationCircuitType::KeccakChi5
                    );
                    generate_memory_values_delegation::<
                        _,
                        { crate::witness::circuit_type::DelegationCircuitType::KeccakChi5 as u16 },
                    >(compiled_circuit, trace, memory, stream)?;
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
                    Some(TracingDataDevice::Unrolled(UnrolledTracingDataDevice::Unified(trace))),
                ) => {
                    // Inline i/t paged sweep FIRST (page-based-reuse): it zeroes the
                    // whole matrix (set_to_zero) then writes the teardown columns; the per-row unified
                    // memory-values launch below fills machine_state + shuffle_ram. Mirrors the standalone
                    // InitsAndTeardowns arm above. A TRIVIAL (dummy) chunk has no pages, so its
                    // i/t columns stay all zero, as the CPU reference commits them.
                    generate_memory_and_witness_values_unrolled_inits_and_teardowns(
                        &compiled_circuit.memory_layout,
                        log_domain_size,
                        PAGE_SIZE_LOG2,
                        inits_and_teardowns
                            .expect("unified circuit requires init/teardown buffers"),
                        memory,
                        stream,
                    )?;
                    generate_memory_values_unrolled_unified(
                        &compiled_circuit.memory_layout,
                        decoder_table.expect("unified circuit requires a decoder table"),
                        trace,
                        memory,
                        stream,
                    )?;
                }
                _ => unimplemented!(
            "commit_memory received an unsupported witness shape for circuit {circuit_type:?}"
        ),
            }
            let _ = evaluations;
            memory_holder.commit_all(context)?;
            let cap = memory_holder.unified_device_cap();
            Ok((cap.as_ptr() as usize, cap.len()))
        },
        |&cap_location| cap_location,
    )?;
    let (cap_addr, cap_len) = match cap_location {
        PhaseOutcome::Executed(cap_location) | PhaseOutcome::Replayed(cap_location) => cap_location,
    };
    // SAFETY: the cap lives at this address in both the executed and the
    // replayed graph, and nothing reallocates it before this copy is enqueued.
    let cap_device = unsafe { DeviceSlice::from_raw_parts(cap_addr as *const Digest, cap_len) };
    // Schedule a D2H of the unified device cap into a pinned host buffer; the
    // callback below slices that single contiguous cap into per-coset
    // `MerkleTreeCapVarLength` entries (canonical bit-reversed coset order).
    let log_lde = memory_holder.log_lde_factor;
    let lde_factor = 1usize << log_lde;
    let cap_size = 1usize << log_tree_cap_size;
    let mut cap_host = unsafe { context.alloc_host_uninit_slice::<Digest>(cap_size) };
    memory_copy_async(&mut cap_host, cap_device, stream)?;
    let cap_host_accessor = cap_host.get_accessor();
    let mut tree_caps = Box::new(None);
    let dst_tree_caps_accessor = UnsafeMutAccessor::new(tree_caps.as_mut());
    let transform_tree_caps_fn = move || unsafe {
        let unified = cap_host_accessor.get();
        debug_assert_eq!(unified.len() % lde_factor, 0);
        let per_coset = unified.len() / lde_factor;
        // Reorder the unified cap from bit-reversed to natural coset order.
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
    let mut callbacks = Callbacks::new();
    callbacks.schedule(transform_tree_caps_fn, stream)?;
    // `cap_host` (pool-backed pinned host buffer) drops at end of this function;
    // the callback above has already been scheduled, so the contract's
    // scheduled-not-completed lifetime rule is satisfied.
    drop(cap_host);
    range.end(stream)?;
    let is_finished_event = CudaEvent::create_with_flags(
        CudaEventCreateFlags::DISABLE_TIMING | CudaEventCreateFlags::BLOCKING_SYNC,
    )?;
    is_finished_event.record(stream)?;
    let job = MemoryCommitmentJob {
        is_finished_event,
        callbacks,
        inputs,
        tree_caps,
        range,
    };
    Ok(job)
}

/// Device ranges a commitment graph reads, and the visible trace length.
fn commit_replay_inputs(
    decoder_table: Option<&DeviceSlice<ExecutorFamilyDecoderData>>,
    inits_and_teardowns: Option<&crate::witness::trace_unrolled::InitsAndTeardownsTraceDevice>,
    tracing_data: Option<&TracingDataDevice>,
    memory_holder: &TraceHolder<BF>,
) -> (Vec<(usize, usize)>, Option<u32>) {
    let mut ranges = memory_holder.device_ranges();
    let mut cycles = None;
    if let Some(decoder_table) = decoder_table {
        ranges.push((
            decoder_table.as_ptr() as usize,
            std::mem::size_of_val(decoder_table),
        ));
    }
    if let Some(it) = inits_and_teardowns {
        ranges.extend([
            device_range(&it.page_indices),
            device_range(&it.values_packed),
            device_range(&it.timestamps_packed),
        ]);
    }
    if let Some(tracing_data) = tracing_data {
        let (range, len) = tracing_data.range_and_len();
        ranges.push(range);
        cycles = Some(len as u32);
    }
    (ranges, cycles)
}

#[doc(hidden)]
pub fn commit_memory<'a>(
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
        None,
        context,
    )
}

pub fn commit_memory_from_transfers<'a, A: GoodAllocator + 'a>(
    circuit_type: CircuitType,
    compiled_circuit: &GKRCircuitArtifact<BF>,
    inputs: super::memory_transfer::GpuGKRCommitMemoryTransfer<'a, A>,
    prover_config: &ProverConfig,
    context: &ProverContext,
) -> CudaResult<MemoryCommitmentJob<'a>> {
    // One exec-stream wait covers every H2D bundled by `inputs` (decoder,
    // inits_and_teardowns, tracing_data).
    inputs.ensure_transferred(context)?;
    let super::memory_transfer::GpuGKRCommitMemoryTransfer {
        transfer,
        decoder,
        inits_and_teardowns,
        tracing_data,
    } = inputs;
    // Device reservations live through enqueue; H2D sources move into the job
    // and live through its completion synchronization.
    commit_memory_inner(
        circuit_type,
        compiled_circuit,
        decoder.as_ref().map(|t| &t.data_device[..]),
        inits_and_teardowns.as_ref().map(|t| &t.data_device),
        tracing_data.as_ref().map(|t| &t.data_device),
        prover_config,
        Some(transfer.into_keepalive()),
        context,
    )
}
