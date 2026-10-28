use crate::trace::holder::{bitreverse_index, TraceHolder, TreesCacheMode};
use crate::trace::tracing_data::{
    DelegationTracingDataDevice, TracingDataDevice, UnrolledTracingDataDevice,
};
use crate::witness::circuit_type::{CircuitType, UnrolledCircuitType};
use crate::witness::memory_delegation::generate_memory_values_delegation;
use crate::witness::memory_unrolled::{
    generate_memory_and_witness_values_unrolled_inits_and_teardowns,
    generate_memory_values_unrolled_memory, generate_memory_values_unrolled_non_memory,
    generate_memory_values_unrolled_unified,
};
use crate::witness::trace_unrolled::{ExecutorFamilyDecoderData, PAGE_SIZE_LOG2};
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::context::UnsafeMutAccessor;
use gpu_core::primitives::device_structures::DeviceMatrixMut;
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::BF;
use gpu_hash::blake2s::Digest;
use gpu_prover_context::transfer::TransferKeepalive;
use gpu_prover_context::ProverContext;

use crate::upstream::{
    BaseColumns, BaseCommitmentGeometry, BaseOracleRole, CommitmentMode, GKRCircuitArtifact,
    MerkleTreeCapVarLength, ProverConfig,
};
use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use fft::GoodAllocator;

pub struct MemoryCommitmentJob<'a> {
    geometry: Option<BaseCommitmentGeometry>,
    is_finished_event: CudaEvent,
    callbacks: Callbacks<'a>,
    inputs: Option<TransferKeepalive<'a>>,
    tree_caps: Box<Option<Vec<MerkleTreeCapVarLength>>>,
    range: Range,
}

impl<'a> MemoryCommitmentJob<'a> {
    pub fn base_commitment_geometry(&self) -> Option<BaseCommitmentGeometry> {
        self.geometry
    }
    pub fn finish(self) -> CudaResult<(Vec<MerkleTreeCapVarLength>, f32)> {
        let Self {
            geometry: _,
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

/// The GPU prover commits every base column set over the circuit's own
/// `2^trace_len_log2` domain (one committed column per base column) and starts
/// WHIR from that size: it does not implement the base-commitment packing of
/// `ProverConfig::pack_log2` (`2^pack_log2` consecutive columns per committed
/// polynomial, WHIR message `2^(trace_len_log2 + pack_log2)`, `pack_log2` extra
/// claim-point coordinates drawn after the GKR phase). Every GPU entry that
/// takes a `ProverConfig` (the memory commitments here, `prove()` and the DR
/// preflight in `gpu_circuit_prover`) calls this before enqueuing any
/// commitment or proof kernel (the preflight rejects before transfers are
/// even constructed), so a packed config fails closed instead of yielding an
/// unpacked proof that the verifier generated from the same config rejects.
pub fn assert_unpacked_prover_config(prover_config: &ProverConfig) {
    assert_eq!(
        prover_config.pack_log2(),
        0,
        "GPU prover does not implement base-commitment packing: ProverConfig::pack_log2 = {} \
         (WHIR message 2^{}); prove packed configs with the CPU prover",
        prover_config.pack_log2(),
        prover_config.whir_message_size_log2(),
    );
    assert!(
        !prover_config.is_virtual_packing(),
        "GPU prover does not implement virtual packing (WhirBaseRoundSchedule::fold_log2 = 0, one \
         value per column per base leaf); prove such configs with the CPU prover"
    );
}

#[derive(Clone, Copy)]
enum MemoryCommitmentShape<'a> {
    Unpacked(&'a ProverConfig),
    Geometry(BaseCommitmentGeometry),
}

/// Bind protocol geometry to the existing logical memory producer before transfers.
pub fn validate_memory_commitment_geometry<F: crate::upstream::PrimeField>(
    geometry: &BaseCommitmentGeometry,
    compiled_circuit: &GKRCircuitArtifact<F>,
) {
    assert_eq!(
        geometry.commitment_mode(),
        CommitmentMode::SeparateMemoryAndWitness,
        "memory precommit requires separate memory and witness commitments"
    );
    assert_eq!(
        geometry.logical_columns(),
        BaseColumns::of(compiled_circuit),
        "memory precommit columns disagree with compiled circuit"
    );
    assert_eq!(
        1usize << geometry.trace_len_log2(),
        compiled_circuit.trace_len,
        "memory precommit trace length disagrees with compiled circuit"
    );
    TraceHolder::<F>::validate_base_layout(geometry, TreesCacheMode::CachePartial);
}

/// Geometry-taking form of the existing BF memory producer. Config-driven
/// entries retain their packing guards until full-proof admission is qualified.
#[allow(clippy::too_many_arguments)]
pub fn commit_memory_for_geometry<'a>(
    circuit_type: CircuitType,
    compiled_circuit: &GKRCircuitArtifact<BF>,
    decoder_table: Option<&DeviceSlice<ExecutorFamilyDecoderData>>,
    inits_and_teardowns: Option<&crate::witness::trace_unrolled::InitsAndTeardownsTraceDevice>,
    tracing_data: Option<&TracingDataDevice>,
    geometry: BaseCommitmentGeometry,
    context: &ProverContext,
) -> CudaResult<MemoryCommitmentJob<'a>> {
    commit_memory_inner(
        circuit_type,
        compiled_circuit,
        decoder_table,
        inits_and_teardowns,
        tracing_data,
        MemoryCommitmentShape::Geometry(geometry),
        None,
        context,
    )
}

fn commit_memory_inner<'a>(
    circuit_type: CircuitType,
    compiled_circuit: &GKRCircuitArtifact<BF>,
    decoder_table: Option<&DeviceSlice<ExecutorFamilyDecoderData>>,
    inits_and_teardowns: Option<&crate::witness::trace_unrolled::InitsAndTeardownsTraceDevice>,
    tracing_data: Option<&TracingDataDevice>,
    shape: MemoryCommitmentShape<'_>,
    inputs: Option<TransferKeepalive<'a>>,
    context: &ProverContext,
) -> CudaResult<MemoryCommitmentJob<'a>> {
    let trace_len = compiled_circuit.trace_len;
    assert!(trace_len.is_power_of_two());
    let log_domain_size = trace_len.trailing_zeros();
    let producing_geometry = match shape {
        MemoryCommitmentShape::Unpacked(_) => None,
        MemoryCommitmentShape::Geometry(geometry) => Some(geometry),
    };
    let mut memory_holder = match shape {
        MemoryCommitmentShape::Unpacked(config) => {
            assert_unpacked_prover_config(config);
            TraceHolder::new(
                log_domain_size,
                config.lde_factor().trailing_zeros(),
                config.base_oracles_values_per_leaf().trailing_zeros(),
                config.cap_size.trailing_zeros(),
                compiled_circuit.memory_layout.total_width,
                TreesCacheMode::CachePartial,
                context,
            )?
        }
        MemoryCommitmentShape::Geometry(geometry) => {
            validate_memory_commitment_geometry(&geometry, compiled_circuit);
            crate::trace::holder::validate_baby_bear_base_geometry(
                &geometry,
                context
                    .ntt_device_context()
                    .whir_leaf_transform_params()
                    .omega_log_order,
            );
            TraceHolder::new_base(
                geometry,
                BaseOracleRole::Memory,
                TreesCacheMode::CachePartial,
                context,
            )?
        }
    };
    let range = Range::new("commit_memory")?;
    let stream = context.get_exec_stream();
    range.start(stream)?;
    if producing_geometry.is_none() || memory_holder.columns_count != 0 {
        let evaluations = memory_holder.get_uninit_hypercube_evals_mut();
        let memory = &mut DeviceMatrixMut::new(evaluations, trace_len);
        match (circuit_type, tracing_data.as_ref()) {
            (
                CircuitType::Delegation(circuit_type),
                Some(TracingDataDevice::Delegation(
                    DelegationTracingDataDevice::BigIntWithControl(trace),
                )),
            ) => {
                assert_eq!(
                    circuit_type,
                    crate::witness::circuit_type::DelegationCircuitType::BigIntWithControl
                );
                generate_memory_values_delegation::<
                    _,
                    {
                        crate::witness::circuit_type::DelegationCircuitType::BigIntWithControl
                            as u16
                    },
                >(compiled_circuit, trace, memory, stream)?;
            }
            (
                CircuitType::Delegation(circuit_type),
                Some(TracingDataDevice::Delegation(
                    DelegationTracingDataDevice::Blake2WithCompression(trace),
                )),
            ) => {
                assert_eq!(
                    circuit_type,
                    crate::witness::circuit_type::DelegationCircuitType::Blake2WithCompression
                );
                generate_memory_values_delegation::<
                    _,
                    {
                        crate::witness::circuit_type::DelegationCircuitType::Blake2WithCompression
                            as u16
                    },
                >(compiled_circuit, trace, memory, stream)?;
            }
            (
                CircuitType::Delegation(circuit_type),
                Some(TracingDataDevice::Delegation(DelegationTracingDataDevice::Blake2GFunction(
                    trace,
                ))),
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
                Some(TracingDataDevice::Delegation(DelegationTracingDataDevice::KeccakSpecial5(
                    trace,
                ))),
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
                Some(TracingDataDevice::Delegation(
                    DelegationTracingDataDevice::KeccakColumnParity(trace),
                )),
            ) => {
                assert_eq!(
                    circuit_type,
                    crate::witness::circuit_type::DelegationCircuitType::KeccakColumnParity
                );
                generate_memory_values_delegation::<
                    _,
                    {
                        crate::witness::circuit_type::DelegationCircuitType::KeccakColumnParity
                            as u16
                    },
                >(compiled_circuit, trace, memory, stream)?;
            }
            (
                CircuitType::Delegation(circuit_type),
                Some(TracingDataDevice::Delegation(DelegationTracingDataDevice::KeccakThetaRho(
                    trace,
                ))),
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
                    inits_and_teardowns.expect("unified circuit requires init/teardown buffers"),
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
    }
    memory_holder.commit_all(context)?;
    // Schedule a D2H of the unified device cap into a pinned host buffer; the
    // callback below slices that single contiguous cap into per-coset
    // `MerkleTreeCapVarLength` entries (canonical bit-reversed coset order).
    let log_lde = memory_holder.log_lde_factor;
    let lde_factor = 1usize << log_lde;
    let cap_size = memory_holder.unified_device_cap().len();
    let mut cap_host = unsafe { context.alloc_host_uninit_slice::<Digest>(cap_size) };
    if cap_size != 0 {
        memory_copy_async(&mut cap_host, memory_holder.unified_device_cap(), stream)?;
    }
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
    let is_finished_event = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
    is_finished_event.record(stream)?;
    let job = MemoryCommitmentJob {
        geometry: producing_geometry,
        is_finished_event,
        callbacks,
        inputs,
        tree_caps,
        range,
    };
    Ok(job)
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
        MemoryCommitmentShape::Unpacked(prover_config),
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
    // reject a packed config before touching the streams
    assert_unpacked_prover_config(prover_config);
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
        MemoryCommitmentShape::Unpacked(prover_config),
        Some(transfer.into_keepalive()),
        context,
    )
}

#[cfg(test)]
mod tests {
    use super::assert_unpacked_prover_config;
    use prover::definitions::SecurityLevel;
    use prover::gkr::prover_config::example_configs::{
        config_for_security_level_under_pessimistic_conjecture,
        packed_config_for_security_level_under_pessimistic_conjecture,
    };

    #[test]
    fn cpu_unpacked_prover_config_is_accepted() {
        let config =
            config_for_security_level_under_pessimistic_conjecture(20, SecurityLevel::Sec100);
        assert_eq!(config.pack_log2(), 0);
        assert_unpacked_prover_config(&config);
    }

    #[test]
    #[should_panic(expected = "GPU prover does not implement base-commitment packing")]
    fn cpu_packed_prover_config_is_rejected() {
        let config = packed_config_for_security_level_under_pessimistic_conjecture(
            20,
            4,
            SecurityLevel::Sec100,
        );
        assert_eq!(config.pack_log2(), 4);
        assert_unpacked_prover_config(&config);
    }
}
