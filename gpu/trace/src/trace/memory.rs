use crate::trace::holder::{
    bitreverse_index, TraceHolder, TreesCacheMode, TreesHolder, WitnessPostCommitStorage,
};
use crate::trace::memory_transfer::{
    validate_partial_trees, PartialTrees, PartialTreesGeometry, PARTIAL_TREES_LAYOUT_VERSION,
};
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
use era_cudart::slice::{CudaSliceMut, DeviceSlice};
use fft::GoodAllocator;

pub struct MemoryCommitmentJob<'a> {
    geometry: Option<BaseCommitmentGeometry>,
    is_finished_event: CudaEvent,
    callbacks: Callbacks<'a>,
    inputs: Option<TransferKeepalive<'a>>,
    tree_caps: Box<Option<Vec<MerkleTreeCapVarLength>>>,
    partial_trees: Option<(PartialTreesGeometry, Box<Option<Vec<Digest>>>)>,
    range: Range,
}

impl<'a> MemoryCommitmentJob<'a> {
    pub fn base_commitment_geometry(&self) -> Option<BaseCommitmentGeometry> {
        self.geometry
    }
    pub fn finish(self) -> CudaResult<(Vec<MerkleTreeCapVarLength>, f32)> {
        let (tree_caps, partial_trees, commitment_time_ms) = self.finish_with_partial_trees()?;
        assert!(
            partial_trees.is_none(),
            "exported partial trees must be taken with finish_with_partial_trees"
        );
        Ok((tree_caps, commitment_time_ms))
    }

    /// The per-coset caps plus the partial trees, if this commitment exported them.
    pub fn finish_with_partial_trees(
        self,
    ) -> CudaResult<(Vec<MerkleTreeCapVarLength>, Option<PartialTrees>, f32)> {
        let Self {
            geometry: _,
            is_finished_event,
            callbacks,
            inputs,
            tree_caps,
            partial_trees,
            range,
        } = self;
        is_finished_event.synchronize()?;
        drop(callbacks);
        drop(inputs);
        let tree_caps = tree_caps.unwrap();
        let partial_trees = partial_trees.map(|(geometry, nodes)| {
            let trees = PartialTrees {
                layout_version: PARTIAL_TREES_LAYOUT_VERSION,
                geometry,
                nodes: nodes.unwrap(),
            };
            validate_partial_trees(&trees, &geometry, &tree_caps);
            trees
        });
        let commitment_time_ms = range.elapsed()?;
        Ok((tree_caps, partial_trees, commitment_time_ms))
    }
}

/// Whether base storage must carry the resolved commitment geometry.
/// Cross-crate producers preserve the legacy k0/f1 separate allocation path,
/// while virtual or merged commitments also carry geometry at pad zero.
pub fn uses_base_commitment_geometry(geometry: &BaseCommitmentGeometry) -> bool {
    geometry.pack_log2() != 0
        || geometry.is_virtual_packing()
        || geometry.commitment_mode() == CommitmentMode::MergedMemoryAndWitness
}

/// Field-free admission shared by config-driven memory and proof entries.
/// The generated base opening verifier has one or two accumulators (f0/f1).
pub fn validate_separate_base_commitment_geometry(geometry: &BaseCommitmentGeometry) {
    assert!(
        geometry.values_per_leaf() <= 2,
        "GPU base opening verifier supports only fold_log2<=1 (one or two accumulators)"
    );
    assert_eq!(
        geometry.commitment_mode(),
        CommitmentMode::SeparateMemoryAndWitness,
        "memory-only producer requires separate memory and witness commitments"
    );
}

/// Check the immutable config/geometry pair against its logical producer.
/// Legacy k0/f1 does not enter the packed holder's transform/policy validators.
pub fn validate_memory_commitment_config<F: crate::upstream::PrimeField>(
    config: &ProverConfig,
    geometry: &BaseCommitmentGeometry,
    circuit: &GKRCircuitArtifact<F>,
) {
    let expected = BaseCommitmentGeometry::from_config(config, BaseColumns::of(circuit))
        .expect("invalid memory commitment config");
    assert_eq!(
        *geometry, expected,
        "memory commitment config/geometry mismatch"
    );
    assert_eq!(
        1usize << geometry.trace_len_log2(),
        circuit.trace_len,
        "memory commitment config trace length mismatch"
    );
    validate_separate_base_commitment_geometry(geometry);
    if uses_base_commitment_geometry(geometry) {
        validate_memory_commitment_geometry(geometry, circuit);
    }
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
    validate_stage1_commitment_geometry(geometry, compiled_circuit);
}

/// Field-independent shape binding for separate or concatenated stage1 storage.
pub fn validate_stage1_commitment_geometry<F: crate::upstream::PrimeField>(
    geometry: &BaseCommitmentGeometry,
    compiled_circuit: &GKRCircuitArtifact<F>,
) {
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

fn commit_memory_inner<'a>(
    circuit_type: CircuitType,
    compiled_circuit: &GKRCircuitArtifact<BF>,
    decoder_table: Option<&DeviceSlice<ExecutorFamilyDecoderData>>,
    inits_and_teardowns: Option<&crate::witness::trace_unrolled::InitsAndTeardownsTraceDevice>,
    tracing_data: Option<&TracingDataDevice>,
    shape: MemoryCommitmentShape<'_>,
    partial_tree_reduction_layers: u32,
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
        MemoryCommitmentShape::Unpacked(config) => TraceHolder::new(
            log_domain_size,
            config.lde_factor().trailing_zeros(),
            config.base_oracles_values_per_leaf().trailing_zeros(),
            config.cap_size.trailing_zeros(),
            compiled_circuit.memory_layout.total_width,
            TreesCacheMode::CachePartial,
            partial_tree_reduction_layers,
            context,
        )?,
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
                partial_tree_reduction_layers,
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
                CircuitType::Unrolled(
                    unified @ (UnrolledCircuitType::Unified | UnrolledCircuitType::Unified22),
                ),
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
                    unified,
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
    schedule_memory_commitment_job(&mut memory_holder, Callbacks::new(), inputs, range, context)
}

/// Commits `holder` (already holding its hypercube evals) and returns the job
/// whose `finish` yields the per-coset caps in natural coset order.
pub fn schedule_memory_commitment_job<'a>(
    holder: &mut TraceHolder<BF>,
    callbacks: Callbacks<'a>,
    inputs: Option<TransferKeepalive<'a>>,
    range: Range,
    context: &ProverContext,
) -> CudaResult<MemoryCommitmentJob<'a>> {
    holder.commit_all(context)?;
    schedule_memory_cap_readback(holder, callbacks, inputs, range, false, context)
}

pub fn schedule_memory_commitment_job_in_place<'a>(
    holder: &mut TraceHolder<BF>,
    callbacks: Callbacks<'a>,
    inputs: Option<TransferKeepalive<'a>>,
    range: Range,
    context: &ProverContext,
) -> CudaResult<MemoryCommitmentJob<'a>> {
    holder.install_partial_trees(context)?;
    holder.commit_in_place(None, context)?;
    schedule_memory_cap_readback(holder, callbacks, inputs, range, false, context)
}

/// With `persist_partial_trees`, the job also exports the partial trees for
/// the proof to open instead of rebuilding them.
pub fn schedule_memory_commitment_job_with_monomials<'a>(
    holder: &mut TraceHolder<BF>,
    callbacks: Callbacks<'a>,
    inputs: Option<TransferKeepalive<'a>>,
    range: Range,
    persist_partial_trees: bool,
    context: &ProverContext,
) -> CudaResult<MemoryCommitmentJob<'a>> {
    holder.install_partial_trees(context)?;
    holder.commit_with_monomials(None, context)?;
    holder.retain_after_commitment(WitnessPostCommitStorage::RawAndMonomials);
    schedule_memory_cap_readback(
        holder,
        callbacks,
        inputs,
        range,
        persist_partial_trees,
        context,
    )
}

/// Copies only the nodes the builder wrote (`PARTIAL_TREES_LAYOUT_VERSION`)
/// into one compact readback buffer, then into the returned host vector.
fn schedule_partial_trees_readback<'a>(
    holder: &TraceHolder<BF>,
    callbacks: &mut Callbacks<'a>,
    context: &ProverContext,
) -> CudaResult<(PartialTreesGeometry, Box<Option<Vec<Digest>>>)> {
    assert!(
        matches!(holder.trees, TreesHolder::Partial(_)),
        "partial-tree export requires cached partial trees"
    );
    let geometry = PartialTreesGeometry::of_holder(holder);
    let live = geometry.coset_live_len();
    let stream = context.get_exec_stream();
    let mut nodes_host =
        unsafe { context.alloc_host_uninit_slice::<Digest>(geometry.cosets_count() * live) };
    for coset in 0..geometry.cosets_count() {
        let tree = holder
            .get_tree_slice(coset)
            .expect("partial trees are cached");
        // SAFETY: an in-bounds subrange of the readback buffer, written only by
        // this copy and read only by the callback scheduled after it.
        let dst = unsafe { &mut nodes_host.as_mut_slice()[coset * live..(coset + 1) * live] };
        memory_copy_async(dst, &tree[..live], stream)?;
    }
    let nodes_host_accessor = nodes_host.get_accessor();
    let mut nodes = Box::new(None);
    let dst_nodes_accessor = UnsafeMutAccessor::new(nodes.as_mut());
    callbacks.schedule(
        move || unsafe {
            assert!(dst_nodes_accessor
                .get_mut()
                .replace(nodes_host_accessor.get().to_vec())
                .is_none());
        },
        stream,
    )?;
    drop(nodes_host);
    Ok((geometry, nodes))
}

pub fn schedule_memory_cap_readback<'a>(
    holder: &TraceHolder<BF>,
    mut callbacks: Callbacks<'a>,
    inputs: Option<TransferKeepalive<'a>>,
    range: Range,
    persist_partial_trees: bool,
    context: &ProverContext,
) -> CudaResult<MemoryCommitmentJob<'a>> {
    let stream = context.get_exec_stream();
    let unified_cap = holder.unified_device_cap();
    let producing_geometry = holder
        .base_commitment_geometry()
        .map(|(geometry, _)| geometry);
    let log_lde = holder.log_lde_factor;
    // Schedule a D2H of the unified device cap (canonical bit-reversed coset
    // order) into a pinned host buffer; the callback below slices it into
    // per-coset `MerkleTreeCapVarLength` entries in natural coset order.
    let lde_factor = 1usize << log_lde;
    let cap_size = unified_cap.len();
    let mut cap_host = unsafe { context.alloc_host_uninit_slice::<Digest>(cap_size) };
    if cap_size != 0 {
        memory_copy_async(&mut cap_host, unified_cap, stream)?;
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
    callbacks.schedule(transform_tree_caps_fn, stream)?;
    // `cap_host` (pool-backed pinned host buffer) drops at end of this function;
    // the callback above has already been scheduled, so the contract's
    // scheduled-not-completed lifetime rule is satisfied.
    drop(cap_host);
    let partial_trees = if persist_partial_trees {
        Some(schedule_partial_trees_readback(
            holder,
            &mut callbacks,
            context,
        )?)
    } else {
        None
    };
    range.end(stream)?;
    let is_finished_event = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
    is_finished_event.record(stream)?;
    let job = MemoryCommitmentJob {
        geometry: producing_geometry,
        is_finished_event,
        callbacks,
        inputs,
        tree_caps,
        partial_trees,
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
    partial_tree_reduction_layers: u32,
    context: &ProverContext,
) -> CudaResult<MemoryCommitmentJob<'a>> {
    commit_memory_inner(
        circuit_type,
        compiled_circuit,
        decoder_table,
        None,
        Some(tracing_data),
        config_memory_shape(prover_config, compiled_circuit),
        partial_tree_reduction_layers,
        None,
        context,
    )
}

fn config_memory_shape<'a>(
    config: &'a ProverConfig,
    circuit: &GKRCircuitArtifact<BF>,
) -> MemoryCommitmentShape<'a> {
    let geometry = BaseCommitmentGeometry::from_config(config, BaseColumns::of(circuit))
        .expect("invalid memory commitment config");
    memory_shape_for_geometry(config, geometry, circuit)
}

fn memory_shape_for_geometry<'a>(
    config: &'a ProverConfig,
    geometry: BaseCommitmentGeometry,
    circuit: &GKRCircuitArtifact<BF>,
) -> MemoryCommitmentShape<'a> {
    validate_memory_commitment_config(config, &geometry, circuit);
    if uses_base_commitment_geometry(&geometry) {
        MemoryCommitmentShape::Geometry(geometry)
    } else {
        MemoryCommitmentShape::Unpacked(config)
    }
}

pub fn commit_memory_from_transfers<'a, A: GoodAllocator + 'a>(
    circuit_type: CircuitType,
    compiled_circuit: &GKRCircuitArtifact<BF>,
    inputs: super::memory_transfer::GpuGKRCommitMemoryTransfer<'a, A>,
    prover_config: &ProverConfig,
    partial_tree_reduction_layers: u32,
    context: &ProverContext,
) -> CudaResult<MemoryCommitmentJob<'a>> {
    let geometry =
        BaseCommitmentGeometry::from_config(prover_config, BaseColumns::of(compiled_circuit))
            .expect("invalid memory commitment config");
    commit_memory_from_transfers_for_geometry(
        circuit_type,
        compiled_circuit,
        inputs,
        prover_config,
        geometry,
        partial_tree_reduction_layers,
        context,
    )
}

/// Use the worker's already resolved config/geometry without another CPU lookup.
pub fn commit_memory_from_transfers_for_geometry<'a, A: GoodAllocator + 'a>(
    circuit_type: CircuitType,
    compiled_circuit: &GKRCircuitArtifact<BF>,
    inputs: super::memory_transfer::GpuGKRCommitMemoryTransfer<'a, A>,
    prover_config: &ProverConfig,
    geometry: BaseCommitmentGeometry,
    partial_tree_reduction_layers: u32,
    context: &ProverContext,
) -> CudaResult<MemoryCommitmentJob<'a>> {
    let shape = memory_shape_for_geometry(prover_config, geometry, compiled_circuit);
    if geometry.pack_log2() != 0 {
        crate::trace::holder::validate_baby_bear_base_geometry(
            &geometry,
            context
                .ntt_device_context()
                .whir_leaf_transform_params()
                .omega_log_order,
        );
    }
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
        shape,
        partial_tree_reduction_layers,
        Some(transfer.into_keepalive()),
        context,
    )
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod cpu_geometry_routing {
    use super::*;
    use prover::definitions::SecurityLevel;
    use prover::gkr::prover::WhirSchedule;

    #[test]
    fn cpu_nonlegacy_base_routing_includes_pure_virtual_and_empty_sets() {
        for k in [0, 2] {
            for fold in [0, 1] {
                let config = ProverConfig::whir_only(
                    22 - k,
                    WhirSchedule::from_legacy_arrays(2, 16, k, &[fold, 5], &[1, 1], &[2], &[0, 0]),
                    SecurityLevel::Sec100,
                );
                for columns in [
                    BaseColumns {
                        memory: 1,
                        witness: 0,
                        setup: 0,
                    },
                    BaseColumns {
                        memory: 0,
                        witness: 0,
                        setup: 0,
                    },
                ] {
                    let geometry = BaseCommitmentGeometry::from_config(&config, columns).unwrap();
                    assert_eq!(
                        uses_base_commitment_geometry(&geometry),
                        k != 0 || fold == 0
                    );
                    assert_eq!(
                        geometry.oracle(BaseOracleRole::Witness).physical_columns(),
                        0
                    );
                    assert_eq!(geometry.oracle(BaseOracleRole::Setup).physical_columns(), 0);
                }
            }
        }
    }
}
