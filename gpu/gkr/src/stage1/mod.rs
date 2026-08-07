use std::ops::DerefMut;
use std::sync::Arc;

use self::multiplicities::generate_range_check_multiplicities_from_mappings;
use crate::proof_layout::GpuGKRTraceGeometry;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_structures::{
    DeviceMatrix, DeviceMatrixImpl, DeviceMatrixMut, DeviceMatrixMutImpl,
};
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::BF;
use gpu_ops::simple::{set_to_ones, set_to_zero};
use gpu_prover_context::ProverContext;
use gpu_trace::trace::holder::{TraceHolder, TreesCacheMode};
use gpu_trace::trace::tracing_data::{
    DelegationTracingDataDevice, TracingDataDevice, UnrolledTracingDataDevice,
};
use gpu_trace::witness::circuit_type::{CircuitType, DelegationCircuitType, UnrolledCircuitType};
use gpu_trace::witness::memory_delegation::generate_memory_and_witness_values_delegation;
use gpu_trace::witness::memory_unrolled::{
    generate_memory_and_witness_values_unrolled_inits_and_teardowns,
    generate_memory_and_witness_values_unrolled_memory,
    generate_memory_and_witness_values_unrolled_non_memory,
    generate_memory_and_witness_values_unrolled_unified,
};
use gpu_trace::witness::multiplicities::{
    generate_generic_lookup_multiplicities, generate_range_check_lookup_mappings,
};
use gpu_trace::witness::trace_unrolled::{
    ExecutorFamilyDecoderData, InitsAndTeardownsTraceDevice, PAGE_SIZE_LOG2,
};
use gpu_trace::witness::witness_delegation::generate_witness_values_delegation;
use gpu_trace::witness::witness_unrolled::{
    generate_witness_values_unrolled_memory, generate_witness_values_unrolled_non_memory,
    generate_witness_values_unrolled_unified,
};

use crate::upstream::GKRCircuitArtifact;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;

mod multiplicities;

#[doc(hidden)]
pub struct GpuGKRLookupMappings {
    generic_family: Option<DeviceAllocation<u32>>,
    range_check_16: Option<DeviceAllocation<u32>>,
    timestamp: Option<DeviceAllocation<u32>>,
    pub trace_len: usize,
    pub num_generic_sets: usize,
    pub has_decoder: bool,
}

impl GpuGKRLookupMappings {
    pub fn has_generic_family(&self) -> bool {
        self.generic_family.is_some()
    }
    pub fn has_range_check_16(&self) -> bool {
        self.range_check_16.is_some()
    }
    pub fn has_timestamp(&self) -> bool {
        self.timestamp.is_some()
    }

    pub fn generic_family(&self) -> &DeviceAllocation<u32> {
        self.generic_family
            .as_ref()
            .expect("generic-family lookup mappings were released")
    }

    pub fn range_check_16(&self) -> &DeviceAllocation<u32> {
        self.range_check_16
            .as_ref()
            .expect("range-check lookup mappings were released")
    }

    pub fn timestamp(&self) -> &DeviceAllocation<u32> {
        self.timestamp
            .as_ref()
            .expect("timestamp lookup mappings were released")
    }

    pub(crate) fn release_generic_family(&mut self) {
        self.generic_family = None;
    }

    pub(crate) fn release_range_check_16(&mut self) {
        self.range_check_16 = None;
    }

    pub(crate) fn release_timestamp(&mut self) {
        self.timestamp = None;
    }
}

/// Stage-1 keepalive: only the tracing-range NVTX scopes need to outlive the
/// stream-scheduled work. The trace holders themselves are dropped (stream-
/// ordered) inside `into_keepalive`.
pub type GpuGKRStage1Keepalive = Vec<Range>;

pub struct GpuGKRStage1Output {
    tracing_ranges: Vec<Range>,
    pub memory_trace_holder: TraceHolder<BF>,
    pub witness_trace_holder: TraceHolder<BF>,
    pub(crate) scratch_space_trace: Option<Arc<DeviceAllocation<BF>>>,
    pub lookup_mappings: GpuGKRLookupMappings,
}

impl GpuGKRStage1Output {
    pub fn into_keepalive(self) -> GpuGKRStage1Keepalive {
        let Self { tracing_ranges, .. } = self;
        // memory_trace_holder, witness_trace_holder, lookup_mappings drop here —
        // all exec-stream ops that used them have already been scheduled.
        tracing_ranges
    }

    fn allocate_trace_holder(
        columns_count: usize,
        geometry: GpuGKRTraceGeometry,
        context: &ProverContext,
    ) -> CudaResult<TraceHolder<BF>> {
        TraceHolder::new(
            geometry.log_domain_size,
            geometry.log_lde_factor,
            geometry.log_rows_per_leaf,
            geometry.log_tree_cap_size,
            columns_count,
            TreesCacheMode::CachePartial,
            context,
        )
    }

    pub fn generate(
        circuit_type: CircuitType,
        compiled_circuit: &GKRCircuitArtifact<BF>,
        geometry: GpuGKRTraceGeometry,
        setup_hypercube_evals: Option<&DeviceSlice<BF>>,
        decoder_table: Option<&DeviceSlice<ExecutorFamilyDecoderData>>,
        inits_and_teardowns: Option<&InitsAndTeardownsTraceDevice>,
        tracing_data: Option<&TracingDataDevice>,
        witness_cap_dst: Option<&mut DeviceSlice<u32>>,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let trace_len = compiled_circuit.trace_len;
        assert_eq!(trace_len, 1usize << geometry.log_domain_size);
        let stream = context.get_exec_stream();
        let mut tracing_ranges = Vec::new();
        let stage1_range = Range::new("gkr.stage1.generate")?;
        stage1_range.start(stream)?;

        let mut memory_trace_holder = TraceHolder::new_without_cosets(
            geometry.log_domain_size,
            geometry.log_lde_factor,
            geometry.log_rows_per_leaf,
            geometry.log_tree_cap_size,
            compiled_circuit.memory_layout.total_width,
            TreesCacheMode::CacheNone,
            context,
        )?;
        let mut witness_trace_holder = Self::allocate_trace_holder(
            compiled_circuit.witness_layout.total_width,
            geometry,
            context,
        )?;
        let mut scratch_space_trace = if compiled_circuit.scratch_space_size > 0 {
            Some(context.alloc(
                compiled_circuit.scratch_space_size * trace_len,
                AllocationPlacement::Top,
            )?)
        } else {
            None
        };
        if let Some(scratch_space_trace) = scratch_space_trace.as_mut() {
            set_to_zero(scratch_space_trace.deref_mut(), context.get_exec_stream())?;
        }

        let num_generic_sets = compiled_circuit.generic_lookups.len();
        let has_decoder = compiled_circuit.has_decoder_lookup;
        let num_generic_family_cols = num_generic_sets + usize::from(has_decoder);
        let mut generic_family = context.alloc(
            num_generic_family_cols * trace_len,
            AllocationPlacement::Top,
        )?;
        if !generic_family.is_empty() {
            set_to_ones(generic_family.deref_mut(), context.get_exec_stream())?;
        }

        let generic_lookup_tables: &DeviceSlice<BF> =
            setup_hypercube_evals.unwrap_or_else(DeviceSlice::empty);

        let (memory_raw, witness_raw) = (
            memory_trace_holder.get_uninit_hypercube_evals_mut(),
            witness_trace_holder.get_uninit_hypercube_evals_mut(),
        );
        let mut memory_matrix = DeviceMatrixMut::new(memory_raw, trace_len);
        let mut witness_matrix = DeviceMatrixMut::new(witness_raw, trace_len);
        let empty_scratch = DeviceSlice::empty_mut();
        let mut scratch_matrix = if let Some(scratch_space_trace) = scratch_space_trace.as_mut() {
            DeviceMatrixMut::new(scratch_space_trace.deref_mut(), trace_len)
        } else {
            DeviceMatrixMut::new(empty_scratch, trace_len)
        };

        {
            let generic_prefix_len = num_generic_sets * trace_len;
            let (generic_mapping_prefix, decoder_mapping_suffix) =
                generic_family.split_at_mut(generic_prefix_len);
            let decoder_lookup_mapping = if has_decoder {
                assert_eq!(decoder_mapping_suffix.len(), trace_len);
                decoder_mapping_suffix
            } else {
                DeviceSlice::empty_mut()
            };

            match (circuit_type, tracing_data) {
                (
                    CircuitType::Delegation(circuit_type),
                    Some(TracingDataDevice::Delegation(
                        DelegationTracingDataDevice::BigIntWithControl(trace),
                    )),
                ) => {
                    assert_eq!(circuit_type, DelegationCircuitType::BigIntWithControl);
                    let witness_values_range =
                        Range::new("gkr.stage1.generate.memory_and_witness_values")?;
                    witness_values_range.start(stream)?;
                    generate_memory_and_witness_values_delegation(
                        compiled_circuit,
                        trace,
                        &mut memory_matrix,
                        &mut witness_matrix,
                        context.get_exec_stream(),
                    )?;
                    generate_witness_values_delegation(
                        trace,
                        &DeviceMatrix::new(generic_lookup_tables, trace_len),
                        &DeviceMatrix::new(memory_matrix.slice(), trace_len),
                        &mut witness_matrix,
                        &mut scratch_matrix,
                        &mut DeviceMatrixMut::new(generic_mapping_prefix, trace_len),
                        context.get_exec_stream(),
                    )?;
                    witness_values_range.end(stream)?;
                    tracing_ranges.push(witness_values_range);
                }
                (
                    CircuitType::Delegation(circuit_type),
                    Some(TracingDataDevice::Delegation(
                        DelegationTracingDataDevice::Blake2WithCompression(trace),
                    )),
                ) => {
                    assert_eq!(circuit_type, DelegationCircuitType::Blake2WithCompression);
                    let witness_values_range =
                        Range::new("gkr.stage1.generate.memory_and_witness_values")?;
                    witness_values_range.start(stream)?;
                    generate_memory_and_witness_values_delegation(
                        compiled_circuit,
                        trace,
                        &mut memory_matrix,
                        &mut witness_matrix,
                        context.get_exec_stream(),
                    )?;
                    generate_witness_values_delegation(
                        trace,
                        &DeviceMatrix::new(generic_lookup_tables, trace_len),
                        &DeviceMatrix::new(memory_matrix.slice(), trace_len),
                        &mut witness_matrix,
                        &mut scratch_matrix,
                        &mut DeviceMatrixMut::new(generic_mapping_prefix, trace_len),
                        context.get_exec_stream(),
                    )?;
                    witness_values_range.end(stream)?;
                    tracing_ranges.push(witness_values_range);
                }
                (
                    CircuitType::Delegation(circuit_type),
                    Some(TracingDataDevice::Delegation(
                        DelegationTracingDataDevice::Blake2GFunction(trace),
                    )),
                ) => {
                    assert_eq!(circuit_type, DelegationCircuitType::Blake2GFunction);
                    let witness_values_range =
                        Range::new("gkr.stage1.generate.memory_and_witness_values")?;
                    witness_values_range.start(stream)?;
                    generate_memory_and_witness_values_delegation(
                        compiled_circuit,
                        trace,
                        &mut memory_matrix,
                        &mut witness_matrix,
                        context.get_exec_stream(),
                    )?;
                    generate_witness_values_delegation(
                        trace,
                        &DeviceMatrix::new(generic_lookup_tables, trace_len),
                        &DeviceMatrix::new(memory_matrix.slice(), trace_len),
                        &mut witness_matrix,
                        &mut scratch_matrix,
                        &mut DeviceMatrixMut::new(generic_mapping_prefix, trace_len),
                        context.get_exec_stream(),
                    )?;
                    witness_values_range.end(stream)?;
                    tracing_ranges.push(witness_values_range);
                }
                (
                    CircuitType::Delegation(circuit_type),
                    Some(TracingDataDevice::Delegation(
                        DelegationTracingDataDevice::KeccakSpecial5(trace),
                    )),
                ) => {
                    assert_eq!(circuit_type, DelegationCircuitType::KeccakSpecial5);
                    let witness_values_range =
                        Range::new("gkr.stage1.generate.memory_and_witness_values")?;
                    witness_values_range.start(stream)?;
                    generate_memory_and_witness_values_delegation(
                        compiled_circuit,
                        trace,
                        &mut memory_matrix,
                        &mut witness_matrix,
                        context.get_exec_stream(),
                    )?;
                    generate_witness_values_delegation(
                        trace,
                        &DeviceMatrix::new(generic_lookup_tables, trace_len),
                        &DeviceMatrix::new(memory_matrix.slice(), trace_len),
                        &mut witness_matrix,
                        &mut scratch_matrix,
                        &mut DeviceMatrixMut::new(generic_mapping_prefix, trace_len),
                        context.get_exec_stream(),
                    )?;
                    witness_values_range.end(stream)?;
                    tracing_ranges.push(witness_values_range);
                }
                (
                    CircuitType::Unrolled(UnrolledCircuitType::Memory(circuit_type)),
                    Some(TracingDataDevice::Unrolled(UnrolledTracingDataDevice::Memory(trace))),
                ) => {
                    let witness_values_range =
                        Range::new("gkr.stage1.generate.memory_and_witness_values")?;
                    witness_values_range.start(stream)?;
                    let decoder_table = if compiled_circuit.has_decoder_lookup {
                        decoder_table.expect("decoder lookup requires transferred decoder table")
                    } else {
                        DeviceSlice::empty()
                    };
                    generate_memory_and_witness_values_unrolled_memory(
                        circuit_type,
                        &compiled_circuit.memory_layout,
                        &compiled_circuit.aux_layout_data,
                        decoder_table,
                        compiled_circuit.offset_for_decoder_table as u32,
                        trace,
                        &mut memory_matrix,
                        &mut witness_matrix,
                        decoder_lookup_mapping,
                        context.get_exec_stream(),
                    )?;
                    generate_witness_values_unrolled_memory(
                        circuit_type,
                        trace,
                        &DeviceMatrix::new(generic_lookup_tables, trace_len),
                        &DeviceMatrix::new(memory_matrix.slice(), trace_len),
                        &mut witness_matrix,
                        &mut scratch_matrix,
                        &mut DeviceMatrixMut::new(generic_mapping_prefix, trace_len),
                        context.get_exec_stream(),
                    )?;
                    witness_values_range.end(stream)?;
                    tracing_ranges.push(witness_values_range);
                }
                (
                    CircuitType::Unrolled(UnrolledCircuitType::NonMemory(circuit_type)),
                    Some(TracingDataDevice::Unrolled(UnrolledTracingDataDevice::NonMemory(trace))),
                ) => {
                    let witness_values_range =
                        Range::new("gkr.stage1.generate.memory_and_witness_values")?;
                    witness_values_range.start(stream)?;
                    let decoder_table = if compiled_circuit.has_decoder_lookup {
                        decoder_table.expect("decoder lookup requires transferred decoder table")
                    } else {
                        DeviceSlice::empty()
                    };
                    generate_memory_and_witness_values_unrolled_non_memory(
                        circuit_type,
                        &compiled_circuit.memory_layout,
                        &compiled_circuit.aux_layout_data,
                        decoder_table,
                        compiled_circuit.offset_for_decoder_table as u32,
                        trace,
                        &mut memory_matrix,
                        &mut witness_matrix,
                        decoder_lookup_mapping,
                        context.get_exec_stream(),
                    )?;
                    generate_witness_values_unrolled_non_memory(
                        circuit_type,
                        trace,
                        &DeviceMatrix::new(generic_lookup_tables, trace_len),
                        &DeviceMatrix::new(memory_matrix.slice(), trace_len),
                        &mut witness_matrix,
                        &mut scratch_matrix,
                        &mut DeviceMatrixMut::new(generic_mapping_prefix, trace_len),
                        context.get_exec_stream(),
                    )?;
                    witness_values_range.end(stream)?;
                    tracing_ranges.push(witness_values_range);
                }
                (CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns), _) => {
                    let witness_values_range =
                        Range::new("gkr.stage1.generate.memory_and_witness_values")?;
                    witness_values_range.start(stream)?;
                    let inits_and_teardowns = inits_and_teardowns.expect(
                        "standalone init/teardown circuit requires transferred init/teardown data",
                    );
                    generate_memory_and_witness_values_unrolled_inits_and_teardowns(
                        &compiled_circuit.memory_layout,
                        geometry.log_domain_size,
                        PAGE_SIZE_LOG2,
                        inits_and_teardowns,
                        &mut memory_matrix,
                        context.get_exec_stream(),
                    )?;
                    witness_values_range.end(stream)?;
                    tracing_ranges.push(witness_values_range);
                }
                (
                    CircuitType::Unrolled(UnrolledCircuitType::Unified),
                    Some(TracingDataDevice::Unrolled(UnrolledTracingDataDevice::Unified(trace))),
                ) => {
                    let witness_values_range =
                        Range::new("gkr.stage1.generate.memory_and_witness_values")?;
                    witness_values_range.start(stream)?;
                    // Inline inits/teardowns: a paged RAM-word sweep into the SAME memory matrix
                    // (page-based-reuse, per Global Constraints). MUST run BEFORE the per-row launch:
                    // generate_memory_and_witness_values_unrolled_inits_and_teardowns zeroes the whole
                    // matrix before writing the teardown columns, and derives pages_per_set_log2
                    // itself. Mirrors the standalone inits-and-teardowns arm above.
                    // `None` = a TRIVIAL (dummy) unified init/teardown chunk (CPU reference
                    // commits all-zero i&t columns): the i/t launcher only zeroes the whole
                    // matrix and writes teardown timestamp/value columns at page-covered rows,
                    // so the all-zero case is exactly "zero the matrix, skip the page sweep".
                    match inits_and_teardowns {
                        Some(inits_and_teardowns) => {
                            generate_memory_and_witness_values_unrolled_inits_and_teardowns(
                                &compiled_circuit.memory_layout,
                                geometry.log_domain_size,
                                PAGE_SIZE_LOG2,
                                inits_and_teardowns,
                                &mut memory_matrix,
                                context.get_exec_stream(),
                            )?;
                        }
                        None => {
                            gpu_ops::simple::set_to_zero(
                                memory_matrix.slice_mut(),
                                context.get_exec_stream(),
                            )?;
                        }
                    }
                    let decoder_table = if compiled_circuit.has_decoder_lookup {
                        decoder_table.expect("decoder lookup requires transferred decoder table")
                    } else {
                        DeviceSlice::empty()
                    };
                    generate_memory_and_witness_values_unrolled_unified(
                        &compiled_circuit.memory_layout,
                        &compiled_circuit.aux_layout_data,
                        decoder_table,
                        compiled_circuit.offset_for_decoder_table as u32,
                        trace,
                        &mut memory_matrix,
                        &mut witness_matrix,
                        decoder_lookup_mapping,
                        context.get_exec_stream(),
                    )?;
                    generate_witness_values_unrolled_unified(
                        trace,
                        &DeviceMatrix::new(generic_lookup_tables, trace_len),
                        &DeviceMatrix::new(memory_matrix.slice(), trace_len),
                        &mut witness_matrix,
                        &mut scratch_matrix,
                        &mut DeviceMatrixMut::new(generic_mapping_prefix, trace_len),
                        context.get_exec_stream(),
                    )?;
                    witness_values_range.end(stream)?;
                    tracing_ranges.push(witness_values_range);
                }
                _ => unimplemented!(
                    "GPU GKR stage1 received an unsupported witness shape for circuit {circuit_type:?}",
                ),
            }
        }

        let generic_lookup_multiplicities_range = compiled_circuit
            .witness_layout
            .multiplicities_columns_for_generic_lookup
            .clone();
        if !generic_lookup_multiplicities_range.is_empty() {
            let multiplicities_range = Range::new("gkr.stage1.generate.generic_multiplicities")?;
            multiplicities_range.start(stream)?;
            let generic_lookup_multiplicities = &mut witness_matrix.slice_mut()
                [generic_lookup_multiplicities_range.start * trace_len
                    ..generic_lookup_multiplicities_range.end * trace_len];
            generate_generic_lookup_multiplicities(
                &mut DeviceMatrixMut::new(&mut generic_family, trace_len),
                &mut DeviceMatrixMut::new(generic_lookup_multiplicities, trace_len),
                u32::BITS as i32, // generic lookups: full 32-bit sort
                context,
            )?;
            multiplicities_range.end(stream)?;
            tracing_ranges.push(multiplicities_range);
        }

        let range_mapping_range = Range::new("gkr.stage1.generate.range_check_lookup_mappings")?;
        range_mapping_range.start(stream)?;
        let (mut range_check_16, mut timestamp) = generate_range_check_lookup_mappings(
            compiled_circuit,
            &DeviceMatrix::new(memory_matrix.slice(), trace_len),
            &DeviceMatrix::new(scratch_matrix.slice(), trace_len),
            &DeviceMatrix::new(witness_matrix.slice(), trace_len),
            context,
        )?;
        range_mapping_range.end(stream)?;
        tracing_ranges.push(range_mapping_range);

        let range_multiplicities_range =
            Range::new("gkr.stage1.generate.range_check_multiplicities")?;
        range_multiplicities_range.start(stream)?;
        generate_range_check_multiplicities_from_mappings(
            compiled_circuit,
            &mut DeviceMatrixMut::new(&mut range_check_16, trace_len),
            &mut DeviceMatrixMut::new(&mut timestamp, trace_len),
            &mut witness_matrix,
            context,
        )?;
        range_multiplicities_range.end(stream)?;
        tracing_ranges.push(range_multiplicities_range);

        if witness_trace_holder.columns_count > 0 {
            let witness_commit_range = Range::new("gkr.stage1.commit.witness_trace")?;
            witness_commit_range.start(stream)?;
            match witness_cap_dst {
                Some(dst) => witness_trace_holder.commit_all_into(dst, context)?,
                None => witness_trace_holder.commit_all(context)?,
            }
            witness_commit_range.end(stream)?;
            tracing_ranges.push(witness_commit_range);
        }
        stage1_range.end(stream)?;
        tracing_ranges.push(stage1_range);

        let lookup_mappings = GpuGKRLookupMappings {
            generic_family: Some(generic_family),
            range_check_16: Some(range_check_16),
            timestamp: Some(timestamp),
            trace_len,
            num_generic_sets,
            has_decoder,
        };

        Ok(Self {
            tracing_ranges,
            memory_trace_holder,
            witness_trace_holder,
            scratch_space_trace: scratch_space_trace.map(Arc::new),
            lookup_mappings,
        })
    }
}
