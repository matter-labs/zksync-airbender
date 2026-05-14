use std::ops::DerefMut;
use std::sync::Arc;

use crate::allocator::tracker::AllocationPlacement;
use crate::ops::simple::{set_to_ones, set_to_zero};
use crate::primitives::circuit_type::{CircuitType, DelegationCircuitType, UnrolledCircuitType};
use crate::primitives::context::{DeviceAllocation, ProverContext};
use crate::primitives::device_structures::{
    DeviceMatrix, DeviceMatrixImpl, DeviceMatrixMut, DeviceMatrixMutImpl,
};
use crate::primitives::device_tracing::Range;
use crate::primitives::field::BF;
use crate::prover::trace::holder::{TraceHolder, TreesCacheMode};
use crate::prover::trace::tracing_data::{
    DelegationTracingDataDevice, TracingDataDevice, UnrolledTracingDataDevice,
};
use crate::witness::memory_delegation::generate_memory_and_witness_values_delegation;
use crate::witness::memory_unrolled::{
    generate_memory_and_witness_values_unrolled_inits_and_teardowns,
    generate_memory_and_witness_values_unrolled_memory,
    generate_memory_and_witness_values_unrolled_non_memory,
};
use crate::witness::multiplicities::{
    generate_generic_lookup_multiplicities, generate_range_check_lookup_mappings,
    generate_range_check_multiplicities_from_mappings,
};
use crate::witness::trace_unrolled::{
    ExecutorFamilyDecoderData, InitsAndTeardownsTraceDevice, PAGE_SIZE_LOG2,
};
use crate::witness::witness_delegation::generate_witness_values_delegation;
use crate::witness::witness_unrolled::{
    generate_witness_values_unrolled_memory, generate_witness_values_unrolled_non_memory,
};

use crate::upstream::GKRCircuitArtifact;
#[cfg(test)]
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;

pub(crate) struct GpuGKRLookupMappings {
    generic_family: Option<DeviceAllocation<u32>>,
    range_check_16: Option<DeviceAllocation<u32>>,
    timestamp: Option<DeviceAllocation<u32>>,
    pub(crate) trace_len: usize,
    pub(crate) num_generic_sets: usize,
    pub(crate) has_decoder: bool,
}

impl GpuGKRLookupMappings {
    #[cfg(test)]
    pub(crate) fn has_generic_family(&self) -> bool {
        self.generic_family.is_some()
    }

    #[cfg(test)]
    pub(crate) fn has_range_check_16(&self) -> bool {
        self.range_check_16.is_some()
    }

    #[cfg(test)]
    pub(crate) fn has_timestamp(&self) -> bool {
        self.timestamp.is_some()
    }

    pub(crate) fn generic_family(&self) -> &DeviceAllocation<u32> {
        self.generic_family
            .as_ref()
            .expect("generic-family lookup mappings were released")
    }

    pub(crate) fn range_check_16(&self) -> &DeviceAllocation<u32> {
        self.range_check_16
            .as_ref()
            .expect("range-check lookup mappings were released")
    }

    pub(crate) fn timestamp(&self) -> &DeviceAllocation<u32> {
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

    fn column_range(&self, column: usize) -> core::ops::Range<usize> {
        let start = column * self.trace_len;
        start..start + self.trace_len
    }

    pub(crate) fn generic_mapping(&self, set_idx: usize) -> &DeviceSlice<u32> {
        assert!(set_idx < self.num_generic_sets);
        &self.generic_family()[self.column_range(set_idx)]
    }

    pub(crate) fn decoder_mapping(&self) -> Option<&DeviceSlice<u32>> {
        self.has_decoder
            .then(|| &self.generic_family()[self.column_range(self.num_generic_sets)])
    }

    pub(crate) fn range_check_mapping(&self, set_idx: usize) -> &DeviceSlice<u32> {
        &self.range_check_16()[self.column_range(set_idx)]
    }

    pub(crate) fn timestamp_mapping(&self, set_idx: usize) -> &DeviceSlice<u32> {
        &self.timestamp()[self.column_range(set_idx)]
    }
}

/// Stage-1 keepalive: only the tracing-range NVTX scopes need to outlive the
/// stream-scheduled work. The trace holders themselves are dropped (stream-
/// ordered) inside `into_keepalive`.
pub(crate) type GpuGKRStage1Keepalive = Vec<Range>;

#[derive(Clone, Copy, Debug)]
pub(crate) struct GpuGKRTraceGeometry {
    pub(crate) log_domain_size: u32,
    pub(crate) log_lde_factor: u32,
    pub(crate) log_rows_per_leaf: u32,
    pub(crate) log_tree_cap_size: u32,
}

pub(crate) struct GpuGKRStage1Output {
    tracing_ranges: Vec<Range>,
    pub(crate) memory_trace_holder: TraceHolder<BF>,
    pub(crate) witness_trace_holder: TraceHolder<BF>,
    pub(crate) scratch_space_trace: Option<Arc<DeviceAllocation<BF>>>,
    pub(crate) lookup_mappings: GpuGKRLookupMappings,
}

impl GpuGKRStage1Output {
    pub(crate) fn into_keepalive(self) -> GpuGKRStage1Keepalive {
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

    pub(crate) fn generate(
        circuit_type: CircuitType,
        compiled_circuit: &GKRCircuitArtifact<BF>,
        geometry: GpuGKRTraceGeometry,
        setup_hypercube_evals: Option<&DeviceSlice<BF>>,
        decoder_table: Option<&DeviceSlice<ExecutorFamilyDecoderData>>,
        inits_and_teardowns: Option<&InitsAndTeardownsTraceDevice>,
        tracing_data: Option<&TracingDataDevice>,
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
        let mut empty_scratch = DeviceSlice::empty_mut();
        let mut scratch_matrix = if let Some(scratch_space_trace) = scratch_space_trace.as_mut() {
            DeviceMatrixMut::new(scratch_space_trace.deref_mut(), trace_len)
        } else {
            DeviceMatrixMut::new(&mut empty_scratch, trace_len)
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
                        geometry.log_domain_size as u32,
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
                    Some(TracingDataDevice::Unrolled(UnrolledTracingDataDevice::Unified(_))),
                ) => unimplemented!("GPU GKR stage1 unified path is not implemented yet"),
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

        drop(memory_matrix);
        drop(witness_matrix);

        // Memory commit is deferred: cosets and trees are materialized right before WHIR fold
        // queries. Tree caps for memory are provided externally to prove().

        let witness_commit_range = Range::new("gkr.stage1.commit.witness_trace")?;
        witness_commit_range.start(stream)?;
        witness_trace_holder.commit_all(context)?;
        witness_commit_range.end(stream)?;
        tracing_ranges.push(witness_commit_range);
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

    #[cfg(test)]
    pub(crate) fn empty_for_tests(context: &ProverContext) -> CudaResult<Self> {
        Ok(Self {
            tracing_ranges: Vec::new(),
            memory_trace_holder: TraceHolder::new_without_cosets(
                1,
                0,
                0,
                0,
                0,
                TreesCacheMode::CacheNone,
                context,
            )?,
            witness_trace_holder: TraceHolder::new_without_cosets(
                1,
                0,
                0,
                0,
                0,
                TreesCacheMode::CacheNone,
                context,
            )?,
            scratch_space_trace: None,
            lookup_mappings: GpuGKRLookupMappings {
                generic_family: None,
                range_check_16: None,
                timestamp: None,
                trace_len: 0,
                num_generic_sets: 0,
                has_decoder: false,
            },
        })
    }

    #[cfg(test)]
    pub(crate) fn with_lookup_mappings_for_tests(
        context: &ProverContext,
        trace_len: usize,
        generic_sets: &[&[u32]],
        decoder: Option<&[u32]>,
        range_check_16_sets: &[&[u32]],
        timestamp_sets: &[&[u32]],
    ) -> CudaResult<Self> {
        fn flatten_columns(trace_len: usize, columns: &[&[u32]]) -> Vec<u32> {
            let mut flattened = Vec::with_capacity(trace_len * columns.len());
            for column in columns {
                assert_eq!(
                    column.len(),
                    trace_len,
                    "test lookup mapping column length mismatch"
                );
                flattened.extend_from_slice(column);
            }
            flattened
        }

        fn upload_columns(
            context: &ProverContext,
            trace_len: usize,
            columns: &[&[u32]],
        ) -> CudaResult<Option<DeviceAllocation<u32>>> {
            if columns.is_empty() {
                return Ok(None);
            }
            let flattened = flatten_columns(trace_len, columns);
            let mut device = context.alloc(flattened.len(), AllocationPlacement::BestFit)?;
            memory_copy_async(&mut device, &flattened, context.get_exec_stream())?;
            Ok(Some(device))
        }

        let mut generic_columns = generic_sets.to_vec();
        if let Some(decoder) = decoder {
            generic_columns.push(decoder);
        }

        let result = Self {
            tracing_ranges: Vec::new(),
            memory_trace_holder: TraceHolder::new_without_cosets(
                1,
                0,
                0,
                0,
                0,
                TreesCacheMode::CacheNone,
                context,
            )?,
            witness_trace_holder: TraceHolder::new_without_cosets(
                1,
                0,
                0,
                0,
                0,
                TreesCacheMode::CacheNone,
                context,
            )?,
            scratch_space_trace: None,
            lookup_mappings: GpuGKRLookupMappings {
                generic_family: upload_columns(context, trace_len, &generic_columns)?,
                range_check_16: upload_columns(context, trace_len, range_check_16_sets)?,
                timestamp: upload_columns(context, trace_len, timestamp_sets)?,
                trace_len,
                num_generic_sets: generic_sets.len(),
                has_decoder: decoder.is_some(),
            },
        };
        context.get_exec_stream().synchronize()?;
        Ok(result)
    }
}
