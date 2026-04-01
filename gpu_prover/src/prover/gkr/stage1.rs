use std::ops::DerefMut;

use crate::allocator::tracker::AllocationPlacement;
use crate::ops::simple::set_by_val;
use crate::primitives::circuit_type::{CircuitType, UnrolledCircuitType};
use crate::primitives::context::{DeviceAllocation, ProverContext};
use crate::primitives::device_structures::{
    DeviceMatrix, DeviceMatrixImpl, DeviceMatrixMut, DeviceMatrixMutImpl,
};
use crate::primitives::device_tracing::Range;
use crate::primitives::field::BF;
use crate::prover::gkr::setup::GpuGKRSetupTransfer;
use crate::prover::trace_holder::{TraceHolder, TreesCacheMode};
use crate::prover::tracing_data::{TracingDataDevice, UnrolledTracingDataDevice};
use crate::witness::memory_unrolled::generate_memory_and_witness_values_unrolled_non_memory;
use crate::witness::multiplicities::{
    generate_generic_lookup_multiplicities, generate_range_check_lookup_mappings,
    generate_range_check_multiplicities_from_mappings,
};
use crate::witness::trace_unrolled::ExecutorFamilyDecoderData;
use crate::witness::witness_unrolled::generate_witness_values_unrolled_non_memory;
use cs::gkr_compiler::GKRCircuitArtifact;
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
    pub(crate) fn has_generic_family(&self) -> bool {
        self.generic_family.is_some()
    }

    pub(crate) fn has_range_check_16(&self) -> bool {
        self.range_check_16.is_some()
    }

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

    pub(crate) fn all_generic_family_mappings(&self) -> DeviceMatrix<'_, u32> {
        DeviceMatrix::new(self.generic_family(), self.trace_len)
    }
}

pub(crate) struct GpuGKRStage1Keepalive {
    _tracing_ranges: Vec<Range>,
}

pub(crate) struct GpuGKRStage1Output {
    tracing_ranges: Vec<Range>,
    pub(crate) memory_trace_holder: TraceHolder<BF>,
    pub(crate) witness_trace_holder: TraceHolder<BF>,
    pub(crate) lookup_mappings: GpuGKRLookupMappings,
}

impl GpuGKRStage1Output {
    pub(crate) fn into_keepalive(self) -> GpuGKRStage1Keepalive {
        let Self { tracing_ranges, .. } = self;
        // memory_trace_holder, witness_trace_holder, lookup_mappings drop here —
        // all exec-stream ops that used them have already been scheduled.
        GpuGKRStage1Keepalive {
            _tracing_ranges: tracing_ranges,
        }
    }

    fn allocate_trace_holder(
        columns_count: usize,
        setup: &GpuGKRSetupTransfer<'_>,
        context: &ProverContext,
    ) -> CudaResult<TraceHolder<BF>> {
        TraceHolder::new(
            setup.trace_holder.log_domain_size,
            setup.trace_holder.log_lde_factor,
            setup.trace_holder.log_rows_per_leaf,
            setup.trace_holder.log_tree_cap_size,
            columns_count,
            TreesCacheMode::CachePartial,
            context,
        )
    }

    pub(crate) fn generate(
        circuit_type: CircuitType,
        compiled_circuit: &GKRCircuitArtifact<BF>,
        setup: &GpuGKRSetupTransfer<'_>,
        decoder_table: Option<&DeviceSlice<ExecutorFamilyDecoderData>>,
        tracing_data: &TracingDataDevice,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        setup.ensure_transferred(context)?;
        let trace_len = compiled_circuit.trace_len;
        assert_eq!(trace_len, 1usize << setup.trace_holder.log_domain_size);
        let stream = context.get_exec_stream();
        let mut tracing_ranges = Vec::new();
        let stage1_range = Range::new("gkr.stage1.generate")?;
        stage1_range.start(stream)?;

        let mut memory_trace_holder = TraceHolder::new_without_cosets(
            setup.trace_holder.log_domain_size,
            setup.trace_holder.log_lde_factor,
            setup.trace_holder.log_rows_per_leaf,
            setup.trace_holder.log_tree_cap_size,
            compiled_circuit.memory_layout.total_width,
            TreesCacheMode::CacheNone,
            context,
        )?;
        let mut witness_trace_holder = Self::allocate_trace_holder(
            compiled_circuit.witness_layout.total_width,
            setup,
            context,
        )?;

        let num_generic_sets = compiled_circuit.generic_lookups.len();
        let has_decoder = compiled_circuit.has_decoder_lookup;
        let num_generic_family_cols = num_generic_sets + usize::from(has_decoder);
        let mut generic_family = context.alloc(
            num_generic_family_cols * trace_len,
            AllocationPlacement::Top,
        )?;
        if !generic_family.is_empty() {
            set_by_val(
                u32::MAX,
                generic_family.deref_mut(),
                context.get_exec_stream(),
            )?;
        }

        let setup_raw = setup.trace_holder.get_hypercube_evals();
        let generic_lookup_tables: &DeviceSlice<BF> = if setup.host.columns_count > 0 {
            &setup_raw[..]
        } else {
            DeviceSlice::empty()
        };

        let (memory_raw, witness_raw) = (
            memory_trace_holder.get_uninit_hypercube_evals_mut(),
            witness_trace_holder.get_uninit_hypercube_evals_mut(),
        );
        let mut memory_matrix = DeviceMatrixMut::new(memory_raw, trace_len);
        let mut witness_matrix = DeviceMatrixMut::new(witness_raw, trace_len);

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
                    CircuitType::Unrolled(UnrolledCircuitType::NonMemory(circuit_type)),
                    TracingDataDevice::Unrolled(UnrolledTracingDataDevice::NonMemory(trace)),
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
                        &mut DeviceMatrixMut::new(generic_mapping_prefix, trace_len),
                        context.get_exec_stream(),
                    )?;
                    witness_values_range.end(stream)?;
                    tracing_ranges.push(witness_values_range);
                }
                _ => unimplemented!(
                    "GPU GKR stage1 currently supports only unrolled non-memory traces",
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
            lookup_mappings,
        })
    }
}
