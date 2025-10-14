use super::callbacks::Callbacks;
use super::context::{DeviceAllocation, HostAllocation, ProverContext};
use super::setup::SetupPrecomputations;
use super::trace_holder::{TraceHolder, TreesCacheMode};
use super::tracing_data::{TracingDataDevice, TracingDataTransfer, UnrolledTracingDataDevice};
use super::BF;
use crate::allocator::tracker::AllocationPlacement;
use crate::device_structures::{DeviceMatrix, DeviceMatrixChunk, DeviceMatrixMut};
use crate::ops_simple::{set_by_ref, set_to_zero};
use crate::witness::memory_delegation::generate_memory_and_witness_values_delegation;
use crate::witness::memory_main::generate_memory_and_witness_values_main;
use crate::witness::memory_unrolled::{
    generate_memory_and_witness_values_inits_and_teardowns,
    generate_memory_and_witness_values_unrolled_memory,
    generate_memory_and_witness_values_unrolled_non_memory,
};
use crate::witness::multiplicities::{
    generate_generic_lookup_multiplicities, generate_range_check_multiplicities,
};
use crate::witness::trace_unrolled::ExecutorFamilyDecoderData;
use crate::witness::witness_delegation::generate_witness_values_delegation;
use crate::witness::witness_main::generate_witness_values_main;
use crate::witness::witness_unrolled::{
    generate_witness_values_unrolled_memory, generate_witness_values_unrolled_non_memory,
};
use cs::definitions::{
    timestamp_high_contribution_from_circuit_sequence, BoundaryConstraintLocation, ColumnSet,
    COMMON_TABLE_WIDTH, NUM_COLUMNS_FOR_COMMON_TABLE_WIDTH_SETUP,
};
use cs::one_row_compiler::{read_value, CompiledCircuitArtifact};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use fft::GoodAllocator;
use itertools::Itertools;
use std::cmp::{max, min};
use std::sync::Arc;

pub(crate) struct StageOneOutput {
    pub witness_holder: TraceHolder<BF>,
    pub memory_holder: TraceHolder<BF>,
    pub generic_lookup_mapping: Option<DeviceAllocation<u32>>,
    pub public_inputs: Option<HostAllocation<[BF]>>,
}

impl StageOneOutput {
    pub fn allocate_trace_holders(
        circuit: &CompiledCircuitArtifact<BF>,
        log_lde_factor: u32,
        log_tree_cap_size: u32,
        recompute_cosets: bool,
        trees_cache_mode: TreesCacheMode,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let trace_len = circuit.trace_len;
        assert!(trace_len.is_power_of_two());
        let log_domain_size = trace_len.trailing_zeros();
        let witness_columns_count = circuit.witness_layout.total_width;
        let witness_holder = TraceHolder::new(
            log_domain_size,
            log_lde_factor,
            0,
            log_tree_cap_size,
            witness_columns_count,
            true,
            true,
            recompute_cosets,
            trees_cache_mode,
            context,
        )?;
        let memory_columns_count = circuit.memory_layout.total_width;
        let memory_holder = TraceHolder::new(
            log_domain_size,
            log_lde_factor,
            0,
            log_tree_cap_size,
            memory_columns_count,
            true,
            true,
            recompute_cosets,
            trees_cache_mode,
            context,
        )?;
        Ok(Self {
            witness_holder,
            memory_holder,
            generic_lookup_mapping: None,
            public_inputs: None,
        })
    }

    pub fn generate_witness<'a>(
        &mut self,
        circuit: &CompiledCircuitArtifact<BF>,
        decoder_table: Option<&DeviceSlice<ExecutorFamilyDecoderData>>,
        default_pc_value_in_padding: u32,
        setup: &mut SetupPrecomputations,
        tracing_data_transfer: TracingDataTransfer<'a, impl GoodAllocator>,
        circuit_sequence: usize,
        callbacks: &mut Callbacks<'a>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let trace_len = circuit.trace_len;
        assert!(trace_len.is_power_of_two());
        let log_domain_size = trace_len.trailing_zeros();
        let TracingDataTransfer {
            circuit_type,
            data_host: _,
            data_device,
            transfer,
        } = tracing_data_transfer;
        transfer.ensure_transferred(context)?;
        callbacks.extend(transfer.callbacks);
        let stream = context.get_exec_stream();
        let witness_subtree = &circuit.witness_layout;
        let memory_subtree = &circuit.memory_layout;
        let setup_evaluations = setup.trace_holder.get_evaluations(context)?;
        assert_eq!(COMMON_TABLE_WIDTH, 3);
        assert_eq!(NUM_COLUMNS_FOR_COMMON_TABLE_WIDTH_SETUP, 4);
        let generic_lookup_setup_columns = circuit.setup_layout.generic_lookup_setup_columns;
        let generic_lookup_tables = if generic_lookup_setup_columns.num_elements == 0 {
            DeviceSlice::empty()
        } else {
            let lookup_start = generic_lookup_setup_columns.start * trace_len;
            let lookup_len = NUM_COLUMNS_FOR_COMMON_TABLE_WIDTH_SETUP * trace_len;
            &setup_evaluations[lookup_start..][..lookup_len]
        };
        let timestamp_high_from_circuit_sequence =
            timestamp_high_contribution_from_circuit_sequence(circuit_sequence, trace_len);
        let mut memory_evaluations = self.memory_holder.get_uninit_evaluations_mut();
        let mut witness_evaluations = self.witness_holder.get_uninit_evaluations_mut();
        let mut multiplicities_columns_count = 0;
        let mut multiplicities_range_start = usize::MAX;
        let mut multiplicities_range_end = 0;
        let mut update_multiplicities_range = |column_set: ColumnSet<1>| {
            if column_set.num_elements > 0 {
                let ColumnSet {
                    start,
                    num_elements,
                } = column_set;
                multiplicities_range_start = min(multiplicities_range_start, start);
                multiplicities_columns_count += num_elements;
                multiplicities_range_end = max(multiplicities_range_end, start + num_elements);
            }
        };
        let range_check_16_multiplicities_columns =
            witness_subtree.multiplicities_columns_for_range_check_16;
        update_multiplicities_range(range_check_16_multiplicities_columns);
        let timestamp_range_check_multiplicities_columns =
            witness_subtree.multiplicities_columns_for_timestamp_range_check;
        update_multiplicities_range(timestamp_range_check_multiplicities_columns);
        let decoder_multiplicities_columns =
            witness_subtree.multiplicities_columns_for_decoder_in_executor_families;
        update_multiplicities_range(decoder_multiplicities_columns);
        let generic_multiplicities_columns =
            witness_subtree.multiplicities_columns_for_generic_lookup;
        update_multiplicities_range(generic_multiplicities_columns);
        let mut generic_lookup_mapping = if generic_multiplicities_columns.num_elements == 0 {
            context.alloc(0, AllocationPlacement::Top)?
        } else {
            let size = witness_subtree.width_3_lookups.len() << log_domain_size;
            context.alloc(size, AllocationPlacement::Top)?
        };
        let mut decoder_lookup_mapping = if decoder_multiplicities_columns.num_elements == 0 {
            assert!(decoder_table.is_none());
            context.alloc(0, AllocationPlacement::BestFit)?
        } else {
            assert_eq!(decoder_multiplicities_columns.num_elements, 1);
            assert!(decoder_table.is_some());
            context.alloc(1 << log_domain_size, AllocationPlacement::BestFit)?
        };
        assert_eq!(
            multiplicities_range_start + multiplicities_columns_count,
            multiplicities_range_end
        );
        let all_multiplicities = &mut witness_evaluations
            [multiplicities_range_start << log_domain_size..]
            [..multiplicities_columns_count << log_domain_size];
        match data_device {
            TracingDataDevice::Main {
                inits_and_teardowns,
                trace,
            } => {
                set_to_zero(&mut witness_evaluations, stream)?;
                generate_memory_and_witness_values_main(
                    memory_subtree,
                    &circuit.memory_queries_timestamp_comparison_aux_vars,
                    &inits_and_teardowns,
                    &circuit.lazy_init_address_aux_vars,
                    &trace,
                    timestamp_high_from_circuit_sequence,
                    &mut DeviceMatrixMut::new(&mut memory_evaluations, trace_len),
                    &mut DeviceMatrixMut::new(&mut witness_evaluations, trace_len),
                    stream,
                )?;
                assert_ne!(generic_multiplicities_columns.num_elements, 0);
                generate_witness_values_main(
                    circuit_type.as_main().unwrap(),
                    &trace,
                    &DeviceMatrix::new(&generic_lookup_tables, trace_len),
                    &DeviceMatrix::new(&memory_evaluations, trace_len),
                    &mut DeviceMatrixMut::new(&mut witness_evaluations, trace_len),
                    &mut DeviceMatrixMut::new(&mut generic_lookup_mapping, trace_len),
                    stream,
                )?;
            }
            TracingDataDevice::Delegation(trace) => {
                set_to_zero(all_multiplicities, stream)?;
                generate_memory_and_witness_values_delegation(
                    memory_subtree,
                    &circuit.register_and_indirect_access_timestamp_comparison_aux_vars,
                    &trace,
                    &mut DeviceMatrixMut::new(&mut memory_evaluations, trace_len),
                    &mut DeviceMatrixMut::new(&mut witness_evaluations, trace_len),
                    stream,
                )?;
                assert_ne!(generic_multiplicities_columns.num_elements, 0);
                generate_witness_values_delegation(
                    circuit_type.as_delegation().unwrap(),
                    &trace,
                    &DeviceMatrix::new(&generic_lookup_tables, trace_len),
                    &DeviceMatrix::new(&memory_evaluations, trace_len),
                    &mut DeviceMatrixMut::new(&mut witness_evaluations, trace_len),
                    &mut DeviceMatrixMut::new(&mut generic_lookup_mapping, trace_len),
                    stream,
                )?;
            }
            TracingDataDevice::Unrolled(unrolled) => match unrolled {
                UnrolledTracingDataDevice::Memory(trace) => {
                    set_to_zero(&mut witness_evaluations, stream)?;
                    generate_memory_and_witness_values_unrolled_memory(
                        memory_subtree,
                        &circuit.memory_queries_timestamp_comparison_aux_vars,
                        circuit.executor_family_circuit_next_timestamp_aux_var,
                        decoder_table.unwrap(),
                        &trace,
                        &mut DeviceMatrixMut::new(&mut memory_evaluations, trace_len),
                        &mut DeviceMatrixMut::new(&mut witness_evaluations, trace_len),
                        &mut decoder_lookup_mapping,
                        stream,
                    )?;
                    generate_witness_values_unrolled_memory(
                        circuit_type.as_unrolled().unwrap().as_memory().unwrap(),
                        &trace,
                        &DeviceMatrix::new(&generic_lookup_tables, trace_len),
                        &DeviceMatrix::new(&memory_evaluations, trace_len),
                        &mut DeviceMatrixMut::new(&mut witness_evaluations, trace_len),
                        &mut DeviceMatrixMut::new(&mut generic_lookup_mapping, trace_len),
                        stream,
                    )?;
                }
                UnrolledTracingDataDevice::NonMemory(trace) => {
                    set_to_zero(&mut witness_evaluations, stream)?;
                    generate_memory_and_witness_values_unrolled_non_memory(
                        memory_subtree,
                        &circuit.memory_queries_timestamp_comparison_aux_vars,
                        circuit.executor_family_circuit_next_timestamp_aux_var,
                        decoder_table.unwrap(),
                        default_pc_value_in_padding,
                        &trace,
                        &mut DeviceMatrixMut::new(&mut memory_evaluations, trace_len),
                        &mut DeviceMatrixMut::new(&mut witness_evaluations, trace_len),
                        &mut decoder_lookup_mapping,
                        stream,
                    )?;
                    generate_witness_values_unrolled_non_memory(
                        circuit_type.as_unrolled().unwrap().as_non_memory().unwrap(),
                        &trace,
                        &DeviceMatrix::new(&generic_lookup_tables, trace_len),
                        &DeviceMatrix::new(&memory_evaluations, trace_len),
                        &mut DeviceMatrixMut::new(&mut witness_evaluations, trace_len),
                        &mut DeviceMatrixMut::new(&mut generic_lookup_mapping, trace_len),
                        stream,
                    )?;
                }
                UnrolledTracingDataDevice::InitsAndTeardowns(inits_and_teardowns) => {
                    set_to_zero(all_multiplicities, stream)?;
                    generate_memory_and_witness_values_inits_and_teardowns(
                        memory_subtree,
                        &inits_and_teardowns,
                        &circuit.lazy_init_address_aux_vars,
                        &mut DeviceMatrixMut::new(&mut memory_evaluations, trace_len),
                        &mut DeviceMatrixMut::new(&mut witness_evaluations, trace_len),
                        stream,
                    )?;
                }
            },
        };
        if range_check_16_multiplicities_columns.num_elements != 0
            || timestamp_range_check_multiplicities_columns.num_elements != 0
        {
            generate_range_check_multiplicities(
                circuit,
                &DeviceMatrix::new(setup_evaluations, trace_len),
                &mut DeviceMatrixMut::new(&mut witness_evaluations, trace_len),
                &DeviceMatrix::new(&memory_evaluations, trace_len),
                timestamp_high_from_circuit_sequence,
                trace_len,
                context,
            )?;
        }
        if decoder_multiplicities_columns.num_elements != 0 {
            let multiplicities = &mut witness_evaluations
                [decoder_multiplicities_columns.start << log_domain_size..]
                [..decoder_multiplicities_columns.num_elements << log_domain_size];
            generate_generic_lookup_multiplicities(
                &mut DeviceMatrixMut::new(&mut decoder_lookup_mapping, trace_len),
                &mut DeviceMatrixMut::new(multiplicities, trace_len),
                context,
            )?;
        }
        if generic_multiplicities_columns.num_elements != 0 {
            let multiplicities = &mut witness_evaluations
                [generic_multiplicities_columns.start << log_domain_size..]
                [..generic_multiplicities_columns.num_elements << log_domain_size];
            generate_generic_lookup_multiplicities(
                &mut DeviceMatrixMut::new(&mut generic_lookup_mapping, trace_len),
                &mut DeviceMatrixMut::new(multiplicities, trace_len),
                context,
            )?;
        }
        self.generic_lookup_mapping = Some(generic_lookup_mapping);
        Ok(())
    }

    pub fn commit_witness(
        &mut self,
        circuit: &Arc<CompiledCircuitArtifact<BF>>,
        callbacks: &mut Callbacks,
        context: &ProverContext,
    ) -> CudaResult<()> {
        self.memory_holder
            .make_evaluations_sum_to_zero_extend_and_commit(context)?;
        self.witness_holder
            .make_evaluations_sum_to_zero_extend_and_commit(context)?;
        self.produce_public_inputs(circuit, callbacks, context)?;
        Ok(())
    }

    pub fn produce_public_inputs(
        &mut self,
        circuit: &Arc<CompiledCircuitArtifact<BF>>,
        callbacks: &mut Callbacks,
        context: &ProverContext,
    ) -> CudaResult<()> {
        if self.public_inputs.is_some() {
            return Ok(());
        }
        if circuit.public_inputs.is_empty() {
            self.public_inputs = Some(unsafe { context.alloc_host_uninit_slice(0) });
            return Ok(());
        }
        let holder = &mut self.witness_holder;
        let columns_count = holder.columns_count;
        let trace_len = 1 << holder.log_domain_size;
        let stream = context.get_exec_stream();
        let mut d_witness_first_row = context.alloc(columns_count, AllocationPlacement::BestFit)?;
        let mut d_witness_one_before_last_row =
            context.alloc(columns_count, AllocationPlacement::BestFit)?;
        let mut h_witness_first_row = unsafe { context.alloc_host_uninit_slice(columns_count) };
        let h_witness_first_row_accessor = h_witness_first_row.get_mut_accessor();
        let mut h_witness_one_before_last_row =
            unsafe { context.alloc_host_uninit_slice(columns_count) };
        let h_witness_one_before_last_row_accessor =
            h_witness_one_before_last_row.get_mut_accessor();
        let evaluations = holder.get_evaluations(context)?;
        let first_row_src = DeviceMatrixChunk::new(evaluations, trace_len, 0, 1);
        let one_before_last_row_src =
            DeviceMatrixChunk::new(evaluations, trace_len, trace_len - 2, 1);
        let mut first_row_dst = DeviceMatrixMut::new(&mut d_witness_first_row, 1);
        let mut one_before_last_row_dst =
            DeviceMatrixMut::new(&mut d_witness_one_before_last_row, 1);
        set_by_ref(&first_row_src, &mut first_row_dst, stream)?;
        set_by_ref(
            &one_before_last_row_src,
            &mut one_before_last_row_dst,
            stream,
        )?;
        memory_copy_async(
            unsafe { h_witness_first_row_accessor.get_mut() },
            &d_witness_first_row,
            stream,
        )?;
        memory_copy_async(
            unsafe { h_witness_one_before_last_row_accessor.get_mut() },
            &d_witness_one_before_last_row,
            stream,
        )?;
        let mut public_inputs =
            unsafe { context.alloc_host_uninit_slice(circuit.public_inputs.len()) };
        let unsage_public_inputs = public_inputs.get_mut_accessor();
        let circuit_clone = circuit.clone();
        let function = move || unsafe {
            let mut first_row_public_inputs = vec![];
            let mut one_before_last_row_public_inputs = vec![];
            let witness_first_row = h_witness_first_row_accessor.get();
            let witness_one_before_last_row = h_witness_one_before_last_row_accessor.get();
            for (location, column_address) in circuit_clone.public_inputs.iter() {
                match location {
                    BoundaryConstraintLocation::FirstRow => {
                        let value = read_value(*column_address, witness_first_row, &[]);
                        first_row_public_inputs.push(value);
                    }
                    BoundaryConstraintLocation::OneBeforeLastRow => {
                        let value = read_value(*column_address, witness_one_before_last_row, &[]);
                        one_before_last_row_public_inputs.push(value);
                    }
                    BoundaryConstraintLocation::LastRow => {
                        panic!("public inputs on the last row are not supported");
                    }
                }
            }
            let public_inputs = unsage_public_inputs.get_mut();
            let mut iter = public_inputs.iter_mut();
            iter.set_from(first_row_public_inputs);
            iter.set_from(one_before_last_row_public_inputs);
        };
        callbacks.schedule(function, stream)?;
        self.public_inputs = Some(public_inputs);
        Ok(())
    }
}
