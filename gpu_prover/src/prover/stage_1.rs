use super::context::ProverContext;
use super::setup::SetupPrecomputations;
use super::trace_holder::TraceHolder;
use super::tracing_data::{TracingDataDevice, TracingDataTransfer};
use super::BF;
use crate::device_structures::{DeviceMatrix, DeviceMatrixChunk, DeviceMatrixMut};
use crate::ops_simple::{set_by_ref, set_to_zero};
use crate::prover::callbacks::Callbacks;
use crate::witness::memory_delegation::generate_memory_and_witness_values_delegation;
use crate::witness::memory_main::generate_memory_and_witness_values_main;
use crate::witness::multiplicities::{
    generate_generic_lookup_multiplicities, generate_range_check_multiplicities,
};
use crate::witness::witness_delegation::generate_witness_values_delegation;
use crate::witness::witness_main::generate_witness_values_main;
use cs::definitions::{
    timestamp_high_contribution_from_circuit_sequence, BoundaryConstraintLocation,
    COMMON_TABLE_WIDTH, NUM_COLUMNS_FOR_COMMON_TABLE_WIDTH_SETUP,
};
use cs::one_row_compiler::{read_value, CompiledCircuitArtifact};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use std::ops::Deref;
use std::sync::{Arc, Mutex};

pub(crate) struct StageOneOutput<'a, C: ProverContext> {
    pub witness_holder: TraceHolder<BF, C>,
    pub memory_holder: TraceHolder<BF, C>,
    pub generic_lookup_mapping: Option<C::Allocation<u32>>,
    pub callbacks: Option<Callbacks<'a>>,
    pub public_inputs: Option<Arc<Mutex<Vec<BF>>>>,
}

impl<'a, C: ProverContext> StageOneOutput<'a, C> {
    pub fn allocate_trace_holders(
        circuit: &CompiledCircuitArtifact<BF>,
        log_lde_factor: u32,
        log_tree_cap_size: u32,
        context: &C,
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
            context,
        )?;
        Ok(Self {
            witness_holder,
            memory_holder,
            generic_lookup_mapping: None,
            callbacks: None,
            public_inputs: None,
        })
    }

    pub fn generate_witness(
        &mut self,
        circuit: &CompiledCircuitArtifact<BF>,
        setup: &SetupPrecomputations<C>,
        tracing_data_transfer: TracingDataTransfer<'a, C>,
        circuit_sequence: usize,
        context: &C,
    ) -> CudaResult<()> {
        let trace_len = circuit.trace_len;
        assert!(trace_len.is_power_of_two());
        let log_domain_size = trace_len.trailing_zeros();
        let witness_subtree = &circuit.witness_layout;
        let memory_subtree = &circuit.memory_layout;
        let generic_lookup_mapping_size = witness_subtree.width_3_lookups.len() << log_domain_size;
        let mut generic_lookup_mapping = context.alloc(generic_lookup_mapping_size)?;
        let TracingDataTransfer {
            circuit_type,
            data_host: _,
            data_device,
            transfer,
        } = tracing_data_transfer;
        transfer.ensure_transferred(context)?;
        self.callbacks = Some(transfer.callbacks);
        let stream = context.get_exec_stream();
        assert_eq!(COMMON_TABLE_WIDTH, 3);
        assert_eq!(NUM_COLUMNS_FOR_COMMON_TABLE_WIDTH_SETUP, 4);
        let lookup_start = circuit.setup_layout.generic_lookup_setup_columns.start * trace_len;
        let lookup_len = NUM_COLUMNS_FOR_COMMON_TABLE_WIDTH_SETUP * trace_len;
        let setup_evaluations = &setup.trace_holder.get_evaluations();
        let generic_lookup_tables = &setup_evaluations[lookup_start..][..lookup_len];
        let timestamp_high_from_circuit_sequence =
            timestamp_high_contribution_from_circuit_sequence(circuit_sequence, trace_len);
        let generic_multiplicities_columns =
            witness_subtree.multiplicities_columns_for_generic_lookup;
        let range_check_16_multiplicities_columns =
            witness_subtree.multiplicities_columns_for_range_check_16;
        let timestamp_range_check_multiplicities_columns =
            witness_subtree.multiplicities_columns_for_timestamp_range_check;
        assert_eq!(
            range_check_16_multiplicities_columns.start
                + range_check_16_multiplicities_columns.num_elements,
            timestamp_range_check_multiplicities_columns.start
        );
        assert_eq!(
            timestamp_range_check_multiplicities_columns.start
                + timestamp_range_check_multiplicities_columns.num_elements,
            generic_multiplicities_columns.start
        );
        let witness_holder = &mut self.witness_holder;
        let memory_holder = &mut self.memory_holder;
        match data_device {
            TracingDataDevice::Main {
                setup_and_teardown,
                trace,
            } => {
                set_to_zero(witness_holder.get_evaluations_mut(), stream)?;
                generate_memory_and_witness_values_main(
                    memory_subtree,
                    &circuit.memory_queries_timestamp_comparison_aux_vars,
                    &setup_and_teardown,
                    circuit.lazy_init_address_aux_vars.as_ref().unwrap(),
                    &trace,
                    timestamp_high_from_circuit_sequence,
                    &mut DeviceMatrixMut::new(memory_holder.get_evaluations_mut(), trace_len),
                    &mut DeviceMatrixMut::new(witness_holder.get_evaluations_mut(), trace_len),
                    stream,
                )?;
                generate_witness_values_main(
                    circuit_type.as_main().unwrap(),
                    &trace,
                    &DeviceMatrix::new(&generic_lookup_tables, trace_len),
                    &DeviceMatrix::new(memory_holder.get_evaluations(), trace_len),
                    &mut DeviceMatrixMut::new(witness_holder.get_evaluations_mut(), trace_len),
                    &mut DeviceMatrixMut::new(&mut generic_lookup_mapping, trace_len),
                    stream,
                )?;
            }
            TracingDataDevice::Delegation(trace) => {
                let all_multiplicities_columns_count = range_check_16_multiplicities_columns
                    .num_elements
                    + timestamp_range_check_multiplicities_columns.num_elements
                    + generic_multiplicities_columns.num_elements;
                let all_multiplicities = &mut witness_holder.get_evaluations_mut()
                    [range_check_16_multiplicities_columns.start * trace_len..]
                    [..all_multiplicities_columns_count * trace_len];
                set_to_zero(all_multiplicities, stream)?;
                generate_memory_and_witness_values_delegation(
                    memory_subtree,
                    &circuit.register_and_indirect_access_timestamp_comparison_aux_vars,
                    &trace,
                    &mut DeviceMatrixMut::new(memory_holder.get_evaluations_mut(), trace_len),
                    &mut DeviceMatrixMut::new(witness_holder.get_evaluations_mut(), trace_len),
                    stream,
                )?;
                generate_witness_values_delegation(
                    circuit_type.as_delegation().unwrap(),
                    &trace,
                    &DeviceMatrix::new(&generic_lookup_tables, trace_len),
                    &DeviceMatrix::new(memory_holder.get_evaluations(), trace_len),
                    &mut DeviceMatrixMut::new(witness_holder.get_evaluations_mut(), trace_len),
                    &mut DeviceMatrixMut::new(&mut generic_lookup_mapping, trace_len),
                    stream,
                )?;
            }
        };
        let generic_lookup_multiplicities = &mut witness_holder.get_evaluations_mut()
            [generic_multiplicities_columns.start * trace_len..]
            [..generic_multiplicities_columns.num_elements * trace_len];
        generate_generic_lookup_multiplicities(
            &mut DeviceMatrixMut::new(&mut generic_lookup_mapping, trace_len),
            &mut DeviceMatrixMut::new(generic_lookup_multiplicities, trace_len),
            context,
        )?;
        generate_range_check_multiplicities(
            circuit,
            &DeviceMatrix::new(setup.trace_holder.get_evaluations(), trace_len),
            &mut DeviceMatrixMut::new(witness_holder.get_evaluations_mut(), trace_len),
            &DeviceMatrix::new(memory_holder.get_evaluations(), trace_len),
            timestamp_high_from_circuit_sequence,
            trace_len,
            context,
        )?;
        self.generic_lookup_mapping = Some(generic_lookup_mapping);
        Ok(())
    }

    pub fn commit_witness(
        &mut self,
        circuit: &Arc<CompiledCircuitArtifact<BF>>,
        context: &C,
    ) -> CudaResult<()>
    where
        C::HostAllocator: 'a,
    {
        self.memory_holder
            .make_evaluations_sum_to_zero_extend_and_commit(context)?;
        self.memory_holder.produce_tree_caps(context)?;
        self.witness_holder
            .make_evaluations_sum_to_zero_extend_and_commit(context)?;
        self.witness_holder.produce_tree_caps(context)?;
        self.produce_public_inputs(circuit, context)?;
        Ok(())
    }

    pub fn produce_public_inputs(
        &mut self,
        circuit: &Arc<CompiledCircuitArtifact<BF>>,
        context: &C,
    ) -> CudaResult<()>
    where
        C::HostAllocator: 'a,
    {
        if self.public_inputs.is_some() {
            return Ok(());
        }
        if circuit.public_inputs.is_empty() {
            self.public_inputs = Some(Arc::new(Mutex::new(Vec::with_capacity(0))));
            return Ok(());
        }
        let holder = &self.witness_holder;
        let columns_count = holder.columns_count;
        let trace_len = 1 << holder.log_domain_size;
        let stream = context.get_exec_stream();
        let mut d_witness_first_row = context.alloc(columns_count)?;
        let mut d_witness_one_before_last_row = context.alloc(columns_count)?;
        let mut h_witness_first_row =
            Vec::with_capacity_in(columns_count, C::HostAllocator::default());
        let mut h_witness_one_before_last_row =
            Vec::with_capacity_in(columns_count, C::HostAllocator::default());
        unsafe { h_witness_first_row.set_len(columns_count) };
        unsafe { h_witness_one_before_last_row.set_len(columns_count) };
        let first_row_src = DeviceMatrixChunk::new(holder.get_evaluations(), trace_len, 0, 1);
        let one_before_last_row_src =
            DeviceMatrixChunk::new(holder.get_evaluations(), trace_len, trace_len - 2, 1);
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
            &mut h_witness_first_row,
            d_witness_first_row.deref(),
            stream,
        )?;
        memory_copy_async(
            &mut h_witness_one_before_last_row,
            d_witness_one_before_last_row.deref(),
            stream,
        )?;
        let public_inputs = Arc::new(Mutex::new(Vec::with_capacity(circuit.public_inputs.len())));
        let public_inputs_clone = public_inputs.clone();
        let circuit_clone = circuit.clone();
        let function = move || {
            let mut first_row_public_inputs = vec![];
            let mut one_before_last_row_public_inputs = vec![];
            for (location, column_address) in circuit_clone.public_inputs.iter() {
                match location {
                    BoundaryConstraintLocation::FirstRow => {
                        let value = read_value(*column_address, &h_witness_first_row, &[]);
                        first_row_public_inputs.push(value);
                    }
                    BoundaryConstraintLocation::OneBeforeLastRow => {
                        let value =
                            read_value(*column_address, &h_witness_one_before_last_row, &[]);
                        one_before_last_row_public_inputs.push(value);
                    }
                    BoundaryConstraintLocation::LastRow => {
                        panic!("public inputs on the last row are not supported");
                    }
                }
            }
            let mut guard = public_inputs_clone.lock().unwrap();
            guard.extend(first_row_public_inputs);
            guard.extend(one_before_last_row_public_inputs);
        };
        self.callbacks
            .as_mut()
            .unwrap()
            .schedule(function, stream)?;
        self.public_inputs = Some(public_inputs);
        Ok(())
    }

    pub fn get_public_inputs(&self) -> Arc<Mutex<Vec<BF>>> {
        self.public_inputs.clone().unwrap()
    }
}
