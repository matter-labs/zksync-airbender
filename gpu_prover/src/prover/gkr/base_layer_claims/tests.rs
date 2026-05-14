use std::collections::BTreeMap;

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;

use serial_test::serial;
use worker::Worker;

use super::{
    schedule_prepare_base_layer_claims_with_sources, GpuGKRBaseLayerClaimsScheduledExecution,
    VIRTUAL_SETUP_CLAIMS_OUTPUT_LEN,
};
use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::context::ProverContext;
use crate::primitives::field::{BF, E4};
use crate::prover::proof::layout::ProofLayout;
use crate::prover::test_utils::make_test_context;
use crate::prover::trace::holder::{TraceHolder, TreesCacheMode};
use crate::upstream::{
    evaluate_virtual_inits_and_teardowns_base_address_setup_polys,
    evaluate_virtual_range_check_setup_poly, make_eq_poly_in_full, Field, FieldExtension,
    GKRAddress, GKRLayerDescription, PrimeField, TIMESTAMP_COLUMNS_NUM_BITS,
};

#[derive(Clone)]
pub(crate) struct GpuGKRBaseLayerTailSnapshot<E> {
    pub(crate) extra_evaluations_addresses: Box<[GKRAddress]>,
    pub(crate) extra_evaluations_values: Box<[E]>,
    pub(crate) virtual_setup_claims: [E; VIRTUAL_SETUP_CLAIMS_OUTPUT_LEN],
    pub(crate) mem_polys_claims: Box<[E]>,
    pub(crate) wit_polys_claims: Box<[E]>,
    pub(crate) setup_polys_claims: Box<[E]>,
}

impl<E: Copy + 'static> GpuGKRBaseLayerClaimsScheduledExecution<E> {
    pub(crate) fn wait(
        mut self,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRBaseLayerTailSnapshot<E>> {
        let mut callbacks = crate::primitives::callbacks::Callbacks::new();
        if let Some(closure) = self.pending_aggregation.take() {
            callbacks.schedule(closure, context.get_exec_stream())?;
        }
        context.get_exec_stream().synchronize()?;
        // SAFETY: stream is synchronized; the host-pinned buffers are stable
        // and the aggregation callback has finished writing them.
        let extra_evaluations_addresses: Box<[GKRAddress]> = unsafe {
            self.extras_addresses_accessor
                .get()
                .iter()
                .copied()
                .collect()
        };
        let extra_evaluations_values: Box<[E]> = unsafe {
            self.extras_values_accessor
                .expect("test base-layer wait requires host extra values")
                .get()
                .iter()
                .copied()
                .collect()
        };
        let virtual_setup_claims = {
            let accessor = self
                .virtual_setup_claims_accessor
                .expect("test base-layer wait requires virtual setup readback");
            let slice = unsafe { accessor.get() };
            assert_eq!(slice.len(), VIRTUAL_SETUP_CLAIMS_OUTPUT_LEN);
            let mut arr = [slice[0]; VIRTUAL_SETUP_CLAIMS_OUTPUT_LEN];
            arr.copy_from_slice(slice);
            arr
        };
        let mem_polys_claims: Box<[E]> = unsafe {
            self.mem_polys_claims_accessor
                .expect("test base-layer wait requires memory claim readback")
                .get()
                .iter()
                .copied()
                .collect()
        };
        let wit_polys_claims: Box<[E]> = unsafe {
            self.wit_polys_claims_accessor
                .expect("test base-layer wait requires witness claim readback")
                .get()
                .iter()
                .copied()
                .collect()
        };
        let setup_polys_claims: Box<[E]> = unsafe {
            self.setup_polys_claims_accessor
                .expect("test base-layer wait requires setup claim readback")
                .get()
                .iter()
                .copied()
                .collect()
        };
        Ok(GpuGKRBaseLayerTailSnapshot {
            extra_evaluations_addresses,
            extra_evaluations_values,
            virtual_setup_claims,
            mem_polys_claims,
            wit_polys_claims,
            setup_polys_claims,
        })
    }
}

pub(crate) fn schedule_prepare_base_layer_claims<E>(
    layer_desc: &GKRLayerDescription,
    base_layer_point: &[E],
    layer_0_claims: &BTreeMap<GKRAddress, E>,
    setup_trace_holder: &TraceHolder<BF>,
    memory_trace_holder: &TraceHolder<BF>,
    witness_trace_holder: &TraceHolder<BF>,
    proof_layout: &ProofLayout,
    context: &ProverContext,
) -> CudaResult<GpuGKRBaseLayerClaimsScheduledExecution<E>>
where
    E: Copy + super::super::GpuKernels + FieldExtension<BF> + Field + crate::ops::cub::device_reduce::Reduce + 'static,
{
    let initial_addresses: Vec<GKRAddress> = layer_0_claims.keys().copied().collect();
    // Test-only convenience: stage the host-provided base layer point through a
    // pinned host buffer + ephemeral device buffer so the new prove-time API
    // (device claim_point in) keeps a single source of truth. Production callers
    // pass a device slice from backward directly.
    let mut point_host = unsafe { context.alloc_host_uninit_slice::<E>(base_layer_point.len()) };
    unsafe {
        point_host
            .get_mut_accessor()
            .get_mut()
            .copy_from_slice(base_layer_point);
    }
    let mut point_device =
        context.alloc::<E>(base_layer_point.len(), AllocationPlacement::BestFit)?;
    memory_copy_async(&mut point_device, &point_host, context.get_exec_stream())?;
    schedule_prepare_base_layer_claims_with_sources(
        layer_desc.clone(),
        &point_device,
        &initial_addresses,
        setup_trace_holder,
        memory_trace_holder,
        witness_trace_holder,
        None,
        proof_layout,
        None,
        context,
    )
}

pub(crate) fn prepare_base_layer_claims<E>(
    layer_desc: &GKRLayerDescription,
    base_layer_point: &[E],
    layer_0_claims: &BTreeMap<GKRAddress, E>,
    setup_trace_holder: &TraceHolder<BF>,
    memory_trace_holder: &TraceHolder<BF>,
    witness_trace_holder: &TraceHolder<BF>,
    proof_layout: &ProofLayout,
    context: &ProverContext,
) -> CudaResult<GpuGKRBaseLayerTailSnapshot<E>>
where
    E: Copy + super::super::GpuKernels + FieldExtension<BF> + Field + crate::ops::cub::device_reduce::Reduce + 'static,
{
    schedule_prepare_base_layer_claims(
        layer_desc,
        base_layer_point,
        layer_0_claims,
        setup_trace_holder,
        memory_trace_holder,
        witness_trace_holder,
        proof_layout,
        context,
    )?
    .wait(context)
}

fn evaluate_base_poly_with_eq<F: PrimeField, E: FieldExtension<F> + Field>(
    values: &[F],
    eq: &[E],
) -> E {
    assert_eq!(values.len(), eq.len());
    let mut result = E::ZERO;
    for (value, eq_value) in values.iter().zip(eq.iter()) {
        let mut term = *eq_value;
        term.mul_assign_by_base(value);
        result.add_assign(&term);
    }
    result
}

fn make_trace_holder(
    values: &[BF],
    columns_count: usize,
    trace_len: usize,
    context: &crate::primitives::context::ProverContext,
) -> TraceHolder<BF> {
    let mut trace_holder = TraceHolder::<BF>::new(
        trace_len.trailing_zeros(),
        0,
        0,
        0,
        columns_count,
        TreesCacheMode::CacheNone,
        context,
    )
    .unwrap();
    memory_copy_async(
        trace_holder.get_uninit_hypercube_evals_mut(),
        values,
        context.get_exec_stream(),
    )
    .unwrap();
    trace_holder
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn base_layer_claims_match_cpu() {
    let trace_len = 1usize << 19;
    let trace_len_log2 = trace_len.trailing_zeros();
    let memory_columns = 3usize;
    let witness_columns = 2usize;
    let setup_columns = 4usize;
    let context = make_test_context(256, 64);

    let memory_values: Vec<_> = (0..memory_columns * trace_len)
        .map(|i| BF::from_u32_unchecked(i as u32 + 1))
        .collect();
    let witness_values: Vec<_> = (0..witness_columns * trace_len)
        .map(|i| BF::from_u32_unchecked(i as u32 + 101))
        .collect();
    let setup_values: Vec<_> = (0..setup_columns * trace_len)
        .map(|i| BF::from_u32_unchecked(i as u32 + 1001))
        .collect();

    let memory_trace_holder =
        make_trace_holder(&memory_values, memory_columns, trace_len, &context);
    let witness_trace_holder =
        make_trace_holder(&witness_values, witness_columns, trace_len, &context);
    let setup_trace_holder = make_trace_holder(&setup_values, setup_columns, trace_len, &context);

    let base_layer_point: Vec<_> = (0..trace_len_log2)
        .map(|i| E4::from_base(BF::from_u32_unchecked(2 * i + 3)))
        .collect();
    let layer_desc = GKRLayerDescription {
        layer: 1,
        gates_with_external_connections: Vec::new(),
        cached_relations: BTreeMap::new(),
        intermediate_layer_width: Some(0),
        gates: Vec::new(),
    };

    let proof_layout = crate::prover::proof::layout::ProofLayout::new(
        &crate::prover::proof::layout::placeholder_inputs_for_prove(),
    );
    let output = prepare_base_layer_claims(
        &layer_desc,
        &base_layer_point,
        &BTreeMap::new(),
        &setup_trace_holder,
        &memory_trace_holder,
        &witness_trace_holder,
        &proof_layout,
        &context,
    )
    .unwrap();

    let worker = Worker::new();
    let eq_precomputed = make_eq_poly_in_full(&base_layer_point, &worker);
    let eq_at_z = eq_precomputed.last().unwrap();

    let expected_memory: Vec<_> = (0..memory_columns)
        .map(|column| {
            evaluate_base_poly_with_eq::<BF, E4>(
                &memory_values[column * trace_len..(column + 1) * trace_len],
                eq_at_z,
            )
        })
        .collect();
    let expected_witness: Vec<_> = (0..witness_columns)
        .map(|column| {
            evaluate_base_poly_with_eq::<BF, E4>(
                &witness_values[column * trace_len..(column + 1) * trace_len],
                eq_at_z,
            )
        })
        .collect();
    let expected_setup: Vec<_> = (0..setup_columns)
        .map(|column| {
            evaluate_base_poly_with_eq::<BF, E4>(
                &setup_values[column * trace_len..(column + 1) * trace_len],
                eq_at_z,
            )
        })
        .collect();
    let expected_range_16 =
        evaluate_virtual_range_check_setup_poly::<BF, E4, 16>(&base_layer_point, trace_len_log2);
    let expected_timestamp = evaluate_virtual_range_check_setup_poly::<
        BF,
        E4,
        TIMESTAMP_COLUMNS_NUM_BITS,
    >(&base_layer_point, trace_len_log2);
    let (expected_inits_low, expected_inits_high) =
        evaluate_virtual_inits_and_teardowns_base_address_setup_polys::<BF, E4, 2>(
            &base_layer_point,
            trace_len_log2,
        );

    assert_eq!(output.virtual_setup_claims[0], expected_range_16);
    assert_eq!(output.virtual_setup_claims[1], expected_timestamp);
    assert_eq!(output.virtual_setup_claims[2], expected_inits_low);
    assert_eq!(output.virtual_setup_claims[3], expected_inits_high);
    assert_eq!(output.mem_polys_claims.as_ref(), expected_memory.as_slice());
    assert_eq!(
        output.wit_polys_claims.as_ref(),
        expected_witness.as_slice()
    );
    assert_eq!(
        output.setup_polys_claims.as_ref(),
        expected_setup.as_slice(),
    );
    // No cached relations in this test case, so the schedule-time extras
    // plan is empty.
    assert!(output.extra_evaluations_addresses.is_empty());
    assert!(output.extra_evaluations_values.is_empty());

    for (column, expected) in expected_memory.iter().copied().enumerate() {
        assert_eq!(output.mem_polys_claims[column], expected);
    }
    for (column, expected) in expected_witness.iter().copied().enumerate() {
        assert_eq!(output.wit_polys_claims[column], expected);
    }
    for (column, expected) in expected_setup.iter().copied().enumerate() {
        assert_eq!(output.setup_polys_claims[column], expected);
    }
}
