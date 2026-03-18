use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

use cs::definitions::GKRAddress;
use cs::gkr_compiler::GKRLayerDescription;
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use field::{Field, FieldExtension};

use super::backward::{launch_build_eq_values, GpuDimensionReducingKernelSet};
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::cub::device_reduce::{
    batch_reduce, get_batch_reduce_temp_storage_bytes, ReduceOperation,
};
use crate::ops::simple::{add_into_y, mul, set_to_zero, Add, BinaryOp, Mul};
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{HostAllocation, ProverContext};
use crate::primitives::device_structures::{DeviceMatrixChunk, DeviceMatrixMut, DeviceVectorChunk};
use crate::primitives::device_tracing::Range;
use crate::primitives::field::BF;
use crate::prover::trace_holder::TraceHolder;

const MAX_REDUCTION_ROW_CHUNK_LOG2: u32 = 20;
const TARGET_WEIGHTED_BUFFER_BYTES: usize = 64 * 1024 * 1024;
const MAX_COLUMN_BATCH: usize = 8;

#[derive(Clone)]
pub(crate) struct GpuGKRBaseLayerTailOutput<E> {
    pub(crate) completed_claims: BTreeMap<GKRAddress, E>,
    pub(crate) mem_polys_claims: Vec<E>,
    pub(crate) wit_polys_claims: Vec<E>,
    pub(crate) setup_polys_claims: Vec<E>,
}

impl<E: Copy> GpuGKRBaseLayerTailOutput<E> {
    pub(crate) fn claim_for_address(&self, address: GKRAddress) -> Option<E> {
        claim_from_dense_vectors(
            &self.mem_polys_claims,
            &self.wit_polys_claims,
            &self.setup_polys_claims,
            address,
        )
    }
}

pub(crate) struct ScheduledBaseLayerClaimsState<E> {
    result: Option<GpuGKRBaseLayerTailOutput<E>>,
}

pub(crate) fn clone_base_layer_claims_result<E>(
    shared_state: &Arc<Mutex<ScheduledBaseLayerClaimsState<E>>>,
) -> GpuGKRBaseLayerTailOutput<E>
where
    E: Clone,
{
    shared_state
        .lock()
        .unwrap()
        .result
        .as_ref()
        .cloned()
        .expect("base-layer claims result must be available")
}

pub(crate) fn fill_base_layer_claim_vectors<E>(
    shared_state: &Arc<Mutex<ScheduledBaseLayerClaimsState<E>>>,
    mem_dst: &mut [E],
    wit_dst: &mut [E],
    setup_dst: &mut [E],
) where
    E: Copy,
{
    let state = shared_state.lock().unwrap();
    let result = state
        .result
        .as_ref()
        .expect("base-layer claims result must be available");
    assert_eq!(
        mem_dst.len(),
        result.mem_polys_claims.len(),
        "memory claims destination length mismatch"
    );
    assert_eq!(
        wit_dst.len(),
        result.wit_polys_claims.len(),
        "witness claims destination length mismatch"
    );
    assert_eq!(
        setup_dst.len(),
        result.setup_polys_claims.len(),
        "setup claims destination length mismatch"
    );
    mem_dst.copy_from_slice(&result.mem_polys_claims);
    wit_dst.copy_from_slice(&result.wit_polys_claims);
    setup_dst.copy_from_slice(&result.setup_polys_claims);
}

pub(crate) fn fill_mem_polys_claims<E>(
    shared_state: &Arc<Mutex<ScheduledBaseLayerClaimsState<E>>>,
    dst: &mut [E],
) where
    E: Copy,
{
    let state = shared_state.lock().unwrap();
    let src = &state
        .result
        .as_ref()
        .expect("base-layer claims result must be available")
        .mem_polys_claims;
    assert_eq!(
        dst.len(),
        src.len(),
        "memory claims destination length mismatch"
    );
    dst.copy_from_slice(src);
}

pub(crate) fn fill_wit_polys_claims<E>(
    shared_state: &Arc<Mutex<ScheduledBaseLayerClaimsState<E>>>,
    dst: &mut [E],
) where
    E: Copy,
{
    let state = shared_state.lock().unwrap();
    let src = &state
        .result
        .as_ref()
        .expect("base-layer claims result must be available")
        .wit_polys_claims;
    assert_eq!(
        dst.len(),
        src.len(),
        "witness claims destination length mismatch"
    );
    dst.copy_from_slice(src);
}

pub(crate) fn fill_setup_polys_claims<E>(
    shared_state: &Arc<Mutex<ScheduledBaseLayerClaimsState<E>>>,
    dst: &mut [E],
) where
    E: Copy,
{
    let state = shared_state.lock().unwrap();
    let src = &state
        .result
        .as_ref()
        .expect("base-layer claims result must be available")
        .setup_polys_claims;
    assert_eq!(
        dst.len(),
        src.len(),
        "setup claims destination length mismatch"
    );
    dst.copy_from_slice(src);
}

pub(crate) struct GpuGKRBaseLayerClaimsScheduledExecution<E> {
    #[allow(dead_code)]
    tracing_ranges: Vec<Range>,
    #[allow(dead_code)]
    claim_point_host: HostAllocation<[E]>,
    #[allow(dead_code)]
    start_callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    mem_polys_claims: Vec<HostAllocation<[E]>>,
    #[allow(dead_code)]
    wit_polys_claims: Vec<HostAllocation<[E]>>,
    #[allow(dead_code)]
    setup_polys_claims: Vec<HostAllocation<[E]>>,
    #[allow(dead_code)]
    finish_callbacks: Callbacks<'static>,
    shared_state: Arc<Mutex<ScheduledBaseLayerClaimsState<E>>>,
}

impl<E> GpuGKRBaseLayerClaimsScheduledExecution<E> {
    pub(crate) fn shared_state_handle(&self) -> Arc<Mutex<ScheduledBaseLayerClaimsState<E>>> {
        Arc::clone(&self.shared_state)
    }

    pub(crate) fn wait(self, context: &ProverContext) -> CudaResult<GpuGKRBaseLayerTailOutput<E>> {
        context.get_exec_stream().synchronize()?;
        self.shared_state
            .lock()
            .unwrap()
            .result
            .take()
            .ok_or(era_cudart_sys::CudaError::ErrorInvalidValue)
    }
}

fn claim_from_dense_vectors<E: Copy>(
    mem_polys_claims: &[E],
    wit_polys_claims: &[E],
    setup_polys_claims: &[E],
    address: GKRAddress,
) -> Option<E> {
    match address {
        GKRAddress::BaseLayerMemory(offset) => mem_polys_claims.get(offset).copied(),
        GKRAddress::BaseLayerWitness(offset) => wit_polys_claims.get(offset).copied(),
        GKRAddress::Setup(offset) => setup_polys_claims.get(offset).copied(),
        _ => None,
    }
}

fn fill_missing_cached_dependency_claims<E: Copy>(
    layer_desc: &GKRLayerDescription,
    completed_claims: &mut BTreeMap<GKRAddress, E>,
    mem_polys_claims: &[E],
    wit_polys_claims: &[E],
    setup_polys_claims: &[E],
) {
    for (cached_addr, relation) in layer_desc.cached_relations.iter() {
        debug_assert!(
            completed_claims.contains_key(cached_addr),
            "Missing claim for cached address {:?}",
            cached_addr
        );

        for dep in relation.dependencies() {
            if completed_claims.contains_key(&dep) {
                continue;
            }

            let value = claim_from_dense_vectors(
                mem_polys_claims,
                wit_polys_claims,
                setup_polys_claims,
                dep,
            )
            .unwrap_or_else(|| {
                panic!(
                    "Unexpected dependency address {:?} for cached relation {:?}",
                    dep, cached_addr
                )
            });
            completed_claims.insert(dep, value);
        }
    }
}

fn schedule_reduce_trace_holder_claims<E>(
    trace_holder: &TraceHolder<BF>,
    eq_values: &DeviceSlice<E>,
    context: &ProverContext,
) -> CudaResult<Vec<HostAllocation<[E]>>>
where
    E: GpuDimensionReducingKernelSet + Field + 'static,
    Add: BinaryOp<E, E, E>,
    Mul: BinaryOp<BF, E, E>,
{
    let trace_len = 1usize << trace_holder.log_domain_size;
    assert_eq!(eq_values.len(), trace_len);
    let columns_count = trace_holder.columns_count;
    if columns_count == 0 {
        return Ok(Vec::new());
    }

    let row_chunk_size = trace_len.min(1usize << MAX_REDUCTION_ROW_CHUNK_LOG2);
    assert!(row_chunk_size.is_power_of_two());
    assert_eq!(trace_len % row_chunk_size, 0);

    let max_values_per_batch =
        (TARGET_WEIGHTED_BUFFER_BYTES / core::mem::size_of::<E>()).max(row_chunk_size);
    let columns_per_batch = (max_values_per_batch / row_chunk_size)
        .clamp(1, MAX_COLUMN_BATCH)
        .min(columns_count);

    let mut weighted_rows = context.alloc(
        columns_per_batch * row_chunk_size,
        AllocationPlacement::BestFit,
    )?;
    let mut partial_sums = context.alloc(columns_per_batch, AllocationPlacement::BestFit)?;
    let mut batch_sums = context.alloc(columns_per_batch, AllocationPlacement::BestFit)?;
    let reduction_temp_bytes = get_batch_reduce_temp_storage_bytes::<E>(
        ReduceOperation::Sum,
        columns_per_batch as i32,
        row_chunk_size as i32,
    )?;
    let mut reduction_temp = context.alloc(reduction_temp_bytes, AllocationPlacement::BestFit)?;
    let stream = context.get_exec_stream();
    let raw_values = trace_holder.get_hypercube_evals();
    let mut host_batches = Vec::with_capacity(columns_count.div_ceil(columns_per_batch));

    for column_start in (0..columns_count).step_by(columns_per_batch) {
        let batch_cols = columns_per_batch.min(columns_count - column_start);
        {
            let batch_sums_slice = &mut batch_sums[..batch_cols];
            set_to_zero(batch_sums_slice, stream)?;
        }

        let column_offset = column_start * trace_len;
        let batch_values = &raw_values[column_offset..column_offset + batch_cols * trace_len];

        for row_start in (0..trace_len).step_by(row_chunk_size) {
            let eq_chunk = DeviceVectorChunk::new(eq_values, row_start, row_chunk_size);
            let values_chunk =
                DeviceMatrixChunk::new(batch_values, trace_len, row_start, row_chunk_size);

            {
                let weighted_slice = &mut weighted_rows[..batch_cols * row_chunk_size];
                let mut weighted_matrix = DeviceMatrixMut::new(weighted_slice, row_chunk_size);
                mul(&values_chunk, &eq_chunk, &mut weighted_matrix, stream)?;
                let partial_sums_slice = &mut partial_sums[..batch_cols];
                batch_reduce(
                    ReduceOperation::Sum,
                    &mut reduction_temp,
                    &weighted_matrix,
                    partial_sums_slice,
                    stream,
                )?;
            }

            let partial_sums_slice = &partial_sums[..batch_cols];
            let batch_sums_slice = &mut batch_sums[..batch_cols];
            add_into_y(partial_sums_slice, batch_sums_slice, stream)?;
        }

        let mut host_batch_sums = unsafe { context.alloc_host_uninit_slice(batch_cols) };
        {
            let batch_sums_slice = &batch_sums[..batch_cols];
            memory_copy_async(&mut host_batch_sums, batch_sums_slice, stream)?;
        }
        host_batches.push(host_batch_sums);
    }

    Ok(host_batches)
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn schedule_prepare_base_layer_claims_with_sources<E>(
    layer_desc: GKRLayerDescription,
    claim_point_len: usize,
    point_fill: impl Fn(&mut [E]) + Send + Sync + 'static,
    initial_claims: impl Fn() -> BTreeMap<GKRAddress, E> + Send + Sync + 'static,
    setup_trace_holder: &TraceHolder<BF>,
    memory_trace_holder: &TraceHolder<BF>,
    witness_trace_holder: &TraceHolder<BF>,
    context: &ProverContext,
) -> CudaResult<GpuGKRBaseLayerClaimsScheduledExecution<E>>
where
    E: GpuDimensionReducingKernelSet + FieldExtension<BF> + Field + 'static,
    Add: BinaryOp<E, E, E>,
    Mul: BinaryOp<BF, E, E>,
{
    for (label, trace_holder) in [
        ("memory", memory_trace_holder),
        ("witness", witness_trace_holder),
    ] {
        assert_eq!(
            trace_holder.log_domain_size, setup_trace_holder.log_domain_size,
            "{label} trace holder must match setup trace length",
        );
    }

    let trace_len = 1usize << setup_trace_holder.log_domain_size;
    assert_eq!(
        claim_point_len,
        trace_len.trailing_zeros() as usize,
        "base-layer point must match trace length"
    );

    let stream = context.get_exec_stream();
    let mut tracing_ranges = Vec::new();
    let schedule_range = Range::new("gkr.base_layer_claims.schedule")?;
    schedule_range.start(stream)?;

    let mut start_callbacks = Callbacks::new();
    let mut claim_point_host = unsafe { context.alloc_host_uninit_slice(claim_point_len) };
    let claim_point_accessor = claim_point_host.get_mut_accessor();
    start_callbacks.schedule(
        move || unsafe {
            point_fill(claim_point_accessor.get_mut());
        },
        stream,
    )?;
    let mut claim_point_device = context.alloc(claim_point_len, AllocationPlacement::BestFit)?;
    memory_copy_async(&mut claim_point_device, &claim_point_host, stream)?;
    let mut eq_values = context.alloc(trace_len, AllocationPlacement::BestFit)?;
    launch_build_eq_values(
        claim_point_device.as_ptr(),
        0,
        claim_point_len,
        eq_values.as_mut_ptr(),
        trace_len,
        context,
    )?;

    let mem_polys_claims =
        schedule_reduce_trace_holder_claims(memory_trace_holder, &eq_values, context)?;
    let wit_polys_claims =
        schedule_reduce_trace_holder_claims(witness_trace_holder, &eq_values, context)?;
    let setup_polys_claims =
        schedule_reduce_trace_holder_claims(setup_trace_holder, &eq_values, context)?;

    let shared_state = Arc::new(Mutex::new(ScheduledBaseLayerClaimsState { result: None }));
    let mut finish_callbacks = Callbacks::new();
    let mem_polys_claims_accessors = mem_polys_claims
        .iter()
        .map(HostAllocation::get_accessor)
        .collect::<Vec<_>>();
    let wit_polys_claims_accessors = wit_polys_claims
        .iter()
        .map(HostAllocation::get_accessor)
        .collect::<Vec<_>>();
    let setup_polys_claims_accessors = setup_polys_claims
        .iter()
        .map(HostAllocation::get_accessor)
        .collect::<Vec<_>>();
    let shared_state_for_callback = Arc::clone(&shared_state);
    finish_callbacks.schedule(
        move || unsafe {
            let collect = |accessors: &[crate::primitives::context::UnsafeAccessor<[E]>]| {
                let total_len = accessors.iter().map(|accessor| accessor.get().len()).sum();
                let mut values = Vec::with_capacity(total_len);
                for accessor in accessors.iter() {
                    values.extend_from_slice(accessor.get());
                }
                values
            };

            let mem_polys_claims = collect(&mem_polys_claims_accessors);
            let wit_polys_claims = collect(&wit_polys_claims_accessors);
            let setup_polys_claims = collect(&setup_polys_claims_accessors);
            let mut completed_claims = initial_claims();
            fill_missing_cached_dependency_claims(
                &layer_desc,
                &mut completed_claims,
                &mem_polys_claims,
                &wit_polys_claims,
                &setup_polys_claims,
            );
            shared_state_for_callback.lock().unwrap().result = Some(GpuGKRBaseLayerTailOutput {
                completed_claims,
                mem_polys_claims,
                wit_polys_claims,
                setup_polys_claims,
            });
        },
        stream,
    )?;

    schedule_range.end(stream)?;
    tracing_ranges.push(schedule_range);

    Ok(GpuGKRBaseLayerClaimsScheduledExecution {
        tracing_ranges,
        claim_point_host,
        start_callbacks,
        mem_polys_claims,
        wit_polys_claims,
        setup_polys_claims,
        finish_callbacks,
        shared_state,
    })
}

pub(crate) fn schedule_prepare_base_layer_claims<E>(
    layer_desc: &GKRLayerDescription,
    base_layer_point: &[E],
    layer_0_claims: &BTreeMap<GKRAddress, E>,
    setup_trace_holder: &TraceHolder<BF>,
    memory_trace_holder: &TraceHolder<BF>,
    witness_trace_holder: &TraceHolder<BF>,
    context: &ProverContext,
) -> CudaResult<GpuGKRBaseLayerClaimsScheduledExecution<E>>
where
    E: GpuDimensionReducingKernelSet + FieldExtension<BF> + Field + 'static,
    Add: BinaryOp<E, E, E>,
    Mul: BinaryOp<BF, E, E>,
{
    let base_layer_point = base_layer_point.to_vec();
    let layer_0_claims = layer_0_claims.clone();
    schedule_prepare_base_layer_claims_with_sources(
        layer_desc.clone(),
        base_layer_point.len(),
        move |dst| dst.copy_from_slice(&base_layer_point),
        move || layer_0_claims.clone(),
        setup_trace_holder,
        memory_trace_holder,
        witness_trace_holder,
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
    context: &ProverContext,
) -> CudaResult<GpuGKRBaseLayerTailOutput<E>>
where
    E: GpuDimensionReducingKernelSet + FieldExtension<BF> + Field + 'static,
    Add: BinaryOp<E, E, E>,
    Mul: BinaryOp<BF, E, E>,
{
    schedule_prepare_base_layer_claims(
        layer_desc,
        base_layer_point,
        layer_0_claims,
        setup_trace_holder,
        memory_trace_holder,
        witness_trace_holder,
        context,
    )?
    .wait(context)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use cs::definitions::GKRAddress;
    use cs::gkr_compiler::GKRLayerDescription;
    use era_cudart::memory::memory_copy_async;
    use field::{Field, FieldExtension, PrimeField};
    use prover::gkr::sumcheck::eq_poly::make_eq_poly_in_full;
    use serial_test::serial;
    use worker::Worker;

    use super::prepare_base_layer_claims;
    use crate::primitives::field::{BF, E4};
    use crate::prover::test_utils::make_test_context;
    use crate::prover::trace_holder::{TraceHolder, TreesCacheMode};

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
        let trace_len = 1usize << 4;
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
        let setup_trace_holder =
            make_trace_holder(&setup_values, setup_columns, trace_len, &context);

        let base_layer_point = vec![
            E4::from_base(BF::from_u32_unchecked(3)),
            E4::from_base(BF::from_u32_unchecked(5)),
            E4::from_base(BF::from_u32_unchecked(7)),
            E4::from_base(BF::from_u32_unchecked(11)),
        ];
        let layer_desc = GKRLayerDescription {
            layer: 0,
            gates_with_external_connections: Vec::new(),
            cached_relations: BTreeMap::new(),
            gates: Vec::new(),
            additional_base_layer_openings: Vec::new(),
        };

        let output = prepare_base_layer_claims(
            &layer_desc,
            &base_layer_point,
            &BTreeMap::new(),
            &setup_trace_holder,
            &memory_trace_holder,
            &witness_trace_holder,
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

        assert!(output.completed_claims.is_empty());
        assert_eq!(output.mem_polys_claims, expected_memory);
        assert_eq!(output.wit_polys_claims, expected_witness);
        assert_eq!(output.setup_polys_claims, expected_setup);

        for (column, expected) in expected_memory.iter().copied().enumerate() {
            assert_eq!(
                output.claim_for_address(GKRAddress::BaseLayerMemory(column)),
                Some(expected),
            );
        }
        for (column, expected) in expected_witness.iter().copied().enumerate() {
            assert_eq!(
                output.claim_for_address(GKRAddress::BaseLayerWitness(column)),
                Some(expected),
            );
        }
        for (column, expected) in expected_setup.iter().copied().enumerate() {
            assert_eq!(
                output.claim_for_address(GKRAddress::Setup(column)),
                Some(expected),
            );
        }
    }
}
