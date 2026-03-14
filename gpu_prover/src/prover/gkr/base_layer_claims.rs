use std::collections::BTreeMap;

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
use crate::primitives::context::{HostAllocation, ProverContext};
use crate::primitives::device_structures::{DeviceMatrixChunk, DeviceMatrixMut, DeviceVectorChunk};
use crate::primitives::field::BF;
use crate::prover::trace_holder::TraceHolder;

const MAX_REDUCTION_ROW_CHUNK_LOG2: u32 = 20;
const TARGET_WEIGHTED_BUFFER_BYTES: usize = 64 * 1024 * 1024;
const MAX_COLUMN_BATCH: usize = 8;

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

fn alloc_host_and_copy<T: Copy>(context: &ProverContext, values: &[T]) -> HostAllocation<[T]> {
    let mut allocation = unsafe { context.alloc_transient_host_uninit_slice(values.len()) };
    unsafe {
        allocation
            .get_mut_accessor()
            .get_mut()
            .copy_from_slice(values);
    }
    allocation
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

fn reduce_trace_holder_claims<E>(
    trace_holder: &TraceHolder<BF>,
    eq_values: &DeviceSlice<E>,
    context: &ProverContext,
) -> CudaResult<Vec<E>>
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
    let mut result = Vec::with_capacity(columns_count);

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

        let mut host_batch_sums = unsafe { context.alloc_transient_host_uninit_slice(batch_cols) };
        {
            let batch_sums_slice = &batch_sums[..batch_cols];
            memory_copy_async(&mut host_batch_sums, batch_sums_slice, stream)?;
        }
        stream.synchronize()?;
        unsafe {
            result.extend_from_slice(host_batch_sums.get_accessor().get());
        }
    }

    Ok(result)
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
    let trace_len = 1usize << setup_trace_holder.log_domain_size;
    assert_eq!(
        base_layer_point.len(),
        trace_len.trailing_zeros() as usize,
        "base-layer point must match trace length"
    );
    for (label, trace_holder) in [
        ("memory", memory_trace_holder),
        ("witness", witness_trace_holder),
    ] {
        assert_eq!(
            trace_holder.log_domain_size, setup_trace_holder.log_domain_size,
            "{label} trace holder must match setup trace length",
        );
    }

    let claim_point_host = alloc_host_and_copy(context, base_layer_point);
    let mut claim_point_device =
        context.alloc(base_layer_point.len(), AllocationPlacement::BestFit)?;
    let mut eq_values = context.alloc(trace_len, AllocationPlacement::BestFit)?;
    let stream = context.get_exec_stream();
    memory_copy_async(&mut claim_point_device, &claim_point_host, stream)?;
    launch_build_eq_values(
        claim_point_device.as_ptr(),
        0,
        base_layer_point.len(),
        eq_values.as_mut_ptr(),
        trace_len,
        context,
    )?;

    let mem_polys_claims = reduce_trace_holder_claims(memory_trace_holder, &eq_values, context)?;
    let wit_polys_claims = reduce_trace_holder_claims(witness_trace_holder, &eq_values, context)?;
    let setup_polys_claims = reduce_trace_holder_claims(setup_trace_holder, &eq_values, context)?;

    let mut completed_claims = layer_0_claims.clone();
    fill_missing_cached_dependency_claims(
        layer_desc,
        &mut completed_claims,
        &mem_polys_claims,
        &wit_polys_claims,
        &setup_polys_claims,
    );

    Ok(GpuGKRBaseLayerTailOutput {
        completed_claims,
        mem_polys_claims,
        wit_polys_claims,
        setup_polys_claims,
    })
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use cs::definitions::GKRAddress;
    use cs::gkr_compiler::GKRLayerDescription;
    use era_cudart::memory::memory_copy;
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
        memory_copy(trace_holder.get_uninit_hypercube_evals_mut(), values).unwrap();
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
