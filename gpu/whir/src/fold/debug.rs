use super::*;

use era_cudart::memory::memory_copy_async;

use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::static_host::alloc_static_pinned_box_from_slice;

use crate::kernels::{accumulate_whir_base_columns, serialize_whir_e4_columns};
use crate::upstream::DefaultTreeConstructor;
use crate::upstream::PrimeField;
// Only consumed by the `#[cfg(test)]` query-parity helpers below.
#[cfg(test)]
use crate::upstream::BaseFieldQuery;
use core::marker::PhantomData;
// Only consumed by the `#[cfg(test)]` query-parity helpers below.
#[cfg(test)]
use gpu_core::primitives::callbacks::Callbacks;
#[cfg(test)]
use gpu_core::primitives::context::HostAllocation;
#[cfg(test)]
use gpu_hash::blake2s::Digest;

pub(super) fn copy_small_to_device<T: Copy>(
    dst: &mut DeviceSlice<T>,
    values: &[T],
    context: &ProverContext,
) -> CudaResult<()> {
    assert_eq!(dst.len(), values.len());
    let host = alloc_static_pinned_box_from_slice(values)?;
    memory_copy_async(dst, &host[..], context.get_exec_stream())
}

pub(super) fn copy_scalar_to_device(
    value: E4,
    state: &mut GpuWhirState,
    context: &ProverContext,
) -> CudaResult<()> {
    copy_small_to_device(&mut state.scalar, &[value], context)
}

pub(super) fn read_reduce_outputs(
    count: usize,
    state: &mut GpuWhirState,
    context: &ProverContext,
) -> CudaResult<Vec<E4>> {
    let stream = context.get_exec_stream();
    let mut host = unsafe { context.alloc_host_uninit_slice(count) };
    memory_copy_async(&mut host, &state.reduce_out[..count], stream)?;
    stream.synchronize()?;
    Ok(unsafe { host.get_accessor().get().to_vec() })
}

pub(super) fn copy_back<T: Clone>(values: &DeviceSlice<T>, context: &ProverContext) -> Vec<T> {
    let mut host = unsafe { context.alloc_host_uninit_slice(values.len()) };
    memory_copy_async(&mut host, values, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    unsafe { host.get_accessor().get().to_vec() }
}

// Only consumed (transitively, via `GpuScheduledBaseFieldQuery::decode`) by
// `fold::tests::query_tests`.
#[cfg(test)]
pub(super) fn decode_base_leaf_values(
    leafs: &[BF],
    values_per_leaf: usize,
    columns_count: usize,
) -> Vec<Vec<BF>> {
    assert_eq!(leafs.len(), values_per_leaf * columns_count);
    let mut result = (0..values_per_leaf)
        .map(|_| Vec::with_capacity(columns_count))
        .collect::<Vec<_>>();
    for column in 0..columns_count {
        for slot in 0..values_per_leaf {
            result[slot].push(leafs[column * values_per_leaf + slot]);
        }
    }
    result
}

/// `(coset_index, decoded_leaf_columns, cpu_query)`.
#[cfg(test)]
type DecodedBaseTraceHolderQuery = (
    usize,
    Vec<Vec<BF>>,
    BaseFieldQuery<BF, DefaultTreeConstructor>,
);

// Only consumed by `fold::tests::query_tests`.
#[cfg(test)]
pub(crate) fn query_base_trace_holder_for_folded_index(
    trace_holder: &mut TraceHolder<BF>,
    index: usize,
    context: &ProverContext,
) -> CudaResult<DecodedBaseTraceHolderQuery> {
    let scheduled =
        schedule_query_base_trace_holder_for_folded_index(trace_holder, index, context)?;
    context.get_exec_stream().synchronize()?;
    let (decoded, cpu_query) = scheduled.decode();
    Ok((scheduled.coset_index, decoded, cpu_query))
}

// Only consumed by `query_base_trace_holder_for_folded_index` above (test-only).
#[cfg(test)]
pub(crate) fn schedule_query_base_trace_holder_for_folded_index(
    trace_holder: &mut TraceHolder<BF>,
    index: usize,
    context: &ProverContext,
) -> CudaResult<GpuScheduledBaseFieldQuery> {
    let lde_factor = 1usize << trace_holder.log_lde_factor;
    let values_per_leaf = 1usize << trace_holder.log_rows_per_leaf;
    let coset_tree_size = (1usize << trace_holder.log_domain_size) / values_per_leaf;
    assert!(values_per_leaf.is_power_of_two());
    assert!(index < (1usize << trace_holder.log_domain_size) * lde_factor / values_per_leaf);
    let value_coset_index = index & (lde_factor - 1);
    let value_internal_index = index / lde_factor;
    let mut callbacks = Callbacks::new();
    let mut host_value_index = unsafe { context.alloc_host_uninit_slice(1) };
    let vi_accessor = host_value_index.get_mut_accessor();
    callbacks.schedule(
        move || unsafe { vi_accessor.get_mut()[0] = value_internal_index as u32 },
        context.get_exec_stream(),
    )?;
    let mut device_value_index = context.alloc(1, AllocationPlacement::BestFit)?;
    memory_copy_async(
        &mut device_value_index,
        &host_value_index,
        context.get_exec_stream(),
    )?;
    drop(host_value_index);
    let value_query =
        trace_holder.get_query_leafs(value_coset_index, &device_value_index, context)?;

    let stage1_coset_index = index / coset_tree_size;
    let path_coset_index = bitreverse_index(stage1_coset_index, trace_holder.log_lde_factor);
    let path_internal_index = index % coset_tree_size;
    let mut host_path_index = unsafe { context.alloc_host_uninit_slice(1) };
    let pi_accessor = host_path_index.get_mut_accessor();
    callbacks.schedule(
        move || unsafe { pi_accessor.get_mut()[0] = path_internal_index as u32 },
        context.get_exec_stream(),
    )?;
    let mut device_path_index = context.alloc(1, AllocationPlacement::BestFit)?;
    memory_copy_async(
        &mut device_path_index,
        &host_path_index,
        context.get_exec_stream(),
    )?;
    drop(host_path_index);
    let path_query =
        trace_holder.get_query_merkle_paths(path_coset_index, &device_path_index, context)?;
    Ok(GpuScheduledBaseFieldQuery {
        index,
        coset_index: value_coset_index,
        callbacks,
        leafs: value_query,
        merkle_paths: path_query,
        values_per_leaf,
        columns_count: trace_holder.columns_count,
    })
}

pub(super) fn build_initial_batched_evals_device_impl(
    memory_trace_holder: &TraceHolder<BF>,
    memory_weights: &[E4],
    witness_trace_holder: &TraceHolder<BF>,
    witness_weights: &[E4],
    setup_trace_holder: &TraceHolder<BF>,
    setup_weights: &[E4],
    use_hypercube_evals: bool,
    result: &mut DeviceSlice<E4>,
    mut upload_weights: impl FnMut(&mut DeviceSlice<E4>, &[E4], &ProverContext) -> CudaResult<()>,
    context: &ProverContext,
) -> CudaResult<Vec<DeviceAllocation<E4>>> {
    let stream = context.get_exec_stream();
    let mut weight_buffers = Vec::with_capacity(3);

    assert!(!memory_weights.is_empty());
    assert!(!witness_weights.is_empty());
    assert!(!setup_weights.is_empty());

    let mut device_memory_weights =
        context.alloc(memory_weights.len(), AllocationPlacement::BestFit)?;
    let mut device_witness_weights =
        context.alloc(witness_weights.len(), AllocationPlacement::BestFit)?;
    let mut device_setup_weights =
        context.alloc(setup_weights.len(), AllocationPlacement::BestFit)?;

    upload_weights(&mut device_memory_weights, memory_weights, context)?;
    upload_weights(&mut device_witness_weights, witness_weights, context)?;
    upload_weights(&mut device_setup_weights, setup_weights, context)?;

    let rows = result.len();
    let memory_values = get_base_columns(memory_trace_holder, rows, use_hypercube_evals);
    let witness_values = get_base_columns(witness_trace_holder, rows, use_hypercube_evals);
    let setup_values = get_base_columns(setup_trace_holder, rows, use_hypercube_evals);

    accumulate_whir_base_columns(
        &memory_values,
        &witness_values,
        &setup_values,
        &device_memory_weights,
        &device_witness_weights,
        &device_setup_weights,
        result,
        stream,
    )?;

    weight_buffers.push(device_memory_weights);
    weight_buffers.push(device_witness_weights);
    weight_buffers.push(device_setup_weights);

    Ok(weight_buffers)
}

pub(super) fn build_initial_batched_evals_device(
    memory_trace_holder: &TraceHolder<BF>,
    memory_weights: &[E4],
    witness_trace_holder: &TraceHolder<BF>,
    witness_weights: &[E4],
    setup_trace_holder: &TraceHolder<BF>,
    setup_weights: &[E4],
    use_hypercube_evals: bool,
    result: &mut DeviceSlice<E4>,
    context: &ProverContext,
) -> CudaResult<Vec<DeviceAllocation<E4>>> {
    build_initial_batched_evals_device_impl(
        memory_trace_holder,
        memory_weights,
        witness_trace_holder,
        witness_weights,
        setup_trace_holder,
        setup_weights,
        use_hypercube_evals,
        result,
        copy_small_to_device,
        context,
    )
}

pub(super) fn initialize_batched_forms_impl(
    memory_trace_holder: &TraceHolder<BF>,
    witness_trace_holder: &TraceHolder<BF>,
    setup_trace_holder: &TraceHolder<BF>,
    mem_polys_claims_len: usize,
    wit_polys_claims_len: usize,
    setup_polys_claims_len: usize,
    batching_challenge: E4,
    use_hypercube_evals_for_batching: bool,
    state: &mut GpuWhirState,
    mut build_initial_form: impl FnMut(
        &TraceHolder<BF>,
        &[E4],
        &TraceHolder<BF>,
        &[E4],
        &TraceHolder<BF>,
        &[E4],
        bool,
        &mut DeviceSlice<E4>,
        &ProverContext,
    ) -> CudaResult<Vec<DeviceAllocation<E4>>>,
    context: &ProverContext,
) -> CudaResult<[Vec<E4>; 3]> {
    assert_batching_source_supported(use_hypercube_evals_for_batching);
    let trace_len = state.current_len;
    assert_eq!(
        memory_trace_holder.log_domain_size,
        witness_trace_holder.log_domain_size
    );
    assert_eq!(
        memory_trace_holder.log_domain_size,
        setup_trace_holder.log_domain_size
    );
    assert_eq!(trace_len, 1usize << memory_trace_holder.log_domain_size);

    let total_base_oracles = memory_trace_holder.columns_count
        + witness_trace_holder.columns_count
        + setup_trace_holder.columns_count;
    let challenge_powers = materialize_powers_serial_starting_with_one::<E4, std::alloc::Global>(
        batching_challenge,
        total_base_oracles,
    );
    let (memory_weights, rest) = challenge_powers.split_at(mem_polys_claims_len);
    let (witness_weights, setup_weights) = rest.split_at(wit_polys_claims_len);
    debug_assert_eq!(setup_weights.len(), setup_polys_claims_len);

    let _weight_buffers = build_initial_form(
        memory_trace_holder,
        memory_weights,
        witness_trace_holder,
        witness_weights,
        setup_trace_holder,
        setup_weights,
        use_hypercube_evals_for_batching,
        &mut state.sumchecked_poly_evaluation_form,
        context,
    )?;

    // The shared initializer consumes serialized BF limbs.
    let mut vectorized_scratch =
        context.alloc::<BF>(trace_len * EXT4_DEGREE, AllocationPlacement::BestFit)?;
    serialize_whir_e4_columns(
        &state.sumchecked_poly_evaluation_form[..trace_len],
        &mut vectorized_scratch[..],
        context.get_exec_stream(),
    )?;
    initialize_batched_monomial_form(
        memory_trace_holder.log_domain_size as usize,
        use_hypercube_evals_for_batching,
        &mut vectorized_scratch[..],
        state,
        context,
    )?;

    Ok([
        memory_weights.to_vec(),
        witness_weights.to_vec(),
        setup_weights.to_vec(),
    ])
}

pub(super) fn initialize_batched_forms(
    memory_trace_holder: &TraceHolder<BF>,
    witness_trace_holder: &TraceHolder<BF>,
    setup_trace_holder: &TraceHolder<BF>,
    mem_polys_claims_len: usize,
    wit_polys_claims_len: usize,
    setup_polys_claims_len: usize,
    batching_challenge: E4,
    use_hypercube_evals_for_batching: bool,
    state: &mut GpuWhirState,
    context: &ProverContext,
) -> CudaResult<[Vec<E4>; 3]> {
    initialize_batched_forms_impl(
        memory_trace_holder,
        witness_trace_holder,
        setup_trace_holder,
        mem_polys_claims_len,
        wit_polys_claims_len,
        setup_polys_claims_len,
        batching_challenge,
        use_hypercube_evals_for_batching,
        state,
        |memory_trace_holder,
         memory_weights,
         witness_trace_holder,
         witness_weights,
         setup_trace_holder,
         setup_weights,
         use_hypercube_evals_for_batching,
         result,
         context| {
            build_initial_batched_evals_device(
                memory_trace_holder,
                memory_weights,
                witness_trace_holder,
                witness_weights,
                setup_trace_holder,
                setup_weights,
                use_hypercube_evals_for_batching,
                result,
                context,
            )
        },
        context,
    )
}

pub(super) fn build_initial_state(
    memory_trace_holder: &TraceHolder<BF>,
    mem_polys_claims: &[E4],
    witness_trace_holder: &TraceHolder<BF>,
    wit_polys_claims: &[E4],
    setup_trace_holder: &TraceHolder<BF>,
    setup_polys_claims: &[E4],
    original_evaluation_point: &[E4],
    batching_challenge: E4,
    use_hypercube_evals_for_batching: bool,
    state: &mut GpuWhirState,
    context: &ProverContext,
) -> CudaResult<([Vec<E4>; 3], E4)> {
    let trace_len = state.current_len;
    assert_eq!(
        original_evaluation_point.len(),
        trace_len.trailing_zeros() as usize
    );

    let batch_challenges = initialize_batched_forms(
        memory_trace_holder,
        witness_trace_holder,
        setup_trace_holder,
        mem_polys_claims.len(),
        wit_polys_claims.len(),
        setup_polys_claims.len(),
        batching_challenge,
        use_hypercube_evals_for_batching,
        state,
        context,
    )?;

    let mut point_device: DeviceAllocation<E4> = context.alloc(
        original_evaluation_point.len(),
        AllocationPlacement::BestFit,
    )?;
    copy_small_to_device(&mut point_device[..], original_evaluation_point, context)?;
    launch_build_eq_values_from_point(
        point_device.as_ptr(),
        0,
        original_evaluation_point.len(),
        state.eq_group_tables.as_mut_ptr(),
        state.eq_poly.as_mut_ptr(),
        trace_len,
        context,
    )?;
    context.get_exec_stream().synchronize()?;
    drop(point_device);

    let mut batched_claim = E4::ZERO;
    for (weights, claims) in
        batch_challenges
            .iter()
            .zip([mem_polys_claims, wit_polys_claims, setup_polys_claims])
    {
        for (weight, claim) in weights.iter().zip(claims.iter()) {
            let mut term = *claim;
            term.mul_assign(weight);
            batched_claim.add_assign(&term);
        }
    }

    Ok((batch_challenges, batched_claim))
}

pub(super) fn special_three_point_eval_device(
    state: &mut GpuWhirState,
    context: &ProverContext,
) -> CudaResult<(E4, E4, E4)> {
    let half = state.current_len / 2;
    assert!(half <= state.scratch0.len());
    let stream = context.get_exec_stream();

    {
        let (eval_low, _) =
            state.sumchecked_poly_evaluation_form[..state.current_len].split_at(half);
        let (eq_low, _) = state.eq_poly[..state.current_len].split_at(half);
        mul(eval_low, eq_low, &mut state.scratch0[..half], stream)?;
    }
    whir_sum(
        &state.scratch0[..half],
        &mut state.scratch1[..],
        &mut state.reduce_out[0],
        stream,
    )?;

    {
        let (_, eval_high) =
            state.sumchecked_poly_evaluation_form[..state.current_len].split_at(half);
        let (_, eq_high) = state.eq_poly[..state.current_len].split_at(half);
        mul(eval_high, eq_high, &mut state.scratch0[..half], stream)?;
    }
    whir_sum(
        &state.scratch0[..half],
        &mut state.scratch1[..],
        &mut state.reduce_out[1],
        stream,
    )?;

    {
        let (eval_low, eval_high) =
            state.sumchecked_poly_evaluation_form[..state.current_len].split_at(half);
        let (eq_low, eq_high) = state.eq_poly[..state.current_len].split_at(half);
        add(eval_low, eval_high, &mut state.scratch0[..half], stream)?;
        add(eq_low, eq_high, &mut state.scratch1[..half], stream)?;
    }
    mul_into_x(&mut state.scratch0[..half], &state.scratch1[..half], stream)?;
    // `scratch1`'s eq sums were consumed by the stream-ordered `mul_into_x`
    // above, so it is free to serve as the sum's partials buffer.
    whir_sum(
        &state.scratch0[..half],
        &mut state.scratch1[..],
        &mut state.reduce_out[2],
        stream,
    )?;

    let mut outputs = read_reduce_outputs(3, state, context)?;
    let quart = BF::from_u32_unchecked(4).inverse().unwrap();
    outputs[2].mul_assign_by_base(&quart);
    Ok((outputs[0], outputs[1], outputs[2]))
}

// Only consumed by `fold::tests` (`special_three_point_eval_device`'s CPU-parity test).
#[cfg(test)]
pub(super) fn schedule_special_three_point_eval_device(
    state: &mut GpuWhirState,
    context: &ProverContext,
) -> CudaResult<HostAllocation<[E4]>> {
    schedule_special_three_point_eval_device_compute(state, context)?;
    schedule_reduce_outputs_readback(3, state, context)
}

pub(super) fn fold_monomial_form_in_place_device(
    state: &mut GpuWhirState,
    challenge: E4,
    context: &ProverContext,
) -> CudaResult<()> {
    copy_scalar_to_device(challenge, state, context)?;
    let half = state.current_len / 2;
    whir_fold_split_half_in_place_vectorized(
        &mut state.sumchecked_poly_monomial_form,
        &state.scalar[0],
        half,
        context.get_exec_stream(),
    )?;
    Ok(())
}

pub(super) fn fold_evaluation_form_in_place_device(
    state: &mut GpuWhirState,
    challenge: E4,
    context: &ProverContext,
) -> CudaResult<()> {
    copy_scalar_to_device(challenge, state, context)?;
    whir_fold_split_half_in_place(
        &mut state.sumchecked_poly_evaluation_form[..state.current_len],
        &state.scalar[0],
        context.get_exec_stream(),
    )
}

pub(super) fn fold_eq_poly_in_place_device(
    state: &mut GpuWhirState,
    challenge: E4,
    context: &ProverContext,
) -> CudaResult<()> {
    copy_scalar_to_device(challenge, state, context)?;
    whir_fold_split_half_in_place(
        &mut state.eq_poly[..state.current_len],
        &state.scalar[0],
        context.get_exec_stream(),
    )
}

pub(super) fn evaluate_monomial_form_device(
    state: &mut GpuWhirState,
    point: E4,
    context: &ProverContext,
) -> CudaResult<E4> {
    let mut d_point = context.alloc(1, AllocationPlacement::BestFit)?;
    memory_copy_async(&mut d_point[..1], &[point], context.get_exec_stream())?;

    // SAFETY: `state.reduce_out[0]` is a live, disjoint single-`E4` slot inside
    // `state.reduce_out`. The impl below only mutably borrows
    // `state.{scratch0, scratch1, sumchecked_poly_monomial_form,
    // current_len}`, none of which overlap with `state.reduce_out`. Aliasing
    // through a raw pointer here sidesteps the borrow checker's inability to
    // split-borrow disjoint fields across a method call; the downstream
    // `read_reduce_outputs` reads from the same slot.
    let reduce_out_ptr = state.reduce_out.as_mut_ptr();
    let out = unsafe { era_cudart::slice::DeviceVariable::from_raw_parts_mut(reduce_out_ptr) };
    schedule_monomial_eval_device_impl(state, &d_point, out, context)?;

    let result = read_reduce_outputs(1, state, context)?[0];

    Ok(result)
}

pub(super) fn vectorized_to_e4_coeffs(
    vectorized_coeffs: &[BF],
    stride: usize,
    count: usize,
) -> Vec<E4> {
    use itertools::Itertools;
    (0..count)
        .map(|i| {
            let coeffs = std::array::from_fn(|j| vectorized_coeffs[i + stride * j]);
            E4::from_array_of_base(coeffs)
        })
        .collect_vec()
}

#[cfg(test)]
pub(crate) struct GpuScheduledBaseFieldQuery {
    pub(crate) index: usize,
    pub(crate) coset_index: usize,
    // Keeps index-fill callbacks alive until the stream executes them.
    #[allow(dead_code)]
    pub(crate) callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    pub(crate) leafs: HostAllocation<[BF]>,
    #[allow(dead_code)]
    pub(crate) merkle_paths: HostAllocation<[Digest]>,
    pub(crate) values_per_leaf: usize,
    pub(crate) columns_count: usize,
}

#[cfg(test)]
impl GpuScheduledBaseFieldQuery {
    pub(crate) fn decode(&self) -> (Vec<Vec<BF>>, BaseFieldQuery<BF, DefaultTreeConstructor>) {
        let leafs_accessor = self.leafs.get_accessor();
        let path_accessor = self.merkle_paths.get_accessor();
        let leafs = unsafe { leafs_accessor.get() };
        let path = unsafe { path_accessor.get().to_vec() };
        let decoded = decode_base_leaf_values(leafs, self.values_per_leaf, self.columns_count);
        let cpu_query = BaseFieldQuery {
            index: self.index,
            leaf_values_concatenated: decoded.iter().flatten().copied().collect(),
            path,
            _marker: PhantomData,
        };

        (decoded, cpu_query)
    }
}
