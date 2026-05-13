use super::super::*;

use era_cudart::memory::memory_copy_async;
use fft::bitreverse_enumeration_inplace;

use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::static_host::{
    alloc_static_pinned_box_from_slice, alloc_static_pinned_box_uninit,
};
use fft::batch_inverse_inplace;
use field::PrimeField;

use super::GpuScheduledBaseFieldQuery;

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

pub(crate) fn query_base_trace_holder_for_folded_index(
    trace_holder: &mut TraceHolder<BF>,
    index: usize,
    context: &ProverContext,
) -> CudaResult<(
    usize,
    Vec<Vec<BF>>,
    BaseFieldQuery<BF, DefaultTreeConstructor>,
)> {
    let scheduled =
        schedule_query_base_trace_holder_for_folded_index(trace_holder, index, context)?;
    context.get_exec_stream().synchronize()?;
    let (decoded, cpu_query) = scheduled.decode();
    Ok((scheduled.coset_index, decoded, cpu_query))
}

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

pub(super) fn special_lagrange_interpolate(
    eval_at_0: E4,
    eval_at_1: E4,
    eval_at_random: E4,
    random_point: E4,
) -> [E4; 3] {
    let mut coeffs_for_0 = [E4::ZERO, E4::ZERO, E4::ONE];
    coeffs_for_0[1] = E4::ONE;
    coeffs_for_0[1].add_assign(&random_point);
    coeffs_for_0[1].negate();
    coeffs_for_0[0] = random_point;

    let mut coeffs_for_1 = [E4::ZERO, E4::ZERO, E4::ONE];
    coeffs_for_1[1] = random_point;
    coeffs_for_1[1].negate();

    let mut coeffs_for_random = [E4::ZERO, E4::ZERO, E4::ONE];
    coeffs_for_random[1] = E4::ONE;
    coeffs_for_random[1].negate();

    let mut dens = [E4::ONE, E4::ONE, E4::ONE];
    let mut t = E4::ZERO;
    t.sub_assign(&E4::ONE);
    dens[0].mul_assign(&t);
    let mut t = E4::ZERO;
    t.sub_assign(&random_point);
    dens[0].mul_assign(&t);

    let mut t = E4::ONE;
    t.sub_assign(&random_point);
    dens[1].mul_assign(&t);

    let t = random_point;
    dens[2].mul_assign(&t);
    let mut t = random_point;
    t.sub_assign(&E4::ONE);
    dens[2].mul_assign(&t);

    let mut buffer = [E4::ZERO; 3];
    batch_inverse_inplace(&mut dens, &mut buffer);

    let mut result = [E4::ZERO; 3];
    for (eval, den, coeffs) in [
        (eval_at_0, dens[0], coeffs_for_0),
        (eval_at_1, dens[1], coeffs_for_1),
        (eval_at_random, dens[2], coeffs_for_random),
    ] {
        for (dst, coeff) in result.iter_mut().zip(coeffs.into_iter()) {
            let mut term = coeff;
            term.mul_assign(&den);
            term.mul_assign(&eval);
            dst.add_assign(&term);
        }
    }

    result
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

    assert!(memory_weights.len() > 0);
    assert!(witness_weights.len() > 0);
    assert!(setup_weights.len() > 0);

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
        |dst, values, context| copy_small_to_device(dst, values, context),
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

    initialize_batched_monomial_form(
        memory_trace_holder.log_domain_size as usize,
        use_hypercube_evals_for_batching,
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

    copy_small_to_device(
        &mut state.point_pows[..original_evaluation_point.len()],
        original_evaluation_point,
        context,
    )?;
    launch_build_eq_values_from_point(
        state.point_pows.as_ptr(),
        0,
        original_evaluation_point.len(),
        state.eq_group_tables.as_mut_ptr(),
        state.eq_poly.as_mut_ptr(),
        trace_len,
        context,
    )?;
    context.get_exec_stream().synchronize()?;

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
    reduce(
        ReduceOperation::Sum,
        &mut state.reduce_temp,
        &state.scratch0[..half],
        &mut state.reduce_out[0],
        stream,
    )?;

    {
        let (_, eval_high) =
            state.sumchecked_poly_evaluation_form[..state.current_len].split_at(half);
        let (_, eq_high) = state.eq_poly[..state.current_len].split_at(half);
        mul(eval_high, eq_high, &mut state.scratch0[..half], stream)?;
    }
    reduce(
        ReduceOperation::Sum,
        &mut state.reduce_temp,
        &state.scratch0[..half],
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
    reduce(
        ReduceOperation::Sum,
        &mut state.reduce_temp,
        &state.scratch0[..half],
        &mut state.reduce_out[2],
        stream,
    )?;

    let mut outputs = read_reduce_outputs(3, state, context)?;
    let quart = BF::from_u32_unchecked(4).inverse().unwrap();
    outputs[2].mul_assign_by_base(&quart);
    Ok((outputs[0], outputs[1], outputs[2]))
}

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

    schedule_monomial_eval_device_impl(state, &d_point, context)?;

    let result = read_reduce_outputs(1, state, context)?[0];

    Ok(result)
}

pub(crate) fn debug_build_initial_state_for_test(
    memory_trace_holder: &TraceHolder<BF>,
    mem_polys_claims: &[E4],
    witness_trace_holder: &TraceHolder<BF>,
    wit_polys_claims: &[E4],
    setup_trace_holder: &TraceHolder<BF>,
    setup_polys_claims: &[E4],
    original_evaluation_point: &[E4],
    batching_challenge: E4,
    use_hypercube_evals_for_batching: bool,
    context: &ProverContext,
) -> CudaResult<([Vec<E4>; 3], E4, Vec<E4>, Vec<E4>, Vec<E4>)> {
    fn copy_back<T: Clone>(values: &DeviceSlice<T>, context: &ProverContext) -> Vec<T> {
        let mut host = unsafe { context.alloc_host_uninit_slice(values.len()) };
        memory_copy_async(&mut host, values, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        unsafe { host.get_accessor().get().to_vec() }
    }

    let trace_len = 1usize << memory_trace_holder.log_domain_size;
    let mut state = GpuWhirState::new(trace_len, context)?;
    let (batch_challenges, claim) = build_initial_state(
        memory_trace_holder,
        mem_polys_claims,
        witness_trace_holder,
        wit_polys_claims,
        setup_trace_holder,
        setup_polys_claims,
        original_evaluation_point,
        batching_challenge,
        use_hypercube_evals_for_batching,
        &mut state,
        context,
    )?;

    let monomials_vectorized = copy_back(state.sumchecked_poly_monomial_form.slice(), context);
    let mut monomials = vectorized_to_e4_coeffs(
        &monomials_vectorized,
        state.original_trace_len,
        state.current_len,
    );
    bitreverse_enumeration_inplace(&mut monomials);

    Ok((
        batch_challenges,
        claim,
        monomials,
        copy_back(&state.sumchecked_poly_evaluation_form[..trace_len], context),
        copy_back(&state.eq_poly[..trace_len], context),
    ))
}

pub(crate) fn debug_build_initial_batched_evals_for_test(
    memory_trace_holder: &TraceHolder<BF>,
    mem_polys_claims: &[E4],
    witness_trace_holder: &TraceHolder<BF>,
    wit_polys_claims: &[E4],
    setup_trace_holder: &TraceHolder<BF>,
    setup_polys_claims: &[E4],
    batching_challenge: E4,
    use_hypercube_evals: bool,
    context: &ProverContext,
) -> CudaResult<Vec<E4>> {
    fn copy_back(values: &DeviceSlice<E4>, context: &ProverContext) -> Vec<E4> {
        let mut host = unsafe { context.alloc_host_uninit_slice(values.len()) };
        memory_copy_async(&mut host, values, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        unsafe { host.get_accessor().get().to_vec() }
    }

    let trace_len = 1usize << memory_trace_holder.log_domain_size;
    let mut state = GpuWhirState::new(trace_len, context)?;
    let total_base_oracles = memory_trace_holder.columns_count
        + witness_trace_holder.columns_count
        + setup_trace_holder.columns_count;
    let challenge_powers = materialize_powers_serial_starting_with_one::<E4, std::alloc::Global>(
        batching_challenge,
        total_base_oracles,
    );
    let (memory_weights, rest) = challenge_powers.split_at(mem_polys_claims.len());
    let (witness_weights, setup_weights) = rest.split_at(wit_polys_claims.len());
    debug_assert_eq!(setup_weights.len(), setup_polys_claims.len());

    let _weight_buffers = build_initial_batched_evals_device(
        memory_trace_holder,
        memory_weights,
        witness_trace_holder,
        witness_weights,
        setup_trace_holder,
        setup_weights,
        use_hypercube_evals,
        &mut state.sumchecked_poly_evaluation_form,
        context,
    )?;
    Ok(copy_back(
        &state.sumchecked_poly_evaluation_form[..trace_len],
        context,
    ))
}

pub(crate) fn debug_build_initial_state_snapshots_for_test(
    memory_trace_holder: &TraceHolder<BF>,
    mem_polys_claims: &[E4],
    witness_trace_holder: &TraceHolder<BF>,
    wit_polys_claims: &[E4],
    setup_trace_holder: &TraceHolder<BF>,
    setup_polys_claims: &[E4],
    original_evaluation_point: &[E4],
    batching_challenge: E4,
    use_hypercube_evals_for_batching: bool,
    context: &ProverContext,
) -> CudaResult<(Vec<E4>, Vec<E4>)> {
    fn copy_back(values: &DeviceSlice<E4>, context: &ProverContext) -> Vec<E4> {
        let mut host = unsafe { context.alloc_host_uninit_slice(values.len()) };
        memory_copy_async(&mut host, values, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        unsafe { host.get_accessor().get().to_vec() }
    }

    let trace_len = 1usize << memory_trace_holder.log_domain_size;
    let mut state = GpuWhirState::new(trace_len, context)?;
    let batch_challenges = initialize_batched_forms(
        memory_trace_holder,
        witness_trace_holder,
        setup_trace_holder,
        mem_polys_claims.len(),
        wit_polys_claims.len(),
        setup_polys_claims.len(),
        batching_challenge,
        use_hypercube_evals_for_batching,
        &mut state,
        context,
    )?;
    let pre_eq = copy_back(&state.sumchecked_poly_evaluation_form[..trace_len], context);

    copy_small_to_device(
        &mut state.point_pows[..original_evaluation_point.len()],
        original_evaluation_point,
        context,
    )?;
    launch_build_eq_values_from_point(
        state.point_pows.as_ptr(),
        0,
        original_evaluation_point.len(),
        state.eq_group_tables.as_mut_ptr(),
        state.eq_poly.as_mut_ptr(),
        trace_len,
        context,
    )?;
    context.get_exec_stream().synchronize()?;

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
    debug_assert!(!batched_claim.is_zero() || batched_claim == E4::ZERO);

    let post_eq = copy_back(&state.sumchecked_poly_evaluation_form[..trace_len], context);
    Ok((pre_eq, post_eq))
}

pub(crate) struct DebugInitialWhirRoundCheckpoint {
    pub(crate) sumcheck_polys: Vec<[E4; 3]>,
    pub(crate) folding_challenges: Vec<E4>,
    pub(crate) folded_monomial_form: Vec<E4>,
    pub(crate) recursive_cap: MerkleTreeCapVarLength,
    pub(crate) ood_point: E4,
    pub(crate) ood_value: E4,
    pub(crate) transcript_seed: Seed,
}

pub(crate) struct DebugWhirInitialFoldState {
    state: GpuWhirState,
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn debug_initial_round_checkpoint_for_test(
    memory_trace_holder: &TraceHolder<BF>,
    mem_polys_claims: &[E4],
    witness_trace_holder: &TraceHolder<BF>,
    wit_polys_claims: &[E4],
    setup_trace_holder: &TraceHolder<BF>,
    setup_polys_claims: &[E4],
    original_evaluation_point: &[E4],
    original_lde_factor: usize,
    batching_challenge: E4,
    num_initial_folding_rounds: usize,
    first_recursive_lde_factor: usize,
    next_folding_steps: usize,
    tree_cap_size: usize,
    use_hypercube_evals_for_batching: bool,
    transcript_seed: Seed,
    context: &ProverContext,
) -> CudaResult<DebugInitialWhirRoundCheckpoint> {
    let two_inv = BF::from_u32_unchecked(2).inverse().unwrap();
    let trace_len = 1usize << memory_trace_holder.log_domain_size;
    let mut state = GpuWhirState::new(trace_len, context)?;
    build_initial_state(
        memory_trace_holder,
        mem_polys_claims,
        witness_trace_holder,
        wit_polys_claims,
        setup_trace_holder,
        setup_polys_claims,
        original_evaluation_point,
        batching_challenge,
        use_hypercube_evals_for_batching,
        &mut state,
        context,
    )?;

    let mut transcript_seed = transcript_seed;
    let mut sumcheck_polys = Vec::with_capacity(num_initial_folding_rounds);
    let mut folding_challenges = Vec::with_capacity(num_initial_folding_rounds);
    for _ in 0..num_initial_folding_rounds {
        let (f0, f1, f_half) = special_three_point_eval_device(&mut state, context)?;
        let coeffs = special_lagrange_interpolate(f0, f1, f_half, E4::from_base(two_inv));
        sumcheck_polys.push(coeffs);
        commit_field_els::<BF, E4>(&mut transcript_seed, &coeffs);
        let folding_challenge = draw_random_field_els::<BF, E4>(&mut transcript_seed, 1)[0];
        folding_challenges.push(folding_challenge);
        fold_monomial_form_in_place_device(&mut state, folding_challenge, context)?;
        fold_evaluation_form_in_place_device(&mut state, folding_challenge, context)?;
        fold_eq_poly_in_place_device(&mut state, folding_challenge, context)?;
        state.current_len /= 2;
    }

    let mut folded_monomial_form_host = alloc_static_pinned_box_uninit(trace_len * EXT4_DEGREE)?;
    memory_copy_async(
        &mut folded_monomial_form_host,
        state.sumchecked_poly_monomial_form.slice(),
        context.get_exec_stream(),
    )?;
    context.get_exec_stream().synchronize()?;
    let folded_monomial_form_vectorized = folded_monomial_form_host.to_vec();
    let mut folded_monomial_form = vectorized_to_e4_coeffs(
        &folded_monomial_form_vectorized,
        state.original_trace_len,
        state.current_len,
    );
    bitreverse_enumeration_inplace(&mut folded_monomial_form);

    let oracle = GpuWhirExtensionOracle::from_device_monomial_coeffs(
        &state.sumchecked_poly_monomial_form,
        state.current_len,
        first_recursive_lde_factor,
        1 << next_folding_steps,
        tree_cap_size,
        context,
    )?;
    let recursive_cap = oracle.get_tree_cap(context)?;
    add_whir_commitment_to_transcript(
        &mut transcript_seed,
        &WhirCommitment::<BF, DefaultTreeConstructor> {
            cap: recursive_cap.clone(),
            _marker: PhantomData,
        },
    );

    let _rs_domain_log2 = trace_len.trailing_zeros() as usize
        + original_lde_factor.trailing_zeros() as usize
        - num_initial_folding_rounds;
    let ood_point = draw_random_field_els::<BF, E4>(&mut transcript_seed, 1)[0];
    let ood_value = evaluate_monomial_form_device(&mut state, ood_point, context)?;
    commit_field_els::<BF, E4>(&mut transcript_seed, &[ood_value]);

    Ok(DebugInitialWhirRoundCheckpoint {
        sumcheck_polys,
        folding_challenges,
        folded_monomial_form,
        recursive_cap,
        ood_point,
        ood_value,
        transcript_seed,
    })
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn debug_build_initial_fold_state_for_test(
    memory_trace_holder: &TraceHolder<BF>,
    mem_polys_claims: &[E4],
    witness_trace_holder: &TraceHolder<BF>,
    wit_polys_claims: &[E4],
    setup_trace_holder: &TraceHolder<BF>,
    setup_polys_claims: &[E4],
    original_evaluation_point: &[E4],
    batching_challenge: E4,
    use_hypercube_evals_for_batching: bool,
    context: &ProverContext,
) -> CudaResult<DebugWhirInitialFoldState> {
    let trace_len = 1usize << memory_trace_holder.log_domain_size;
    let mut state = GpuWhirState::new(trace_len, context)?;
    build_initial_state(
        memory_trace_holder,
        mem_polys_claims,
        witness_trace_holder,
        wit_polys_claims,
        setup_trace_holder,
        setup_polys_claims,
        original_evaluation_point,
        batching_challenge,
        use_hypercube_evals_for_batching,
        &mut state,
        context,
    )?;
    Ok(DebugWhirInitialFoldState { state })
}

pub(crate) fn debug_apply_initial_fold_challenge_for_test(
    debug_state: &mut DebugWhirInitialFoldState,
    challenge: E4,
    context: &ProverContext,
) -> CudaResult<Vec<E4>> {
    fold_monomial_form_in_place_device(&mut debug_state.state, challenge, context)?;
    fold_evaluation_form_in_place_device(&mut debug_state.state, challenge, context)?;
    fold_eq_poly_in_place_device(&mut debug_state.state, challenge, context)?;
    debug_state.state.current_len /= 2;

    let mut host =
        alloc_static_pinned_box_uninit(debug_state.state.original_trace_len * EXT4_DEGREE)?;
    memory_copy_async(
        &mut host,
        debug_state.state.sumchecked_poly_monomial_form.slice(),
        context.get_exec_stream(),
    )?;
    context.get_exec_stream().synchronize()?;
    let monomials_vectorized = host.to_vec();
    let mut monomials = vectorized_to_e4_coeffs(
        &monomials_vectorized,
        debug_state.state.original_trace_len,
        debug_state.state.current_len,
    );
    bitreverse_enumeration_inplace(&mut monomials);
    Ok(monomials)
}

pub(super) fn vectorized_to_e4_coeffs(
    vectorized_coeffs: &[BF],
    stride: usize,
    count: usize,
) -> Vec<E4> {
    use itertools::Itertools;
    let coeffs = (0..count)
        .map(|i| {
            let coeffs = std::array::from_fn(|j| vectorized_coeffs[i + stride * j]);
            E4::from_array_of_base(coeffs)
        })
        .collect_vec();
    coeffs
}
