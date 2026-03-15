use core::marker::PhantomData;

use era_cudart::memory::{memory_copy, memory_copy_async};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use fft::{
    batch_inverse_inplace, bitreverse_enumeration_inplace, domain_generator_for_size,
    materialize_powers_serial_starting_with_one,
};
use field::{Field, FieldExtension, PrimeField};
use prover::gkr::prover::transcript_utils::{
    add_whir_commitment_to_transcript, commit_field_els, draw_query_bits, draw_random_field_els,
};
use prover::gkr::sumcheck::evaluate_small_univariate_poly;
use prover::gkr::whir::{
    BaseFieldQuery, ExtensionFieldQuery, WhirBaseLayerCommitmentAndQueries, WhirCommitment,
    WhirIntermediateCommitmentAndQueries, WhirPolyCommitProof,
};
use prover::merkle_trees::{DefaultTreeConstructor, MerkleTreeCapVarLength};
use prover::prover_stages::query_producer::assemble_query_index;
use prover::transcript::Seed;
use worker::Worker;

use crate::allocator::tracker::AllocationPlacement;
use crate::ntt::{hypercube_coeffs_natural_to_natural_evals, natural_evals_to_bitreversed_coeffs};
use crate::ops::complex::{
    accumulate_whir_base_columns, bit_reverse, bit_reverse_in_place, deserialize_whir_e4_columns,
    get_powers_by_val, serialize_whir_e4_columns, whir_fold_monomial,
    whir_fold_split_half_in_place,
};
use crate::ops::cub::device_reduce::{get_reduce_temp_storage_bytes, reduce, ReduceOperation};
use crate::ops::simple::{add, add_into_y, mul, mul_into_x, set_to_zero};
use crate::primitives::context::{DeviceAllocation, HostAllocation, ProverContext};
use crate::primitives::device_structures::{DeviceMatrix, DeviceMatrixMut};
use crate::primitives::field::{BF, E4};
use crate::prover::gkr::backward::launch_build_eq_values;
use crate::prover::trace_holder::TraceHolder;
use crate::prover::whir::{GpuWhirExtensionOracle, GpuWhirExtensionQuery};

const EXT4_DEGREE: usize = <E4 as FieldExtension<BF>>::DEGREE;

struct GpuWhirState {
    sumchecked_poly_monomial_form: DeviceAllocation<E4>,
    monomial_buffer: DeviceAllocation<E4>,
    sumchecked_poly_evaluation_form: DeviceAllocation<E4>,
    eq_poly: DeviceAllocation<E4>,
    scratch0: DeviceAllocation<E4>,
    scratch1: DeviceAllocation<E4>,
    point_pows: DeviceAllocation<E4>,
    scalar: DeviceAllocation<E4>,
    reduce_temp: DeviceAllocation<u8>,
    reduce_out: DeviceAllocation<E4>,
    current_len: usize,
}

impl GpuWhirState {
    fn new(trace_len: usize, context: &ProverContext) -> CudaResult<Self> {
        assert!(trace_len.is_power_of_two());
        assert!(trace_len >= 2);
        let half_len = trace_len / 2;
        let reduce_temp_bytes =
            get_reduce_temp_storage_bytes::<E4>(ReduceOperation::Sum, half_len as i32)?;
        Ok(Self {
            sumchecked_poly_monomial_form: context
                .alloc(trace_len, AllocationPlacement::BestFit)?,
            monomial_buffer: context.alloc(half_len, AllocationPlacement::BestFit)?,
            sumchecked_poly_evaluation_form: context
                .alloc(trace_len, AllocationPlacement::BestFit)?,
            eq_poly: context.alloc(trace_len, AllocationPlacement::BestFit)?,
            scratch0: context.alloc(half_len, AllocationPlacement::BestFit)?,
            scratch1: context.alloc(half_len, AllocationPlacement::BestFit)?,
            point_pows: context.alloc(
                trace_len.trailing_zeros() as usize,
                AllocationPlacement::BestFit,
            )?,
            scalar: context.alloc(1, AllocationPlacement::BestFit)?,
            reduce_temp: context.alloc(reduce_temp_bytes, AllocationPlacement::BestFit)?,
            reduce_out: context.alloc(3, AllocationPlacement::BestFit)?,
            current_len: trace_len,
        })
    }
}

fn alloc_transient_host_and_copy<T: Copy>(
    context: &ProverContext,
    values: &[T],
) -> HostAllocation<[T]> {
    let mut allocation = unsafe { context.alloc_transient_host_uninit_slice(values.len()) };
    unsafe {
        allocation
            .get_mut_accessor()
            .get_mut()
            .copy_from_slice(values);
    }
    allocation
}

fn copy_small_to_device<T: Copy>(
    dst: &mut DeviceSlice<T>,
    values: &[T],
    _context: &ProverContext,
) -> CudaResult<()> {
    assert_eq!(dst.len(), values.len());
    memory_copy(dst, values)
}

fn copy_scalar_to_device(
    value: E4,
    state: &mut GpuWhirState,
    context: &ProverContext,
) -> CudaResult<()> {
    copy_small_to_device(&mut state.scalar, &[value], context)
}

fn read_reduce_outputs(
    count: usize,
    state: &mut GpuWhirState,
    context: &ProverContext,
) -> CudaResult<Vec<E4>> {
    let stream = context.get_exec_stream();
    let mut host = unsafe { context.alloc_transient_host_uninit_slice(count) };
    memory_copy_async(&mut host, &state.reduce_out[..count], stream)?;
    stream.synchronize()?;
    Ok(unsafe { host.get_accessor().get().to_vec() })
}

fn full_cap_from_trace_holder(trace_holder: &TraceHolder<BF>) -> MerkleTreeCapVarLength {
    MerkleTreeCapVarLength {
        cap: trace_holder
            .get_tree_caps()
            .into_iter()
            .flat_map(|subcap| subcap.cap)
            .collect(),
    }
}

fn decode_base_leaf_values(
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

fn bitreverse_index(index: usize, num_bits: u32) -> usize {
    index.reverse_bits() >> (usize::BITS - num_bits)
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
    let lde_factor = 1usize << trace_holder.log_lde_factor;
    let values_per_leaf = 1usize << trace_holder.log_rows_per_leaf;
    let coset_tree_size = (1usize << trace_holder.log_domain_size) / values_per_leaf;
    assert!(values_per_leaf.is_power_of_two());
    assert!(index < (1usize << trace_holder.log_domain_size) * lde_factor / values_per_leaf);
    let value_coset_index = index & (lde_factor - 1);
    let value_internal_index = index / lde_factor;
    let host_value_index = alloc_transient_host_and_copy(context, &[value_internal_index as u32]);
    let mut device_value_index = context.alloc(1, AllocationPlacement::BestFit)?;
    memory_copy_async(
        &mut device_value_index,
        &host_value_index,
        context.get_exec_stream(),
    )?;
    let value_query =
        trace_holder.get_leafs_and_merkle_paths(value_coset_index, &device_value_index, context)?;

    let stage1_coset_index = index / coset_tree_size;
    let path_coset_index = bitreverse_index(stage1_coset_index, trace_holder.log_lde_factor);
    let path_internal_index = index % coset_tree_size;
    let host_path_index = alloc_transient_host_and_copy(context, &[path_internal_index as u32]);
    let mut device_path_index = context.alloc(1, AllocationPlacement::BestFit)?;
    memory_copy_async(
        &mut device_path_index,
        &host_path_index,
        context.get_exec_stream(),
    )?;
    let path_query =
        trace_holder.get_leafs_and_merkle_paths(path_coset_index, &device_path_index, context)?;
    context.get_exec_stream().synchronize()?;
    let leafs = unsafe { value_query.leafs.get_accessor().get().to_vec() };
    let path = unsafe { path_query.merkle_paths.get_accessor().get().to_vec() };
    let decoded = decode_base_leaf_values(&leafs, values_per_leaf, trace_holder.columns_count);
    let cpu_query = BaseFieldQuery {
        index,
        leaf_values_concatenated: decoded.iter().flatten().copied().collect(),
        path,
        _marker: PhantomData,
    };
    Ok((value_coset_index, decoded, cpu_query))
}

fn into_extension_query(
    query: GpuWhirExtensionQuery,
) -> ExtensionFieldQuery<BF, E4, DefaultTreeConstructor> {
    ExtensionFieldQuery {
        index: query.index,
        leaf_values_concatenated: query.leaf_values_concatenated,
        path: query.path,
        _marker: PhantomData,
    }
}

fn make_pows(mut point: E4, count: usize) -> Vec<E4> {
    let mut result = Vec::with_capacity(count);
    for _ in 0..count {
        result.push(point);
        point.square();
    }
    result
}

fn special_lagrange_interpolate(
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

    let mut t = random_point;
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

fn fold_coset(
    mut flattened_evals: Vec<E4>,
    num_folding_rounds: usize,
    folding_challenges: &[E4],
    base_root_inv: &BF,
    high_powers_offsets: &[BF],
    two_inv: &BF,
) -> E4 {
    let mut root_inv = *base_root_inv;
    let mut buffer = Vec::with_capacity(flattened_evals.len());
    for folding_step in 0..num_folding_rounds {
        let (src, dst) = if folding_step % 2 == 0 {
            (&flattened_evals[..], &mut buffer)
        } else {
            (&buffer[..], &mut flattened_evals)
        };
        dst.clear();
        for (set_idx, [a, b]) in src.as_chunks::<2>().0.iter().enumerate() {
            let mut t = *a;
            t.sub_assign(b);
            t.mul_assign(&folding_challenges[folding_step]);
            let mut root = root_inv;
            root.mul_assign(&high_powers_offsets[set_idx]);
            t.mul_assign_by_base(&root);
            t.add_assign(a);
            t.add_assign(b);
            t.mul_assign_by_base(two_inv);
            dst.push(t);
        }
        root_inv.square();
    }
    if num_folding_rounds % 2 == 1 {
        buffer[0]
    } else {
        flattened_evals[0]
    }
}

fn build_initial_batched_main_domain_poly_device(
    memory_trace_holder: &TraceHolder<BF>,
    memory_weights: &[E4],
    witness_trace_holder: &TraceHolder<BF>,
    witness_weights: &[E4],
    setup_trace_holder: &TraceHolder<BF>,
    setup_weights: &[E4],
    result: &mut DeviceSlice<E4>,
    context: &ProverContext,
) -> CudaResult<Vec<DeviceAllocation<E4>>> {
    let stream = context.get_exec_stream();
    set_to_zero(result, stream)?;
    let mut weight_buffers = Vec::with_capacity(3);

    for (trace_holder, weights) in [
        (memory_trace_holder, memory_weights),
        (witness_trace_holder, witness_weights),
        (setup_trace_holder, setup_weights),
    ] {
        if weights.is_empty() {
            continue;
        }
        assert!(
            trace_holder.are_cosets_materialized(),
            "WHIR initial state requires materialized main-domain cosets",
        );
        let mut device_weights = context.alloc(weights.len(), AllocationPlacement::BestFit)?;
        copy_small_to_device(&mut device_weights, weights, context)?;
        let values = DeviceMatrix::new(trace_holder.get_evaluations(), result.len());
        accumulate_whir_base_columns(&values, &device_weights, result, stream)?;
        weight_buffers.push(device_weights);
    }

    Ok(weight_buffers)
}

fn initialize_batched_forms(
    memory_trace_holder: &TraceHolder<BF>,
    witness_trace_holder: &TraceHolder<BF>,
    setup_trace_holder: &TraceHolder<BF>,
    mem_polys_claims_len: usize,
    wit_polys_claims_len: usize,
    setup_polys_claims_len: usize,
    batching_challenge: E4,
    state: &mut GpuWhirState,
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
    let mut challenge_powers = materialize_powers_serial_starting_with_one::<E4, std::alloc::Global>(
        batching_challenge,
        total_base_oracles,
    );
    challenge_powers[1..].fill(E4::ZERO);
    let (memory_weights, rest) = challenge_powers.split_at(mem_polys_claims_len);
    let (witness_weights, setup_weights) = rest.split_at(wit_polys_claims_len);
    debug_assert_eq!(setup_weights.len(), setup_polys_claims_len);

    let _weight_buffers = build_initial_batched_main_domain_poly_device(
        memory_trace_holder,
        memory_weights,
        witness_trace_holder,
        witness_weights,
        setup_trace_holder,
        setup_weights,
        &mut state.sumchecked_poly_evaluation_form,
        context,
    )?;

    let mut serialized = context.alloc(trace_len * EXT4_DEGREE, AllocationPlacement::BestFit)?;
    let mut bf_scratch = context.alloc(trace_len, AllocationPlacement::BestFit)?;
    let stream = context.get_exec_stream();
    serialize_whir_e4_columns(
        &state.sumchecked_poly_evaluation_form[..trace_len],
        &mut serialized,
        stream,
    )?;
    for column in 0..EXT4_DEGREE {
        let src = &serialized[column * trace_len..(column + 1) * trace_len];
        natural_evals_to_bitreversed_coeffs(
            src,
            &mut bf_scratch,
            trace_len.trailing_zeros() as usize,
            stream,
        )?;
        let dst = &mut serialized[column * trace_len..(column + 1) * trace_len];
        memory_copy_async(dst, &bf_scratch, stream)?;
    }
    {
        let mut coeffs_matrix = DeviceMatrixMut::new(&mut serialized, trace_len);
        bit_reverse_in_place(&mut coeffs_matrix, stream)?;
    }
    deserialize_whir_e4_columns(
        &serialized,
        &mut state.sumchecked_poly_monomial_form[..trace_len],
        stream,
    )?;
    for column in 0..EXT4_DEGREE {
        let src = &serialized[column * trace_len..(column + 1) * trace_len];
        hypercube_coeffs_natural_to_natural_evals(
            src,
            &mut bf_scratch,
            trace_len.trailing_zeros() as usize,
            stream,
        )?;
        let dst = &mut serialized[column * trace_len..(column + 1) * trace_len];
        memory_copy_async(dst, &bf_scratch, stream)?;
    }
    {
        let mut evals_matrix = DeviceMatrixMut::new(&mut serialized, trace_len);
        bit_reverse_in_place(&mut evals_matrix, stream)?;
    }
    deserialize_whir_e4_columns(
        &serialized,
        &mut state.sumchecked_poly_evaluation_form[..trace_len],
        stream,
    )?;
    stream.synchronize()?;

    Ok([
        memory_weights.to_vec(),
        witness_weights.to_vec(),
        setup_weights.to_vec(),
    ])
}

fn build_initial_state(
    memory_trace_holder: &TraceHolder<BF>,
    mem_polys_claims: &[E4],
    witness_trace_holder: &TraceHolder<BF>,
    wit_polys_claims: &[E4],
    setup_trace_holder: &TraceHolder<BF>,
    setup_polys_claims: &[E4],
    original_evaluation_point: &[E4],
    batching_challenge: E4,
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
        state,
        context,
    )?;

    copy_small_to_device(
        &mut state.point_pows[..original_evaluation_point.len()],
        original_evaluation_point,
        context,
    )?;
    launch_build_eq_values(
        state.point_pows.as_ptr(),
        0,
        original_evaluation_point.len(),
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

fn special_three_point_eval_device(
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

fn fold_monomial_form_in_place_device(
    state: &mut GpuWhirState,
    challenge: E4,
    context: &ProverContext,
) -> CudaResult<()> {
    copy_scalar_to_device(challenge, state, context)?;
    let half = state.current_len / 2;
    whir_fold_monomial(
        &state.sumchecked_poly_monomial_form[..state.current_len],
        &state.scalar[0],
        &mut state.monomial_buffer[..half],
        context.get_exec_stream(),
    )?;
    core::mem::swap(
        &mut state.sumchecked_poly_monomial_form,
        &mut state.monomial_buffer,
    );
    Ok(())
}

fn fold_evaluation_form_in_place_device(
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

fn fold_eq_poly_in_place_device(
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

fn evaluate_monomial_form_device(
    state: &mut GpuWhirState,
    point: E4,
    context: &ProverContext,
) -> CudaResult<E4> {
    let stream = context.get_exec_stream();
    let chunk_size = state.scratch0.len().min(state.current_len);
    let mut result = E4::ZERO;

    for chunk_start in (0..state.current_len).step_by(chunk_size) {
        let chunk_len = chunk_size.min(state.current_len - chunk_start);
        let coeffs = &state.sumchecked_poly_monomial_form[chunk_start..chunk_start + chunk_len];
        let powers = &mut state.scratch0[..chunk_len];
        let products = &mut state.scratch1[..chunk_len];
        get_powers_by_val(point, chunk_start as u32, false, powers, stream)?;
        mul(coeffs, powers, products, stream)?;
        reduce(
            ReduceOperation::Sum,
            &mut state.reduce_temp,
            &state.scratch1[..chunk_len],
            &mut state.reduce_out[0],
            stream,
        )?;
        let partial = read_reduce_outputs(1, state, context)?[0];
        result.add_assign(&partial);
    }

    Ok(result)
}

fn accumulate_eq_sample_in_place_device(
    state: &mut GpuWhirState,
    point: E4,
    challenge: E4,
    context: &ProverContext,
) -> CudaResult<()> {
    let log_n = state.current_len.trailing_zeros() as usize;
    assert!(state.current_len <= state.scratch0.len());
    let pows = make_pows(point, log_n);
    copy_small_to_device(&mut state.point_pows[..log_n], &pows, context)?;
    launch_build_eq_values(
        state.point_pows.as_ptr(),
        0,
        log_n,
        state.scratch0.as_mut_ptr(),
        state.current_len,
        context,
    )?;
    copy_scalar_to_device(challenge, state, context)?;
    mul_into_x(
        &mut state.scratch0[..state.current_len],
        &state.scalar[0],
        context.get_exec_stream(),
    )?;
    add_into_y(
        &state.scratch0[..state.current_len],
        &mut state.eq_poly[..state.current_len],
        context.get_exec_stream(),
    )
}

pub(crate) fn gpu_whir_fold_supported_path(
    memory_trace_holder: &mut TraceHolder<BF>,
    mem_polys_claims: Vec<E4>,
    witness_trace_holder: &mut TraceHolder<BF>,
    wit_polys_claims: Vec<E4>,
    setup_trace_holder: &mut TraceHolder<BF>,
    setup_polys_claims: Vec<E4>,
    original_evaluation_point: Vec<E4>,
    original_lde_factor: usize,
    batching_challenge: E4,
    whir_steps_schedule: Vec<usize>,
    whir_queries_schedule: Vec<usize>,
    whir_steps_lde_factors: Vec<usize>,
    whir_pow_schedule: Vec<u32>,
    mut transcript_seed: Seed,
    tree_cap_size: usize,
    trace_len_log2: usize,
    worker: &Worker,
    context: &ProverContext,
) -> CudaResult<WhirPolyCommitProof<BF, E4, DefaultTreeConstructor>> {
    let trace_len = 1usize << trace_len_log2;
    assert_eq!(memory_trace_holder.log_domain_size as usize, trace_len_log2);
    assert_eq!(
        witness_trace_holder.log_domain_size as usize,
        trace_len_log2
    );
    assert_eq!(setup_trace_holder.log_domain_size as usize, trace_len_log2);
    assert_eq!(
        1usize << memory_trace_holder.log_lde_factor,
        original_lde_factor
    );
    assert_eq!(
        1usize << memory_trace_holder.log_rows_per_leaf,
        1usize << whir_steps_schedule[0]
    );
    assert_eq!(
        1usize << witness_trace_holder.log_rows_per_leaf,
        1usize << whir_steps_schedule[0]
    );
    assert_eq!(
        1usize << setup_trace_holder.log_rows_per_leaf,
        1usize << whir_steps_schedule[0]
    );

    memory_trace_holder.ensure_cosets_materialized(context)?;
    witness_trace_holder.ensure_cosets_materialized(context)?;
    setup_trace_holder.ensure_cosets_materialized(context)?;

    let mut proof = WhirPolyCommitProof {
        witness_commitment: WhirBaseLayerCommitmentAndQueries {
            commitment: WhirCommitment {
                cap: full_cap_from_trace_holder(witness_trace_holder),
                _marker: PhantomData,
            },
            num_columns: witness_trace_holder.columns_count,
            evals: wit_polys_claims.clone(),
            queries: vec![],
        },
        memory_commitment: WhirBaseLayerCommitmentAndQueries {
            commitment: WhirCommitment {
                cap: full_cap_from_trace_holder(memory_trace_holder),
                _marker: PhantomData,
            },
            num_columns: memory_trace_holder.columns_count,
            evals: mem_polys_claims.clone(),
            queries: vec![],
        },
        setup_commitment: WhirBaseLayerCommitmentAndQueries {
            commitment: WhirCommitment {
                cap: full_cap_from_trace_holder(setup_trace_holder),
                _marker: PhantomData,
            },
            num_columns: setup_trace_holder.columns_count,
            evals: setup_polys_claims.clone(),
            queries: vec![],
        },
        sumcheck_polys: vec![],
        intermediate_whir_oracles: Vec::with_capacity(whir_steps_lde_factors.len()),
        ood_samples: vec![],
        pow_nonces: vec![],
        final_monomials: vec![],
    };

    let mut state = GpuWhirState::new(trace_len, context)?;
    let (batch_challenges, mut claim) = build_initial_state(
        memory_trace_holder,
        &mem_polys_claims,
        witness_trace_holder,
        &wit_polys_claims,
        setup_trace_holder,
        &setup_polys_claims,
        &original_evaluation_point,
        batching_challenge,
        &mut state,
        context,
    )?;

    let mut whir_steps_schedule = whir_steps_schedule.into_iter().peekable();
    let mut whir_queries_schedule = whir_queries_schedule.into_iter();
    let mut whir_steps_lde_factors = whir_steps_lde_factors.into_iter();
    let mut whir_pow_schedule = whir_pow_schedule.into_iter();
    let two_inv = BF::from_u32_unchecked(2).inverse().unwrap();
    let num_whir_steps = proof.intermediate_whir_oracles.capacity();
    let mut rs_oracle;

    {
        let num_initial_folding_rounds = whir_steps_schedule.next().unwrap();
        let num_queries = whir_queries_schedule.next().unwrap();
        let pow_bits = whir_pow_schedule.next().unwrap();
        let rs_domain_log2 = trace_len_log2 + (original_lde_factor.trailing_zeros() as usize);
        let query_domain_log2 = rs_domain_log2 - num_initial_folding_rounds;
        let mut folding_challenges_in_round = Vec::with_capacity(num_initial_folding_rounds);

        for _ in 0..num_initial_folding_rounds {
            let (f0, f1, f_half) = special_three_point_eval_device(&mut state, context)?;
            let coeffs = special_lagrange_interpolate(f0, f1, f_half, E4::from_base(two_inv));
            proof.sumcheck_polys.push(coeffs);
            commit_field_els::<BF, E4>(&mut transcript_seed, &coeffs);
            let folding_challenge = draw_random_field_els::<BF, E4>(&mut transcript_seed, 1)[0];
            folding_challenges_in_round.push(folding_challenge);
            claim = evaluate_small_univariate_poly::<BF, E4, 3>(&coeffs, &folding_challenge);
            fold_monomial_form_in_place_device(&mut state, folding_challenge, context)?;
            fold_evaluation_form_in_place_device(&mut state, folding_challenge, context)?;
            fold_eq_poly_in_place_device(&mut state, folding_challenge, context)?;
            state.current_len /= 2;
        }

        let lde_factor = whir_steps_lde_factors.next().unwrap();
        let next_folding_steps = *whir_steps_schedule.peek().unwrap();
        rs_oracle = GpuWhirExtensionOracle::from_device_monomial_coeffs(
            &state.sumchecked_poly_monomial_form[..state.current_len],
            lde_factor,
            1 << next_folding_steps,
            tree_cap_size,
            context,
        )?;
        let commitment = WhirIntermediateCommitmentAndQueries {
            commitment: WhirCommitment {
                cap: rs_oracle.get_tree_cap(),
                _marker: PhantomData,
            },
            queries: vec![],
        };
        add_whir_commitment_to_transcript(&mut transcript_seed, &commitment.commitment);
        proof.intermediate_whir_oracles.push(commitment);

        let ood_point = draw_random_field_els::<BF, E4>(&mut transcript_seed, 1)[0];
        let ood_value = evaluate_monomial_form_device(&mut state, ood_point, context)?;
        commit_field_els::<BF, E4>(&mut transcript_seed, &[ood_value]);
        proof.ood_samples.push(ood_value);

        let query_domain_size = 1u64 << query_domain_log2;
        let query_domain_generator = domain_generator_for_size::<BF>(query_domain_size);
        let extended_generator = domain_generator_for_size::<BF>(1u64 << rs_domain_log2);
        let mut high_powers_offsets =
            materialize_powers_serial_starting_with_one::<BF, std::alloc::Global>(
                domain_generator_for_size::<BF>(1u64 << num_initial_folding_rounds)
                    .inverse()
                    .unwrap(),
                1 << (num_initial_folding_rounds - 1),
            );
        bitreverse_enumeration_inplace(&mut high_powers_offsets);
        let query_index_bits = query_domain_size.trailing_zeros() as usize;
        let (nonce, mut bit_source) = draw_query_bits(
            &mut transcript_seed,
            num_queries * query_index_bits,
            pow_bits,
            worker,
        );
        proof.pow_nonces.push(nonce);
        let delinearization_challenge = draw_random_field_els::<BF, E4>(&mut transcript_seed, 1)[0];
        let mut claim_correction = {
            let mut t = ood_value;
            t.mul_assign(&delinearization_challenge);
            t
        };
        accumulate_eq_sample_in_place_device(
            &mut state,
            ood_point,
            delinearization_challenge,
            context,
        )?;

        for _ in 0..num_queries {
            let query_index = assemble_query_index(query_index_bits, &mut bit_source);
            let query_point = query_domain_generator.pow(query_index as u32);
            let base_root = extended_generator.pow(query_index as u32);
            let base_root_inv = base_root.inverse().unwrap();
            let mut batched_evals = vec![E4::ZERO; 1 << num_initial_folding_rounds];

            for (leaf_values, weights) in [
                {
                    let (_, leaf_values, query) = query_base_trace_holder_for_folded_index(
                        memory_trace_holder,
                        query_index,
                        context,
                    )?;
                    proof.memory_commitment.queries.push(query);
                    (leaf_values, &batch_challenges[0])
                },
                {
                    let (_, leaf_values, query) = query_base_trace_holder_for_folded_index(
                        witness_trace_holder,
                        query_index,
                        context,
                    )?;
                    proof.witness_commitment.queries.push(query);
                    (leaf_values, &batch_challenges[1])
                },
                {
                    let (_, leaf_values, query) = query_base_trace_holder_for_folded_index(
                        setup_trace_holder,
                        query_index,
                        context,
                    )?;
                    proof.setup_commitment.queries.push(query);
                    (leaf_values, &batch_challenges[2])
                },
            ] {
                for (dst, src) in batched_evals.iter_mut().zip(leaf_values.iter()) {
                    for (value, weight) in src.iter().zip(weights.iter()) {
                        let mut term = *weight;
                        term.mul_assign_by_base(value);
                        dst.add_assign(&term);
                    }
                }
            }

            let folded = fold_coset(
                batched_evals,
                num_initial_folding_rounds,
                &folding_challenges_in_round,
                &base_root_inv,
                &high_powers_offsets,
                &two_inv,
            );
            let mut t = folded;
            t.mul_assign(&delinearization_challenge);
            claim_correction.add_assign(&t);
            accumulate_eq_sample_in_place_device(
                &mut state,
                E4::from_base(query_point),
                delinearization_challenge,
                context,
            )?;
        }
        claim.add_assign(&claim_correction);
    }

    let num_internal_whir_steps = num_whir_steps - 1;
    for _ in 0..num_internal_whir_steps {
        let num_folding_steps = whir_steps_schedule.next().unwrap();
        let num_queries = whir_queries_schedule.next().unwrap();
        let pow_bits = whir_pow_schedule.next().unwrap();
        let rs_domain_log2 = state.current_len.trailing_zeros() as usize
            + rs_oracle.lde_factor().trailing_zeros() as usize;
        let query_domain_log2 = rs_domain_log2 - num_folding_steps;
        let mut folding_challenges_in_round = Vec::with_capacity(num_folding_steps);

        for _ in 0..num_folding_steps {
            let (f0, f1, f_half) = special_three_point_eval_device(&mut state, context)?;
            let coeffs = special_lagrange_interpolate(f0, f1, f_half, E4::from_base(two_inv));
            proof.sumcheck_polys.push(coeffs);
            commit_field_els::<BF, E4>(&mut transcript_seed, &coeffs);
            let folding_challenge = draw_random_field_els::<BF, E4>(&mut transcript_seed, 1)[0];
            folding_challenges_in_round.push(folding_challenge);
            claim = evaluate_small_univariate_poly::<BF, E4, 3>(&coeffs, &folding_challenge);
            fold_monomial_form_in_place_device(&mut state, folding_challenge, context)?;
            fold_evaluation_form_in_place_device(&mut state, folding_challenge, context)?;
            fold_eq_poly_in_place_device(&mut state, folding_challenge, context)?;
            state.current_len /= 2;
        }

        let lde_factor = whir_steps_lde_factors.next().unwrap();
        let next_folding_steps = *whir_steps_schedule.peek().unwrap();
        let next_oracle = GpuWhirExtensionOracle::from_device_monomial_coeffs(
            &state.sumchecked_poly_monomial_form[..state.current_len],
            lde_factor,
            1 << next_folding_steps,
            tree_cap_size,
            context,
        )?;
        proof
            .intermediate_whir_oracles
            .push(WhirIntermediateCommitmentAndQueries {
                commitment: WhirCommitment {
                    cap: next_oracle.get_tree_cap(),
                    _marker: PhantomData,
                },
                queries: vec![],
            });
        let mut rs_oracle_to_query = rs_oracle;
        rs_oracle = next_oracle;

        let ood_point = E4::from_base(BF::from_u32_unchecked(42));
        let ood_value = evaluate_monomial_form_device(&mut state, ood_point, context)?;
        proof.ood_samples.push(ood_value);

        let query_domain_size = 1u64 << query_domain_log2;
        let query_domain_generator = domain_generator_for_size::<BF>(query_domain_size);
        let extended_generator = domain_generator_for_size::<BF>(1u64 << rs_domain_log2);
        let mut high_powers_offsets =
            materialize_powers_serial_starting_with_one::<BF, std::alloc::Global>(
                domain_generator_for_size::<BF>(1u64 << num_folding_steps)
                    .inverse()
                    .unwrap(),
                1 << (num_folding_steps - 1),
            );
        bitreverse_enumeration_inplace(&mut high_powers_offsets);
        let query_index_bits = query_domain_size.trailing_zeros() as usize;
        let (nonce, mut bit_source) = draw_query_bits(
            &mut transcript_seed,
            num_queries * query_index_bits,
            pow_bits,
            worker,
        );
        proof.pow_nonces.push(nonce);
        let delinearization_challenge = draw_random_field_els::<BF, E4>(&mut transcript_seed, 1)[0];
        let mut claim_correction = {
            let mut t = ood_value;
            t.mul_assign(&delinearization_challenge);
            t
        };
        accumulate_eq_sample_in_place_device(
            &mut state,
            ood_point,
            delinearization_challenge,
            context,
        )?;

        for _ in 0..num_queries {
            let query_index = assemble_query_index(query_index_bits, &mut bit_source);
            let query_point = query_domain_generator.pow(query_index as u32);
            let base_root = extended_generator.pow(query_index as u32);
            let base_root_inv = base_root.inverse().unwrap();
            let (_, evals, query) =
                rs_oracle_to_query.query_for_folded_index(query_index, context)?;
            let intermediate_oracle_idx = proof.intermediate_whir_oracles.len() - 2;
            let intermediate_oracle = &mut proof.intermediate_whir_oracles[intermediate_oracle_idx];
            intermediate_oracle
                .queries
                .push(into_extension_query(query));
            let folded = fold_coset(
                evals,
                num_folding_steps,
                &folding_challenges_in_round,
                &base_root_inv,
                &high_powers_offsets,
                &two_inv,
            );
            let mut t = folded;
            t.mul_assign(&delinearization_challenge);
            claim_correction.add_assign(&t);
            accumulate_eq_sample_in_place_device(
                &mut state,
                E4::from_base(query_point),
                delinearization_challenge,
                context,
            )?;
        }

        claim.add_assign(&claim_correction);
    }

    {
        let num_folding_steps = whir_steps_schedule.next().unwrap();
        let num_queries = whir_queries_schedule.next().unwrap();
        let pow_bits = whir_pow_schedule.next().unwrap();
        let rs_domain_log2 = state.current_len.trailing_zeros() as usize
            + rs_oracle.lde_factor().trailing_zeros() as usize;
        let query_domain_log2 = rs_domain_log2 - num_folding_steps;
        let mut folding_challenges_in_round = Vec::with_capacity(num_folding_steps);

        for _ in 0..num_folding_steps {
            let (f0, f1, f_half) = special_three_point_eval_device(&mut state, context)?;
            let coeffs = special_lagrange_interpolate(f0, f1, f_half, E4::from_base(two_inv));
            proof.sumcheck_polys.push(coeffs);
            commit_field_els::<BF, E4>(&mut transcript_seed, &coeffs);
            let folding_challenge = draw_random_field_els::<BF, E4>(&mut transcript_seed, 1)[0];
            folding_challenges_in_round.push(folding_challenge);
            claim = evaluate_small_univariate_poly::<BF, E4, 3>(&coeffs, &folding_challenge);
            fold_monomial_form_in_place_device(&mut state, folding_challenge, context)?;
            fold_evaluation_form_in_place_device(&mut state, folding_challenge, context)?;
            fold_eq_poly_in_place_device(&mut state, folding_challenge, context)?;
            state.current_len /= 2;
        }

        let query_domain_size = 1u64 << query_domain_log2;
        let query_domain_generator = domain_generator_for_size::<BF>(query_domain_size);
        let extended_generator = domain_generator_for_size::<BF>(1u64 << rs_domain_log2);
        let mut high_powers_offsets =
            materialize_powers_serial_starting_with_one::<BF, std::alloc::Global>(
                domain_generator_for_size::<BF>(1u64 << num_folding_steps)
                    .inverse()
                    .unwrap(),
                1 << (num_folding_steps - 1),
            );
        bitreverse_enumeration_inplace(&mut high_powers_offsets);
        let query_index_bits = query_domain_size.trailing_zeros() as usize;
        let (nonce, mut bit_source) = draw_query_bits(
            &mut transcript_seed,
            num_queries * query_index_bits,
            pow_bits,
            worker,
        );
        proof.pow_nonces.push(nonce);

        for _ in 0..num_queries {
            let query_index = assemble_query_index(query_index_bits, &mut bit_source);
            let query_point = query_domain_generator.pow(query_index as u32);
            let base_root = extended_generator.pow(query_index as u32);
            let base_root_inv = base_root.inverse().unwrap();
            let (_, evals, query) = rs_oracle.query_for_folded_index(query_index, context)?;
            proof
                .intermediate_whir_oracles
                .last_mut()
                .unwrap()
                .queries
                .push(into_extension_query(query));
            let _folded = fold_coset(
                evals,
                num_folding_steps,
                &folding_challenges_in_round,
                &base_root_inv,
                &high_powers_offsets,
                &two_inv,
            );
            let _ = query_point;
        }
    }

    debug_assert!(!claim.is_zero() || claim == E4::ZERO);
    Ok(proof)
}

#[cfg(test)]
pub(crate) fn debug_build_initial_state_for_test(
    memory_trace_holder: &TraceHolder<BF>,
    mem_polys_claims: &[E4],
    witness_trace_holder: &TraceHolder<BF>,
    wit_polys_claims: &[E4],
    setup_trace_holder: &TraceHolder<BF>,
    setup_polys_claims: &[E4],
    original_evaluation_point: &[E4],
    batching_challenge: E4,
    context: &ProverContext,
) -> CudaResult<([Vec<E4>; 3], E4, Vec<E4>, Vec<E4>, Vec<E4>)> {
    fn copy_back(values: &DeviceSlice<E4>, context: &ProverContext) -> Vec<E4> {
        context.get_exec_stream().synchronize().unwrap();
        let mut host = unsafe { context.alloc_host_uninit_slice(values.len()) };
        memory_copy(&mut host, values).unwrap();
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
        &mut state,
        context,
    )?;

    Ok((
        batch_challenges,
        claim,
        copy_back(&state.sumchecked_poly_monomial_form[..trace_len], context),
        copy_back(&state.sumchecked_poly_evaluation_form[..trace_len], context),
        copy_back(&state.eq_poly[..trace_len], context),
    ))
}

#[cfg(test)]
pub(crate) fn debug_build_initial_batched_main_domain_poly_for_test(
    memory_trace_holder: &TraceHolder<BF>,
    mem_polys_claims: &[E4],
    witness_trace_holder: &TraceHolder<BF>,
    wit_polys_claims: &[E4],
    setup_trace_holder: &TraceHolder<BF>,
    setup_polys_claims: &[E4],
    batching_challenge: E4,
    context: &ProverContext,
) -> CudaResult<Vec<E4>> {
    fn copy_back(values: &DeviceSlice<E4>, context: &ProverContext) -> Vec<E4> {
        context.get_exec_stream().synchronize().unwrap();
        let mut host = unsafe { context.alloc_host_uninit_slice(values.len()) };
        memory_copy(&mut host, values).unwrap();
        unsafe { host.get_accessor().get().to_vec() }
    }

    fn copy_back_bf(values: &DeviceSlice<BF>, context: &ProverContext) -> Vec<BF> {
        context.get_exec_stream().synchronize().unwrap();
        let mut host = unsafe { context.alloc_host_uninit_slice(values.len()) };
        memory_copy(&mut host, values).unwrap();
        unsafe { host.get_accessor().get().to_vec() }
    }

    let trace_len = 1usize << memory_trace_holder.log_domain_size;
    let mut state = GpuWhirState::new(trace_len, context)?;
    let total_base_oracles = memory_trace_holder.columns_count
        + witness_trace_holder.columns_count
        + setup_trace_holder.columns_count;
    let mut challenge_powers = materialize_powers_serial_starting_with_one::<E4, std::alloc::Global>(
        batching_challenge,
        total_base_oracles,
    );
    challenge_powers[1..].fill(E4::ZERO);
    let (memory_weights, rest) = challenge_powers.split_at(mem_polys_claims.len());
    let (witness_weights, setup_weights) = rest.split_at(wit_polys_claims.len());
    debug_assert_eq!(setup_weights.len(), setup_polys_claims.len());

    let _weight_buffers = build_initial_batched_main_domain_poly_device(
        memory_trace_holder,
        memory_weights,
        witness_trace_holder,
        witness_weights,
        setup_trace_holder,
        setup_weights,
        &mut state.sumchecked_poly_evaluation_form,
        context,
    )?;
    context.get_exec_stream().synchronize()?;
    Ok(copy_back(
        &state.sumchecked_poly_evaluation_form[..trace_len],
        context,
    ))
}

#[cfg(test)]
pub(crate) fn debug_build_initial_state_snapshots_for_test(
    memory_trace_holder: &TraceHolder<BF>,
    mem_polys_claims: &[E4],
    witness_trace_holder: &TraceHolder<BF>,
    wit_polys_claims: &[E4],
    setup_trace_holder: &TraceHolder<BF>,
    setup_polys_claims: &[E4],
    original_evaluation_point: &[E4],
    batching_challenge: E4,
    context: &ProverContext,
) -> CudaResult<(Vec<E4>, Vec<E4>)> {
    fn copy_back(values: &DeviceSlice<E4>, context: &ProverContext) -> Vec<E4> {
        context.get_exec_stream().synchronize().unwrap();
        let mut host = unsafe { context.alloc_host_uninit_slice(values.len()) };
        memory_copy(&mut host, values).unwrap();
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
        &mut state,
        context,
    )?;
    let pre_eq = copy_back(&state.sumchecked_poly_evaluation_form[..trace_len], context);

    copy_small_to_device(
        &mut state.point_pows[..original_evaluation_point.len()],
        original_evaluation_point,
        context,
    )?;
    launch_build_eq_values(
        state.point_pows.as_ptr(),
        0,
        original_evaluation_point.len(),
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

#[cfg(test)]
mod tests {
    use super::*;

    use std::alloc::Global;

    use era_cudart::memory::memory_copy;
    use fft::{bitreverse_enumeration_inplace, Twiddles};
    use prover::gkr::sumcheck::eq_poly::make_eq_poly_in_full;
    use prover::gkr::whir::hypercube_to_monomial::multivariate_coeffs_into_hypercube_evals;
    use prover::merkle_trees::blake2s_for_everything_tree::Blake2sU32MerkleTreeWithCap;
    use prover::merkle_trees::ColumnMajorMerkleTreeConstructor;
    use serial_test::serial;

    use crate::allocator::tracker::AllocationPlacement;
    use crate::prover::test_utils::make_test_context;
    use crate::prover::trace_holder::TreesCacheMode;

    fn sample_ext(seed: u32) -> E4 {
        E4::from_array_of_base([
            BF::from_u32_unchecked(seed + 1),
            BF::from_u32_unchecked(seed + 2),
            BF::from_u32_unchecked(seed + 3),
            BF::from_u32_unchecked(seed + 4),
        ])
    }

    fn alloc_and_copy(values: &[E4], context: &ProverContext) -> DeviceAllocation<E4> {
        let mut device = context
            .alloc(values.len(), AllocationPlacement::BestFit)
            .unwrap();
        memory_copy(&mut device, values).unwrap();
        device
    }

    fn copy_back(values: &DeviceSlice<E4>, context: &ProverContext) -> Vec<E4> {
        context.get_exec_stream().synchronize().unwrap();
        let mut host = unsafe { context.alloc_host_uninit_slice(values.len()) };
        memory_copy(&mut host, values).unwrap();
        unsafe { host.get_accessor().get().to_vec() }
    }

    fn copy_back_bf(values: &DeviceSlice<BF>, context: &ProverContext) -> Vec<BF> {
        context.get_exec_stream().synchronize().unwrap();
        let mut host = unsafe { context.alloc_host_uninit_slice(values.len()) };
        memory_copy(&mut host, values).unwrap();
        unsafe { host.get_accessor().get().to_vec() }
    }

    fn fold_monomial_form_for_test(input: &mut Vec<E4>, challenge: E4) {
        let mut buffer = Vec::with_capacity(input.len() / 2);
        for [c0, c1] in input.as_chunks::<2>().0.iter() {
            let mut result = *c1;
            result.mul_assign(&challenge);
            result.add_assign(c0);
            buffer.push(result);
        }
        *input = buffer;
    }

    fn fold_evaluation_form_for_test(input: &mut Vec<E4>, challenge: E4) {
        let half_len = input.len() / 2;
        let (first_half, second_half) = input.split_at_mut(half_len);
        for (a, b) in first_half.iter_mut().zip(second_half.iter()) {
            let mut t = *b;
            t.sub_assign(a);
            t.mul_assign(&challenge);
            a.add_assign(&t);
        }
        input.truncate(half_len);
    }

    fn special_three_point_eval_for_test(a: &[E4], b: &[E4]) -> (E4, E4, E4) {
        let half = a.len() / 2;
        let quart = BF::from_u32_unchecked(4).inverse().unwrap();
        let (a_low, a_high) = a.split_at(half);
        let (b_low, b_high) = b.split_at(half);
        let mut f0 = E4::ZERO;
        let mut f1 = E4::ZERO;
        let mut f_half = E4::ZERO;
        for ((a0, a1), (b0, b1)) in a_low
            .iter()
            .zip(a_high.iter())
            .zip(b_low.iter().zip(b_high.iter()))
        {
            let mut t0 = *a0;
            t0.mul_assign(b0);
            f0.add_assign(&t0);

            let mut t1 = *a1;
            t1.mul_assign(b1);
            f1.add_assign(&t1);

            let mut t_half = *a0;
            t_half.add_assign(a1);
            let mut eq_half = *b0;
            eq_half.add_assign(b1);
            t_half.mul_assign(&eq_half);
            f_half.add_assign(&t_half);
        }
        f_half.mul_assign_by_base(&quart);
        (f0, f1, f_half)
    }

    fn evaluate_monomial_form_for_test(coeffs: &[E4], point: E4) -> E4 {
        let mut result = E4::ZERO;
        let mut current = E4::ONE;
        for coeff in coeffs.iter() {
            let mut term = *coeff;
            term.mul_assign(&current);
            result.add_assign(&term);
            current.mul_assign(&point);
        }
        result
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn whir_special_three_point_eval_matches_cpu() {
        let context = make_test_context(256, 32);
        let mut state = GpuWhirState::new(8, &context).unwrap();
        let evals = (0..8)
            .map(|i| sample_ext(10 * i as u32))
            .collect::<Vec<_>>();
        let eq = (0..8)
            .map(|i| sample_ext(100 + 10 * i as u32))
            .collect::<Vec<_>>();
        state.current_len = evals.len();
        state.sumchecked_poly_evaluation_form = alloc_and_copy(&evals, &context);
        state.eq_poly = alloc_and_copy(&eq, &context);

        let actual = special_three_point_eval_device(&mut state, &context).unwrap();
        let expected = special_three_point_eval_for_test(&evals, &eq);

        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn whir_special_three_point_eval_large_matches_cpu() {
        let n = 1 << 16;
        let context = make_test_context(1024, 64);
        let mut state = GpuWhirState::new(n, &context).unwrap();
        let evals = (0..n)
            .map(|i| sample_ext(((i * 17) % 1000) as u32))
            .collect::<Vec<_>>();
        let eq = (0..n)
            .map(|i| sample_ext(2000 + ((i * 29) % 1000) as u32))
            .collect::<Vec<_>>();
        state.current_len = n;
        state.sumchecked_poly_evaluation_form = alloc_and_copy(&evals, &context);
        state.eq_poly = alloc_and_copy(&eq, &context);

        let actual = special_three_point_eval_device(&mut state, &context).unwrap();
        let expected = special_three_point_eval_for_test(&evals, &eq);

        assert_eq!(actual, expected);
    }

    fn make_trace_holder(columns: &[Vec<BF>], context: &ProverContext) -> TraceHolder<BF> {
        assert!(!columns.is_empty());
        let rows = columns[0].len();
        let mut trace_holder = TraceHolder::new(
            rows.trailing_zeros(),
            0,
            0,
            0,
            columns.len(),
            TreesCacheMode::CacheNone,
            context,
        )
        .unwrap();
        let flat = columns
            .iter()
            .flat_map(|column| column.iter().copied())
            .collect::<Vec<_>>();
        memory_copy(trace_holder.get_uninit_hypercube_evals_mut(), &flat).unwrap();
        trace_holder
            .materialize_cosets_from_owned_hypercube(context)
            .unwrap();
        trace_holder
    }

    fn make_lde_trace_holder(
        columns: &[Vec<BF>],
        log_lde_factor: u32,
        log_rows_per_leaf: u32,
        log_tree_cap_size: u32,
        context: &ProverContext,
    ) -> TraceHolder<BF> {
        assert!(!columns.is_empty());
        let rows = columns[0].len();
        let mut trace_holder = TraceHolder::new(
            rows.trailing_zeros(),
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            columns.len(),
            TreesCacheMode::CacheFull,
            context,
        )
        .unwrap();
        let flat = columns
            .iter()
            .flat_map(|column| column.iter().copied())
            .collect::<Vec<_>>();
        memory_copy(trace_holder.get_uninit_hypercube_evals_mut(), &flat).unwrap();
        trace_holder
            .materialize_cosets_from_owned_hypercube(context)
            .unwrap();
        trace_holder.commit_all(context).unwrap();
        trace_holder
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn whir_fold_helpers_match_cpu() {
        let context = make_test_context(256, 32);
        let mut state = GpuWhirState::new(8, &context).unwrap();
        let challenge = sample_ext(777);

        let monomial = (0..8)
            .map(|i| sample_ext(20 * i as u32))
            .collect::<Vec<_>>();
        let evals = (0..8)
            .map(|i| sample_ext(200 + 20 * i as u32))
            .collect::<Vec<_>>();
        let eq = (0..8)
            .map(|i| sample_ext(400 + 20 * i as u32))
            .collect::<Vec<_>>();

        state.current_len = 8;
        state.sumchecked_poly_monomial_form = alloc_and_copy(&monomial, &context);
        state.monomial_buffer = context.alloc(4, AllocationPlacement::BestFit).unwrap();
        state.sumchecked_poly_evaluation_form = alloc_and_copy(&evals, &context);
        state.eq_poly = alloc_and_copy(&eq, &context);

        let mut expected_monomial = monomial.clone();
        let mut expected_evals = evals.clone();
        let mut expected_eq = eq.clone();

        fold_monomial_form_for_test(&mut expected_monomial, challenge);
        fold_evaluation_form_for_test(&mut expected_evals, challenge);
        fold_evaluation_form_for_test(&mut expected_eq, challenge);

        fold_monomial_form_in_place_device(&mut state, challenge, &context).unwrap();
        fold_evaluation_form_in_place_device(&mut state, challenge, &context).unwrap();
        fold_eq_poly_in_place_device(&mut state, challenge, &context).unwrap();
        state.current_len = 4;

        assert_eq!(
            copy_back(
                &state.sumchecked_poly_monomial_form[..state.current_len],
                &context
            ),
            expected_monomial
        );
        assert_eq!(
            copy_back(
                &state.sumchecked_poly_evaluation_form[..state.current_len],
                &context
            ),
            expected_evals
        );
        assert_eq!(
            copy_back(&state.eq_poly[..state.current_len], &context),
            expected_eq
        );
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn whir_evaluate_monomial_matches_cpu() {
        let context = make_test_context(256, 32);
        let mut state = GpuWhirState::new(8, &context).unwrap();
        let coeffs = (0..8)
            .map(|i| sample_ext(50 * i as u32))
            .collect::<Vec<_>>();
        let point = sample_ext(999);
        state.current_len = coeffs.len();
        state.sumchecked_poly_monomial_form = alloc_and_copy(&coeffs, &context);

        let actual = evaluate_monomial_form_device(&mut state, point, &context).unwrap();
        let expected = evaluate_monomial_form_for_test(&coeffs, point);

        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn whir_initial_state_matches_cpu() {
        let context = make_test_context(256, 32);
        let worker = Worker::new();
        let memory_columns = vec![
            (0..8)
                .map(|i| BF::from_u32_unchecked(10 + i as u32))
                .collect(),
            (0..8)
                .map(|i| BF::from_u32_unchecked(30 + i as u32))
                .collect(),
        ];
        let witness_columns = vec![(0..8)
            .map(|i| BF::from_u32_unchecked(50 + i as u32))
            .collect()];
        let setup_columns = vec![(0..8)
            .map(|i| BF::from_u32_unchecked(70 + i as u32))
            .collect()];

        let memory_trace_holder = make_trace_holder(&memory_columns, &context);
        let witness_trace_holder = make_trace_holder(&witness_columns, &context);
        let setup_trace_holder = make_trace_holder(&setup_columns, &context);
        let domain_size = memory_columns[0].len();
        let memory_main_domain = copy_back_bf(memory_trace_holder.get_evaluations(), &context)
            .chunks_exact(domain_size)
            .map(|chunk| chunk.to_vec())
            .collect::<Vec<_>>();
        let witness_main_domain = copy_back_bf(witness_trace_holder.get_evaluations(), &context)
            .chunks_exact(domain_size)
            .map(|chunk| chunk.to_vec())
            .collect::<Vec<_>>();
        let setup_main_domain = copy_back_bf(setup_trace_holder.get_evaluations(), &context)
            .chunks_exact(domain_size)
            .map(|chunk| chunk.to_vec())
            .collect::<Vec<_>>();

        let mem_polys_claims = vec![sample_ext(10), sample_ext(20)];
        let wit_polys_claims = vec![sample_ext(30)];
        let setup_polys_claims = vec![sample_ext(40)];
        let original_evaluation_point = vec![sample_ext(100), sample_ext(200), sample_ext(300)];
        let batching_challenge = sample_ext(500);

        let mut state = GpuWhirState::new(8, &context).unwrap();
        let (batch_challenges, claim) = build_initial_state(
            &memory_trace_holder,
            &mem_polys_claims,
            &witness_trace_holder,
            &wit_polys_claims,
            &setup_trace_holder,
            &setup_polys_claims,
            &original_evaluation_point,
            batching_challenge,
            &mut state,
            &context,
        )
        .unwrap();

        let total_base_oracles = 4usize;
        let mut challenge_powers = materialize_powers_serial_starting_with_one::<
            E4,
            std::alloc::Global,
        >(batching_challenge, total_base_oracles);
        challenge_powers[1..].fill(E4::ZERO);
        let (memory_weights, rest) = challenge_powers.split_at(mem_polys_claims.len());
        let (witness_weights, setup_weights) = rest.split_at(wit_polys_claims.len());

        assert_eq!(batch_challenges[0], memory_weights);
        assert_eq!(batch_challenges[1], witness_weights);
        assert_eq!(batch_challenges[2], setup_weights);

        let mut expected_evals = vec![E4::ZERO; 8];
        for (weights, columns) in [
            (memory_weights, memory_main_domain.as_slice()),
            (witness_weights, witness_main_domain.as_slice()),
            (setup_weights, setup_main_domain.as_slice()),
        ] {
            for (column, weight) in columns.iter().zip(weights.iter()) {
                for (dst, src) in expected_evals.iter_mut().zip(column.iter()) {
                    let mut term = *weight;
                    term.mul_assign_by_base(src);
                    dst.add_assign(&term);
                }
            }
        }

        let twiddles = Twiddles::<BF, Global>::new(expected_evals.len(), &worker);
        let mut expected_monomials = expected_evals.clone();
        let expected_log_n = expected_monomials.len().trailing_zeros();
        fft::naive::cache_friendly_ntt_natural_to_bitreversed(
            &mut expected_monomials,
            expected_log_n,
            &twiddles.inverse_twiddles[..],
        );
        let size_inv = BF::from_u32_unchecked(expected_monomials.len() as u32)
            .inverse()
            .unwrap();
        for value in expected_monomials.iter_mut() {
            value.mul_assign_by_base(&size_inv);
        }
        bitreverse_enumeration_inplace(&mut expected_monomials);

        let mut expected_eval_form = expected_monomials.clone();
        let expected_eval_log_n = expected_eval_form.len().trailing_zeros();
        multivariate_coeffs_into_hypercube_evals(&mut expected_eval_form, expected_eval_log_n);
        bitreverse_enumeration_inplace(&mut expected_eval_form);

        let expected_eq = make_eq_poly_in_full::<E4>(&original_evaluation_point, &worker)
            .pop()
            .unwrap()
            .into_vec();

        let mut expected_claim = E4::ZERO;
        for (weights, claims) in [
            (memory_weights, mem_polys_claims.as_slice()),
            (witness_weights, wit_polys_claims.as_slice()),
            (setup_weights, setup_polys_claims.as_slice()),
        ] {
            for (weight, claim_value) in weights.iter().zip(claims.iter()) {
                let mut term = *claim_value;
                term.mul_assign(weight);
                expected_claim.add_assign(&term);
            }
        }

        assert_eq!(claim, expected_claim);
        assert_eq!(
            copy_back(&state.sumchecked_poly_monomial_form[..8], &context),
            expected_monomials
        );
        assert_eq!(
            copy_back(&state.sumchecked_poly_evaluation_form[..8], &context),
            expected_eval_form
        );
        assert_eq!(copy_back(&state.eq_poly[..8], &context), expected_eq);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn base_query_paths_match_cpu_tree() {
        let context = make_test_context(256, 32);
        let worker = Worker::new();
        let columns: Vec<Vec<BF>> = vec![
            (0..8)
                .map(|i| BF::from_u32_unchecked(10 + i as u32))
                .collect(),
            (0..8)
                .map(|i| BF::from_u32_unchecked(30 + i as u32))
                .collect(),
        ];
        let log_lde_factor = 2u32;
        let log_rows_per_leaf = 1u32;
        let log_tree_cap_size = 3u32;
        let rows = columns[0].len();
        let mut trace_holder = make_lde_trace_holder(
            &columns,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            &context,
        );

        let lde_factor = 1usize << log_lde_factor;
        let cosets_host = (0..lde_factor)
            .map(|coset_index| {
                copy_back_bf(trace_holder.get_coset_evaluations(coset_index), &context)
            })
            .collect::<Vec<_>>();
        let source_storage = cosets_host
            .iter()
            .map(|host| {
                (0..columns.len())
                    .map(|column| {
                        let start = column * rows;
                        &host[start..start + rows]
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let source_refs = source_storage
            .iter()
            .map(|columns| columns.as_slice())
            .collect::<Vec<_>>();
        let cpu_tree = <Blake2sU32MerkleTreeWithCap<Global> as ColumnMajorMerkleTreeConstructor<
            BF,
        >>::construct_from_cosets::<BF, Global>(
            &source_refs,
            1usize << log_rows_per_leaf,
            1usize << log_tree_cap_size,
            true,
            true,
            false,
            &worker,
        );

        let total_queries = (rows << log_lde_factor) >> log_rows_per_leaf;
        for query_index in 0..total_queries {
            let (_, _, gpu_query) =
                query_base_trace_holder_for_folded_index(&mut trace_holder, query_index, &context)
                    .unwrap();
            let (_, cpu_path) =
                <Blake2sU32MerkleTreeWithCap<Global> as ColumnMajorMerkleTreeConstructor<BF>>::get_proof::<Global>(
                    &cpu_tree,
                    query_index,
                );
            assert_eq!(gpu_query.path, cpu_path, "query_index={}", query_index);
        }
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn whir_build_eq_values_preserves_large_eval_buffer() {
        let context = make_test_context(2048, 32);
        let trace_len = 1usize << 24;
        let sample_len = 1024usize;
        let mid = trace_len / 2;
        let stream = context.get_exec_stream();

        let mut evals = context
            .alloc(trace_len, AllocationPlacement::BestFit)
            .unwrap();
        let fill = E4::from_array_of_base([BF::new(7), BF::new(13), BF::new(29), BF::new(43)]);
        get_powers_by_val(fill, 0, false, &mut evals, stream).unwrap();
        stream.synchronize().unwrap();

        let mut expected_head = vec![E4::ZERO; sample_len];
        let mut expected_mid = vec![E4::ZERO; sample_len];
        let mut expected_tail = vec![E4::ZERO; sample_len];
        memory_copy(&mut expected_head, &evals[..sample_len]).unwrap();
        memory_copy(&mut expected_mid, &evals[mid..mid + sample_len]).unwrap();
        memory_copy(
            &mut expected_tail,
            &evals[trace_len - sample_len..trace_len],
        )
        .unwrap();

        let mut point = context.alloc(24, AllocationPlacement::BestFit).unwrap();
        let coordinates = (0..24)
            .map(|idx| {
                E4::from_array_of_base([
                    BF::new((idx + 3) as u32),
                    BF::new((idx + 17) as u32),
                    BF::new((idx + 31) as u32),
                    BF::new((idx + 53) as u32),
                ])
            })
            .collect::<Vec<_>>();
        copy_small_to_device(&mut point, &coordinates, &context).unwrap();

        let mut eq = context
            .alloc(trace_len, AllocationPlacement::BestFit)
            .unwrap();
        launch_build_eq_values(
            point.as_ptr(),
            0,
            coordinates.len(),
            eq.as_mut_ptr(),
            trace_len,
            &context,
        )
        .unwrap();
        stream.synchronize().unwrap();

        let mut actual_head = vec![E4::ZERO; sample_len];
        let mut actual_mid = vec![E4::ZERO; sample_len];
        let mut actual_tail = vec![E4::ZERO; sample_len];
        memory_copy(&mut actual_head, &evals[..sample_len]).unwrap();
        memory_copy(&mut actual_mid, &evals[mid..mid + sample_len]).unwrap();
        memory_copy(&mut actual_tail, &evals[trace_len - sample_len..trace_len]).unwrap();

        assert_eq!(actual_head, expected_head);
        assert_eq!(actual_mid, expected_mid);
        assert_eq!(actual_tail, expected_tail);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn whir_large_e4_bit_reverse_and_copy_matches_cpu() {
        let context = make_test_context(2048, 32);
        let trace_len = 1usize << 24;
        let sample_len = 1024usize;
        let mid = trace_len / 2;
        let stream = context.get_exec_stream();

        let fill = E4::from_array_of_base([BF::new(5), BF::new(11), BF::new(17), BF::new(23)]);
        let mut values = context
            .alloc(trace_len, AllocationPlacement::BestFit)
            .unwrap();
        let mut scratch = context
            .alloc(trace_len, AllocationPlacement::BestFit)
            .unwrap();
        get_powers_by_val(fill, 0, false, &mut values, stream).unwrap();
        let src = DeviceMatrix::new(&values, trace_len);
        let mut dst = DeviceMatrixMut::new(&mut scratch, trace_len);
        bit_reverse(&src, &mut dst, stream).unwrap();
        memory_copy_async(&mut values, &scratch, stream).unwrap();
        stream.synchronize().unwrap();

        let mut actual_head = vec![E4::ZERO; sample_len];
        let mut actual_mid = vec![E4::ZERO; sample_len];
        let mut actual_tail = vec![E4::ZERO; sample_len];
        memory_copy(&mut actual_head, &values[..sample_len]).unwrap();
        memory_copy(&mut actual_mid, &values[mid..mid + sample_len]).unwrap();
        memory_copy(&mut actual_tail, &values[trace_len - sample_len..trace_len]).unwrap();

        let expected_for_index = |index: usize| {
            fill.pow(
                (index.reverse_bits() >> (usize::BITS - trace_len.trailing_zeros()))
                    .try_into()
                    .unwrap(),
            )
        };
        let expected_head = (0..sample_len).map(expected_for_index).collect::<Vec<_>>();
        let expected_mid = (mid..mid + sample_len)
            .map(expected_for_index)
            .collect::<Vec<_>>();
        let expected_tail = ((trace_len - sample_len)..trace_len)
            .map(expected_for_index)
            .collect::<Vec<_>>();

        assert_eq!(actual_head, expected_head);
        assert_eq!(actual_mid, expected_mid);
        assert_eq!(actual_tail, expected_tail);
    }
}
