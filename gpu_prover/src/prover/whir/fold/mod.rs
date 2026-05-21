#[cfg(test)]
use core::marker::PhantomData;
#[cfg(test)]
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use fft::domain_generator_for_size;
#[cfg(test)]
use fft::materialize_powers_serial_starting_with_one;

use crate::allocator::tracker::AllocationPlacement;
#[cfg(test)]
use crate::ops::blake2s::Digest;
use crate::ops::cub::device_reduce::{get_reduce_temp_storage_bytes, reduce, ReduceOperation};
use crate::ops::cub::CUB_TEMP_STORAGE_EXTRA_ALIGNMENT_LOG2;
use crate::ops::ntt::{
    hypercube_coeffs_bitrev_to_bitrev_evals, hypercube_x1_msb_evals_to_x1_msb_monomials,
    natural_evals_to_bitreversed_monomials,
};
#[cfg(test)]
use crate::ops::simple::{add, mul, mul_into_x};
use crate::ops::transpose::transpose;
use crate::primitives::callbacks::Callbacks;
#[cfg(test)]
use crate::primitives::context::HostAllocation;
use crate::primitives::context::{DeviceAllocation, ProverContext};
use crate::primitives::device_structures::{
    DeviceMatrix, DeviceMatrixChunk, DeviceMatrixImpl, DeviceMatrixMut, DeviceMatrixOwnsAllocation,
};
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E4};
use crate::prover::gkr::backward::{eq_group_tables_len, launch_build_eq_values_from_point};
use crate::prover::pow::{schedule_pow_verify_and_query_indexes, PowAndQueryIndexesState};
use crate::prover::proof::layout::ProofLayout;
use crate::prover::trace::holder::TraceHolder;
use crate::prover::whir::kernels::{
    accumulate_whir_base_columns, batched_eq_factor_scratch_lens, deserialize_whir_e4_columns,
    launch_batched_accumulate_eq_samples, launch_whir_three_point_partials,
    partially_evaluate_monomials_by_ref, serialize_whir_e4_columns, whir_fold_split_half_in_place,
    whir_fold_split_half_in_place_pair, whir_fold_split_half_in_place_vectorized,
};
use crate::prover::whir::GpuWhirExtensionOracle;
use crate::upstream::FieldExtension;
#[cfg(test)]
use crate::upstream::{
    add_whir_commitment_to_transcript, commit_field_els, draw_random_field_els, BaseFieldQuery,
    DefaultTreeConstructor, Field, MerkleTreeCapVarLength, Seed, WhirCommitment,
};

const EXT4_DEGREE: usize = <E4 as FieldExtension<BF>>::DEGREE;

mod schedule;

pub(crate) use schedule::schedule_gpu_whir_fold_with_sources;

pub(super) struct GpuWhirState {
    sumchecked_poly_monomial_form: DeviceMatrixOwnsAllocation<BF>,
    sumchecked_poly_evaluation_form: DeviceAllocation<E4>,
    eq_poly: DeviceAllocation<E4>,
    eq_group_tables: DeviceAllocation<E4>,
    scratch0: DeviceAllocation<E4>,
    scratch1: DeviceAllocation<E4>,
    #[allow(dead_code)]
    scalar: DeviceAllocation<E4>,
    reduce_temp: DeviceAllocation<u8>,
    reduce_out: DeviceAllocation<E4>,
    current_len: usize,
    original_trace_len: usize,
}

// Per-fold-round-group device buffers. Aggregated into one struct because
// they have a shared lifetime: every scheduled stream op holding into them
// remains in flight until the surrounding `GpuWhirFoldScheduledExecution` is
// dropped. The rolling `device_seed` is owned by the outer scheduler and
// borrowed in here, so it does not appear in this struct.
pub(super) struct FoldRoundGroupKeepalives {
    pub(super) device_challenges: Vec<DeviceAllocation<E4>>,
}

impl FoldRoundGroupKeepalives {
    pub(super) fn new() -> Self {
        Self {
            device_challenges: Vec::new(),
        }
    }
}

pub(crate) struct GpuWhirFoldScheduledExecution {
    #[allow(dead_code)]
    _tracing_ranges: Vec<Range>,
    #[allow(dead_code)]
    _fold_round_group_keepalives: FoldRoundGroupKeepalives,
    // Keepalives for the device-side PoW verify + query index assembly
    // (one entry per WHIR round that goes through schedule_pow_verify_and_query_indexes).
    #[allow(dead_code)]
    _pow_round_state: Vec<PowAndQueryIndexesState>,
    // Per-round device-resident OOD points produced by `schedule_ood_sample_phase`
    // and consumed by `schedule_delinearization_running_powers_phase`. Held on
    // the scheduled-execution keepalive so the device buffers outlive every
    // kernel reading them.
    #[allow(dead_code)]
    _ood_point_devices: Vec<DeviceAllocation<E4>>,
    // Per-round device-side ephemerals used by delinearization (delin_base,
    // anchor_powers from `ab_squaring_sequence_e4_kernel`, and per-query
    // pows from `ab_query_squaring_sequences_bf_to_e4_kernel`) — owned here
    // so they outlive the kernels reading them.
    #[allow(dead_code)]
    _delinearization_ephemerals: Vec<DeviceAllocation<E4>>,
    #[allow(dead_code)]
    _query_index_callbacks: Vec<Callbacks<'static>>,
    // Trace holders of retired intermediate WHIR oracles — kept alive so any
    // scheduled D2D/D2H reads against their unified device cap remain valid.
    #[allow(dead_code)]
    _recursive_caps_keepalive: Vec<crate::prover::whir::GpuWhirExtensionOracleKeepalive>,
}

impl GpuWhirState {
    fn new(trace_len: usize, context: &ProverContext) -> CudaResult<Self> {
        assert!(trace_len.is_power_of_two());
        assert!(trace_len >= 2);
        let half_len = trace_len / 2;
        let max_log_n = trace_len.trailing_zeros() as usize;
        let reduce_temp_bytes =
            get_reduce_temp_storage_bytes::<E4>(ReduceOperation::Sum, half_len as i32)?;
        Ok(Self {
            sumchecked_poly_monomial_form: DeviceMatrixOwnsAllocation::new(
                context.alloc(trace_len * EXT4_DEGREE, AllocationPlacement::BestFit)?,
                trace_len,
            ),
            sumchecked_poly_evaluation_form: context
                .alloc(trace_len, AllocationPlacement::BestFit)?,
            eq_poly: context.alloc(trace_len, AllocationPlacement::BestFit)?,
            eq_group_tables: context.alloc(
                eq_group_tables_len(max_log_n).max(1),
                AllocationPlacement::BestFit,
            )?,
            scratch0: context.alloc(half_len, AllocationPlacement::BestFit)?,
            scratch1: context.alloc(half_len, AllocationPlacement::BestFit)?,
            scalar: context.alloc(1, AllocationPlacement::BestFit)?,
            reduce_temp: context
                .alloc_with_extra_alignment::<u8, CUB_TEMP_STORAGE_EXTRA_ALIGNMENT_LOG2>(
                    reduce_temp_bytes,
                    AllocationPlacement::BestFit,
                )?,
            reduce_out: context.alloc(3, AllocationPlacement::BestFit)?,
            current_len: trace_len,
            original_trace_len: trace_len,
        })
    }
}

#[cfg(test)]
pub(super) fn schedule_reduce_outputs_readback(
    count: usize,
    state: &mut GpuWhirState,
    context: &ProverContext,
) -> CudaResult<HostAllocation<[E4]>> {
    let mut host = unsafe { context.alloc_host_uninit_slice(count) };
    memory_copy_async(
        &mut host,
        &state.reduce_out[..count],
        context.get_exec_stream(),
    )?;
    Ok(host)
}

#[cfg(test)]
pub(super) fn bitreverse_index(index: usize, num_bits: u32) -> usize {
    if num_bits == 0 {
        debug_assert_eq!(index, 0);
        return 0;
    }
    index.reverse_bits() >> (usize::BITS - num_bits)
}

pub(super) fn get_base_columns<'a>(
    trace_holder: &'a TraceHolder<BF>,
    rows: usize,
    use_hypercube_evals: bool,
) -> DeviceMatrix<'a, BF> {
    let values = if use_hypercube_evals {
        // Use the logical hypercube-evaluation view here. `raw_hypercube_backing`
        // preserves ownership only; WHIR needs the row-shaped evaluation slice
        // that `get_hypercube_evals` already exposes.
        DeviceMatrix::new(trace_holder.get_hypercube_evals(), rows)
    } else {
        assert!(
            trace_holder.are_cosets_materialized(),
            "{} {}",
            "Tried to build WHIR initial state from coset 0, ",
            "but cosets are not materialized",
        );
        DeviceMatrix::new(trace_holder.get_evaluations(), rows)
    };
    values
}

// Also initializes evaluation form if use_hypercube_evals_for_batching was false.
pub(super) fn initialize_batched_monomial_form(
    log_domain_size: usize,
    use_hypercube_evals_for_batching: bool,
    state: &mut GpuWhirState,
    context: &ProverContext,
) -> CudaResult<()> {
    let trace_len = 1 << log_domain_size;
    let mut vectorized_scratch =
        context.alloc(trace_len * EXT4_DEGREE, AllocationPlacement::BestFit)?;
    let stream = context.get_exec_stream();
    serialize_whir_e4_columns(
        &state.sumchecked_poly_evaluation_form[..trace_len],
        &mut vectorized_scratch,
        stream,
    )?;
    let vectorized_batched_evals_matrix = DeviceMatrix::new(&vectorized_scratch, trace_len);

    if use_hypercube_evals_for_batching {
        hypercube_x1_msb_evals_to_x1_msb_monomials(
            &vectorized_batched_evals_matrix,
            &mut state.sumchecked_poly_monomial_form,
            log_domain_size,
            false, // transpsoed_monomials,
            stream,
            context.get_device_properties(),
        )?;
        // If we're in this branch, it means state.sumchecked_poly_evaluation_form was
        // directly created by batching base hypercube evaluation columns, so we're done.
    } else {
        natural_evals_to_bitreversed_monomials(
            &vectorized_batched_evals_matrix,
            &mut state.sumchecked_poly_monomial_form,
            log_domain_size,
            false, // transposed_monomials
            stream,
            context.get_device_properties(),
        )?;
        let monomials_slice = state.sumchecked_poly_monomial_form.slice();
        for column in 0..EXT4_DEGREE {
            let src = &monomials_slice[column * trace_len..(column + 1) * trace_len];
            let dst = &mut vectorized_scratch[column * trace_len..(column + 1) * trace_len];
            // Interestingly, both work (I think because addition is commutative).
            // hypercube_coeffs_natural_to_natural_evals(
            hypercube_coeffs_bitrev_to_bitrev_evals(src, dst, log_domain_size, stream)?;
        }
        deserialize_whir_e4_columns(
            &vectorized_scratch,
            &mut state.sumchecked_poly_evaluation_form[..trace_len],
            stream,
        )?;
    }

    Ok(())
}

pub(super) fn schedule_initialize_batched_forms(
    memory_trace_holder: &TraceHolder<BF>,
    witness_trace_holder: &TraceHolder<BF>,
    setup_trace_holder: &TraceHolder<BF>,
    mem_polys_claims_len: usize,
    wit_polys_claims_len: usize,
    setup_polys_claims_len: usize,
    batching_challenge_device: &DeviceSlice<E4>,
    use_hypercube_evals_for_batching: bool,
    state: &mut GpuWhirState,
    context: &ProverContext,
) -> CudaResult<()> {
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
    assert!(!batching_challenge_device.is_empty());

    let total_base_oracles = memory_trace_holder.columns_count
        + witness_trace_holder.columns_count
        + setup_trace_holder.columns_count;
    let stream = context.get_exec_stream();

    // Device-native materialization of `[1, x, x^2, ..., x^(total_base_oracles - 1)]`
    // — replaces the prior host callback + H2D path.
    let mut challenge_powers_device: DeviceAllocation<E4> =
        context.alloc(total_base_oracles, AllocationPlacement::BestFit)?;
    crate::ops::powers::get_powers_by_ref(
        &batching_challenge_device[0],
        0,
        false,
        &mut challenge_powers_device[..],
        stream,
    )?;

    assert!(
        mem_polys_claims_len + wit_polys_claims_len + setup_polys_claims_len > 0,
        "WHIR base-folding needs at least one base column across memory/witness/setup",
    );

    let challenge_powers_device_slice = &mut challenge_powers_device[..];
    let (device_memory_weights, rest) =
        challenge_powers_device_slice.split_at_mut(mem_polys_claims_len);
    let (device_witness_weights, device_setup_weights) = rest.split_at_mut(wit_polys_claims_len);
    assert_eq!(device_setup_weights.len(), setup_polys_claims_len);

    let rows = state.sumchecked_poly_evaluation_form.len();
    let memory_values =
        get_base_columns(memory_trace_holder, rows, use_hypercube_evals_for_batching);
    let witness_values =
        get_base_columns(witness_trace_holder, rows, use_hypercube_evals_for_batching);
    let setup_values = get_base_columns(setup_trace_holder, rows, use_hypercube_evals_for_batching);

    accumulate_whir_base_columns(
        &memory_values,
        &witness_values,
        &setup_values,
        &device_memory_weights,
        &device_witness_weights,
        &device_setup_weights,
        &mut state.sumchecked_poly_evaluation_form,
        stream,
    )?;

    initialize_batched_monomial_form(
        memory_trace_holder.log_domain_size as usize,
        use_hypercube_evals_for_batching,
        state,
        context,
    )?;

    Ok(())
}

/// Computes the three sumcheck reductions needed per WHIR fold round into
/// `state.reduce_out[0..3]`. Output layout:
///   [0] = ⟨eval_low, eq_low⟩          = f(0)
///   [1] = ⟨eval_high, eq_high⟩        = f(1)
///   [2] = ⟨eval_low+eval_high, eq_low+eq_high⟩   (callers scale by 1/4 to get f(1/2))
///
/// Leaves the result on the device; callers that need a host copy must follow
/// up with `schedule_reduce_outputs_readback(3, ...)`.
pub(super) fn schedule_special_three_point_eval_device_compute(
    state: &mut GpuWhirState,
    context: &ProverContext,
) -> CudaResult<()> {
    let half = state.current_len / 2;
    let stream = context.get_exec_stream();
    let eval = &state.sumchecked_poly_evaluation_form[..state.current_len];
    let eq = &state.eq_poly[..state.current_len];
    launch_whir_three_point_partials(
        eval,
        eq,
        &mut state.scratch0[..],
        &mut state.reduce_out[..3],
        half,
        stream,
    )
}

pub(super) fn schedule_monomial_eval_device_impl(
    state: &mut GpuWhirState,
    point: &DeviceSlice<E4>,
    out: &mut era_cudart::slice::DeviceVariable<E4>,
    context: &ProverContext,
) -> CudaResult<()> {
    let stream = context.get_exec_stream();

    let partials_count = partially_evaluate_monomials_by_ref(
        &state.sumchecked_poly_monomial_form,
        &mut state.scratch0[..],
        &mut state.scratch1[..],
        point,
        state.current_len,
        stream,
    )?;

    let reduce_temp_bytes =
        get_reduce_temp_storage_bytes::<E4>(ReduceOperation::Sum, partials_count as i32)?;
    assert!(state.reduce_temp.len() >= reduce_temp_bytes);

    reduce(
        ReduceOperation::Sum,
        &mut state.reduce_temp,
        &state.scratch0[..partials_count],
        out,
        stream,
    )
}

#[cfg(test)]
pub(super) fn schedule_monomial_eval_device(
    state: &mut GpuWhirState,
    point: &DeviceSlice<E4>,
    context: &ProverContext,
) -> CudaResult<Vec<HostAllocation<[E4]>>> {
    // SAFETY: `state.reduce_out[0]` is a live, disjoint single-`E4` slot inside
    // `state.reduce_out`. The impl below only mutably borrows
    // `state.{reduce_temp, scratch0, scratch1, sumchecked_poly_monomial_form,
    // current_len}`, none of which overlap with `state.reduce_out`. Aliasing
    // through a raw pointer here sidesteps the borrow checker's inability to
    // split-borrow disjoint fields across a method call; the schedule-time
    // contract for this slot is preserved.
    let reduce_out_ptr = state.reduce_out.as_mut_ptr();
    let out = unsafe { era_cudart::slice::DeviceVariable::from_raw_parts_mut(reduce_out_ptr) };
    schedule_monomial_eval_device_impl(state, point, out, context)?;

    let mut result = Vec::new();
    result.push(schedule_reduce_outputs_readback(1, state, context)?);

    Ok(result)
}

/// Returned scratch allocations must outlive the launched kernels — push onto
/// a per-round keepalive vec.
pub(super) fn schedule_accumulate_eq_samples_batched(
    state: &mut GpuWhirState,
    claim_points: &DeviceSlice<E4>,
    challenges: &DeviceSlice<E4>,
    num_queries: usize,
    challenge_count: usize,
    context: &ProverContext,
) -> CudaResult<(DeviceAllocation<E4>, DeviceAllocation<E4>)> {
    assert_eq!(claim_points.len(), num_queries * challenge_count);
    assert!(challenges.len() >= num_queries);
    let (high_len, low_len) = batched_eq_factor_scratch_lens(num_queries);
    let mut eq_high_scratch = context.alloc::<E4>(high_len, AllocationPlacement::BestFit)?;
    let mut eq_low_scratch = context.alloc::<E4>(low_len, AllocationPlacement::BestFit)?;
    launch_batched_accumulate_eq_samples(
        claim_points.as_ptr(),
        challenges.as_ptr(),
        num_queries,
        challenge_count,
        eq_high_scratch.as_mut_ptr(),
        eq_low_scratch.as_mut_ptr(),
        state.eq_poly.as_mut_ptr(),
        state.current_len,
        context,
    )?;
    Ok((eq_high_scratch, eq_low_scratch))
}

#[cfg(test)]
pub(crate) use tests::{
    debug_apply_initial_fold_challenge_for_test, debug_build_initial_batched_evals_for_test,
    debug_build_initial_fold_state_for_test, debug_build_initial_state_for_test,
    debug_build_initial_state_snapshots_for_test, debug_initial_round_checkpoint_for_test,
};

#[cfg(test)]
mod tests;
