// Only consumed by the #[cfg(test)] `schedule_reduce_outputs_readback` below.
#[cfg(test)]
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use fft::domain_generator_for_size;
#[cfg(test)]
use fft::materialize_powers_serial_starting_with_one;

#[cfg(test)]
use crate::kernels::whir_fold_adjacent;
use crate::kernels::{
    accumulate_whir_base_columns_with_serialized_bf, batched_eq_factor_scratch_lens,
    launch_batched_accumulate_eq_samples, launch_split_accumulate_eq_samples,
    launch_whir_three_point_partials, partially_evaluate_monomials_by_ref,
    split_eq_factor_scratch_lens, whir_fold_adjacent_pair, whir_fold_adjacent_vectorized, whir_sum,
};
use crate::pow::{schedule_pow_verify_and_query_indexes, PowAndQueryIndexesState};
#[cfg(test)]
use crate::upstream::Field;
use crate::upstream::FieldExtension;
use crate::GpuWhirExtensionOracle;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
// Only consumed by #[cfg(test)] readback helpers (`schedule_reduce_outputs_readback`,
// `schedule_monomial_eval_device`).
#[cfg(test)]
use gpu_core::primitives::context::HostAllocation;
use gpu_core::primitives::device_structures::{
    DeviceMatrix, DeviceMatrixChunk, DeviceMatrixImpl, DeviceMatrixMut, DeviceMatrixOwnsAllocation,
};
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::{BF, E4};
use gpu_gkr::backward::{eq_group_tables_len, launch_build_eq_values_from_point};
use gpu_gkr::proof_layout::ProofLayout;
use gpu_ntt::ntt::hypercube_evals_to_monomials;
#[cfg(test)]
use gpu_ops::simple::{add, mul, mul_into_x};
use gpu_ops::transpose::transpose;
use gpu_prover_context::ProverContext;
use gpu_trace::trace::holder::TraceHolder;

const EXT4_DEGREE: usize = <E4 as FieldExtension<BF>>::DEGREE;

mod schedule;

// pub: re-exported for the apex proof orchestration (see schedule::… definition).
pub use schedule::schedule_gpu_whir_fold_with_sources;

pub(super) struct GpuWhirState {
    sumchecked_poly_monomial_form: DeviceMatrixOwnsAllocation<BF>,
    sumchecked_poly_evaluation_form: DeviceAllocation<E4>,
    eq_poly: DeviceAllocation<E4>,
    /// Fold destinations for the LSB (adjacent-pair) monomial-form,
    /// evaluation-form and eq folds. The pairing makes the read range overlap
    /// the write range across blocks, so each round folds out of place and
    /// swaps the buffers; a half-length partner suffices because the live
    /// length halves every round.
    monomial_form_fold_dst: DeviceMatrixOwnsAllocation<BF>,
    eval_form_fold_dst: DeviceAllocation<E4>,
    eq_poly_fold_dst: DeviceAllocation<E4>,
    eq_group_tables: DeviceAllocation<E4>,
    scratch0: DeviceAllocation<E4>,
    scratch1: DeviceAllocation<E4>,
    #[cfg(test)]
    scalar: DeviceAllocation<E4>,
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

// pub: returned to the apex proof orchestration, which holds it as a scheduled
// keepalive on the proof job until `prove()` finishes.
pub struct GpuWhirFoldScheduledExecution {
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
    // Trace holders of retired intermediate WHIR oracles — kept alive so any
    // scheduled D2D/D2H reads against their unified device cap remain valid.
    #[allow(dead_code)]
    _recursive_caps_keepalive: Vec<crate::GpuWhirExtensionOracleKeepalive>,
}

impl GpuWhirFoldScheduledExecution {
    /// Release the device-resident reservations this scheduled WHIR fold
    /// execution still owns. All fold / OOD / delinearization / PoW / query
    /// kernels and the slab-bound D2D/D2H copies that read them have been
    /// enqueued on `exec_stream` by prove-end, so these pool reservations free
    /// stream-ordered. The tracing ranges stay (they may still be consumed on
    /// the exec stream). Each clear is on its
    /// own line so a single buffer class can be re-retained when bisecting a
    /// multi-schedule regression.
    // pub: the apex proof driver (`proof/mod.rs`) releases the WHIR scheduled
    // execution's device buffers at finish across the crate boundary.
    pub fn release_device_buffers(&mut self) {
        // Per-fold-round device challenge buffers.
        self._fold_round_group_keepalives.device_challenges.clear();
        // Per-round OOD points + delinearization ephemerals.
        self._ood_point_devices.clear();
        self._delinearization_ephemerals.clear();
        // PoW raw-bits + assembled query-index device buffers.
        self._pow_round_state.clear();
        // Retired intermediate-oracle trace holders (their unified device caps).
        self._recursive_caps_keepalive.clear();
    }
}

impl GpuWhirState {
    fn new(trace_len: usize, context: &ProverContext) -> CudaResult<Self> {
        assert!(trace_len.is_power_of_two());
        assert!(trace_len >= 2);
        let half_len = trace_len / 2;
        let max_log_n = trace_len.trailing_zeros() as usize;
        Ok(Self {
            sumchecked_poly_monomial_form: DeviceMatrixOwnsAllocation::new(
                context.alloc(trace_len * EXT4_DEGREE, AllocationPlacement::BestFit)?,
                trace_len,
            ),
            sumchecked_poly_evaluation_form: context
                .alloc(trace_len, AllocationPlacement::BestFit)?,
            eq_poly: context.alloc(trace_len, AllocationPlacement::BestFit)?,
            monomial_form_fold_dst: DeviceMatrixOwnsAllocation::new(
                context.alloc(half_len * EXT4_DEGREE, AllocationPlacement::BestFit)?,
                half_len,
            ),
            eval_form_fold_dst: context.alloc(half_len, AllocationPlacement::BestFit)?,
            eq_poly_fold_dst: context.alloc(half_len, AllocationPlacement::BestFit)?,
            eq_group_tables: context.alloc(
                eq_group_tables_len(max_log_n).max(1),
                AllocationPlacement::BestFit,
            )?,
            scratch0: context.alloc(half_len, AllocationPlacement::BestFit)?,
            scratch1: context.alloc(half_len, AllocationPlacement::BestFit)?,
            #[cfg(test)]
            scalar: context.alloc(1, AllocationPlacement::BestFit)?,
            reduce_out: context.alloc(3, AllocationPlacement::BestFit)?,
            current_len: trace_len,
            original_trace_len: trace_len,
        })
    }
}

// Only consumed by test-only reduce-output readback paths
// (`schedule_monomial_eval_device`, `debug::schedule_special_three_point_eval_device`).
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

// Only consumed by `fold::tests::query_tests` and
// `debug::schedule_query_base_trace_holder_for_folded_index` (test-only).
#[cfg(test)]
pub(super) fn bitreverse_index(index: usize, num_bits: u32) -> usize {
    if num_bits == 0 {
        debug_assert_eq!(index, 0);
        return 0;
    }
    index.reverse_bits() >> (usize::BITS - num_bits)
}

/// The WHIR fold only supports batching the base oracles from their hypercube
/// evaluations. A coset-0 source would need more than a different column
/// reader: the committed base backing is stored in bitreversed row order while
/// this path needs natural row order, and the monomial form derived from a
/// coset-0 batch is the univariate IFFT of a codeword, which does not carry the
/// natural-order multilinear coefficient labeling the sumcheck folds, the
/// out-of-domain evaluation and `final_monomials` all read. Whoever implements
/// it owns converting all four of those, not just this assert.
pub(super) fn assert_batching_source_supported(use_hypercube_evals_for_batching: bool) {
    assert!(
        use_hypercube_evals_for_batching,
        "WHIR base batching from coset 0 evaluations is not supported: the committed base \
         backing is stored in bitreversed row order, but this path requires natural row order"
    );
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

/// Derives the monomial form from the batched evaluation form.
///
/// Only the hypercube-evals batching source is supported (see
/// `assert_batching_source_supported`, which every caller runs first), so the
/// evaluation form is already the batched base hypercube columns and this only
/// has to transform it.
pub(super) fn initialize_batched_monomial_form(
    log_domain_size: usize,
    use_hypercube_evals_for_batching: bool,
    vectorized_scratch: &mut DeviceSlice<BF>,
    state: &mut GpuWhirState,
    context: &ProverContext,
) -> CudaResult<()> {
    assert_batching_source_supported(use_hypercube_evals_for_batching);
    let trace_len = 1 << log_domain_size;
    assert_eq!(vectorized_scratch.len(), trace_len * EXT4_DEGREE);
    let stream = context.get_exec_stream();
    // The fused `accumulate_whir_base_columns_with_serialized_bf` upstream
    // already populated `vectorized_scratch` with the column-major BF view of
    // `state.sumchecked_poly_evaluation_form`, so no separate serialize pass.
    let vectorized_batched_evals_matrix = DeviceMatrix::new(&*vectorized_scratch, trace_len);

    hypercube_evals_to_monomials(
        &vectorized_batched_evals_matrix,
        &mut state.sumchecked_poly_monomial_form,
        log_domain_size,
        false, // transposed_monomials
        stream,
        context.get_device_properties(),
    )?;

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
    assert!(!batching_challenge_device.is_empty());

    let total_base_oracles = memory_trace_holder.columns_count
        + witness_trace_holder.columns_count
        + setup_trace_holder.columns_count;
    let stream = context.get_exec_stream();

    // Device-native materialization of `[1, x, x^2, ..., x^(total_base_oracles - 1)]`
    // — replaces the prior host callback + H2D path.
    let mut challenge_powers_device: DeviceAllocation<E4> =
        context.alloc(total_base_oracles, AllocationPlacement::BestFit)?;
    gpu_ops::powers::get_powers_by_ref(
        &batching_challenge_device[0],
        0,
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

    let rows = state.original_trace_len;
    let memory_values =
        get_base_columns(memory_trace_holder, rows, use_hypercube_evals_for_batching);
    let witness_values =
        get_base_columns(witness_trace_holder, rows, use_hypercube_evals_for_batching);
    let setup_values = get_base_columns(setup_trace_holder, rows, use_hypercube_evals_for_batching);

    // Pre-allocate the BF column-major scratch the NTT expects, so the fused
    // accumulate kernel can write the serialized form directly and skip the
    // separate serialize pass.
    let mut vectorized_scratch =
        context.alloc(trace_len * EXT4_DEGREE, AllocationPlacement::BestFit)?;
    accumulate_whir_base_columns_with_serialized_bf(
        &memory_values,
        &witness_values,
        &setup_values,
        device_memory_weights,
        device_witness_weights,
        device_setup_weights,
        &mut state.sumchecked_poly_evaluation_form,
        &mut vectorized_scratch[..],
        stream,
    )?;

    initialize_batched_monomial_form(
        memory_trace_holder.log_domain_size as usize,
        use_hypercube_evals_for_batching,
        &mut vectorized_scratch[..],
        state,
        context,
    )?;

    Ok(())
}

/// Computes the three sumcheck reductions needed per WHIR fold round into
/// `state.reduce_out[0..3]`. LSB binding pairs ADJACENT entries, so "even" and
/// "odd" below are the two halves of each pair `(2i, 2i + 1)`. Output layout:
///   [0] = ⟨eval_even, eq_even⟩        = f(0)
///   [1] = ⟨eval_odd, eq_odd⟩          = f(1)
///   [2] = ⟨eval_even+eval_odd, eq_even+eq_odd⟩   (callers scale by 1/4 to get f(1/2))
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

    // `scratch1` is free again here: its only prior use this round
    // (`z_chunk_adjustment`) has been consumed by the stream-ordered
    // monomial-eval kernel above.
    whir_sum(
        &state.scratch0[..partials_count],
        &mut state.scratch1[..],
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
    // `state.{scratch0, scratch1, sumchecked_poly_monomial_form,
    // current_len}`, none of which overlap with `state.reduce_out`. Aliasing
    // through a raw pointer here sidesteps the borrow checker's inability to
    // split-borrow disjoint fields across a method call; the schedule-time
    // contract for this slot is preserved.
    let reduce_out_ptr = state.reduce_out.as_mut_ptr();
    let out = unsafe { era_cudart::slice::DeviceVariable::from_raw_parts_mut(reduce_out_ptr) };
    schedule_monomial_eval_device_impl(state, point, out, context)?;

    Ok(vec![schedule_reduce_outputs_readback(1, state, context)?])
}

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
    if challenge_count >= 2 {
        let (high_len, low_len) = split_eq_factor_scratch_lens(num_queries, challenge_count);
        let mut eq_high_scratch = context.alloc::<E4>(high_len, AllocationPlacement::BestFit)?;
        let mut eq_low_scratch = context.alloc::<E4>(low_len, AllocationPlacement::BestFit)?;
        launch_split_accumulate_eq_samples(
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
    } else {
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
}

#[cfg(test)]
mod debug;

#[cfg(test)]
mod tests;
