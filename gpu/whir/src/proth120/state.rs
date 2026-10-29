use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_structures::{DeviceMatrix, DeviceMatrixMut};
use gpu_core::primitives::field::PR;
use gpu_prover_context::ProverContext;
use gpu_trace::trace::holder::TraceHolder;

use super::in_domain::InDomainState;
use super::kernels;

pub(crate) struct L1WhirState {
    pub(crate) monomials: DeviceAllocation<PR>,
    pub(crate) evals: DeviceAllocation<PR>,
    pub(crate) eq: DeviceAllocation<PR>,
    pub(crate) reduce_out: DeviceAllocation<PR>,
    pub(crate) current_len: usize,
    pub(crate) in_domain: InDomainState,
    eq_lo: DeviceAllocation<PR>,
    eq_hi: DeviceAllocation<PR>,
}

impl L1WhirState {
    pub(crate) fn new(
        log_message: u32,
        term_capacity: usize,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        assert!(
            (1..=26).contains(&log_message),
            "Proth120 WHIR: state log_message outside 1..=26"
        );
        let len = 1usize << log_message;
        Ok(Self {
            monomials: context.alloc(len, AllocationPlacement::BestFit)?,
            evals: context.alloc(len, AllocationPlacement::BestFit)?,
            eq: context.alloc(len, AllocationPlacement::BestFit)?,
            reduce_out: context.alloc(3, AllocationPlacement::BestFit)?,
            current_len: len,
            in_domain: InDomainState::new(term_capacity, context)?,
            eq_lo: context.alloc(1 << (log_message / 2), AllocationPlacement::BestFit)?,
            eq_hi: context.alloc(1 << log_message.div_ceil(2), AllocationPlacement::BestFit)?,
        })
    }
}

pub(crate) fn schedule_accumulate_base(
    base_raw: &TraceHolder<PR>,
    setup_raw: &TraceHolder<PR>,
    powers: &DeviceSlice<PR>,
    state: &mut L1WhirState,
    context: &ProverContext,
) -> CudaResult<()> {
    assert_eq!(
        base_raw.log_domain_size, setup_raw.log_domain_size,
        "Proth120 WHIR: raw trace logs differ"
    );
    let pack_log2 = state
        .current_len
        .trailing_zeros()
        .checked_sub(base_raw.log_domain_size)
        .expect("Proth120 WHIR: raw rows exceed message");
    let rows = 1 << base_raw.log_domain_size;
    kernels::accumulate_base(
        &DeviceMatrix::new(base_raw.get_hypercube_evals(), rows),
        &DeviceMatrix::new(setup_raw.get_hypercube_evals(), rows),
        pack_log2,
        powers,
        &mut state.evals,
        context.get_exec_stream(),
    )
}

pub(crate) fn schedule_monomials(
    state: &mut L1WhirState,
    context: &ProverContext,
) -> CudaResult<()> {
    gpu_ntt::proth120::hypercube_evals_to_monomials(
        &DeviceMatrix::new(&state.evals[..state.current_len], state.current_len),
        &mut DeviceMatrixMut::new(&mut state.monomials[..state.current_len], state.current_len),
        context.get_exec_stream(),
    )
}

pub(crate) fn schedule_eq_from_point(
    point: &DeviceSlice<PR>,
    state: &mut L1WhirState,
    context: &ProverContext,
) -> CudaResult<()> {
    assert_eq!(
        state.current_len,
        1usize << point.len(),
        "Proth120 WHIR: point length differs from state"
    );
    kernels::eq_from_point(
        point,
        &mut state.eq_lo,
        &mut state.eq_hi,
        &mut state.eq,
        context.get_exec_stream(),
    )
}

pub(crate) fn schedule_batched_opening(
    powers: &DeviceSlice<PR>,
    claims: &DeviceSlice<PR>,
    out: &mut DeviceSlice<PR>,
    context: &ProverContext,
) -> CudaResult<()> {
    kernels::batched_opening(powers, claims, out, context.get_exec_stream())
}

pub(crate) fn schedule_three_point(
    state: &mut L1WhirState,
    context: &ProverContext,
) -> CudaResult<()> {
    let mut partials = context.alloc(
        kernels::whir_three_point_partials_len(state.current_len / 2).max(1),
        AllocationPlacement::BestFit,
    )?;
    kernels::three_point(
        &state.evals,
        &state.eq,
        &mut partials,
        &mut state.reduce_out,
        context.get_exec_stream(),
    )
}

pub(crate) fn schedule_round_update(
    state: &mut L1WhirState,
    seed: &mut DeviceSlice<u8>,
    coeffs_dst: &mut DeviceSlice<PR>,
    challenge_out: &mut DeviceSlice<PR>,
    context: &ProverContext,
) -> CudaResult<()> {
    if state.in_domain.try_update_and_fold(
        &mut state.reduce_out,
        seed,
        coeffs_dst,
        challenge_out,
        context,
    )? {
        return Ok(());
    }
    kernels::round_update(
        &mut state.reduce_out,
        seed,
        coeffs_dst,
        challenge_out,
        context.get_exec_stream(),
    )
}

pub(crate) fn schedule_fold_state(
    state: &mut L1WhirState,
    challenge: &DeviceSlice<PR>,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(
        state.current_len >= 2,
        "Proth120 WHIR: cannot fold a constant"
    );
    let len = state.current_len / 2;
    let mut monomials = context.alloc(len, AllocationPlacement::BestFit)?;
    let mut evals = context.alloc(len, AllocationPlacement::BestFit)?;
    let mut eq = context.alloc(len, AllocationPlacement::BestFit)?;
    kernels::fold_adjacent(
        &state.monomials,
        &mut monomials,
        challenge,
        context.get_exec_stream(),
    )?;
    kernels::fold_adjacent_pair(
        &state.evals,
        &mut evals,
        &state.eq,
        &mut eq,
        challenge,
        context.get_exec_stream(),
    )?;
    state.monomials = monomials;
    state.evals = evals;
    state.eq = eq;
    state.current_len = len;
    Ok(())
}

pub(crate) fn schedule_monomial_eval(
    state: &L1WhirState,
    point: &DeviceSlice<PR>,
    out: &mut DeviceSlice<PR>,
    context: &ProverContext,
) -> CudaResult<()> {
    let (len0, len1) = kernels::monomial_eval_scratch_lens(state.current_len);
    let mut scratch0 = context.alloc(len0, AllocationPlacement::BestFit)?;
    let mut scratch1 = context.alloc(len1.max(1), AllocationPlacement::BestFit)?;
    kernels::monomial_eval(
        &state.monomials,
        &mut scratch0,
        &mut scratch1,
        point,
        out,
        context.get_exec_stream(),
    )
}
