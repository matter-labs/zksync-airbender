use super::*;

use std::alloc::Global;

use era_cudart::memory::memory_copy_async;
use fft::{bitreverse_enumeration_inplace, Twiddles};

use serial_test::serial;

use crate::allocator::tracker::AllocationPlacement;
use crate::ops::ntt::MIN_LOG_N_FOR_MULTISTAGE_KERNELS;
use crate::prover::test_utils::make_test_context;
use crate::prover::trace::holder::TreesCacheMode;
use crate::prover::whir::tests::e4_coeffs_to_vectorized;

use crate::upstream::{make_eq_poly_in_full, multivariate_coeffs_into_hypercube_evals, PrimeField};
use worker::Worker;

fn sample_ext(seed: u32) -> E4 {
    E4::from_array_of_base([
        BF::from_u32_unchecked(seed + 1),
        BF::from_u32_unchecked(seed + 2),
        BF::from_u32_unchecked(seed + 3),
        BF::from_u32_unchecked(seed + 4),
    ])
}

fn alloc_and_copy<T>(values: &[T], context: &ProverContext) -> DeviceAllocation<T> {
    let mut device = context
        .alloc(values.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut device, values, context.get_exec_stream()).unwrap();
    device
}

fn copy_back(values: &DeviceSlice<E4>, context: &ProverContext) -> Vec<E4> {
    let mut host = unsafe { context.alloc_host_uninit_slice(values.len()) };
    memory_copy_async(&mut host, values, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    unsafe { host.get_accessor().get().to_vec() }
}

fn copy_back_bf(values: &DeviceSlice<BF>, context: &ProverContext) -> Vec<BF> {
    let mut host = unsafe { context.alloc_host_uninit_slice(values.len()) };
    memory_copy_async(&mut host, values, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
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

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn scheduled_whir_special_three_point_eval_matches_cpu() {
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

    let scheduled = schedule_special_three_point_eval_device(&mut state, &context).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    let mut actual = unsafe { scheduled.get_accessor().get() }.to_vec();
    actual[2].mul_assign_by_base(&BF::from_u32_unchecked(4).inverse().unwrap());

    let expected = special_three_point_eval_for_test(&evals, &eq);
    assert_eq!(actual.as_slice(), &[expected.0, expected.1, expected.2]);
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
    memory_copy_async(
        trace_holder.get_uninit_hypercube_evals_mut(),
        &flat,
        context.get_exec_stream(),
    )
    .unwrap();
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
    memory_copy_async(
        trace_holder.get_uninit_hypercube_evals_mut(),
        &flat,
        context.get_exec_stream(),
    )
    .unwrap();
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
    let mut monomial_bitreversed = monomial.clone();
    bitreverse_enumeration_inplace(&mut monomial_bitreversed);
    let monomial_vectorized = e4_coeffs_to_vectorized(&monomial_bitreversed);
    state.sumchecked_poly_monomial_form = DeviceMatrixOwnsAllocation::new(
        alloc_and_copy(&monomial_vectorized, &context),
        state.current_len,
    );
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

    let monomial_vectorized = copy_back_bf(state.sumchecked_poly_monomial_form.slice(), &context);
    let mut monomial_from_gpu = vectorized_to_e4_coeffs(
        &monomial_vectorized,
        state.original_trace_len,
        state.current_len,
    );
    bitreverse_enumeration_inplace(&mut monomial_from_gpu);
    assert_eq!(monomial_from_gpu, expected_monomial);
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
fn whir_multi_step_fold_helpers_match_cpu() {
    let context = make_test_context(256, 32);
    let mut state = GpuWhirState::new(16, &context).unwrap();

    let monomial = (0..16)
        .map(|i| sample_ext(20 * i as u32))
        .collect::<Vec<_>>();
    let evals = (0..16)
        .map(|i| sample_ext(200 + 20 * i as u32))
        .collect::<Vec<_>>();
    let eq = (0..16)
        .map(|i| sample_ext(400 + 20 * i as u32))
        .collect::<Vec<_>>();
    let challenges = [
        sample_ext(777),
        sample_ext(888),
        sample_ext(999),
        sample_ext(1111),
    ];

    state.current_len = monomial.len();
    let mut monomial_bitreversed = monomial.clone();
    bitreverse_enumeration_inplace(&mut monomial_bitreversed);
    let monomial_vectorized = e4_coeffs_to_vectorized(&monomial_bitreversed);
    state.sumchecked_poly_monomial_form = DeviceMatrixOwnsAllocation::new(
        alloc_and_copy(&monomial_vectorized, &context),
        state.current_len,
    );
    state.sumchecked_poly_evaluation_form = alloc_and_copy(&evals, &context);
    state.eq_poly = alloc_and_copy(&eq, &context);

    let mut expected_monomial = monomial;
    let mut expected_evals = evals;
    let mut expected_eq = eq;

    for (step_idx, challenge) in challenges.into_iter().enumerate() {
        fold_monomial_form_for_test(&mut expected_monomial, challenge);
        fold_evaluation_form_for_test(&mut expected_evals, challenge);
        fold_evaluation_form_for_test(&mut expected_eq, challenge);

        fold_monomial_form_in_place_device(&mut state, challenge, &context).unwrap();
        fold_evaluation_form_in_place_device(&mut state, challenge, &context).unwrap();
        fold_eq_poly_in_place_device(&mut state, challenge, &context).unwrap();
        state.current_len /= 2;

        let monomial_vectorized =
            copy_back_bf(state.sumchecked_poly_monomial_form.slice(), &context);
        let mut monomial_from_gpu = vectorized_to_e4_coeffs(
            &monomial_vectorized,
            state.original_trace_len,
            state.current_len,
        );
        bitreverse_enumeration_inplace(&mut monomial_from_gpu);
        assert_eq!(
            monomial_from_gpu, expected_monomial,
            "monomial fold diverged at step {step_idx}",
        );
        assert_eq!(
            copy_back(
                &state.sumchecked_poly_evaluation_form[..state.current_len],
                &context
            ),
            expected_evals,
            "evaluation fold diverged at step {step_idx}",
        );
        assert_eq!(
            copy_back(&state.eq_poly[..state.current_len], &context),
            expected_eq,
            "eq fold diverged at step {step_idx}",
        );
    }
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn whir_large_multi_step_monomial_fold_matches_cpu() {
    const LOG_LEN: usize = 18;
    const LEN: usize = 1 << LOG_LEN;
    let context = make_test_context(256, 32);
    let mut state = GpuWhirState::new(LEN, &context).unwrap();

    let monomial = (0..LEN)
        .map(|i| sample_ext(10_000 + i as u32))
        .collect::<Vec<_>>();
    let challenges = [
        sample_ext(777),
        sample_ext(888),
        sample_ext(999),
        sample_ext(1111),
        sample_ext(1222),
        sample_ext(1333),
    ];

    state.current_len = monomial.len();
    let mut monomial_bitreversed = monomial.clone();
    bitreverse_enumeration_inplace(&mut monomial_bitreversed);
    let monomial_vectorized = e4_coeffs_to_vectorized(&monomial_bitreversed);
    state.sumchecked_poly_monomial_form = DeviceMatrixOwnsAllocation::new(
        alloc_and_copy(&monomial_vectorized, &context),
        state.current_len,
    );

    let mut expected_monomial = monomial;
    for (step_idx, challenge) in challenges.into_iter().enumerate() {
        fold_monomial_form_for_test(&mut expected_monomial, challenge);
        fold_monomial_form_in_place_device(&mut state, challenge, &context).unwrap();
        state.current_len /= 2;

        let monomial_vectorized =
            copy_back_bf(state.sumchecked_poly_monomial_form.slice(), &context);
        let mut monomial_from_gpu = vectorized_to_e4_coeffs(
            &monomial_vectorized,
            state.original_trace_len,
            state.current_len,
        );
        bitreverse_enumeration_inplace(&mut monomial_from_gpu);
        assert_eq!(
            monomial_from_gpu, expected_monomial,
            "large monomial fold diverged at step {step_idx}",
        );
    }
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn whir_large_multi_step_fold_helpers_match_cpu() {
    const LOG_LEN: usize = 18;
    const LEN: usize = 1 << LOG_LEN;
    let context = make_test_context(256, 32);
    let mut state = GpuWhirState::new(LEN, &context).unwrap();

    let monomial = (0..LEN)
        .map(|i| sample_ext(20_000 + i as u32))
        .collect::<Vec<_>>();
    let evals = (0..LEN)
        .map(|i| sample_ext(40_000 + i as u32))
        .collect::<Vec<_>>();
    let eq = (0..LEN)
        .map(|i| sample_ext(60_000 + i as u32))
        .collect::<Vec<_>>();
    let challenges = [
        sample_ext(1777),
        sample_ext(1888),
        sample_ext(1999),
        sample_ext(2111),
        sample_ext(2222),
        sample_ext(2333),
    ];

    state.current_len = LEN;
    let mut monomial_bitreversed = monomial.clone();
    bitreverse_enumeration_inplace(&mut monomial_bitreversed);
    let monomial_vectorized = e4_coeffs_to_vectorized(&monomial_bitreversed);
    state.sumchecked_poly_monomial_form = DeviceMatrixOwnsAllocation::new(
        alloc_and_copy(&monomial_vectorized, &context),
        state.current_len,
    );
    state.sumchecked_poly_evaluation_form = alloc_and_copy(&evals, &context);
    state.eq_poly = alloc_and_copy(&eq, &context);

    let mut expected_monomial = monomial;
    let mut expected_evals = evals;
    let mut expected_eq = eq;

    for (step_idx, challenge) in challenges.into_iter().enumerate() {
        fold_monomial_form_for_test(&mut expected_monomial, challenge);
        fold_evaluation_form_for_test(&mut expected_evals, challenge);
        fold_evaluation_form_for_test(&mut expected_eq, challenge);

        fold_monomial_form_in_place_device(&mut state, challenge, &context).unwrap();
        fold_evaluation_form_in_place_device(&mut state, challenge, &context).unwrap();
        fold_eq_poly_in_place_device(&mut state, challenge, &context).unwrap();
        state.current_len /= 2;

        let monomial_vectorized =
            copy_back_bf(state.sumchecked_poly_monomial_form.slice(), &context);
        let mut monomial_from_gpu = vectorized_to_e4_coeffs(
            &monomial_vectorized,
            state.original_trace_len,
            state.current_len,
        );
        bitreverse_enumeration_inplace(&mut monomial_from_gpu);
        assert_eq!(
            monomial_from_gpu, expected_monomial,
            "large combined fold monomial state diverged at step {step_idx}",
        );
        assert_eq!(
            copy_back(
                &state.sumchecked_poly_evaluation_form[..state.current_len],
                &context
            ),
            expected_evals,
            "large combined fold evaluation state diverged at step {step_idx}",
        );
        assert_eq!(
            copy_back(&state.eq_poly[..state.current_len], &context),
            expected_eq,
            "large combined fold eq state diverged at step {step_idx}",
        );
    }
}

#[cfg(not(no_cuda))]
fn run_whir_evaluate_monomial_matches_cpu(count: usize, is_small: bool) {
    let context = make_test_context(256, 32);

    let mut state = GpuWhirState::new(count, &context).unwrap();
    let coeffs = (0..count)
        .map(|i| sample_ext(50 * i as u32))
        .collect::<Vec<_>>();
    let point = sample_ext(999);
    state.current_len = coeffs.len();
    let mut monomial_bitreversed = coeffs.clone();
    bitreverse_enumeration_inplace(&mut monomial_bitreversed);
    let monomial_vectorized = e4_coeffs_to_vectorized(&monomial_bitreversed);
    state.sumchecked_poly_monomial_form = DeviceMatrixOwnsAllocation::new(
        alloc_and_copy(&monomial_vectorized, &context),
        state.current_len,
    );

    if is_small {
        // lets partially_evaluate_monomials_by_ref work with artificially small size
        state.scratch0 = context
            .alloc(state.current_len, AllocationPlacement::BestFit)
            .unwrap();
    }

    let actual = evaluate_monomial_form_device(&mut state, point, &context).unwrap();
    let expected = evaluate_monomial_form_for_test(&coeffs, point);

    assert_eq!(actual, expected);
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn whir_evaluate_monomial_matches_cpu_small() {
    run_whir_evaluate_monomial_matches_cpu(8, true);
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn whir_evaluate_monomial_matches_cpu_large() {
    run_whir_evaluate_monomial_matches_cpu(8192, false);
}

#[cfg(not(no_cuda))]
fn run_scheduled_whir_evaluate_monomial_matches_cpu(count: usize, is_small: bool) {
    let context = make_test_context(256, 32);

    let mut state = GpuWhirState::new(count, &context).unwrap();
    let coeffs = (0..count)
        .map(|i| sample_ext(50 * i as u32))
        .collect::<Vec<_>>();
    let point = sample_ext(999);
    state.current_len = coeffs.len();
    let mut monomial_bitreversed = coeffs.clone();
    bitreverse_enumeration_inplace(&mut monomial_bitreversed);
    let monomial_vectorized = e4_coeffs_to_vectorized(&monomial_bitreversed);
    state.sumchecked_poly_monomial_form = DeviceMatrixOwnsAllocation::new(
        alloc_and_copy(&monomial_vectorized, &context),
        state.current_len,
    );
    let point_device = alloc_and_copy(&[point], &context);

    if is_small {
        // lets partially_evaluate_monomials_by_ref work with artificially small size
        state.scratch0 = context
            .alloc(state.current_len, AllocationPlacement::BestFit)
            .unwrap();
    }

    let partials = schedule_monomial_eval_device(&mut state, &point_device, &context).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    let mut actual = E4::ZERO;
    for partial in partials.iter() {
        actual.add_assign(&unsafe { partial.get_accessor().get() }[0]);
    }

    let expected = evaluate_monomial_form_for_test(&coeffs, point);
    assert_eq!(actual, expected);
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn scheduled_whir_evaluate_monomial_matches_cpu_small() {
    run_scheduled_whir_evaluate_monomial_matches_cpu(8, true);
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn scheduled_whir_evaluate_monomial_matches_cpu_large() {
    run_scheduled_whir_evaluate_monomial_matches_cpu(8192, false);
}

#[cfg(not(no_cuda))]
fn run_whir_initial_state_matches_cpu(
    log_count: usize,
    use_hypercube_evals_for_batching: bool,
    is_large: bool,
) {
    let context = if is_large {
        make_test_context(64 * 1024, 1024)
    } else {
        make_test_context(256, 32)
    };
    let worker = Worker::new();
    let count = 1 << log_count;
    let memory_columns = vec![
        (0..count)
            .map(|i| BF::from_u32_unchecked(10 + i as u32))
            .collect(),
        (0..count)
            .map(|i| BF::from_u32_unchecked(30 + i as u32))
            .collect(),
    ];
    let witness_columns = vec![(0..count)
        .map(|i| BF::from_u32_unchecked(50 + i as u32))
        .collect()];
    let setup_columns = vec![(0..count)
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
    let original_evaluation_point = (0..log_count)
        .map(|i| sample_ext(10 * i as u32))
        .collect::<Vec<_>>();
    let batching_challenge = sample_ext(500);

    let mut state = GpuWhirState::new(count, &context).unwrap();
    let (batch_challenges, claim) = build_initial_state(
        &memory_trace_holder,
        &mem_polys_claims,
        &witness_trace_holder,
        &wit_polys_claims,
        &setup_trace_holder,
        &setup_polys_claims,
        &original_evaluation_point,
        batching_challenge,
        use_hypercube_evals_for_batching,
        &mut state,
        &context,
    )
    .unwrap();

    let total_base_oracles = 4usize;
    let challenge_powers = materialize_powers_serial_starting_with_one::<E4, std::alloc::Global>(
        batching_challenge,
        total_base_oracles,
    );
    let (memory_weights, rest) = challenge_powers.split_at(mem_polys_claims.len());
    let (witness_weights, setup_weights) = rest.split_at(wit_polys_claims.len());

    assert_eq!(batch_challenges[0], memory_weights);
    assert_eq!(batch_challenges[1], witness_weights);
    assert_eq!(batch_challenges[2], setup_weights);

    let mut expected_evals = vec![E4::ZERO; count];
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
    let monomial_vectorized = copy_back_bf(state.sumchecked_poly_monomial_form.slice(), &context);
    let mut monomial_from_gpu = vectorized_to_e4_coeffs(
        &monomial_vectorized,
        state.original_trace_len,
        state.current_len,
    );
    bitreverse_enumeration_inplace(&mut monomial_from_gpu);
    assert_eq!(monomial_from_gpu, expected_monomials);
    assert_eq!(
        copy_back(&state.sumchecked_poly_evaluation_form[..count], &context),
        expected_eval_form
    );
    assert_eq!(copy_back(&state.eq_poly[..count], &context), expected_eq);
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn whir_initial_state_matches_cpu_use_coset_0_for_batching_small() {
    run_whir_initial_state_matches_cpu(3, false, false);
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
#[ignore]
fn whir_initial_state_matches_cpu_use_coset_0_for_batching_large() {
    run_whir_initial_state_matches_cpu(MIN_LOG_N_FOR_MULTISTAGE_KERNELS + 1, false, true);
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn whir_initial_state_matches_cpu_use_hypercube_evals_for_batching_small() {
    run_whir_initial_state_matches_cpu(3, true, false);
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
#[ignore]
fn whir_initial_state_matches_cpu_use_hypercube_evals_for_batching_large() {
    run_whir_initial_state_matches_cpu(MIN_LOG_N_FOR_MULTISTAGE_KERNELS + 1, true, true);
}

mod helpers;

pub(crate) use helpers::{
    debug_apply_initial_fold_challenge_for_test, debug_build_initial_batched_evals_for_test,
    debug_build_initial_fold_state_for_test, debug_build_initial_state_for_test,
    debug_build_initial_state_snapshots_for_test, debug_initial_round_checkpoint_for_test,
};

use helpers::{
    build_initial_state, evaluate_monomial_form_device, fold_eq_poly_in_place_device,
    fold_evaluation_form_in_place_device, fold_monomial_form_in_place_device,
    schedule_special_three_point_eval_device, special_three_point_eval_device,
    vectorized_to_e4_coeffs,
};

mod query_tests;

pub(crate) use query_tests::{clone_scheduled_whir_pre_pow_seeds, GpuScheduledBaseFieldQuery};
