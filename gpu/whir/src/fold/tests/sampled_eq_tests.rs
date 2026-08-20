use super::super::*;

use crate::test_utils::make_test_context;
use crate::upstream::make_eq_poly_in_full_lsb;
use worker::Worker;

use super::{copy_back, copy_small_to_device, fold_eq_poly_in_place_device, sample_ext};

/// Independent LSB reference, written from the definition: index bit `j` pairs
/// with `point[j]`. Mirrors the CPU authority
/// `prover::gkr::sumcheck::eq_poly::make_eq_table_lsb_first`, which the WHIR
/// sampled-eq update (`prover/src/gkr/whir/mod.rs`,
/// `update_eq_poly_reference`) calls per contribution.
fn lsb_eq_at(point: &[E4], idx: usize) -> E4 {
    let mut acc = E4::ONE;
    for (j, coordinate) in point.iter().enumerate() {
        let factor = if (idx >> j) & 1 == 1 {
            *coordinate
        } else {
            let mut one_minus = E4::ONE;
            one_minus.sub_assign(coordinate);
            one_minus
        };
        acc.mul_assign(&factor);
    }
    acc
}

/// `sum_q challenges[q] * eq(points[q], idx)` for `idx < acc_size`, the delta
/// the accumulator must add into `eq_poly`.
fn sampled_eq_reference(points: &[Vec<E4>], challenges: &[E4], acc_size: usize) -> Vec<E4> {
    (0..acc_size)
        .map(|idx| {
            let mut acc = E4::ZERO;
            for (point, challenge) in points.iter().zip(challenges.iter()) {
                let mut term = lsb_eq_at(point, idx);
                term.mul_assign(challenge);
                acc.add_assign(&term);
            }
            acc
        })
        .collect()
}

fn make_query_points(num_queries: usize, challenge_count: usize) -> Vec<Vec<E4>> {
    (0..num_queries)
        .map(|q| {
            (0..challenge_count)
                .map(|j| sample_ext((7 * (q * challenge_count + j) + 3) as u32))
                .collect()
        })
        .collect()
}

fn make_challenges(num_queries: usize) -> Vec<E4> {
    (0..num_queries)
        .map(|q| sample_ext((1009 + 11 * q) as u32))
        .collect()
}

/// Runs the production sampled-eq entry point on `state` at its current
/// `current_len` and asserts the device `eq_poly` moved by exactly the
/// independent LSB delta, leaving the tail past `current_len` untouched.
fn assert_sampled_eq_delta(
    state: &mut GpuWhirState,
    num_queries: usize,
    context: &ProverContext,
    label: &str,
) {
    let acc_size = state.current_len;
    let challenge_count = acc_size.trailing_zeros() as usize;
    let allocated = state.eq_poly.len();
    let points = make_query_points(num_queries, challenge_count);
    let challenges = make_challenges(num_queries);
    let flat_points = points.iter().flatten().copied().collect::<Vec<_>>();

    let mut claim_points_device: DeviceAllocation<E4> = context
        .alloc(flat_points.len().max(1), AllocationPlacement::BestFit)
        .unwrap();
    copy_small_to_device(
        &mut claim_points_device[..flat_points.len()],
        &flat_points,
        context,
    )
    .unwrap();
    let mut challenges_device: DeviceAllocation<E4> = context
        .alloc(num_queries, AllocationPlacement::BestFit)
        .unwrap();
    copy_small_to_device(&mut challenges_device[..], &challenges, context).unwrap();

    let before = copy_back(&state.eq_poly[..allocated], context);

    let scratch = schedule_accumulate_eq_samples_batched(
        state,
        &claim_points_device[..flat_points.len()],
        &challenges_device[..],
        num_queries,
        challenge_count,
        context,
    )
    .unwrap();
    context.get_exec_stream().synchronize().unwrap();
    drop(scratch);

    let after = copy_back(&state.eq_poly[..allocated], context);
    let delta = sampled_eq_reference(&points, &challenges, acc_size);
    assert_eq!(after.len(), before.len());

    for idx in 0..acc_size {
        let mut expected = before[idx];
        expected.add_assign(&delta[idx]);
        assert_eq!(
            after[idx],
            expected,
            "{label}: sampled eq diverged at index {idx} (bits {idx:0width$b})",
            width = challenge_count
        );
    }
    for idx in acc_size..allocated {
        assert_eq!(
            after[idx], before[idx],
            "{label}: accumulator wrote past current_len at index {idx}"
        );
    }
}

/// Seeds `state.eq_poly[..count]` through the production initial-eq builder and
/// cross-checks it against the CPU LSB table, so the accumulator's RMW base is
/// both non-zero and itself pinned.
fn seed_initial_eq(
    state: &mut GpuWhirState,
    log_count: usize,
    worker: &Worker,
    context: &ProverContext,
) {
    let count = 1usize << log_count;
    let point = (0..log_count)
        .map(|j| sample_ext((31 * j + 5) as u32))
        .collect::<Vec<_>>();
    let mut point_device: DeviceAllocation<E4> = context
        .alloc(point.len(), AllocationPlacement::BestFit)
        .unwrap();
    copy_small_to_device(&mut point_device[..], &point, context).unwrap();
    launch_build_eq_values_from_point(
        point_device.as_ptr(),
        0,
        point.len(),
        state.eq_group_tables.as_mut_ptr(),
        state.eq_poly.as_mut_ptr(),
        count,
        context,
    )
    .unwrap();
    let expected = make_eq_poly_in_full_lsb::<E4>(&point, worker)
        .pop()
        .unwrap()
        .into_vec();
    assert_eq!(
        copy_back(&state.eq_poly[..count], context),
        expected,
        "initial eq build diverged at log_count={log_count}"
    );
}

fn zero_eq_poly(state: &mut GpuWhirState, context: &ProverContext) {
    let zeros = vec![E4::ZERO; state.eq_poly.len()];
    copy_small_to_device(&mut state.eq_poly[..], &zeros, context).unwrap();
}

#[test]
#[cfg(not(no_cuda))]
fn sampled_eq_matches_cpu_lsb() {
    let context = make_test_context(256, 32);
    let worker = Worker::new();

    // `challenge_count` on both sides of the split/3-slot routing threshold
    // (log_n 1 takes the batched 3-slot path, >= 2 the 2-chunk split), with
    // odd log_n 5 and 7 exercising the uneven `high_bits != low_bits` splits,
    // and `num_queries > 1` exercising the per-query striding.
    for (log_n, num_queries, seed) in [
        (1usize, 3usize, true),
        (2, 2, true),
        (4, 1, true),
        (5, 3, true),
        (5, 2, false),
        (7, 4, true),
    ] {
        let count = 1usize << log_n;
        let mut state = GpuWhirState::new(count, &context).unwrap();
        if seed {
            seed_initial_eq(&mut state, log_n, &worker, &context);
        } else {
            zero_eq_poly(&mut state, &context);
        }
        let label = format!("log_n={log_n} num_queries={num_queries} seeded={seed}");
        assert_sampled_eq_delta(&mut state, num_queries, &context, &label);
    }
}

#[test]
#[cfg(not(no_cuda))]
fn sampled_eq_matches_cpu_lsb_after_fold() {
    let context = make_test_context(256, 32);
    let worker = Worker::new();

    // Recursive-round shape: the fold rounds halve `current_len` twice before
    // the round's sampled-eq accumulate, so `acc_size` is a strict prefix of
    // the allocation and the RMW base is a folded (non-zero) eq_poly.
    let log_full = 7usize;
    let count = 1usize << log_full;
    let mut state = GpuWhirState::new(count, &context).unwrap();
    seed_initial_eq(&mut state, log_full, &worker, &context);

    for round in 0..2 {
        fold_eq_poly_in_place_device(&mut state, sample_ext((601 + round) as u32), &context)
            .unwrap();
        state.current_len /= 2;
    }
    context.get_exec_stream().synchronize().unwrap();
    assert_eq!(state.current_len, 1usize << (log_full - 2));

    assert_sampled_eq_delta(&mut state, 3, &context, "after two folds, log_n=5");
}
