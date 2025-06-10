pub mod precomputes;

pub use self::precomputes::*;

use std::{alloc::Allocator, mem::MaybeUninit, sync::Barrier};

use super::*;
use ::field::*;
use seq_macro::seq;
use std::ops::Range;
use trace_holder::*;
use worker::Worker;

pub mod four_step;

#[cfg(test)]
mod tests;

// NOTE: here two main parameters are important:
// - FFT_UNROLL_FACTOR below
// - literal 64/32 factors in functions below for `unroll_for_loop`

pub const FFT_UNROLL_FACTOR: usize = 64; // presumably width of the cache line

pub fn adjust_to_zero_c0_var_length<const N: usize, A: Allocator + Clone>(
    trace_columns: &mut RowMajorTrace<Mersenne31Field, N, A>,
    columns_range: Range<usize>,
    worker: &Worker,
) {
    // we manually unroll here for efficiency
    assert!(columns_range.end <= trace_columns.width());
    let trace_len = trace_columns.len();
    // assert no u64 overflow
    assert!((worker.num_cores as u64) * (trace_len as u64) < (1u64 << 32));
    let num_chunks = worker.get_geometry(trace_len - 1).len();
    let mut per_thread_accumulators = vec![vec![0u64; columns_range.len()]; num_chunks];

    unsafe {
        worker.scope(trace_len - 1, |scope, geometry| {
            let mut dst_chunks = per_thread_accumulators.chunks_mut(1);
            for thread_idx in 0..geometry.len() {
                let chunk_size = geometry.get_chunk_size(thread_idx);
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                let range = chunk_start..(chunk_start + chunk_size);
                let mut trace_view = trace_columns.row_view(range);
                let dst = dst_chunks.next().unwrap();
                assert_eq!(dst.len(), 1);
                let columns_range = columns_range.clone();

                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    for _i in 0..chunk_size {
                        let mut dst_ptr = dst[0].as_mut_ptr();
                        let row_view = &trace_view.current_row_ref()[columns_range.clone()];
                        let num_unroll_rounds = row_view.len() / 64;
                        let remainder_len = row_view.len() % 64;
                        let mut src_ptr = row_view.as_ptr();
                        for _ in 0..num_unroll_rounds {
                            seq!(N in 0..64 {
                                let column_value = src_ptr.add(N).read().as_u64();
                                let dst_loc = dst_ptr.add(N);
                                assert!(dst_loc.read().checked_add(column_value).is_some());
                                dst_loc.write(dst_loc.read().wrapping_add(column_value));
                            });
                            src_ptr = src_ptr.add(64);
                            dst_ptr = dst_ptr.add(64);
                        }
                        if remainder_len != 0 {
                            for _i in 0..remainder_len {
                                let column_value = src_ptr.read().as_u64();
                                assert!(dst_ptr.read().checked_add(column_value).is_some());
                                dst_ptr.write(dst_ptr.read().wrapping_add(column_value));
                                src_ptr = src_ptr.add(1);
                                dst_ptr = dst_ptr.add(1);
                            }
                        }
                        debug_assert_eq!(src_ptr, row_view.as_ptr_range().end);
                        debug_assert_eq!(dst_ptr, dst[0].as_mut_ptr_range().end);

                        trace_view.advance_row();
                    }
                });
            }
        });
    }

    // now adjust last row. Our sum on the domain must be 0
    let mut adjustment_factors = vec![Mersenne31Field::ZERO; columns_range.len()];
    for src in per_thread_accumulators.into_iter() {
        for (dst, src) in adjustment_factors.iter_mut().zip(src.into_iter()) {
            dst.sub_assign(&Mersenne31Field::from_u64_with_reduction(src));
        }
    }
    let mut row = trace_columns.row_view((trace_len - 1)..trace_len);
    let row = &mut row.current_row()[columns_range];
    assert_eq!(row.len(), adjustment_factors.len());
    for (dst, src) in row.iter_mut().zip(adjustment_factors.into_iter()) {
        *dst = src;
    }
}

#[unroll::unroll_for_loops]
pub fn row_major_ifft<const N: usize, const M: usize>(
    trace_columns: &mut RowMajorTraceFixedColumnsView<Mersenne31Field, N, M>,
    precomputations: &[Mersenne31Complex],
) {
    assert!(M >= 2);
    let trace_len = trace_columns.len();
    assert!(trace_len.is_power_of_two());

    let n = trace_len;
    if n == 1 {
        return;
    }

    if n >= 16 {
        assert_eq!(precomputations.len() * 2, trace_len);
    }

    let mut pairs_per_group = n / 2;
    let mut num_groups = 1;
    let mut distance = n / 2;

    {
        // special case for omega = 1
        debug_assert!(num_groups == 1);
        let idx_1 = 0;
        let idx_2 = pairs_per_group;

        let mut j = idx_1;

        while j < idx_2 {
            let u = *trace_columns.get_row(j);
            let v = *trace_columns.get_row(j + distance);

            let mut add_res = u;
            let mut sub_res = u;
            // dirty unroll trick
            for i in 0..64 {
                debug_assert!(i < FFT_UNROLL_FACTOR);
                if i < M {
                    add_res[i].sub_assign(&v[i]);
                    sub_res[i].sub_assign(&v[i]);
                }
            }

            *trace_columns.get_row_mut(j + distance) = sub_res;
            *trace_columns.get_row_mut(j) = add_res;

            j += 1;
        }

        pairs_per_group /= 2;
        num_groups *= 2;
        distance /= 2;
    }

    while num_groups < n {
        debug_assert!(num_groups > 1);
        let mut k = 0;
        while k < num_groups {
            let idx_1 = k * pairs_per_group * 2;
            let idx_2 = idx_1 + pairs_per_group;
            let twiddle = precomputations[k];

            let mut j = idx_1;
            while j < idx_2 {
                let u = *trace_columns.get_row(j);
                let v = *trace_columns.get_row(j + distance);

                // now butterfly
                let mut add_res = u;
                let mut sub_res = u;
                for i in 0..32 {
                    debug_assert!(i * 2 < FFT_UNROLL_FACTOR);
                    if i < M / 2 {
                        add_res[2 * i].add_assign(&v[2 * i]);
                        add_res[2 * i + 1].add_assign(&v[2 * i + 1]);
                        let mut tmp = Mersenne31Complex {
                            c0: v[2 * i],
                            c1: v[2 * i + 1],
                        };
                        tmp.mul_assign(&twiddle);
                        sub_res[2 * i].sub_assign(&tmp.c0);
                        sub_res[2 * i + 1].sub_assign(&tmp.c1);
                    }
                }

                *trace_columns.get_row_mut(j + distance) = sub_res;
                *trace_columns.get_row_mut(j) = add_res;

                j += 1;
            }

            k += 1;
        }

        pairs_per_group /= 2;
        num_groups *= 2;
        distance /= 2;
    }
}

#[unroll::unroll_for_loops]
pub fn row_major_fft<const N: usize, const M: usize>(
    trace_columns: &mut RowMajorTraceFixedColumnsView<Mersenne31Field, N, M>,
    precomputations: &[Mersenne31Complex],
    powers_to_distribute: &[Mersenne31Complex],
) {
    assert!(M >= 2);
    let trace_len = trace_columns.len();
    assert!(trace_len.is_power_of_two());
    assert_eq!(trace_len, powers_to_distribute.len());

    let n = trace_len;
    if n == 1 {
        return;
    }

    if n >= 16 {
        assert_eq!(precomputations.len() * 2, trace_len);
    }

    let mut pairs_per_group = n / 2;
    let mut num_groups = 1;
    let mut distance = n / 2;

    unsafe {
        // special case for omega = 1
        debug_assert!(num_groups == 1);
        let idx_1 = 0;
        let idx_2 = pairs_per_group;

        let mut j = idx_1;

        while j < idx_2 {
            let u = *trace_columns.get_row(j);
            let v = *trace_columns.get_row(j + distance);
            let pow_for_u = *powers_to_distribute.get_unchecked(j);
            let pow_for_v = *powers_to_distribute.get_unchecked(j + distance);

            #[allow(invalid_value)]
            let mut add_res = [MaybeUninit::uninit().assume_init(); M];
            #[allow(invalid_value)]
            let mut sub_res = [MaybeUninit::uninit().assume_init(); M];

            for i in 0..32 {
                debug_assert!(i * 2 < FFT_UNROLL_FACTOR);
                if i < M / 2 {
                    let mut tmp_u = Mersenne31Complex {
                        c0: u[2 * i],
                        c1: u[2 * i + 1],
                    };
                    tmp_u.mul_assign(&pow_for_u);
                    let mut tmp_v = Mersenne31Complex {
                        c0: v[2 * i],
                        c1: v[2 * i + 1],
                    };
                    tmp_v.mul_assign(&pow_for_v);
                    let (u0, u1) = (tmp_u.c0, tmp_u.c1);
                    let (v0, v1) = (tmp_v.c0, tmp_v.c1);
                    add_res[2 * i] = u0;
                    add_res[2 * i + 1] = u1;
                    add_res[2 * i].add_assign(&v0);
                    add_res[2 * i + 1].add_assign(&v1);
                    sub_res[2 * i] = u0;
                    sub_res[2 * i + 1] = u1;
                    sub_res[2 * i].sub_assign(&v0);
                    sub_res[2 * i + 1].sub_assign(&v1);
                }
            }

            *trace_columns.get_row_mut(j + distance) = sub_res;
            *trace_columns.get_row_mut(j) = add_res;

            j += 1;
        }

        pairs_per_group /= 2;
        num_groups *= 2;
        distance /= 2;
    }

    while num_groups < n {
        debug_assert!(num_groups > 1);
        let mut k = 0;
        while k < num_groups {
            let idx_1 = k * pairs_per_group * 2;
            let idx_2 = idx_1 + pairs_per_group;
            let twiddle = precomputations[k];

            let mut j = idx_1;
            while j < idx_2 {
                let u = *trace_columns.get_row(j);
                let v = *trace_columns.get_row(j + distance);

                // now butterfly
                let mut add_res = u;
                let mut sub_res = u;
                for i in 0..32 {
                    debug_assert!(i * 2 < FFT_UNROLL_FACTOR);
                    if i < M / 2 {
                        add_res[2 * i].add_assign(&v[2 * i]);
                        add_res[2 * i + 1].add_assign(&v[2 * i + 1]);
                        let mut tmp = Mersenne31Complex {
                            c0: v[2 * i],
                            c1: v[2 * i + 1],
                        };
                        tmp.mul_assign(&twiddle);
                        sub_res[2 * i].sub_assign(&tmp.c0);
                        sub_res[2 * i + 1].sub_assign(&tmp.c1);
                    }
                }

                *trace_columns.get_row_mut(j + distance) = sub_res;
                *trace_columns.get_row_mut(j) = add_res;

                j += 1;
            }

            k += 1;
        }

        pairs_per_group /= 2;
        num_groups *= 2;
        distance /= 2;
    }
}

#[derive(Clone, Copy, Debug)]
pub struct PointerWrapper<T: Send + Sync>(pub *mut T);

unsafe impl<T: Send + Sync> Send for PointerWrapper<T> {}
unsafe impl<T: Send + Sync> Sync for PointerWrapper<T> {}

pub fn compute_unroll_params(
    _unpadded_width: usize,
    padded_width: usize,
) -> (usize, usize, usize, usize) {
    #[cfg(target_arch = "aarch64")]
    {
        debug_assert_eq!(CACHE_LINE_MULTIPLE * 2, FFT_UNROLL_FACTOR);
        debug_assert_eq!(CACHE_LINE_MULTIPLE, 32);
    }

    assert_eq!(padded_width % CACHE_LINE_MULTIPLE, 0);
    let unroll_stage_offset = FFT_UNROLL_FACTOR;
    // ideally we want to work only with fully unrolled stages, but check edge cases

    let (num_unrolled, num_remainders, padded_remainder) = if padded_width < FFT_UNROLL_FACTOR {
        assert_eq!(padded_width % CACHE_LINE_MULTIPLE, 0);

        (0, padded_width / CACHE_LINE_MULTIPLE, CACHE_LINE_MULTIPLE)
    } else {
        // under current condition we can not have a case when unpadded width fits into cache multiple, but padded only to the next
        // unroll factor
        let (num_remainders, padded_remainder) = if padded_width % FFT_UNROLL_FACTOR == 0 {
            (0, 0)
        } else {
            (
                (padded_width % FFT_UNROLL_FACTOR) / CACHE_LINE_MULTIPLE,
                CACHE_LINE_MULTIPLE,
            )
        };

        (
            padded_width / FFT_UNROLL_FACTOR,
            num_remainders,
            padded_remainder,
        )
    };

    (
        unroll_stage_offset,
        num_unrolled,
        num_remainders,
        padded_remainder,
    )
}

#[cfg(test)]
mod local_test {
    use crate::FFT_UNROLL_FACTOR;

    use super::compute_unroll_params;

    #[test]
    fn test_unrolls() {
        for i in 1..10 {
            let (_, num_unrolled, num_remainder, padded_reminder) =
                compute_unroll_params(10, i * super::CACHE_LINE_MULTIPLE);

            assert_eq!(
                num_unrolled * FFT_UNROLL_FACTOR + num_remainder * padded_reminder,
                super::CACHE_LINE_MULTIPLE * i
            );
        }
    }
}

// NOTE: this one doesn't involve scaling by 1/N as it'll be merged with multiplication
// by coset factors later on
pub fn parallel_row_major_full_line_partial_ifft<const N: usize, A: Allocator + Clone>(
    trace_columns: &mut RowMajorTrace<Mersenne31Field, N, A>,
    precomputations: &[Mersenne31Complex],
    worker: &Worker,
) {
    if CACHE_LINE_MULTIPLE > N {
        todo!();
    }

    assert!(N >= CACHE_LINE_MULTIPLE);
    let trace_len = trace_columns.len();
    assert!(trace_len.is_power_of_two());

    if trace_len == 1 {
        return;
    }

    // we want to have multiple stages, each using all many threads as possible,
    // and each thread working on radix-2 (for now), working on the full row via unrolled loop over some number
    // of elements each time, and using some prefetch

    if trace_len >= 16 {
        assert_eq!(precomputations.len() * 2, trace_len);
    }

    let n = trace_len;

    let (unroll_stage_offset, num_unrolled_cycles, num_remainder_passes, padded_remainder) =
        compute_unroll_params(trace_columns.width(), trace_columns.padded_width);

    let row_offset = trace_columns.padded_width;

    let num_stages = n.trailing_zeros() as usize;

    let barriers: Vec<_> = (0..num_stages)
        .map(|_| Barrier::new(worker.num_cores))
        .collect();

    let barriers_ref = &barriers;

    let ptr = PointerWrapper(trace_columns.ptr);
    let twiddle_ptr = PointerWrapper(precomputations.as_ptr().cast_mut());

    const RADIX: usize = 2;

    let num_cores = worker.num_cores;

    unsafe {
        worker.scope(trace_len / RADIX, |scope, _| {
            for thread_idx in 0..worker.num_cores {
                Worker::smart_spawn(scope, thread_idx == worker.num_cores - 1, move |_| {
                    let mut num_problems = 1;
                    let mut problem_size = trace_len;
                    let ptr = ptr;
                    let twiddle_ptr = twiddle_ptr;

                    for stage_idx in 0..num_stages {
                        let half_problem_size = problem_size / 2;
                        let distance = half_problem_size;

                        // first stage has trivial twiddles, so we special case it
                        if stage_idx == 0 {
                            assert!(half_problem_size >= num_cores);

                            for problem_idx in 0..num_problems {
                                // inner loop over subproblem size
                                let geometry = Worker::get_geometry_for_num_cores(
                                    num_cores,
                                    half_problem_size,
                                );
                                let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                                let chunk_size = geometry.get_chunk_size(thread_idx);

                                let mut j = problem_idx * problem_size + chunk_start;

                                for _ in 0..chunk_size {
                                    fft_inner_loop_logic_trivial_twiddle(
                                        j,
                                        distance,
                                        row_offset,
                                        num_unrolled_cycles,
                                        unroll_stage_offset,
                                        padded_remainder,
                                        num_remainder_passes,
                                        ptr,
                                    );

                                    j += 1;
                                }
                            }
                        } else {
                            // TODO: add heuristics here to keep good balance
                            if half_problem_size >= num_cores {
                                // same as we did before, but without scaling

                                for problem_idx in 0..num_problems {
                                    // inner loop over subproblem size
                                    let geometry = Worker::get_geometry_for_num_cores(
                                        num_cores,
                                        half_problem_size,
                                    );
                                    let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                                    let chunk_size = geometry.get_chunk_size(thread_idx);

                                    let mut j = problem_idx * problem_size + chunk_start;
                                    let twiddle_index = problem_idx;
                                    let twiddle = twiddle_ptr.0.add(twiddle_index).read();

                                    for _ in 0..chunk_size {
                                        ifft_inner_loop_logic_twiddle(
                                            j,
                                            distance,
                                            row_offset,
                                            num_unrolled_cycles,
                                            unroll_stage_offset,
                                            padded_remainder,
                                            num_remainder_passes,
                                            ptr,
                                            twiddle,
                                        );

                                        j += 1;
                                    }
                                }
                            } else {
                                // we split over outer loop
                                let geometry =
                                    Worker::get_geometry_for_num_cores(num_cores, num_problems);
                                let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                                let chunk_size = geometry.get_chunk_size(thread_idx);

                                let mut problem_idx = chunk_start;
                                for _ in 0..chunk_size {
                                    let mut j = problem_idx * problem_size;
                                    let twiddle_index = problem_idx;
                                    let twiddle = twiddle_ptr.0.add(twiddle_index).read();

                                    for _ in 0..half_problem_size {
                                        ifft_inner_loop_logic_twiddle(
                                            j,
                                            distance,
                                            row_offset,
                                            num_unrolled_cycles,
                                            unroll_stage_offset,
                                            padded_remainder,
                                            num_remainder_passes,
                                            ptr,
                                            twiddle,
                                        );

                                        j += 1;
                                    }

                                    problem_idx += 1;
                                }
                            }
                        }

                        num_problems *= 2;
                        problem_size /= 2;

                        // wait for all threads to finish
                        barriers_ref[stage_idx].wait();
                    }
                });
            }
        });
    }
}

pub fn parallel_row_major_full_line_fft_dit<const N: usize, A: Allocator + Clone>(
    trace_columns: &mut RowMajorTrace<Mersenne31Field, N, A>,
    precomputations: &[Mersenne31Complex],
    scales: &[Mersenne31Complex],
    worker: &Worker,
) {
    if CACHE_LINE_MULTIPLE > N {
        todo!();
    }

    assert!(N >= CACHE_LINE_MULTIPLE);
    let trace_len = trace_columns.len();
    assert_eq!(scales.len(), trace_len);
    assert!(trace_len.is_power_of_two());

    if trace_len == 1 {
        return;
    }

    // we want to have multiple stages, each using all many threads as possible,
    // and each thread working on radix-2 (for now), working on the full row via unrolled loop over some number
    // of elements each time, and using some prefetch

    if trace_len >= 16 {
        assert_eq!(precomputations.len() * 2, trace_len);
    }

    let n = trace_len;

    let (unroll_stage_offset, num_unrolled_cycles, num_remainder_passes, padded_remainder) =
        compute_unroll_params(trace_columns.width(), trace_columns.padded_width);

    let row_offset = trace_columns.padded_width;

    let num_stages = n.trailing_zeros() as usize;

    let barriers: Vec<_> = (0..num_stages)
        .map(|_| Barrier::new(worker.num_cores))
        .collect();

    let barriers_ref = &barriers;

    let ptr = PointerWrapper(trace_columns.ptr);
    let twiddle_ptr = PointerWrapper(precomputations.as_ptr().cast_mut());
    let scales_ptr = PointerWrapper(scales.as_ptr().cast_mut());

    const RADIX: usize = 2;

    let num_cores = worker.num_cores;

    unsafe {
        worker.scope(trace_len / RADIX, |scope, _| {
            for thread_idx in 0..worker.num_cores {
                Worker::smart_spawn(scope, thread_idx == num_cores - 1, move |_| {
                    let mut num_problems = 1;
                    let mut problem_size = trace_len;
                    let ptr = ptr;
                    let twiddle_ptr = twiddle_ptr;
                    let scales_ptr = scales_ptr;

                    for stage_idx in 0..num_stages {
                        let half_problem_size = problem_size / 2;
                        let distance = num_problems;
                        let step = distance * 2;

                        // first stage has trivial twiddles, but we do scale, so we special case it
                        if stage_idx == 0 {
                            assert!(half_problem_size >= num_cores);
                            assert_eq!(step, 2);
                            assert_eq!(num_problems, 1);

                            // there is actually no outer loop
                            for _problem_idx in 0..num_problems {
                                // inner loop over subproblem size
                                let geometry = Worker::get_geometry_for_num_cores(
                                    num_cores,
                                    half_problem_size,
                                );
                                let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                                let chunk_size = geometry.get_chunk_size(thread_idx);

                                let mut j = chunk_start * 2;

                                for _ in 0..chunk_size {
                                    ifft_inner_loop_logic_scale(
                                        j,
                                        distance,
                                        row_offset,
                                        num_unrolled_cycles,
                                        unroll_stage_offset,
                                        padded_remainder,
                                        num_remainder_passes,
                                        ptr,
                                        scales_ptr,
                                    );

                                    j += 2;
                                }
                            }
                        } else {
                            // TODO: add heuristics here to keep good balance
                            if half_problem_size >= num_cores {
                                // same as we did before, but without scaling

                                for problem_idx in 0..num_problems {
                                    // inner loop over subproblem size
                                    let geometry = Worker::get_geometry_for_num_cores(
                                        num_cores,
                                        half_problem_size,
                                    );
                                    let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                                    let chunk_size = geometry.get_chunk_size(thread_idx);

                                    let mut j = problem_idx + chunk_start * step;
                                    let twiddle_index = problem_idx * half_problem_size;
                                    let twiddle = twiddle_ptr.0.add(twiddle_index).read();

                                    for _ in 0..chunk_size {
                                        ifft_inner_loop_logic_twiddle(
                                            j,
                                            distance,
                                            row_offset,
                                            num_unrolled_cycles,
                                            unroll_stage_offset,
                                            padded_remainder,
                                            num_remainder_passes,
                                            ptr,
                                            twiddle,
                                        );

                                        j += step;
                                    }
                                }
                            } else {
                                // we split over outer loop
                                let geometry =
                                    Worker::get_geometry_for_num_cores(num_cores, num_problems);
                                let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                                let chunk_size = geometry.get_chunk_size(thread_idx);

                                let mut problem_idx = chunk_start;
                                for _ in 0..chunk_size {
                                    let mut j = problem_idx;
                                    let twiddle_index = problem_idx * half_problem_size;
                                    let twiddle = twiddle_ptr.0.add(twiddle_index).read();

                                    for _ in 0..half_problem_size {
                                        ifft_inner_loop_logic_twiddle(
                                            j,
                                            distance,
                                            row_offset,
                                            num_unrolled_cycles,
                                            unroll_stage_offset,
                                            padded_remainder,
                                            num_remainder_passes,
                                            ptr,
                                            twiddle,
                                        );

                                        j += step;
                                    }

                                    problem_idx += 1;
                                }
                            }
                        }

                        num_problems *= 2;
                        problem_size /= 2;

                        // wait for all threads to finish
                        barriers_ref[stage_idx].wait();
                    }
                });
            }
        });
    }
}

// NOTE: this one doesn't involve scaling by 1/N as it'll be merged with multiplication
// by coset factors later on
pub fn parallel_row_major_full_line_fft_dif<const N: usize, A: Allocator + Clone>(
    trace_columns: &mut RowMajorTrace<Mersenne31Field, N, A>,
    precomputations: &[Mersenne31Complex],
    scales: &[Mersenne31Complex],
    worker: &Worker,
) {
    if CACHE_LINE_MULTIPLE > N {
        todo!();
    }

    assert!(N >= CACHE_LINE_MULTIPLE);
    let trace_len = trace_columns.len();
    assert!(trace_len.is_power_of_two());
    assert_eq!(trace_len, scales.len());

    if trace_len == 1 {
        return;
    }

    // we want to have multiple stages, each using all many threads as possible,
    // and each thread working on radix-2 (for now), working on the full row via unrolled loop over some number
    // of elements each time, and using some prefetch

    if trace_len >= 16 {
        assert_eq!(precomputations.len() * 2, trace_len);
    }

    let n = trace_len;

    let (unroll_stage_offset, num_unrolled_cycles, num_remainder_passes, padded_remainder) =
        compute_unroll_params(trace_columns.width(), trace_columns.padded_width);

    let row_offset = trace_columns.padded_width;

    let num_stages = n.trailing_zeros() as usize;

    let barriers: Vec<_> = (0..num_stages)
        .map(|_| Barrier::new(worker.num_cores))
        .collect();

    let barriers_ref = &barriers;

    let ptr = PointerWrapper(trace_columns.ptr);
    let twiddle_ptr = PointerWrapper(precomputations.as_ptr().cast_mut());
    let scales_ptr = PointerWrapper(scales.as_ptr().cast_mut());

    const RADIX: usize = 2;

    let num_cores = worker.num_cores;

    unsafe {
        worker.scope(trace_len / RADIX, |scope, _| {
            for thread_idx in 0..worker.num_cores {
                Worker::smart_spawn(scope, thread_idx == worker.num_cores - 1, move |_| {
                    let mut num_problems = 1;
                    let mut problem_size = trace_len;
                    let ptr = ptr;
                    let twiddle_ptr = twiddle_ptr;
                    let scales_ptr = scales_ptr;

                    for stage_idx in 0..num_stages {
                        let half_problem_size = problem_size / 2;
                        let distance = num_problems;
                        let step = distance * 2;
                        // here in the first stage we scale and butterfly, and on the last stage we skip butterflies

                        // Also in the first stage we definitely can not split our parallelism over independent problems,
                        // so we split over independent pairs of rows;
                        if stage_idx == 0 {
                            debug_assert_eq!(distance, 1);
                            assert!(half_problem_size >= num_cores);

                            for problem_idx in 0..num_problems {
                                // inner loop over subproblem size
                                let geometry = Worker::get_geometry_for_num_cores(
                                    num_cores,
                                    half_problem_size,
                                );
                                let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                                let chunk_size = geometry.get_chunk_size(thread_idx);

                                let mut j = chunk_start * step + problem_idx;
                                let mut twiddle_index = chunk_start;

                                for _ in 0..chunk_size {
                                    fft_inner_loop_logic_scale_and_twiddle(
                                        j,
                                        distance,
                                        twiddle_index,
                                        row_offset,
                                        num_unrolled_cycles,
                                        unroll_stage_offset,
                                        padded_remainder,
                                        num_remainder_passes,
                                        ptr,
                                        twiddle_ptr,
                                        scales_ptr,
                                    );

                                    j += step;
                                    twiddle_index += 1;
                                }
                            }
                        } else if stage_idx != num_stages - 1 {
                            // TODO: add heuristics here to keep good balance
                            if half_problem_size >= num_cores {
                                // same as we did before, but without scaling

                                for problem_idx in 0..num_problems {
                                    // inner loop over subproblem size
                                    let geometry = Worker::get_geometry_for_num_cores(
                                        num_cores,
                                        half_problem_size,
                                    );
                                    let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                                    let chunk_size = geometry.get_chunk_size(thread_idx);

                                    let mut j = chunk_start * step + problem_idx;
                                    let mut twiddle_index = chunk_start;

                                    for _ in 0..chunk_size {
                                        fft_inner_loop_logic_twiddle(
                                            j,
                                            distance,
                                            twiddle_index,
                                            row_offset,
                                            num_unrolled_cycles,
                                            unroll_stage_offset,
                                            padded_remainder,
                                            num_remainder_passes,
                                            ptr,
                                            twiddle_ptr,
                                        );

                                        j += step;
                                        twiddle_index += 1;
                                    }
                                }
                            } else {
                                // we split over outer loop
                                let geometry =
                                    Worker::get_geometry_for_num_cores(num_cores, num_problems);
                                let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                                let chunk_size = geometry.get_chunk_size(thread_idx);

                                let mut problem_idx = chunk_start;
                                for _ in 0..chunk_size {
                                    let mut j = problem_idx;
                                    let mut twiddle_index = 0;

                                    for _ in 0..half_problem_size {
                                        fft_inner_loop_logic_twiddle(
                                            j,
                                            distance,
                                            twiddle_index,
                                            row_offset,
                                            num_unrolled_cycles,
                                            unroll_stage_offset,
                                            padded_remainder,
                                            num_remainder_passes,
                                            ptr,
                                            twiddle_ptr,
                                        );

                                        j += step;
                                        twiddle_index += 1;
                                    }

                                    problem_idx += 1;
                                }
                            }
                        } else {
                            debug_assert_eq!(half_problem_size, 1);

                            // we split over outer loop
                            let geometry =
                                Worker::get_geometry_for_num_cores(num_cores, num_problems);
                            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                            let chunk_size = geometry.get_chunk_size(thread_idx);

                            let mut problem_idx = chunk_start;
                            for _ in 0..chunk_size {
                                let j = problem_idx;
                                // there is no inner loop actually

                                fft_inner_loop_logic_trivial_twiddle(
                                    j,
                                    distance,
                                    row_offset,
                                    num_unrolled_cycles,
                                    unroll_stage_offset,
                                    padded_remainder,
                                    num_remainder_passes,
                                    ptr,
                                );

                                problem_idx += 1;
                            }
                        }

                        num_problems *= 2;
                        problem_size /= 2;

                        // wait for all threads to finish
                        barriers_ref[stage_idx].wait();
                    }
                });
            }
        });
    }
}

#[inline(always)]
unsafe fn fft_inner_loop_logic_scale_and_twiddle(
    j: usize,
    distance: usize,
    twiddle_index: usize,
    row_offset: usize,
    num_unrolled_cycles: usize,
    unroll_stage_offset: usize,
    padded_remainder: usize,
    num_remainder_passes: usize,
    ptr: PointerWrapper<Mersenne31Field>,
    twiddle_ptr: PointerWrapper<Mersenne31Complex>,
    scales_ptr: PointerWrapper<Mersenne31Complex>,
) {
    let twiddle = twiddle_ptr.0.add(twiddle_index).read();
    let idx_1 = j;
    let idx_2 = j + distance;
    let u_scale = scales_ptr.0.add(idx_1).read();
    let v_scale = scales_ptr.0.add(idx_2).read();

    let mut u_ptr = ptr.0.add(row_offset * idx_1);
    let mut v_ptr = ptr.0.add(row_offset * idx_2);

    #[cfg(target_arch = "aarch64")]
    {
        prefetch_next_line(u_ptr);
        prefetch_next_line(v_ptr);
        prefetch_next_line(u_ptr.add(CACHE_LINE_MULTIPLE));
        prefetch_next_line(v_ptr.add(CACHE_LINE_MULTIPLE));
    }

    for cycle in 0..num_unrolled_cycles {
        let _last_cycle = cycle == num_unrolled_cycles - 1;
        // prefetch next while we work here
        let u_ptr_next = u_ptr.add(unroll_stage_offset);
        let v_ptr_next = v_ptr.add(unroll_stage_offset);

        #[cfg(target_arch = "aarch64")]
        {
            debug_assert_eq!(CACHE_LINE_MULTIPLE * 2, unroll_stage_offset);
            prefetch_next_line(u_ptr_next);
            prefetch_next_line(v_ptr_next);
            if _last_cycle == false {
                prefetch_next_line(u_ptr_next.add(CACHE_LINE_MULTIPLE));
                prefetch_next_line(v_ptr_next.add(CACHE_LINE_MULTIPLE));
            }
        }

        // to have it in front of us here
        debug_assert_eq!(unroll_stage_offset, 64);

        seq!(N in 0..32 {
            let u_el_ptr = u_ptr.add(2*N).cast::<Mersenne31Complex>();
            let v_el_ptr = v_ptr.add(2*N).cast::<Mersenne31Complex>();

            let mut u = u_el_ptr.read();
            u.mul_assign(&u_scale);
            let mut v = v_el_ptr.read();
            v.mul_assign(&v_scale);

            let mut add_res = u;
            let mut sub_res = u;

            add_res.add_assign(&v);
            u_el_ptr.write(add_res);

            sub_res.sub_assign(&v);
            sub_res.mul_assign(&twiddle);

            v_el_ptr.write(sub_res);
        });

        u_ptr = u_ptr_next;
        v_ptr = v_ptr_next;
    }

    if padded_remainder != 0 {
        debug_assert_eq!(padded_remainder % CACHE_LINE_MULTIPLE, 0);

        #[cfg(target_arch = "aarch64")]
        {
            debug_assert_eq!(CACHE_LINE_MULTIPLE * 2, unroll_stage_offset);
            debug_assert_eq!(CACHE_LINE_MULTIPLE, 32);
            debug_assert_eq!(num_remainder_passes, 1);

            seq!(N in 0..16 {
                let u_el_ptr = u_ptr.add(2*N).cast::<Mersenne31Complex>();
                let v_el_ptr = v_ptr.add(2*N).cast::<Mersenne31Complex>();

                let mut u = u_el_ptr.read();
                u.mul_assign(&u_scale);
                let mut v = v_el_ptr.read();
                v.mul_assign(&v_scale);

                let mut add_res = u;
                let mut sub_res = u;

                add_res.add_assign(&v);
                u_el_ptr.write(add_res);

                sub_res.sub_assign(&v);
                sub_res.mul_assign(&twiddle);

                v_el_ptr.write(sub_res);
            });
        }

        #[cfg(not(target_arch = "aarch64"))]
        {
            debug_assert!(num_remainder_passes <= 3);

            debug_assert_eq!(CACHE_LINE_MULTIPLE * 4, unroll_stage_offset);
            debug_assert_eq!(CACHE_LINE_MULTIPLE, 16);
            for _ in 0..num_remainder_passes {
                let u_ptr_next = u_ptr.add(CACHE_LINE_MULTIPLE);
                let v_ptr_next = v_ptr.add(CACHE_LINE_MULTIPLE);
                prefetch_next_line(u_ptr_next);
                prefetch_next_line(v_ptr_next);

                seq!(N in 0..8 {
                    let u_el_ptr = u_ptr.add(2*N).cast::<Mersenne31Complex>();
                    let v_el_ptr = v_ptr.add(2*N).cast::<Mersenne31Complex>();

                    let mut u = u_el_ptr.read();
                    u.mul_assign(&u_scale);
                    let mut v = v_el_ptr.read();
                    v.mul_assign(&v_scale);

                    let mut add_res = u;
                    let mut sub_res = u;
                    add_res.add_assign(&v);
                    sub_res.sub_assign(&v);

                    u_el_ptr.write(add_res);
                    v_el_ptr.write(sub_res);
                });

                u_ptr = u_ptr_next;
                v_ptr = v_ptr_next;
            }
        }
    }
}

#[inline(always)]
unsafe fn fft_inner_loop_logic_twiddle(
    j: usize,
    distance: usize,
    twiddle_index: usize,
    row_offset: usize,
    num_unrolled_cycles: usize,
    unroll_stage_offset: usize,
    padded_remainder: usize,
    num_remainder_passes: usize,
    ptr: PointerWrapper<Mersenne31Field>,
    twiddle_ptr: PointerWrapper<Mersenne31Complex>,
) {
    let twiddle = twiddle_ptr.0.add(twiddle_index).read();
    let idx_1 = j;
    let idx_2 = j + distance;

    let mut u_ptr = ptr.0.add(row_offset * idx_1);
    let mut v_ptr = ptr.0.add(row_offset * idx_2);

    #[cfg(target_arch = "aarch64")]
    {
        prefetch_next_line(u_ptr);
        prefetch_next_line(v_ptr);
        prefetch_next_line(u_ptr.add(CACHE_LINE_MULTIPLE));
        prefetch_next_line(v_ptr.add(CACHE_LINE_MULTIPLE));
    }

    for cycle in 0..num_unrolled_cycles {
        let _last_cycle = cycle == num_unrolled_cycles - 1;
        // prefetch next while we work here
        let u_ptr_next = u_ptr.add(unroll_stage_offset);
        let v_ptr_next = v_ptr.add(unroll_stage_offset);

        #[cfg(target_arch = "aarch64")]
        {
            debug_assert_eq!(CACHE_LINE_MULTIPLE * 2, unroll_stage_offset);
            prefetch_next_line(u_ptr_next);
            prefetch_next_line(v_ptr_next);
            if _last_cycle == false {
                prefetch_next_line(u_ptr_next.add(CACHE_LINE_MULTIPLE));
                prefetch_next_line(v_ptr_next.add(CACHE_LINE_MULTIPLE));
            }
        }

        // to have it in front of us here
        debug_assert_eq!(unroll_stage_offset, 64);

        seq!(N in 0..32 {
            let u_el_ptr = u_ptr.add(2*N).cast::<Mersenne31Complex>();
            let v_el_ptr = v_ptr.add(2*N).cast::<Mersenne31Complex>();

            let u = u_el_ptr.read();
            let v = v_el_ptr.read();

            let mut add_res = u;
            let mut sub_res = u;

            add_res.add_assign(&v);
            u_el_ptr.write(add_res);

            sub_res.sub_assign(&v);
            sub_res.mul_assign(&twiddle);

            v_el_ptr.write(sub_res);
        });

        u_ptr = u_ptr_next;
        v_ptr = v_ptr_next;
    }

    if padded_remainder != 0 {
        debug_assert_eq!(padded_remainder % CACHE_LINE_MULTIPLE, 0);

        #[cfg(target_arch = "aarch64")]
        {
            debug_assert_eq!(CACHE_LINE_MULTIPLE * 2, unroll_stage_offset);
            debug_assert_eq!(CACHE_LINE_MULTIPLE, 32);
            debug_assert_eq!(num_remainder_passes, 1);

            seq!(N in 0..16 {
                let u_el_ptr = u_ptr.add(2*N).cast::<Mersenne31Complex>();
                let v_el_ptr = v_ptr.add(2*N).cast::<Mersenne31Complex>();

                let u = u_el_ptr.read();
                let v = v_el_ptr.read();

                let mut add_res = u;
                let mut sub_res = u;

                add_res.add_assign(&v);
                u_el_ptr.write(add_res);

                sub_res.sub_assign(&v);
                sub_res.mul_assign(&twiddle);

                v_el_ptr.write(sub_res);
            });
        }

        #[cfg(not(target_arch = "aarch64"))]
        {
            debug_assert!(num_remainder_passes <= 3);

            debug_assert_eq!(CACHE_LINE_MULTIPLE * 4, unroll_stage_offset);
            debug_assert_eq!(CACHE_LINE_MULTIPLE, 16);
            for _ in 0..num_remainder_passes {
                let u_ptr_next = u_ptr.add(CACHE_LINE_MULTIPLE);
                let v_ptr_next = v_ptr.add(CACHE_LINE_MULTIPLE);
                prefetch_next_line(u_ptr_next);
                prefetch_next_line(v_ptr_next);

                seq!(N in 0..8 {
                    let u_el_ptr = u_ptr.add(2*N).cast::<Mersenne31Complex>();
                    let v_el_ptr = v_ptr.add(2*N).cast::<Mersenne31Complex>();

                    let u = u_el_ptr.read();
                    let v = v_el_ptr.read();

                    let mut add_res = u;
                    let mut sub_res = u;

                    add_res.add_assign(&v);
                    sub_res.sub_assign(&v);
                    sub_res.mul_assign(&twiddle);

                    u_el_ptr.write(add_res);
                    v_el_ptr.write(sub_res);
                });

                u_ptr = u_ptr_next;
                v_ptr = v_ptr_next;
            }
        }
    }
}

#[inline(always)]
unsafe fn ifft_inner_loop_logic_scale(
    j: usize,
    distance: usize,
    row_offset: usize,
    num_unrolled_cycles: usize,
    unroll_stage_offset: usize,
    padded_remainder: usize,
    num_remainder_passes: usize,
    ptr: PointerWrapper<Mersenne31Field>,
    scales_ptr: PointerWrapper<Mersenne31Complex>,
) {
    let idx_1 = j;
    let idx_2 = j + distance;

    let u_scale = scales_ptr.0.add(idx_1).read();
    let v_scale = scales_ptr.0.add(idx_2).read();

    let mut u_ptr = ptr.0.add(row_offset * idx_1);
    let mut v_ptr = ptr.0.add(row_offset * idx_2);

    #[cfg(target_arch = "aarch64")]
    {
        prefetch_next_line(u_ptr);
        prefetch_next_line(v_ptr);
        prefetch_next_line(u_ptr.add(CACHE_LINE_MULTIPLE));
        prefetch_next_line(v_ptr.add(CACHE_LINE_MULTIPLE));
    }

    for cycle in 0..num_unrolled_cycles {
        let _last_cycle = cycle == num_unrolled_cycles - 1;
        // prefetch next while we work here
        let u_ptr_next = u_ptr.add(unroll_stage_offset);
        let v_ptr_next = v_ptr.add(unroll_stage_offset);

        #[cfg(target_arch = "aarch64")]
        {
            debug_assert_eq!(CACHE_LINE_MULTIPLE * 2, unroll_stage_offset);
            prefetch_next_line(u_ptr_next);
            prefetch_next_line(v_ptr_next);
            if _last_cycle == false {
                prefetch_next_line(u_ptr_next.add(CACHE_LINE_MULTIPLE));
                prefetch_next_line(v_ptr_next.add(CACHE_LINE_MULTIPLE));
            }
        }

        // to have it in front of us here
        debug_assert_eq!(unroll_stage_offset, 64);

        seq!(N in 0..32 {
            let u_el_ptr = u_ptr.add(2*N).cast::<Mersenne31Complex>();
            let v_el_ptr = v_ptr.add(2*N).cast::<Mersenne31Complex>();

            let mut u = u_el_ptr.read();
            u.mul_assign(&u_scale);
            let mut v = v_el_ptr.read();
            v.mul_assign(&v_scale);

            let mut add_res = u;
            let mut sub_res = u;

            add_res.add_assign(&v);
            u_el_ptr.write(add_res);

            sub_res.sub_assign(&v);
            v_el_ptr.write(sub_res);
        });

        u_ptr = u_ptr_next;
        v_ptr = v_ptr_next;
    }

    if padded_remainder != 0 {
        debug_assert_eq!(padded_remainder % CACHE_LINE_MULTIPLE, 0);

        #[cfg(target_arch = "aarch64")]
        {
            debug_assert_eq!(CACHE_LINE_MULTIPLE * 2, unroll_stage_offset);
            debug_assert_eq!(CACHE_LINE_MULTIPLE, 32);
            debug_assert_eq!(num_remainder_passes, 1);

            seq!(N in 0..16 {
                let u_el_ptr = u_ptr.add(2*N).cast::<Mersenne31Complex>();
                let v_el_ptr = v_ptr.add(2*N).cast::<Mersenne31Complex>();

                let mut u = u_el_ptr.read();
                u.mul_assign(&u_scale);
                let mut v = v_el_ptr.read();
                v.mul_assign(&v_scale);

                let mut add_res = u;
                let mut sub_res = u;

                add_res.add_assign(&v);
                u_el_ptr.write(add_res);

                sub_res.sub_assign(&v);
                v_el_ptr.write(sub_res);
            });
        }

        #[cfg(not(target_arch = "aarch64"))]
        {
            debug_assert!(num_remainder_passes <= 3);

            debug_assert_eq!(CACHE_LINE_MULTIPLE * 4, unroll_stage_offset);
            debug_assert_eq!(CACHE_LINE_MULTIPLE, 16);
            for _ in 0..num_remainder_passes {
                let u_ptr_next = u_ptr.add(CACHE_LINE_MULTIPLE);
                let v_ptr_next = v_ptr.add(CACHE_LINE_MULTIPLE);
                prefetch_next_line(u_ptr_next);
                prefetch_next_line(v_ptr_next);

                seq!(N in 0..8 {
                    let u_el_ptr = u_ptr.add(2*N).cast::<Mersenne31Complex>();
                    let v_el_ptr = v_ptr.add(2*N).cast::<Mersenne31Complex>();

                    let mut u = u_el_ptr.read();
                    u.mul_assign(&u_scale);
                    let mut v = v_el_ptr.read();
                    v.mul_assign(&v_scale);

                    let mut add_res = u;
                    let mut sub_res = u;
                    add_res.add_assign(&v);
                    sub_res.sub_assign(&v);

                    u_el_ptr.write(add_res);
                    v_el_ptr.write(sub_res);
                });

                u_ptr = u_ptr_next;
                v_ptr = v_ptr_next;
            }
        }
    }
}

#[inline(always)]
unsafe fn ifft_inner_loop_logic_twiddle(
    j: usize,
    distance: usize,
    row_offset: usize,
    num_unrolled_cycles: usize,
    unroll_stage_offset: usize,
    padded_remainder: usize,
    num_remainder_passes: usize,
    ptr: PointerWrapper<Mersenne31Field>,
    twiddle: Mersenne31Complex,
) {
    let idx_1 = j;
    let idx_2 = j + distance;

    let mut u_ptr = ptr.0.add(row_offset * idx_1);
    let mut v_ptr = ptr.0.add(row_offset * idx_2);

    #[cfg(target_arch = "aarch64")]
    {
        prefetch_next_line(u_ptr);
        prefetch_next_line(v_ptr);
        prefetch_next_line(u_ptr.add(CACHE_LINE_MULTIPLE));
        prefetch_next_line(v_ptr.add(CACHE_LINE_MULTIPLE));
    }

    for cycle in 0..num_unrolled_cycles {
        let _last_cycle = cycle == num_unrolled_cycles - 1;
        // prefetch next while we work here
        let u_ptr_next = u_ptr.add(unroll_stage_offset);
        let v_ptr_next = v_ptr.add(unroll_stage_offset);

        #[cfg(target_arch = "aarch64")]
        {
            debug_assert_eq!(CACHE_LINE_MULTIPLE * 2, unroll_stage_offset);
            prefetch_next_line(u_ptr_next);
            prefetch_next_line(v_ptr_next);
            if _last_cycle == false {
                prefetch_next_line(u_ptr_next.add(CACHE_LINE_MULTIPLE));
                prefetch_next_line(v_ptr_next.add(CACHE_LINE_MULTIPLE));
            }
        }

        // to have it in front of us here
        debug_assert_eq!(unroll_stage_offset, 64);

        seq!(N in 0..32 {
            let u_el_ptr = u_ptr.add(2*N).cast::<Mersenne31Complex>();
            let v_el_ptr = v_ptr.add(2*N).cast::<Mersenne31Complex>();

            let mut v = v_el_ptr.read();
            v.mul_assign(&twiddle);

            let u = u_el_ptr.read();

            let mut add_res = u;
            let mut sub_res = u;

            add_res.add_assign(&v);
            u_el_ptr.write(add_res);

            sub_res.sub_assign(&v);
            v_el_ptr.write(sub_res);
        });

        u_ptr = u_ptr_next;
        v_ptr = v_ptr_next;
    }

    if padded_remainder != 0 {
        debug_assert_eq!(padded_remainder % CACHE_LINE_MULTIPLE, 0);

        #[cfg(target_arch = "aarch64")]
        {
            debug_assert_eq!(CACHE_LINE_MULTIPLE * 2, unroll_stage_offset);
            debug_assert_eq!(CACHE_LINE_MULTIPLE, 32);
            debug_assert_eq!(num_remainder_passes, 1);

            seq!(N in 0..16 {
                let u_el_ptr = u_ptr.add(2*N).cast::<Mersenne31Complex>();
                let v_el_ptr = v_ptr.add(2*N).cast::<Mersenne31Complex>();

                let mut v = v_el_ptr.read();
                v.mul_assign(&twiddle);

                let u = u_el_ptr.read();

                let mut add_res = u;
                let mut sub_res = u;

                add_res.add_assign(&v);
                u_el_ptr.write(add_res);

                sub_res.sub_assign(&v);
                v_el_ptr.write(sub_res);
            });
        }

        #[cfg(not(target_arch = "aarch64"))]
        {
            debug_assert!(num_remainder_passes <= 3);

            debug_assert_eq!(CACHE_LINE_MULTIPLE * 4, unroll_stage_offset);
            debug_assert_eq!(CACHE_LINE_MULTIPLE, 16);
            for _ in 0..num_remainder_passes {
                let u_ptr_next = u_ptr.add(CACHE_LINE_MULTIPLE);
                let v_ptr_next = v_ptr.add(CACHE_LINE_MULTIPLE);
                prefetch_next_line(u_ptr_next);
                prefetch_next_line(v_ptr_next);

                seq!(N in 0..8 {
                    let u_el_ptr = u_ptr.add(2*N).cast::<Mersenne31Complex>();
                    let v_el_ptr = v_ptr.add(2*N).cast::<Mersenne31Complex>();

                    let mut v = v_el_ptr.read();
                    v.mul_assign(&twiddle);

                    let u = u_el_ptr.read();

                    let mut add_res = u;
                    let mut sub_res = u;

                    add_res.add_assign(&v);
                    u_el_ptr.write(add_res);

                    sub_res.sub_assign(&v);
                    v_el_ptr.write(sub_res);
                });

                u_ptr = u_ptr_next;
                v_ptr = v_ptr_next;
            }
        }
    }
}

#[inline(always)]
unsafe fn fft_inner_loop_logic_trivial_twiddle(
    j: usize,
    distance: usize,
    row_offset: usize,
    num_unrolled_cycles: usize,
    unroll_stage_offset: usize,
    padded_remainder: usize,
    num_remainder_passes: usize,
    ptr: PointerWrapper<Mersenne31Field>,
) {
    let idx_1 = j;
    let idx_2 = j + distance;

    let mut u_ptr = ptr.0.add(row_offset * idx_1);
    let mut v_ptr = ptr.0.add(row_offset * idx_2);

    for cycle in 0..num_unrolled_cycles {
        let _last_cycle = cycle == num_unrolled_cycles - 1;
        // prefetch next while we work here
        let u_ptr_next = u_ptr.add(unroll_stage_offset);
        let v_ptr_next = v_ptr.add(unroll_stage_offset);

        #[cfg(target_arch = "aarch64")]
        {
            debug_assert_eq!(CACHE_LINE_MULTIPLE * 2, unroll_stage_offset);
            prefetch_next_line(u_ptr_next);
            prefetch_next_line(v_ptr_next);
            if _last_cycle == false {
                prefetch_next_line(u_ptr_next.add(CACHE_LINE_MULTIPLE));
                prefetch_next_line(v_ptr_next.add(CACHE_LINE_MULTIPLE));
            }
        }

        // to have it in front of us here
        debug_assert_eq!(unroll_stage_offset, 64);

        seq!(N in 0..64 {
            let u_el_ptr = u_ptr.add(N);
            let v_el_ptr = v_ptr.add(N);

            let u = u_el_ptr.read();
            let v = v_el_ptr.read();

            let mut add_res = u;
            let mut sub_res = u;
            add_res.add_assign(&v);
            u_el_ptr.write(add_res);

            sub_res.sub_assign(&v);
            v_el_ptr.write(sub_res);
        });

        u_ptr = u_ptr_next;
        v_ptr = v_ptr_next;
    }

    if padded_remainder != 0 {
        debug_assert_eq!(padded_remainder % CACHE_LINE_MULTIPLE, 0);

        #[cfg(target_arch = "aarch64")]
        {
            debug_assert_eq!(CACHE_LINE_MULTIPLE * 2, unroll_stage_offset);
            debug_assert_eq!(CACHE_LINE_MULTIPLE, 32);
            debug_assert_eq!(num_remainder_passes, 1);

            seq!(N in 0..32 {
                let u_el_ptr = u_ptr.add(N);
                let v_el_ptr = v_ptr.add(N);

                let u = u_el_ptr.read();
                let v = v_el_ptr.read();

                let mut add_res = u;
                let mut sub_res = u;
                add_res.add_assign(&v);
                u_el_ptr.write(add_res);

                sub_res.sub_assign(&v);
                v_el_ptr.write(sub_res);
            });
        }

        #[cfg(not(target_arch = "aarch64"))]
        {
            debug_assert!(num_remainder_passes <= 3);

            debug_assert_eq!(CACHE_LINE_MULTIPLE * 4, unroll_stage_offset);
            debug_assert_eq!(CACHE_LINE_MULTIPLE, 16);
            for _ in 0..num_remainder_passes {
                let u_ptr_next = u_ptr.add(CACHE_LINE_MULTIPLE);
                let v_ptr_next = v_ptr.add(CACHE_LINE_MULTIPLE);
                prefetch_next_line(u_ptr_next);
                prefetch_next_line(u_ptr_next);

                seq!(N in 0..16 {
                    let u_el_ptr = u_ptr.add(N);
                    let v_el_ptr = v_ptr.add(N);

                    let u = u_el_ptr.read();
                    let v = v_el_ptr.read();

                    let mut add_res = u;
                    let mut sub_res = u;
                    add_res.add_assign(&v);
                    sub_res.sub_assign(&v);

                    u_el_ptr.write(add_res);
                    v_el_ptr.write(sub_res);
                });

                u_ptr = u_ptr_next;
                v_ptr = v_ptr_next;
            }
        }
    }
}
