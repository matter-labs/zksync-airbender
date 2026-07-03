use crate::field_utils::*;
use crate::utils::*;
use ::field::*;
use worker::Worker;

// usually used to get bitreversed evaluation form from the monomial one
pub fn fft_natural_to_bitreversed<F: Field, E: Field + FieldExtension<F>>(
    input: &mut [E],
    coset_initial: F,
    coset_step: F,
    twiddles: &[F],
) {
    debug_assert!(input.len().is_power_of_two());
    debug_assert!(input.len() == twiddles.len() * 2);

    if coset_initial != F::ONE || coset_step != F::ONE {
        distribute_powers_serial(input, coset_initial, coset_step);
    }

    let log_n = input.len().trailing_zeros();
    cache_friendly_ntt_natural_to_bitreversed(input, log_n, twiddles);
}

pub fn fft_natural_to_natural<F: Field, E: Field + FieldExtension<F>>(
    input: &mut [E],
    coset_initial: F,
    coset_step: F,
    twiddles: &[F],
) {
    debug_assert!(input.len().is_power_of_two());
    debug_assert!(input.len() == twiddles.len() * 2);

    if coset_initial != F::ONE || coset_step != F::ONE {
        distribute_powers_serial(input, coset_initial, coset_step);
    }

    let log_n = input.len().trailing_zeros();
    cache_friendly_ntt_natural_to_bitreversed(input, log_n, twiddles);
    bitreverse_enumeration_inplace(input);
}

// usually used to get monomial from natural bitreversed evaluation
pub fn ifft_natural_to_natural<
    P: PrimeField,
    F: Field,
    E: Field + FieldExtension<P> + FieldExtension<F>,
>(
    input: &mut [E],
    coset: F,
    twiddles: &[F],
) {
    debug_assert!(input.len().is_power_of_two());
    debug_assert!(input.len() == twiddles.len() * 2);

    let log_n = input.len().trailing_zeros();
    serial_ct_ntt_natural_to_bitreversed(input, log_n, twiddles);
    bitreverse_enumeration_inplace(input);

    if coset != F::ONE {
        let coset = coset.inverse().expect("inverse of coset must exist");
        distribute_powers_serial(input, F::ONE, coset);
    }

    if input.len() > 1 {
        let n_inv = P::from_u32_with_reduction(input.len() as u32)
            .inverse()
            .unwrap();
        let mut i = 0;
        let work_size = input.len();
        while i < work_size {
            input[i].mul_assign_by_base(&n_inv);
            i += 1;
        }
    }
}

// usually used to get monomial from natural bitreversed evaluation
pub fn partial_ifft_natural_to_natural<F: Field>(input: &mut [F], coset: F, twiddles: &[F]) {
    debug_assert!(input.len().is_power_of_two());
    debug_assert!(input.len() == twiddles.len() * 2);

    let log_n = input.len().trailing_zeros();
    serial_ct_ntt_natural_to_bitreversed(input, log_n, twiddles);
    bitreverse_enumeration_inplace(input);

    if coset != F::ONE {
        let coset = coset.inverse().expect("inverse of coset must exist");
        distribute_powers_serial(input, F::ONE, coset);
    }
}

pub fn serial_ct_ntt_natural_to_bitreversed<F: Field, E: Field + FieldExtension<F>>(
    a: &mut [E],
    log_n: u32,
    omegas_bit_reversed: &[F],
) {
    let n = a.len();
    if n == 1 {
        return;
    }

    if a.len() > 16 {
        debug_assert!(n == omegas_bit_reversed.len() * 2);
    }
    debug_assert!(n == (1 << log_n) as usize);

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
            let u = a[j];
            let v = a[j + distance];

            let mut tmp = u;
            tmp.sub_assign(&v);

            a[j + distance] = tmp;
            a[j].add_assign(&v);

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
            let s = omegas_bit_reversed[k];

            let mut j = idx_1;
            while j < idx_2 {
                let u = a[j];
                let mut v = a[j + distance];
                v.mul_assign_by_base(&s);

                let mut tmp = u;
                tmp.sub_assign(&v);

                a[j + distance] = tmp;
                a[j].add_assign(&v);

                j += 1;
            }

            k += 1;
        }

        pairs_per_group /= 2;
        num_groups *= 2;
        distance /= 2;
    }
}

pub fn serial_ct_ntt_bitreversed_to_natural<F: Field, E: Field + FieldExtension<F>>(
    a: &mut [E],
    log_n: u32,
    omegas_bit_reversed: &[F],
) {
    let n = a.len();
    if n == 1 {
        return;
    }

    if a.len() > 16 {
        debug_assert_eq!(n, omegas_bit_reversed.len() * 2);
    }
    debug_assert!(n == (1 << log_n) as usize);

    let mut pairs_per_group = 1;
    let mut num_groups = n / 2;
    let mut distance = 1;

    while num_groups > 1 {
        // println!("num_groups: {:?}", num_groups);
        debug_assert!(num_groups > 1);
        let mut k = 0;
        while k < num_groups {
            let idx_1 = k * pairs_per_group * 2;
            let idx_2 = idx_1 + pairs_per_group;
            let s = omegas_bit_reversed[k];

            let mut j = idx_1;
            while j < idx_2 {
                let u = a[j];
                let v = a[j + distance];

                let mut tmp = u;
                tmp.sub_assign(&v);
                tmp.mul_assign_by_base(&s);

                a[j + distance] = tmp;
                a[j].add_assign(&v);

                j += 1;
            }

            k += 1;
        }

        pairs_per_group *= 2;
        num_groups /= 2;
        distance *= 2;
    }

    {
        // special case for omega = 1
        debug_assert!(num_groups == 1);
        let idx_1 = 0;
        let idx_2 = pairs_per_group;

        let mut j = idx_1;

        while j < idx_2 {
            let u = a[j];
            let v = a[j + distance];

            let mut tmp = u;
            tmp.sub_assign(&v);

            a[j + distance] = tmp;
            a[j].add_assign(&v);

            j += 1;
        }
    }
}

/// Worker-parallel counterpart of [`serial_ct_ntt_bitreversed_to_natural`].
///
/// Within one NTT stage the `n/2` butterflies touch pairwise-disjoint index pairs
/// `(j, j + distance)`, so each stage is distributed across the worker; stages run
/// sequentially (stage `s+1` reads stage `s`). The per-butterfly arithmetic is
/// identical to the serial routine, so the result is bit-for-bit the same.
pub fn parallel_ct_ntt_bitreversed_to_natural<F: Field, E: Field + FieldExtension<F>>(
    a: &mut [E],
    log_n: u32,
    omegas_bit_reversed: &[F],
    worker: &Worker,
) {
    let n = a.len();
    if n <= 1 {
        return;
    }
    debug_assert!(n == (1 << log_n) as usize);
    if n > 16 {
        debug_assert_eq!(n, omegas_bit_reversed.len() * 2);
    }

    // Small transforms: the per-stage scope overhead dominates, so stay serial.
    const PAR_THRESHOLD: usize = 1 << 12;
    let eff_threshold = PAR_THRESHOLD / (core::mem::size_of::<E>() / core::mem::size_of::<u32>());
    if n < eff_threshold {
        serial_ct_ntt_bitreversed_to_natural(a, log_n, omegas_bit_reversed);
        return;
    }

    // Each butterfly writes a disjoint pair, so threads can share the buffer. Pass
    // the base address as a `usize` (Send) and reconstruct the pointer per thread —
    // the same pattern the column-major LDE uses.
    let base_addr = a.as_mut_ptr() as usize;
    let half = n / 2;

    let mut pairs_per_group = 1usize;
    let mut num_groups = n / 2;

    // Stages with a per-group twiddle (num_groups > 1).
    while num_groups > 1 {
        let ppg = pairs_per_group;
        let ppg_log = ppg.trailing_zeros();
        let omegas = omegas_bit_reversed;
        worker.scope(half, |scope, geometry| {
            for thread_idx in 0..geometry.len() {
                let start = geometry.get_chunk_start_pos(thread_idx);
                let size = geometry.get_chunk_size(thread_idx);
                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let base = base_addr as *mut E;
                    for b in start..(start + size) {
                        // flat butterfly index -> (group k, in-group offset jj)
                        let k = b >> ppg_log;
                        let jj = b & (ppg - 1);
                        let j = k * (ppg << 1) + jj;
                        let s = omegas[k];
                        unsafe {
                            let u = *base.add(j);
                            let v = *base.add(j + ppg);
                            let mut tmp = u;
                            tmp.sub_assign(&v);
                            tmp.mul_assign_by_base(&s);
                            *base.add(j + ppg) = tmp;
                            let mut uu = u;
                            uu.add_assign(&v);
                            *base.add(j) = uu;
                        }
                    }
                });
            }
        });
        pairs_per_group *= 2;
        num_groups /= 2;
    }

    // Final stage (num_groups == 1, omega == 1): butterflies a[j], a[j + half].
    debug_assert_eq!(num_groups, 1);
    debug_assert_eq!(pairs_per_group, half);
    worker.scope(half, |scope, geometry| {
        for thread_idx in 0..geometry.len() {
            let start = geometry.get_chunk_start_pos(thread_idx);
            let size = geometry.get_chunk_size(thread_idx);
            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                let base = base_addr as *mut E;
                for j in start..(start + size) {
                    unsafe {
                        let u = *base.add(j);
                        let v = *base.add(j + half);
                        let mut tmp = u;
                        tmp.sub_assign(&v);
                        *base.add(j + half) = tmp;
                        let mut uu = u;
                        uu.add_assign(&v);
                        *base.add(j) = uu;
                    }
                }
            });
        }
    });
}

pub fn cache_friendly_ntt_natural_to_bitreversed<F: Field, E: Field + FieldExtension<F>>(
    a: &mut [E],
    log_n: u32,
    omegas_bit_reversed: &[F],
) {
    let n = a.len();
    if n == 1 {
        return;
    }

    // const CACHE_SIZE_LOG: u32 = 20; // 1 MB
    const CACHE_SIZE_LOG: u32 = 20; // 1 MB

    const WORD_SIZE_LOG: u32 = 3; // 8 B
    const CACHE_BUNCH_LOG: u32 = CACHE_SIZE_LOG - WORD_SIZE_LOG; // 2^17 B
    let cache_friendly_round = log_n.saturating_sub(CACHE_BUNCH_LOG); // 7 round

    if a.len() > 16 {
        debug_assert!(n == omegas_bit_reversed.len() * 2);
    }
    debug_assert!(n == (1 << log_n) as usize);

    let mut pairs_per_group = n / 2;
    let mut num_groups = 1;
    let mut distance = n / 2;
    let mut round = 0;

    {
        // special case for omega = 1
        debug_assert!(num_groups == 1);
        let idx_1 = 0;
        let idx_2 = pairs_per_group;

        let mut j = idx_1;
        while j < idx_2 {
            let mut u = a[j];
            let v = a[j + distance];
            u.sub_assign(&v);
            a[j + distance] = u;
            a[j].add_assign(&v);
            j += 1;
        }
        pairs_per_group /= 2;
        num_groups *= 2;
        distance /= 2;
        round += 1;
    }

    while round < cache_friendly_round {
        debug_assert!(num_groups > 1);
        let mut k = 0;
        while k < num_groups {
            let idx_1 = k * pairs_per_group * 2;
            let idx_2 = idx_1 + pairs_per_group;
            let s = omegas_bit_reversed[k];

            let mut j = idx_1;
            while j < idx_2 {
                let mut u = a[j];
                let mut v = a[j + distance];
                v.mul_assign_by_base(&s);
                u.sub_assign(&v);
                a[j + distance] = u;
                a[j].add_assign(&v);
                j += 1;
            }
            k += 1;
        }

        pairs_per_group /= 2;
        num_groups *= 2;
        distance /= 2;
        round += 1;
    }
    let mut cache_bunch = 0;
    while cache_bunch < num_groups {
        // num_groups=128 // round loop
        let mut pairs_per_group_in_cache = pairs_per_group;
        let mut distance_in_cache = distance;
        let mut num_groups_in_cache = 1;
        let num_rounds_in_cache = log_n - round; // 17

        let mut round = 0;
        while round < num_rounds_in_cache {
            // experiment

            let mut k = 0;
            while k < num_groups_in_cache {
                // group loop
                let idx_1 = cache_bunch * pairs_per_group * 2 + k * pairs_per_group_in_cache * 2;
                let idx_2 = idx_1 + pairs_per_group_in_cache;
                let s = omegas_bit_reversed[cache_bunch * num_groups_in_cache + k];

                let mut j = idx_1;
                while j < idx_2 {
                    let mut u = a[j];
                    let mut v = a[j + distance_in_cache];
                    v.mul_assign_by_base(&s);
                    u.sub_assign(&v);
                    a[j + distance_in_cache] = u;
                    a[j].add_assign(&v);

                    j += 1;
                }
                k += 1;
            }
            pairs_per_group_in_cache /= 2;
            num_groups_in_cache *= 2;
            distance_in_cache /= 2;
            round += 1;
        }
        cache_bunch += 1;
    }
}

#[cfg(test)]
mod parallel_ntt_tests {
    use super::*;
    use crate::twiddles::precompute_forward_twiddles_for_fft;
    use ::field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
    use rand::{rngs::ThreadRng, RngCore};
    use std::alloc::Global;
    use worker::Worker;

    type F = BabyBearField;
    type E = BabyBearExt4;

    fn random_in_ext(rng: &mut ThreadRng) -> E {
        let coefs = [(); <E as FieldExtension<F>>::DEGREE]
            .map(|_| F::from_u32_with_reduction(rng.next_u32()));
        <E as FieldExtension<F>>::from_coeffs(coefs)
    }

    // Above PAR_THRESHOLD the parallel NTT must be bit-identical to the serial one.
    fn check(log_n: u32) {
        let worker = Worker::new_with_num_threads(4);
        let n = 1usize << log_n;
        let omegas = precompute_forward_twiddles_for_fft::<F, Global>(n, &worker);
        assert_eq!(omegas.len(), n / 2);

        let mut rng = rand::rng();
        let input: Vec<E> = (0..n).map(|_| random_in_ext(&mut rng)).collect();

        let mut serial = input.clone();
        serial_ct_ntt_bitreversed_to_natural(&mut serial, log_n, &omegas);

        let mut parallel = input.clone();
        parallel_ct_ntt_bitreversed_to_natural(&mut parallel, log_n, &omegas, &worker);

        assert_eq!(
            serial, parallel,
            "parallel NTT differs from serial at log_n={log_n}"
        );
    }

    #[test]
    fn parallel_matches_serial() {
        // 12 = exactly PAR_THRESHOLD (serial fallback); 13..18 exercise the parallel path.
        for log_n in [12u32, 13, 14, 16, 18] {
            check(log_n);
        }
    }
}
