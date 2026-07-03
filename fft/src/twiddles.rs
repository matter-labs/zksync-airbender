// this file implements all auxiliary routines required for FFT as well as basic radix_2_implementations
use ::field::*;
use worker::Worker;

use crate::field_utils::*;
use crate::utils::*;
use crate::GoodAllocator;

pub fn precompute_twiddles_for_fft<E: TwoAdicField, A: GoodAllocator, const INVERSED: bool>(
    fft_size: usize,
    worker: &Worker,
) -> Vec<E, A> {
    debug_assert!(fft_size.is_power_of_two());

    let mut omega = domain_generator_for_size::<E>(fft_size as u64);
    if INVERSED {
        omega = omega
            .inverse()
            .expect("must always exist for domain generator");
    }

    // assert_eq!(omega.pow(fft_size as u32), E::ONE);
    // for i in 1..fft_size {
    //     assert_ne!(omega.pow(i as u32), E::ONE);
    // }

    // NB: number of omegas is twice lesss than the number of elements in the original domain
    let num_powers = fft_size / 2;
    let mut powers = materialize_powers_parallel_starting_with_one(omega, num_powers, &worker);
    // NB: all twiddles go in bitreversed order
    bitreverse_enumeration_inplace(&mut powers);

    powers
}

pub fn precompute_all_twiddles_for_fft_serial<
    E: TwoAdicField,
    A: GoodAllocator,
    const INVERSED: bool,
>(
    fft_size: usize,
) -> Vec<E, A> {
    debug_assert!(fft_size.is_power_of_two());

    let mut omega = domain_generator_for_size::<E>(fft_size as u64);
    if INVERSED {
        omega = omega
            .inverse()
            .expect("must always exist for domain generator");
    }

    assert_eq!(omega.pow(fft_size as u32), E::ONE);
    // for i in 1..fft_size {
    //     assert_ne!(omega.pow(i as u32), E::ONE);
    // }

    // NB: number of omegas is twice lesss than the number of elements in the original domain
    let num_powers = fft_size / 2;
    let mut powers = materialize_powers_serial_starting_with_one(omega, num_powers);
    // NB: all twiddles go in bitreversed order
    bitreverse_enumeration_inplace(&mut powers);

    powers
}

pub fn precompute_forward_twiddles_for_fft<E: TwoAdicField, A: GoodAllocator>(
    domain_size: usize,
    worker: &Worker,
) -> Vec<E, A> {
    precompute_twiddles_for_fft::<E, A, false>(domain_size, worker)
}

pub fn precompute_inverse_twiddles_for_fft<E: TwoAdicField, A: GoodAllocator>(
    domain_size: usize,
    worker: &Worker,
) -> Vec<E, A> {
    precompute_twiddles_for_fft::<E, A, true>(domain_size, worker)
}

// Twiddles are agnostic to domains, as we will use separate precomputations to distribute powers
// in a bitreversed manners
#[derive(Clone)]
pub struct Twiddles<E: TwoAdicField, A: GoodAllocator> {
    // Bitreversed
    pub forward_twiddles: Vec<E, A>,
    pub forward_twiddles_not_bitreversed: Vec<E, A>,
    // Bitreversed
    pub inverse_twiddles: Vec<E, A>,
    pub omega: E,
    pub omega_inv: E,
    pub domain_size: usize,
}

impl<E: TwoAdicField, A: GoodAllocator> Twiddles<E, A> {
    pub fn new(domain_size: usize, worker: &Worker) -> Self {
        let omega = domain_generator_for_size::<E>(domain_size as u64);

        assert_eq!(omega.pow(domain_size as u32), E::ONE);

        let omega_inv = omega.inverse().unwrap();

        let forward_twiddles = precompute_forward_twiddles_for_fft(domain_size, worker);
        let mut forward_twiddles_not_bitreversed = forward_twiddles.clone();
        bitreverse_enumeration_inplace(&mut forward_twiddles_not_bitreversed);

        Twiddles {
            forward_twiddles,
            inverse_twiddles: precompute_inverse_twiddles_for_fft(domain_size, worker),
            forward_twiddles_not_bitreversed,
            omega,
            omega_inv,
            domain_size,
        }
    }
}

impl<E: TwoAdicField, A: GoodAllocator + 'static> Twiddles<E, A> {
    pub fn get(domain_size: usize, worker: &Worker) -> std::sync::Arc<Self> {
        use std::collections::HashMap;
        use std::sync::{Arc, LazyLock, Mutex};
        use type_map::concurrent::TypeMap;
        static CACHE: LazyLock<Mutex<TypeMap>> = LazyLock::new(|| Mutex::new(TypeMap::default()));
        let mut guard = CACHE.lock().unwrap();
        let map = guard
            .entry()
            .or_insert_with(HashMap::<usize, Arc<Self>>::new);
        let entry = map
            .entry(domain_size)
            .or_insert_with(|| Arc::new(Self::new(domain_size, worker)));
        entry.clone()
    }
}
