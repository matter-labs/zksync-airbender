// this file implements all auxiliary routines required for FFT as well as basic radix_2_implementations
use std::alloc::Global;

use ::field::*;
use worker::Worker;

use crate::field_utils::*;
use crate::grinded_fft::utils::bitreversed_transpose;
use crate::radix_4_step::Radix4;
use crate::twiddles::precompute_twiddles;
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
pub struct Twiddles<E: TwoAdicField, A: GoodAllocator> {
    pub forward_twiddles: Vec<E, A>,
    pub forward_twiddles_not_bitreversed: Vec<E, A>,
    pub inverse_twiddles: Vec<E, A>,
    pub omega: E,
    pub omega_inv: E,
    pub domain_size: usize,
    //for grinded fft
    pub grinded_fft_forward_twiddles: Radix4,
    pub grinded_fft_inverse_twiddles: Radix4,
}

impl<E: TwoAdicField, A: GoodAllocator> Twiddles<E, A> {
    pub fn new(domain_size: usize, worker: &Worker) -> Self {
        let omega = domain_generator_for_size::<E>(domain_size as u64);

        assert_eq!(omega.pow(domain_size as u32), E::ONE);

        let omega_inv = omega.inverse().unwrap();

        let forward_twiddles = precompute_forward_twiddles_for_fft(domain_size, worker);
        let mut forward_twiddles_not_bitreversed = forward_twiddles.clone();
        bitreverse_enumeration_inplace(&mut forward_twiddles_not_bitreversed);

        //precomputes for grinded fft
        let (grinded_fft_forward_twiddles, grinded_fft_inverse_twiddles) =
            precompute_twiddles(domain_size);

        Twiddles {
            forward_twiddles,
            inverse_twiddles: precompute_inverse_twiddles_for_fft(domain_size, worker),
            forward_twiddles_not_bitreversed,
            omega,
            omega_inv,
            domain_size,
            grinded_fft_forward_twiddles,
            grinded_fft_inverse_twiddles,
        }
    }
}

// All our FFTs are natural ordered values -> bitreversed unscaled monomials -> natural ordered values in other coset,
// so we put scaling by 1/N and multiplication by powers of coset offset to the second FFT
pub struct DomainBoundLdePrecomputations<A: GoodAllocator> {
    pub bitreversed_powers: Vec<Vec<Mersenne31Complex, A>>,
    pub taus: Vec<Mersenne31Complex>,
    pub domain_size: usize,
    pub domain_coset_index: usize,
    pub lde_factor: usize,
    pub coset_offset: Mersenne31Complex,
    //for grinded fft
    pub bitreversed_powers_transposed: Vec<Vec<Mersenne31Complex, A>>,
}

impl<A: GoodAllocator> DomainBoundLdePrecomputations<A> {
    pub fn new(
        source_domain_natural_index: usize,
        domain_size: usize,
        lde_factor: usize,
        worker: &Worker,
    ) -> Self {
        assert!(source_domain_natural_index < lde_factor);

        assert!(lde_factor > 1);
        assert!(lde_factor.is_power_of_two());
        let tau_order = domain_size * lde_factor;
        assert!(tau_order <= Mersenne31Complex::two_adic_group_order());

        let tau = domain_generator_for_size::<Mersenne31Complex>(tau_order as u64);
        let omega = domain_generator_for_size::<Mersenne31Complex>(domain_size as u64);

        assert_eq!(tau.pow(tau_order as u32), Mersenne31Complex::ONE);
        assert_eq!(omega.pow(domain_size as u32), Mersenne31Complex::ONE);

        assert_ne!(tau, omega);
        assert_eq!(omega, tau.pow(lde_factor as u32));

        // now all polys are in the Monomial form, so let's LDE them
        let coset_generators = materialize_powers_serial_starting_with_one::<
            Mersenne31Complex,
            Global,
        >(tau, lde_factor);

        let ifft_merged_scale = Mersenne31Complex::from_base(Mersenne31Field(domain_size as u32));
        let ifft_merged_scale = ifft_merged_scale.inverse().unwrap();

        let mut bitreversed_powers = Vec::with_capacity(lde_factor);
        let mut bitreversed_powers_transposed = Vec::with_capacity(lde_factor);

        let coset_offset = coset_generators[source_domain_natural_index];
        let normalization_factor_from_source_domain = coset_offset.inverse().unwrap();

        for (idx, tau) in coset_generators.iter().enumerate() {
            if idx == source_domain_natural_index {
                let mut tmp = *tau;
                tmp.mul_assign(&normalization_factor_from_source_domain);
                assert_eq!(tmp, Mersenne31Complex::ONE);

                // we just need to scale by 1/N
                let scale = ifft_merged_scale;
                let mut powers = Vec::with_capacity_in(domain_size, A::default());
                powers.resize(domain_size, scale);
                bitreversed_powers.push(powers.clone());
                bitreversed_powers_transposed.push(powers);

                // bitreversed_powers.push(Vec::new_in(A::default()));
                continue;
            }

            if idx != 0 {
                let vanishing = tau.pow(domain_size as u32);
                assert_ne!(
                    vanishing,
                    Mersenne31Complex::ONE,
                    "coset made by tau {:?} is vanishing for index {}",
                    tau,
                    idx,
                );
            }

            // if we go from source domain == 0 (main domain), we are always interested not in the FFT per-se,
            // but in the scaled fft (we assume pre-adjusted c0)
            // In case if we go from the larger domain to some other domain, we should not scale, because it's not
            // a part of circle-FFT logc

            let mut scale = if source_domain_natural_index == 0 {
                // we should also scale by tau^-H/2 our outputs to other domain
                tau.pow((domain_size / 2) as u32).inverse().unwrap()
            } else {
                // if our starting domain is not main domain, we most likely do not care about our code being in almost base field
                Mersenne31Complex::ONE
            };
            scale.mul_assign(&ifft_merged_scale);

            let mut step = *tau;
            step.mul_assign(&normalization_factor_from_source_domain);

            let mut powers = materialize_powers_parallel::<_, A>(scale, step, domain_size, &worker);

            //for grinded fft
            let mut powers_transposed = Vec::with_capacity_in(domain_size, A::default());
            unsafe { powers_transposed.set_len(domain_size) }
            if domain_size.trailing_zeros() % 2 == 0 {
                bitreversed_transpose::<Mersenne31Complex, 4>(16, &powers, &mut powers_transposed);
            } else {
                bitreversed_transpose::<Mersenne31Complex, 4>(8, &powers, &mut powers_transposed);
            }
            bitreversed_powers_transposed.push(powers_transposed);

            bitreverse_enumeration_inplace(&mut powers);
            bitreversed_powers.push(powers);
        }

        assert_eq!(bitreversed_powers.len(), lde_factor);

        Self {
            bitreversed_powers,
            taus: coset_generators,
            domain_size,
            domain_coset_index: source_domain_natural_index,
            lde_factor,
            coset_offset,
            bitreversed_powers_transposed,
        }
    }
}

pub struct LdePrecomputations<A: GoodAllocator> {
    pub domain_bound_precomputations: Vec<Option<DomainBoundLdePrecomputations<A>>>,
    pub domain_size: usize,
    pub lde_factor: usize,
}

impl<A: GoodAllocator> LdePrecomputations<A> {
    pub fn new(
        domain_size: usize,
        lde_factor: usize,
        source_cosets: &[usize],
        worker: &Worker,
    ) -> Self {
        let mut domain_bound_precomputations = Vec::with_capacity(lde_factor);
        assert!(source_cosets.is_sorted());

        for coset_index in source_cosets.iter().copied() {
            assert!(coset_index < lde_factor);
            if coset_index < domain_bound_precomputations.len() {
                for _ in domain_bound_precomputations.len()..coset_index {
                    domain_bound_precomputations.push(None);
                }
            }

            assert_eq!(coset_index, domain_bound_precomputations.len());

            let result =
                DomainBoundLdePrecomputations::new(coset_index, domain_size, lde_factor, worker);
            domain_bound_precomputations.push(Some(result));
        }

        assert_eq!(domain_bound_precomputations.len(), source_cosets.len());

        Self {
            domain_bound_precomputations,
            domain_size,
            lde_factor,
        }
    }
}
