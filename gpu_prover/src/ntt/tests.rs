use std::alloc::Global;

use era_cudart::memory::memory_copy;
use fft::field_utils::{distribute_powers_serial, domain_generator_for_size};
use field::Field;
use serial_test::serial;
use worker::Worker;

use super::{bitreversed_coeffs_to_natural_coset, hypercube_evals_natural_to_bitreversed_coeffs};
use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::context::{ProverContext, ProverContextConfig};
use crate::primitives::field::BF;

fn make_context() -> ProverContext {
    let mut config = ProverContextConfig::default();
    config.max_device_allocation_blocks_count = Some(256);
    config.host_allocator_blocks_count = 32;
    ProverContext::new(&config).unwrap()
}

const TEST_LOG_NS: &[usize] = &[1, 2, 3, 4, 5, 6, 8, 10, 12, 14, 16, 18, 20];

#[test]
fn characterize_cpu_hypercube_ordering() {
    use prover::gkr::whir::hypercube_to_monomial::{
        multivariate_coeffs_into_hypercube_evals, multivariate_hypercube_evals_into_coeffs,
    };

    let coeffs = vec![
        BF::new(3),
        BF::new(5),
        BF::new(7),
        BF::new(11),
        BF::new(13),
        BF::new(17),
        BF::new(19),
        BF::new(23),
    ];
    let mut hypercube_evals = coeffs.clone();
    multivariate_coeffs_into_hypercube_evals(&mut hypercube_evals, 3);

    let mut stage1_input_evals = hypercube_evals.clone();
    fft::bitreverse_enumeration_inplace(&mut stage1_input_evals);

    let mut bitreversed_coeffs = coeffs.clone();
    fft::bitreverse_enumeration_inplace(&mut bitreversed_coeffs);

    let mut recovered_bitreversed = stage1_input_evals.clone();
    multivariate_hypercube_evals_into_coeffs(&mut recovered_bitreversed, 3);
    assert_eq!(recovered_bitreversed, bitreversed_coeffs);

    let mut recovered_natural = stage1_input_evals;
    fft::bitreverse_enumeration_inplace(&mut recovered_natural);
    multivariate_hypercube_evals_into_coeffs(&mut recovered_natural, 3);
    assert_eq!(recovered_natural, coeffs);
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn hypercube_evals_natural_to_bitreversed_coeffs_matches_cpu() {
    let context = make_context();
    let stream = context.get_exec_stream();

    for &log_n in TEST_LOG_NS {
        use prover::gkr::whir::hypercube_to_monomial::multivariate_hypercube_evals_into_coeffs;

        let n = 1usize << log_n;
        let evals = (0..n)
            .map(|idx| BF::new((17 + idx * 13) as u32))
            .collect::<Vec<_>>();
        let mut expected = evals.clone();
        fft::bitreverse_enumeration_inplace(&mut expected);
        multivariate_hypercube_evals_into_coeffs(&mut expected, log_n as u32);
        fft::bitreverse_enumeration_inplace(&mut expected);

        let mut src = context.alloc(n, AllocationPlacement::BestFit).unwrap();
        let mut dst = context.alloc(n, AllocationPlacement::BestFit).unwrap();
        memory_copy(&mut src, &evals).unwrap();
        hypercube_evals_natural_to_bitreversed_coeffs(&src, &mut dst, log_n, stream).unwrap();

        let mut actual = vec![BF::ZERO; n];
        memory_copy(&mut actual, &dst).unwrap();
        assert_eq!(actual, expected, "log_n={}", log_n);
    }
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn bitreversed_coeffs_to_natural_coset_matches_cpu() {
    let worker = Worker::new();
    let context = make_context();
    let stream = context.get_exec_stream();

    for &log_n in TEST_LOG_NS {
        let n = 1usize << log_n;
        let twiddles = fft::Twiddles::<BF, Global>::new(n, &worker);
        let selected_twiddles = &twiddles.forward_twiddles[..(n >> 1)];
        let coeffs_natural = (0..n)
            .map(|idx| BF::new((5 + idx * 19) as u32))
            .collect::<Vec<_>>();
        let mut coeffs_bitreversed = coeffs_natural.clone();
        fft::bitreverse_enumeration_inplace(&mut coeffs_bitreversed);

        let mut src = context.alloc(n, AllocationPlacement::BestFit).unwrap();
        let mut dst = context.alloc(n, AllocationPlacement::BestFit).unwrap();
        memory_copy(&mut src, &coeffs_bitreversed).unwrap();

        for log_lde_factor in [1usize, 2, 3] {
            let tau = domain_generator_for_size::<BF>(1u64 << (log_n + log_lde_factor));
            for coset_index in 0..(1usize << log_lde_factor) {
                bitreversed_coeffs_to_natural_coset(
                    &src,
                    &mut dst,
                    log_n,
                    log_lde_factor,
                    coset_index,
                    stream,
                )
                .unwrap();

                let mut actual = vec![BF::ZERO; n];
                memory_copy(&mut actual, &dst).unwrap();

                let mut expected = coeffs_natural.clone();
                if coset_index != 0 {
                    distribute_powers_serial(&mut expected, BF::ONE, tau.pow(coset_index as u32));
                }
                fft::bitreverse_enumeration_inplace(&mut expected);
                fft::naive::serial_ct_ntt_bitreversed_to_natural(
                    &mut expected,
                    log_n as u32,
                    selected_twiddles,
                );

                assert_eq!(
                    actual, expected,
                    "log_n={}, log_lde_factor={}, coset_index={}",
                    log_n, log_lde_factor, coset_index
                );
            }
        }
    }
}
