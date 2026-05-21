use std::alloc::Global;

use era_cudart::memory::memory_copy_async;
use fft::field_utils::{distribute_powers_serial, domain_generator_for_size};

use serial_test::serial;
use worker::Worker;

use super::{
    bitreversed_coeffs_to_natural_coset, hypercube_coeffs_natural_to_natural_evals,
    hypercube_evals_natural_to_bitreversed_coeffs, natural_evals_to_bitreversed_coeffs,
    transpose_monomials_naive,
};
use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::context::{ProverContext, ProverContextConfig};
use crate::primitives::field::BF;

fn make_context() -> ProverContext {
    let mut config = ProverContextConfig::default();
    // 8 GB device arena (8192 × 1 MB blocks). The heaviest NTT tests run
    // multi-pass at log_n=24 over E4 (16 B/element) — a single buffer is
    // 256 MB and the tests hold several at a time. 8 GB leaves comfortable
    // headroom without claiming half the GPU.
    config.max_device_allocation_blocks_count = Some(8 * 1024);
    // 32 MB host pool: with 8 KB blocks this is 4096 blocks
    let host_block_size = 1usize << config.host_allocator_block_log_size;
    config.host_allocator_blocks_count = (32 * 1024 * 1024) / host_block_size;
    ProverContext::new(&config).unwrap()
}

const TEST_LOG_NS: &[usize] = &[1, 2, 3, 4, 5, 6, 8, 10, 12, 14, 16, 18, 20];

#[test]
#[serial]
fn characterize_cpu_hypercube_ordering() {
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

    let mut bitreversed_input_evals = hypercube_evals.clone();
    fft::bitreverse_enumeration_inplace(&mut bitreversed_input_evals);
    let mut bitreversed_coeffs = coeffs.clone();
    fft::bitreverse_enumeration_inplace(&mut bitreversed_coeffs);

    let mut recovered_bitreversed = bitreversed_input_evals.clone();
    multivariate_hypercube_evals_into_coeffs(&mut recovered_bitreversed, 3);
    assert_eq!(recovered_bitreversed, bitreversed_coeffs);

    let mut recovered_natural = bitreversed_input_evals;
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
        memory_copy_async(&mut src, &evals, stream).unwrap();
        hypercube_evals_natural_to_bitreversed_coeffs(&src, &mut dst, log_n, stream).unwrap();

        let mut actual = vec![BF::ZERO; n];
        memory_copy_async(&mut actual, &dst, stream).unwrap();
        stream.synchronize().unwrap();
        assert_eq!(actual, expected, "log_n={}", log_n);
    }
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn hypercube_coeffs_natural_to_natural_evals_matches_cpu() {
    let context = make_context();
    let stream = context.get_exec_stream();

    for &log_n in TEST_LOG_NS {
        let n = 1usize << log_n;
        let coeffs = (0..n)
            .map(|idx| BF::new((29 + idx * 7) as u32))
            .collect::<Vec<_>>();
        let mut expected = coeffs.clone();
        multivariate_coeffs_into_hypercube_evals(&mut expected, log_n as u32);

        let mut src = context.alloc(n, AllocationPlacement::BestFit).unwrap();
        let mut dst = context.alloc(n, AllocationPlacement::BestFit).unwrap();
        memory_copy_async(&mut src, &coeffs, stream).unwrap();
        hypercube_coeffs_natural_to_natural_evals(&src, &mut dst, log_n, stream).unwrap();

        let mut actual = vec![BF::ZERO; n];
        memory_copy_async(&mut actual, &dst, stream).unwrap();
        stream.synchronize().unwrap();
        assert_eq!(actual, expected, "log_n={}", log_n);
    }
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn natural_evals_to_bitreversed_coeffs_matches_cpu() {
    let context = make_context();
    let stream = context.get_exec_stream();

    for &log_n in TEST_LOG_NS {
        let n = 1usize << log_n;
        let evals = (0..n)
            .map(|idx| BF::new((11 + idx * 23) as u32))
            .collect::<Vec<_>>();
        let mut expected = evals.clone();
        fft::naive::cache_friendly_ntt_natural_to_bitreversed(
            &mut expected,
            log_n as u32,
            &fft::Twiddles::<BF, Global>::new(n, &Worker::new()).inverse_twiddles[..],
        );
        let scale = BF::from_u32_unchecked(n as u32).inverse().unwrap();
        for value in expected.iter_mut() {
            value.mul_assign(&scale);
        }

        let mut src = context.alloc(n, AllocationPlacement::BestFit).unwrap();
        let mut dst = context.alloc(n, AllocationPlacement::BestFit).unwrap();
        memory_copy_async(&mut src, &evals, stream).unwrap();
        natural_evals_to_bitreversed_coeffs(&src, &mut dst, log_n, stream).unwrap();

        let mut actual = vec![BF::ZERO; n];
        memory_copy_async(&mut actual, &dst, stream).unwrap();
        stream.synchronize().unwrap();
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
        memory_copy_async(&mut src, &coeffs_bitreversed, stream).unwrap();

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
                memory_copy_async(&mut actual, &dst, stream).unwrap();
                stream.synchronize().unwrap();

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

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn transpose_monomials_naive_matches_cpu() {
    let context = make_context();
    let stream = context.get_exec_stream();

    for &log_n in &[10usize, 12, 14] {
        let n = 1usize << log_n;
        let mut expected = (0..n)
            .map(|idx| BF::new((37 + idx * 31) as u32))
            .collect::<Vec<_>>();
        let mut actual = expected.clone();
        transpose_monomials(&mut expected);

        let mut values = context.alloc(n, AllocationPlacement::BestFit).unwrap();
        memory_copy_async(&mut values, &actual, stream).unwrap();
        transpose_monomials_naive(&mut values, log_n, stream).unwrap();
        memory_copy_async(&mut actual, &values, stream).unwrap();
        stream.synchronize().unwrap();

        assert_eq!(actual, expected, "log_n={}", log_n);
    }
}

const TEST_LOG_LDE_FACTOR: usize = 2;
const TEST_COSET_INDEX: usize = 1;

#[derive(PartialEq)]
enum InOrOutOfPlace {
    In,
    Out,
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn test_hypercube_evals_to_monomials_2_pass_out_of_place() {
    run_evals_to_monomials(
        23..25,
        4,
        wrap_hypercube_evals_to_monomials_2_pass,
        hypercube_evals_to_monomials_cpu_fn,
        InOrOutOfPlace::Out,
        false,
    );
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn test_hypercube_evals_to_monomials_2_pass_in_place() {
    run_evals_to_monomials(
        23..25,
        4,
        wrap_hypercube_evals_to_monomials_2_pass,
        hypercube_evals_to_monomials_cpu_fn,
        InOrOutOfPlace::In,
        false,
    );
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn test_hypercube_evals_to_monomials_2_pass_transposed_monomials_out_of_place() {
    run_evals_to_monomials(
        23..25,
        4,
        wrap_hypercube_evals_to_monomials_2_pass,
        hypercube_evals_to_monomials_cpu_fn,
        InOrOutOfPlace::Out,
        true,
    );
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn test_hypercube_evals_to_monomials_2_pass_transposed_monomials_in_place() {
    run_evals_to_monomials(
        23..25,
        4,
        wrap_hypercube_evals_to_monomials_2_pass,
        hypercube_evals_to_monomials_cpu_fn,
        InOrOutOfPlace::In,
        true,
    );
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn test_hypercube_evals_to_monomials_3_pass_out_of_place() {
    run_evals_to_monomials(
        21..25,
        4,
        wrap_hypercube_evals_to_monomials_3_pass,
        hypercube_evals_to_monomials_cpu_fn,
        InOrOutOfPlace::Out,
        false,
    );
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn test_hypercube_evals_to_monomials_3_pass_in_place() {
    run_evals_to_monomials(
        21..25,
        4,
        wrap_hypercube_evals_to_monomials_3_pass,
        hypercube_evals_to_monomials_cpu_fn,
        InOrOutOfPlace::In,
        false,
    );
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn test_hypercube_evals_to_monomials_3_pass_transposed_monomials_out_of_place() {
    run_evals_to_monomials(
        21..25,
        4,
        wrap_hypercube_evals_to_monomials_3_pass,
        hypercube_evals_to_monomials_cpu_fn,
        InOrOutOfPlace::Out,
        true,
    );
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn test_hypercube_evals_to_monomials_3_pass_transposed_monomials_in_place() {
    run_evals_to_monomials(
        21..25,
        4,
        wrap_hypercube_evals_to_monomials_3_pass,
        hypercube_evals_to_monomials_cpu_fn,
        InOrOutOfPlace::In,
        true,
    );
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn test_evals_to_monomials_2_pass_out_of_place() {
    run_evals_to_monomials(
        23..25,
        4,
        wrap_evals_to_monomials_2_pass,
        evals_to_monomials_cpu_fn,
        InOrOutOfPlace::Out,
        false,
    );
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn test_evals_to_monomials_2_pass_in_place() {
    run_evals_to_monomials(
        23..25,
        4,
        wrap_evals_to_monomials_2_pass,
        evals_to_monomials_cpu_fn,
        InOrOutOfPlace::In,
        false,
    );
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn test_evals_to_monomials_2_pass_transposed_monomials_out_of_place() {
    run_evals_to_monomials(
        23..25,
        4,
        wrap_evals_to_monomials_2_pass,
        evals_to_monomials_cpu_fn,
        InOrOutOfPlace::Out,
        true,
    );
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn test_evals_to_monomials_2_pass_transposed_monomials_in_place() {
    run_evals_to_monomials(
        23..25,
        4,
        wrap_evals_to_monomials_2_pass,
        evals_to_monomials_cpu_fn,
        InOrOutOfPlace::In,
        true,
    );
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn test_evals_to_monomials_3_pass_out_of_place() {
    run_evals_to_monomials(
        21..25,
        4,
        wrap_evals_to_monomials_3_pass,
        evals_to_monomials_cpu_fn,
        InOrOutOfPlace::Out,
        false,
    );
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn test_evals_to_monomials_3_pass_in_place() {
    run_evals_to_monomials(
        21..25,
        4,
        wrap_evals_to_monomials_3_pass,
        evals_to_monomials_cpu_fn,
        InOrOutOfPlace::In,
        false,
    );
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn test_evals_to_monomials_3_pass_transposed_monomials_out_of_place() {
    run_evals_to_monomials(
        21..25,
        4,
        wrap_evals_to_monomials_3_pass,
        evals_to_monomials_cpu_fn,
        InOrOutOfPlace::Out,
        true,
    );
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn test_evals_to_monomials_3_pass_transposed_monomials_in_place() {
    run_evals_to_monomials(
        21..25,
        4,
        wrap_evals_to_monomials_3_pass,
        evals_to_monomials_cpu_fn,
        InOrOutOfPlace::In,
        true,
    );
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn test_monomials_to_evals_3_pass_out_of_place() {
    run_monomials_to_evals(
        21..25,
        4,
        wrap_monomials_to_evals_3_pass,
        InOrOutOfPlace::Out,
        false,
    );
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn test_monomials_to_evals_3_pass_in_place() {
    run_monomials_to_evals(
        21..25,
        4,
        wrap_monomials_to_evals_3_pass,
        InOrOutOfPlace::In,
        false,
    );
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn test_monomials_to_evals_3_pass_transposed_monomials_out_of_place() {
    run_monomials_to_evals(
        21..25,
        4,
        wrap_monomials_to_evals_3_pass,
        InOrOutOfPlace::Out,
        true,
    );
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn test_monomials_to_evals_3_pass_transposed_monomials_in_place() {
    run_monomials_to_evals(
        21..25,
        4,
        wrap_monomials_to_evals_3_pass,
        InOrOutOfPlace::In,
        true,
    );
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn test_monomials_to_evals_2_pass_out_of_place() {
    run_monomials_to_evals(
        23..25,
        4,
        wrap_monomials_to_evals_2_pass,
        InOrOutOfPlace::Out,
        false,
    );
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn test_monomials_to_evals_2_pass_in_place() {
    run_monomials_to_evals(
        23..25,
        4,
        wrap_monomials_to_evals_2_pass,
        InOrOutOfPlace::In,
        false,
    );
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn test_monomials_to_evals_2_pass_transposed_monomials_out_of_place() {
    run_monomials_to_evals(
        23..25,
        4,
        wrap_monomials_to_evals_2_pass,
        InOrOutOfPlace::Out,
        true,
    );
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn test_monomials_to_evals_2_pass_transposed_monomials_in_place() {
    run_monomials_to_evals(
        23..25,
        4,
        wrap_monomials_to_evals_2_pass,
        InOrOutOfPlace::In,
        true,
    );
}

// Parity tests for the new all-stages-in-block monomials->evals kernels
// covering log_n in [4, 13]. We compare the strategy-routed
// `bitreversed_monomials_to_natural_evals` (which dispatches the new compact
// kernels for these log_n) against a column-by-column reference that calls
// the single-stage radix-2 `bitreversed_coeffs_to_natural_coset` directly.
// The reference path is independent of the selector, so any deviation in the
// new kernel surfaces here.
#[cfg(not(no_cuda))]
#[allow(dead_code)]
fn run_compact_bitreversed_monomials_to_natural_evals_parity(log_n: usize) {
    use super::bitreversed_monomials_to_natural_evals;
    use crate::primitives::device_structures::{DeviceMatrixChunk, DeviceMatrixChunkMut};

    // Sweep over all cosets at log_lde_factor=2 (matches the trace_holder
    // call site) so the largest coset_index — where the bit-26 truncation
    // bug surfaced — is exercised here too.
    const TEST_LOG_LDE_FACTOR: usize = 2;
    const NUM_COLS: usize = 4;

    let context = make_context();
    let stream = context.get_exec_stream();
    let device_props = context.get_device_properties();
    let n = 1usize << log_n;
    let stride = n;
    let memory_size = stride * NUM_COLS;

    let mut inputs_host = vec![BF::ZERO; memory_size];
    for (idx, value) in inputs_host.iter_mut().enumerate() {
        *value = BF::new((17 + (idx as u32).wrapping_mul(31)) as u32);
    }

    let mut inputs_device = context
        .alloc(memory_size, AllocationPlacement::BestFit)
        .unwrap();
    let mut candidate_device = context
        .alloc(memory_size, AllocationPlacement::BestFit)
        .unwrap();
    let mut reference_device = context
        .alloc(memory_size, AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut inputs_device, &inputs_host, stream).unwrap();

    for coset_index in 0..(1usize << TEST_LOG_LDE_FACTOR) {
        // Candidate: route through the strategy/dispatch path (new compact kernels).
        {
            let inputs_matrix = DeviceMatrixChunk::new(&inputs_device[..], stride, 0, n);
            let mut candidate_matrix =
                DeviceMatrixChunkMut::new(&mut candidate_device[..], stride, 0, n);
            bitreversed_monomials_to_natural_evals(
                &inputs_matrix,
                &mut candidate_matrix,
                log_n,
                TEST_LOG_LDE_FACTOR,
                coset_index,
                false,
                stream,
                device_props,
            )
            .unwrap();
        }

        // Reference: column-by-column single-stage NTT (the prior fallback path,
        // which uses `bf::pow` directly and is unaffected by table truncation).
        {
            let reference_slice = &mut reference_device[..];
            let inputs_slice = unsafe {
                era_cudart::slice::DeviceSlice::from_raw_parts(
                    inputs_device.as_ptr(),
                    inputs_device.len(),
                )
            };
            for col in 0..NUM_COLS {
                let range = col * stride..col * stride + n;
                let src = &inputs_slice[range.clone()];
                let dst = &mut reference_slice[range];
                bitreversed_coeffs_to_natural_coset(
                    src,
                    dst,
                    log_n,
                    TEST_LOG_LDE_FACTOR,
                    coset_index,
                    stream,
                )
                .unwrap();
            }
        }

        let mut candidate_host = vec![BF::ZERO; memory_size];
        let mut reference_host = vec![BF::ZERO; memory_size];
        memory_copy_async(&mut candidate_host, &candidate_device, stream).unwrap();
        memory_copy_async(&mut reference_host, &reference_device, stream).unwrap();
        stream.synchronize().unwrap();

        for col in 0..NUM_COLS {
            let start = col * stride;
            for k in 0..n {
                assert_eq!(
                    candidate_host[start + k],
                    reference_host[start + k],
                    "log_n={log_n}, coset_index={coset_index}, col={col}, k={k}"
                );
            }
        }
    }
}

macro_rules! compact_parity_test {
    ($name:ident, $log_n:expr) => {
        #[test]
        #[cfg(not(no_cuda))]
        #[serial]
        fn $name() {
            run_compact_bitreversed_monomials_to_natural_evals_parity($log_n);
        }
    };
}

compact_parity_test!(compact_monomials_to_evals_log_n_4, 4);
compact_parity_test!(compact_monomials_to_evals_log_n_5, 5);
compact_parity_test!(compact_monomials_to_evals_log_n_6, 6);
compact_parity_test!(compact_monomials_to_evals_log_n_7, 7);
compact_parity_test!(compact_monomials_to_evals_log_n_8, 8);
compact_parity_test!(compact_monomials_to_evals_log_n_9, 9);
compact_parity_test!(compact_monomials_to_evals_log_n_10, 10);
compact_parity_test!(compact_monomials_to_evals_log_n_11, 11);
compact_parity_test!(compact_monomials_to_evals_log_n_12, 12);
compact_parity_test!(compact_monomials_to_evals_log_n_13, 13);
compact_parity_test!(compact_monomials_to_evals_log_n_14, 14);
// 2-pass compact-initial range: log_n in [15, 20].
compact_parity_test!(compact_monomials_to_evals_log_n_15, 15);
compact_parity_test!(compact_monomials_to_evals_log_n_16, 16);
compact_parity_test!(compact_monomials_to_evals_log_n_17, 17);
compact_parity_test!(compact_monomials_to_evals_log_n_18, 18);
compact_parity_test!(compact_monomials_to_evals_log_n_19, 19);
compact_parity_test!(compact_monomials_to_evals_log_n_20, 20);

// Parity tests for `bitreversed_monomials_to_natural_evals_multi_coset`: the
// multi-coset entry's per-coset slice of the output must match the
// single-coset path called in a loop. For log_n in [4, 12] the compact 1-pass
// kernel runs all cosets in one launch (`cosets_per_launch = num_cosets`); for
// larger log_n the entry currently falls back to a per-coset loop that
// trivially matches.
#[cfg(not(no_cuda))]
#[allow(dead_code)]
fn run_multi_coset_monomials_to_evals_parity(log_n: usize, num_cosets: usize) {
    use super::{
        bitreversed_monomials_to_natural_evals, bitreversed_monomials_to_natural_evals_multi_coset,
    };
    use crate::primitives::device_structures::{DeviceMatrixChunk, DeviceMatrixChunkMut};

    let log_lde_factor = num_cosets.trailing_zeros() as usize;
    assert_eq!(1usize << log_lde_factor, num_cosets);
    const NUM_COLS: usize = 4;

    let context = make_context();
    let stream = context.get_exec_stream();
    let device_props = context.get_device_properties();
    let n = 1usize << log_n;
    let stride = n;
    let cols_size = stride * NUM_COLS;

    let mut inputs_host = vec![BF::ZERO; cols_size];
    for (idx, value) in inputs_host.iter_mut().enumerate() {
        *value = BF::new((23 + (idx as u32).wrapping_mul(41)) as u32);
    }

    let mut inputs_device = context
        .alloc(cols_size, AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut inputs_device, &inputs_host, stream).unwrap();

    let total_size = num_cosets * cols_size;
    let mut candidate_device = context
        .alloc(total_size, AllocationPlacement::BestFit)
        .unwrap();
    let mut reference_device = context
        .alloc(total_size, AllocationPlacement::BestFit)
        .unwrap();

    {
        let inputs_matrix = DeviceMatrixChunk::new(&inputs_device[..], stride, 0, n);
        bitreversed_monomials_to_natural_evals_multi_coset(
            &inputs_matrix,
            &mut candidate_device[..],
            log_n,
            log_lde_factor,
            0,
            num_cosets,
            NUM_COLS,
            false,
            stream,
            device_props,
        )
        .unwrap();
    }

    {
        let reference_slice = &mut reference_device[..];
        for coset_index in 0..num_cosets {
            let chunk_start = coset_index * cols_size;
            let chunk_end = chunk_start + cols_size;
            let inputs_matrix = DeviceMatrixChunk::new(&inputs_device[..], stride, 0, n);
            let mut ref_chunk = DeviceMatrixChunkMut::new(
                &mut reference_slice[chunk_start..chunk_end],
                stride,
                0,
                n,
            );
            bitreversed_monomials_to_natural_evals(
                &inputs_matrix,
                &mut ref_chunk,
                log_n,
                log_lde_factor,
                coset_index,
                false,
                stream,
                device_props,
            )
            .unwrap();
        }
    }

    let mut candidate_host = vec![BF::ZERO; total_size];
    let mut reference_host = vec![BF::ZERO; total_size];
    memory_copy_async(&mut candidate_host, &candidate_device, stream).unwrap();
    memory_copy_async(&mut reference_host, &reference_device, stream).unwrap();
    stream.synchronize().unwrap();

    for coset_index in 0..num_cosets {
        for col in 0..NUM_COLS {
            let base = coset_index * cols_size + col * stride;
            for k in 0..n {
                assert_eq!(
                    candidate_host[base + k],
                    reference_host[base + k],
                    "log_n={log_n}, num_cosets={num_cosets}, coset={coset_index}, col={col}, k={k}"
                );
            }
        }
    }
}

macro_rules! multi_coset_parity_test {
    ($name:ident, $log_n:expr, $num_cosets:expr) => {
        #[test]
        #[cfg(not(no_cuda))]
        #[serial]
        fn $name() {
            run_multi_coset_monomials_to_evals_parity($log_n, $num_cosets);
        }
    };
}

// Compact 1-pass range: kernel batches all cosets into one launch.
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_4_cosets_4, 4, 4);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_7_cosets_8, 7, 8);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_8_cosets_32, 8, 32);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_11_cosets_16, 11, 16);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_12_cosets_4, 12, 4);
// 2-pass-compact-initial range: kernels batch cosets per launch up to the
// L2-pressure cap from the strategy.
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_13_cosets_8, 13, 8);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_15_cosets_4, 15, 4);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_17_cosets_4, 17, 4);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_19_cosets_2, 19, 2);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_20_cosets_2, 20, 2);
// 3-pass range: kernels batch cosets per launch (typically 1 at this size on
// L4 since one column already fills a third of L2).
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_21_cosets_2, 21, 2);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_22_cosets_2, 22, 2);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_23_cosets_2, 23, 2);

// Direct parity test for the smem-packed multi-NTT-per-block kernel vs the
// compact 1-pass kernel: bypass `select_ntt_strategy` (which routes both
// candidate and reference through smem-packed at log_n in [6, 8]) and call the
// two dispatchers explicitly with matching multi-coset args.
#[cfg(not(no_cuda))]
#[allow(dead_code)]
fn run_smem_packed_vs_compact_parity(
    log_n: usize,
    log_instances_per_block: usize,
    num_cosets: usize,
    num_cols: usize,
) {
    use super::ntt::{monomials_to_evals_compact_1_pass, monomials_to_evals_smem_packed};
    use crate::ops::ntt::OMEGA_LOG_ORDER;
    use crate::primitives::device_structures::{DeviceMatrixChunk, DeviceMatrixChunkMut};

    let log_lde_factor = num_cosets.trailing_zeros() as usize;
    assert_eq!(1usize << log_lde_factor, num_cosets);
    assert!(num_cols.is_power_of_two());
    let context = make_context();
    let stream = context.get_exec_stream();
    let n = 1usize << log_n;
    let stride = n;
    let cols_size = stride * num_cols;
    let total_size = num_cosets * cols_size;

    let mut inputs_host = vec![BF::ZERO; cols_size];
    for (idx, value) in inputs_host.iter_mut().enumerate() {
        *value = BF::new((73 + (idx as u32).wrapping_mul(29)) as u32);
    }
    let mut inputs_device = context
        .alloc(cols_size, AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut inputs_device, &inputs_host, stream).unwrap();

    let mut candidate_device = context
        .alloc(total_size, AllocationPlacement::BestFit)
        .unwrap();
    let mut reference_device = context
        .alloc(total_size, AllocationPlacement::BestFit)
        .unwrap();

    let coset_factor_shift = (OMEGA_LOG_ORDER as usize - log_n - log_lde_factor) as u32;

    {
        let inputs_matrix = DeviceMatrixChunk::new(&inputs_device[..], stride, 0, n);
        let mut outputs_matrix = DeviceMatrixChunkMut::new(&mut candidate_device[..], stride, 0, n);
        monomials_to_evals_smem_packed(
            &inputs_matrix,
            &mut outputs_matrix,
            log_n,
            0,
            coset_factor_shift,
            num_cosets,
            num_cols,
            log_instances_per_block,
            false,
            stream,
        )
        .unwrap();
    }

    {
        let inputs_matrix = DeviceMatrixChunk::new(&inputs_device[..], stride, 0, n);
        let mut outputs_matrix = DeviceMatrixChunkMut::new(&mut reference_device[..], stride, 0, n);
        monomials_to_evals_compact_1_pass(
            &inputs_matrix,
            &mut outputs_matrix,
            log_n,
            0,
            coset_factor_shift,
            num_cosets,
            num_cols,
            num_cols,
            false,
            stream,
        )
        .unwrap();
    }

    let mut candidate_host = vec![BF::ZERO; total_size];
    let mut reference_host = vec![BF::ZERO; total_size];
    memory_copy_async(&mut candidate_host, &candidate_device, stream).unwrap();
    memory_copy_async(&mut reference_host, &reference_device, stream).unwrap();
    stream.synchronize().unwrap();

    for coset_index in 0..num_cosets {
        for col in 0..num_cols {
            let base = coset_index * cols_size + col * stride;
            for k in 0..n {
                assert_eq!(
                    candidate_host[base + k],
                    reference_host[base + k],
                    "log_n={log_n}, log_ipb={log_instances_per_block}, num_cosets={num_cosets}, num_cols={num_cols}, coset={coset_index}, col={col}, k={k}"
                );
            }
        }
    }
}

macro_rules! smem_packed_parity_test {
    ($name:ident, $log_n:expr, $log_ipb:expr, $num_cosets:expr, $num_cols:expr) => {
        #[test]
        #[cfg(not(no_cuda))]
        #[serial]
        fn $name() {
            run_smem_packed_vs_compact_parity($log_n, $log_ipb, $num_cosets, $num_cols);
        }
    };
}

// log_n=6, IPB=8: workload >= 8 required. (cosets=8, cols=1), (cosets=2, cols=4), (cosets=16, cols=4).
smem_packed_parity_test!(smem_packed_log_n_6_ipb_8_cosets_8_cols_1, 6, 3, 8, 1);
smem_packed_parity_test!(smem_packed_log_n_6_ipb_8_cosets_2_cols_4, 6, 3, 2, 4);
smem_packed_parity_test!(smem_packed_log_n_6_ipb_8_cosets_16_cols_4, 6, 3, 16, 4);
// log_n=7, IPB=4.
smem_packed_parity_test!(smem_packed_log_n_7_ipb_4_cosets_4_cols_1, 7, 2, 4, 1);
smem_packed_parity_test!(smem_packed_log_n_7_ipb_4_cosets_1_cols_4, 7, 2, 1, 4);
smem_packed_parity_test!(smem_packed_log_n_7_ipb_4_cosets_8_cols_4, 7, 2, 8, 4);
// log_n=8, IPB=2.
smem_packed_parity_test!(smem_packed_log_n_8_ipb_2_cosets_2_cols_1, 8, 1, 2, 1);
smem_packed_parity_test!(smem_packed_log_n_8_ipb_2_cosets_4_cols_4, 8, 1, 4, 4);

// Extend the strategy-driven multi-coset parity sweep to log_n=6 and 8 (which
// now route through smem-packed) so the end-to-end multi-coset path is also
// covered.
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_6_cosets_8, 6, 8);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_6_cosets_16, 6, 16);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_8_cosets_2, 8, 2);

// Direct parity test for the sub-warp kernel vs the compact 1-pass kernel.
// Same shape as `run_smem_packed_vs_compact_parity`: bypass the strategy and
// call both dispatchers explicitly with matching multi-coset args.
#[cfg(not(no_cuda))]
#[allow(dead_code)]
fn run_subwarp_vs_compact_parity(
    log_n: usize,
    log_instances_per_block: usize,
    num_cosets: usize,
    num_cols: usize,
) {
    use super::ntt::{monomials_to_evals_compact_1_pass, monomials_to_evals_subwarp};
    use crate::ops::ntt::OMEGA_LOG_ORDER;
    use crate::primitives::device_structures::{DeviceMatrixChunk, DeviceMatrixChunkMut};

    let log_lde_factor = num_cosets.trailing_zeros() as usize;
    assert_eq!(1usize << log_lde_factor, num_cosets);
    assert!(num_cols.is_power_of_two());
    let context = make_context();
    let stream = context.get_exec_stream();
    let n = 1usize << log_n;
    let stride = n;
    let cols_size = stride * num_cols;
    let total_size = num_cosets * cols_size;

    let mut inputs_host = vec![BF::ZERO; cols_size];
    for (idx, value) in inputs_host.iter_mut().enumerate() {
        *value = BF::new((59 + (idx as u32).wrapping_mul(37)) as u32);
    }
    let mut inputs_device = context
        .alloc(cols_size, AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut inputs_device, &inputs_host, stream).unwrap();

    let mut candidate_device = context
        .alloc(total_size, AllocationPlacement::BestFit)
        .unwrap();
    let mut reference_device = context
        .alloc(total_size, AllocationPlacement::BestFit)
        .unwrap();

    let coset_factor_shift = (OMEGA_LOG_ORDER as usize - log_n - log_lde_factor) as u32;

    {
        let inputs_matrix = DeviceMatrixChunk::new(&inputs_device[..], stride, 0, n);
        let mut outputs_matrix = DeviceMatrixChunkMut::new(&mut candidate_device[..], stride, 0, n);
        monomials_to_evals_subwarp(
            &inputs_matrix,
            &mut outputs_matrix,
            log_n,
            0,
            coset_factor_shift,
            num_cosets,
            num_cols,
            log_instances_per_block,
            false,
            stream,
        )
        .unwrap();
    }

    {
        let inputs_matrix = DeviceMatrixChunk::new(&inputs_device[..], stride, 0, n);
        let mut outputs_matrix = DeviceMatrixChunkMut::new(&mut reference_device[..], stride, 0, n);
        monomials_to_evals_compact_1_pass(
            &inputs_matrix,
            &mut outputs_matrix,
            log_n,
            0,
            coset_factor_shift,
            num_cosets,
            num_cols,
            num_cols,
            false,
            stream,
        )
        .unwrap();
    }

    let mut candidate_host = vec![BF::ZERO; total_size];
    let mut reference_host = vec![BF::ZERO; total_size];
    memory_copy_async(&mut candidate_host, &candidate_device, stream).unwrap();
    memory_copy_async(&mut reference_host, &reference_device, stream).unwrap();
    stream.synchronize().unwrap();

    for coset_index in 0..num_cosets {
        for col in 0..num_cols {
            let base = coset_index * cols_size + col * stride;
            for k in 0..n {
                assert_eq!(
                    candidate_host[base + k],
                    reference_host[base + k],
                    "log_n={log_n}, log_ipb={log_instances_per_block}, num_cosets={num_cosets}, num_cols={num_cols}, coset={coset_index}, col={col}, k={k}"
                );
            }
        }
    }
}

macro_rules! subwarp_parity_test {
    ($name:ident, $log_n:expr, $log_ipb:expr, $num_cosets:expr, $num_cols:expr) => {
        #[test]
        #[cfg(not(no_cuda))]
        #[serial]
        fn $name() {
            run_subwarp_vs_compact_parity($log_n, $log_ipb, $num_cosets, $num_cols);
        }
    };
}

// log_n=4, IPB=16 (THREADS_PER_INSTANCE=16 -> 256 threads).
subwarp_parity_test!(subwarp_log_n_4_ipb_16_cosets_16_cols_1, 4, 4, 16, 1);
subwarp_parity_test!(subwarp_log_n_4_ipb_16_cosets_4_cols_4, 4, 4, 4, 4);
subwarp_parity_test!(subwarp_log_n_4_ipb_16_cosets_32_cols_4, 4, 4, 32, 4);
// log_n=5, IPB=8 (THREADS_PER_INSTANCE=32 = one warp -> 256 threads).
subwarp_parity_test!(subwarp_log_n_5_ipb_8_cosets_8_cols_1, 5, 3, 8, 1);
subwarp_parity_test!(subwarp_log_n_5_ipb_8_cosets_2_cols_4, 5, 3, 2, 4);
subwarp_parity_test!(subwarp_log_n_5_ipb_8_cosets_16_cols_4, 5, 3, 16, 4);

// Extend the strategy-driven multi-coset sweep to log_n=5 (now routed through
// subwarp at workload >= 8) so the end-to-end multi-coset path is covered.
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_5_cosets_8, 5, 8);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_5_cosets_16, 5, 16);

// Parity test for the sub-warp kernel at log_n in {1, 2, 3}: the existing
// strategy path is gated at MIN_SUPPORTED_LOG_N=4, so the subwarp kernel is
// only reachable here via a direct call. Reference is the per-stage fallback
// `bitreversed_coeffs_to_natural_coset` (single-coset, single-column), looped
// over the (coset, col) workload that subwarp packs into one launch.
#[cfg(not(no_cuda))]
#[allow(dead_code)]
fn run_subwarp_vs_per_stage_parity(
    log_n: usize,
    log_instances_per_block: usize,
    num_cosets: usize,
    num_cols: usize,
) {
    use super::ntt::monomials_to_evals_subwarp;
    use super::{bitreversed_coeffs_to_natural_coset, OMEGA_LOG_ORDER};
    use crate::primitives::device_structures::{DeviceMatrixChunk, DeviceMatrixChunkMut};

    let log_lde_factor = num_cosets.trailing_zeros() as usize;
    assert_eq!(1usize << log_lde_factor, num_cosets);
    assert!(num_cols.is_power_of_two());
    assert!(num_cols * num_cosets >= 1usize << log_instances_per_block);
    let context = make_context();
    let stream = context.get_exec_stream();
    let n = 1usize << log_n;
    let stride = n;
    let cols_size = stride * num_cols;
    let total_size = num_cosets * cols_size;

    let mut inputs_host = vec![BF::ZERO; cols_size];
    for (idx, value) in inputs_host.iter_mut().enumerate() {
        *value = BF::new((41 + (idx as u32).wrapping_mul(53)) as u32);
    }
    let mut inputs_device = context
        .alloc(cols_size, AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut inputs_device, &inputs_host, stream).unwrap();

    let mut candidate_device = context
        .alloc(total_size, AllocationPlacement::BestFit)
        .unwrap();
    let mut reference_device = context
        .alloc(total_size, AllocationPlacement::BestFit)
        .unwrap();

    let coset_factor_shift = (OMEGA_LOG_ORDER as usize - log_n - log_lde_factor) as u32;

    {
        let inputs_matrix = DeviceMatrixChunk::new(&inputs_device[..], stride, 0, n);
        let mut outputs_matrix = DeviceMatrixChunkMut::new(&mut candidate_device[..], stride, 0, n);
        monomials_to_evals_subwarp(
            &inputs_matrix,
            &mut outputs_matrix,
            log_n,
            0,
            coset_factor_shift,
            num_cosets,
            num_cols,
            log_instances_per_block,
            false,
            stream,
        )
        .unwrap();
    }

    // Reference: per-stage fallback called once per (coset, col).
    {
        let reference_slice = &mut reference_device[..];
        for coset_index in 0..num_cosets {
            for col in 0..num_cols {
                let dst_offset = coset_index * cols_size + col * stride;
                let dst_slice = &mut reference_slice[dst_offset..dst_offset + n];
                let src_slice = &inputs_device[col * stride..col * stride + n];
                bitreversed_coeffs_to_natural_coset(
                    src_slice,
                    dst_slice,
                    log_n,
                    log_lde_factor,
                    coset_index,
                    stream,
                )
                .unwrap();
            }
        }
    }

    let mut candidate_host = vec![BF::ZERO; total_size];
    let mut reference_host = vec![BF::ZERO; total_size];
    memory_copy_async(&mut candidate_host, &candidate_device, stream).unwrap();
    memory_copy_async(&mut reference_host, &reference_device, stream).unwrap();
    stream.synchronize().unwrap();

    for coset_index in 0..num_cosets {
        for col in 0..num_cols {
            let base = coset_index * cols_size + col * stride;
            for k in 0..n {
                assert_eq!(
                    candidate_host[base + k],
                    reference_host[base + k],
                    "log_n={log_n}, log_ipb={log_instances_per_block}, num_cosets={num_cosets}, num_cols={num_cols}, coset={coset_index}, col={col}, k={k}"
                );
            }
        }
    }
}

macro_rules! subwarp_per_stage_parity_test {
    ($name:ident, $log_n:expr, $log_ipb:expr, $num_cosets:expr, $num_cols:expr) => {
        #[test]
        #[cfg(not(no_cuda))]
        #[serial]
        fn $name() {
            run_subwarp_vs_per_stage_parity($log_n, $log_ipb, $num_cosets, $num_cols);
        }
    };
}

// log_n=1, IPB=128 (workload >= 128 required).
subwarp_per_stage_parity_test!(subwarp_log_n_1_ipb_128_cosets_128_cols_1, 1, 7, 128, 1);
subwarp_per_stage_parity_test!(subwarp_log_n_1_ipb_128_cosets_32_cols_4, 1, 7, 32, 4);
// log_n=2, IPB=64.
subwarp_per_stage_parity_test!(subwarp_log_n_2_ipb_64_cosets_64_cols_1, 2, 6, 64, 1);
subwarp_per_stage_parity_test!(subwarp_log_n_2_ipb_64_cosets_16_cols_4, 2, 6, 16, 4);
// log_n=3, IPB=32.
subwarp_per_stage_parity_test!(subwarp_log_n_3_ipb_32_cosets_32_cols_1, 3, 5, 32, 1);
subwarp_per_stage_parity_test!(subwarp_log_n_3_ipb_32_cosets_8_cols_4, 3, 5, 8, 4);

// IPB=1 fallback variants: small workload, BLOCK_THREADS = N (= 2 / 4 / 8).
// Exercises the narrowed __shfl_xor_sync warp mask.
subwarp_per_stage_parity_test!(subwarp_log_n_1_ipb_1_cosets_1_cols_1, 1, 0, 1, 1);
subwarp_per_stage_parity_test!(subwarp_log_n_2_ipb_1_cosets_1_cols_1, 2, 0, 1, 1);
subwarp_per_stage_parity_test!(subwarp_log_n_3_ipb_1_cosets_1_cols_1, 3, 0, 1, 1);
subwarp_per_stage_parity_test!(subwarp_log_n_2_ipb_1_cosets_2_cols_1, 2, 0, 2, 1);
subwarp_per_stage_parity_test!(subwarp_log_n_3_ipb_1_cosets_4_cols_1, 3, 0, 4, 1);

// Extend the strategy-driven multi-coset parity sweep to log_n in {1, 2, 3}:
// the multi-coset entry now routes through the strategy at these sizes too,
// hitting the subwarp dispatch (IPB_max for workload >= IPB_max, IPB=1 for
// the per-coset reference).
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_1_cosets_32, 1, 32);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_2_cosets_16, 2, 16);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_3_cosets_8, 3, 8);

mod helpers;
use crate::upstream::{
    multivariate_coeffs_into_hypercube_evals, multivariate_hypercube_evals_into_coeffs, Field,
    PrimeField,
};
#[allow(unused_imports)]
use helpers::*;
