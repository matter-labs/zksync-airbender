use std::alloc::Global;
use std::ops::Range;

use era_cudart::memory::{memory_copy_async, CudaHostAllocFlags, DeviceAllocation, HostAllocation};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use fft::field_utils::{distribute_powers_serial, domain_generator_for_size};
use fft::utils::bitreverse_enumeration_inplace;
use fft::{
    ifft_natural_to_natural, precompute_twiddles_for_fft, serial_ct_ntt_bitreversed_to_natural,
};
use field::{Field, PrimeField};
use prover::gkr::whir::hypercube_to_monomial::{
    multivariate_coeffs_into_hypercube_evals, multivariate_hypercube_evals_into_coeffs,
};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use serial_test::serial;
use worker::Worker;

use super::{
    bitreversed_coeffs_to_natural_coset, evals_to_monomials_2_pass, evals_to_monomials_3_pass,
    hypercube_coeffs_natural_to_natural_evals, hypercube_evals_natural_to_bitreversed_coeffs,
    hypercube_evals_to_monomials_2_pass, hypercube_evals_to_monomials_3_pass,
    monomials_to_evals_2_pass, monomials_to_evals_3_pass, natural_evals_to_bitreversed_coeffs,
    transpose_monomials_naive, OMEGA_LOG_ORDER,
};
use crate::allocator::tracker::AllocationPlacement;
use crate::device_context::DeviceContext;
use crate::device_structures::{
    DeviceMatrixChunk, DeviceMatrixChunkImpl, DeviceMatrixChunkMut, DeviceMatrixChunkMutImpl,
};
use crate::ops::complex::bit_reverse_in_place;
use crate::primitives::context::DeviceProperties;
use crate::primitives::context::{ProverContext, ProverContextConfig};
use crate::primitives::field::BF;

const TEST_DEVICE_ALLOCATOR_BLOCK_LOG_SIZE: u32 = 2;

fn make_context() -> ProverContext {
    let mut config = ProverContextConfig::default();
    let default_block_log_size = config.allocator_block_log_size;
    let arena_bytes = 256usize << default_block_log_size;
    config.allocator_block_log_size = TEST_DEVICE_ALLOCATOR_BLOCK_LOG_SIZE;
    config.max_device_allocation_blocks_count =
        Some(arena_bytes >> TEST_DEVICE_ALLOCATOR_BLOCK_LOG_SIZE);
    // 32 MB host pool: with 8 KB blocks this is 4096 blocks
    let host_block_size = 1usize << config.host_allocator_block_log_size;
    config.host_allocator_blocks_count = (32 * 1024 * 1024) / host_block_size;
    ProverContext::new(&config).unwrap()
}

const TEST_LOG_NS: &[usize] = &[1, 2, 3, 4, 5, 6, 8, 10, 12, 14, 16, 18, 20];

#[test]
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

fn transpose_monomials(vals: &mut [BF]) {
    for chunk in vals.chunks_mut(1024) {
        for row in 0..32 {
            for col in 0..row {
                let a = chunk[row * 32 + col];
                let b = chunk[col * 32 + row];
                chunk[row * 32 + col] = b;
                chunk[col * 32 + row] = a;
            }
        }
    }
}

#[cfg(not(no_cuda))]
fn run_evals_to_monomials(
    log_n_range: Range<usize>,
    num_bf_cols: usize,
    mut gpu_fn: impl FnMut(
        &DeviceMatrixChunk<BF>,
        &mut DeviceMatrixChunkMut<BF>,
        usize,
        bool,
        &CudaStream,
    ) -> CudaResult<()>,
    mut cpu_fn: impl FnMut(&mut [BF], &[BF], usize),
    in_or_out_of_place: InOrOutOfPlace,
    transposed_monomials: bool,
) {
    let _ctx = DeviceContext::create(12).unwrap();
    let n_max = 1 << (log_n_range.end - 1);
    let worker = Worker::new();
    let stream = CudaStream::default();
    let twiddles = precompute_twiddles_for_fft::<BF, Global, true>(n_max, &worker);

    let mut rng = rand::rng();
    const OFFSET: usize = 0;
    let max_stride: usize = n_max + OFFSET;
    let max_memory_size = (max_stride * num_bf_cols) as usize;
    let flush_l2_size = 1 << 26;
    // Using parallel rng generation, as in the benches, does not reduce runtime noticeably
    let mut inputs_orig_host =
        HostAllocation::<BF>::alloc(max_memory_size, CudaHostAllocFlags::DEFAULT).unwrap();
    inputs_orig_host.fill_with(|| BF::from_nonreduced_u32(rng.random()));
    let mut inputs_host =
        HostAllocation::<BF>::alloc(max_memory_size, CudaHostAllocFlags::DEFAULT).unwrap();
    let mut outputs_host =
        HostAllocation::<BF>::alloc(max_memory_size, CudaHostAllocFlags::DEFAULT).unwrap();
    let flush_l2_host =
        HostAllocation::<BF>::alloc(flush_l2_size, CudaHostAllocFlags::DEFAULT).unwrap();
    let mut inputs_device = DeviceAllocation::<BF>::alloc(max_memory_size).unwrap();
    let mut outputs_device = DeviceAllocation::<BF>::alloc(max_memory_size).unwrap();
    let mut flush_l2_device = DeviceAllocation::<BF>::alloc(1 << 26).unwrap();
    let mut flush_l2 = || {
        memory_copy_async(&mut flush_l2_device[..], &flush_l2_host[..], &stream).unwrap();
    };
    for log_n in log_n_range {
        let n = (1 << log_n) as usize;
        let stride = n + OFFSET;
        let memory_size = stride * num_bf_cols;

        (&mut inputs_host[0..memory_size]).copy_from_slice(&inputs_orig_host[0..memory_size]);

        match in_or_out_of_place {
            InOrOutOfPlace::Out => {
                memory_copy_async(
                    &mut inputs_device[0..memory_size],
                    &inputs_host[0..memory_size],
                    &stream,
                )
                .unwrap();
                flush_l2();
                let inputs_device_matrix =
                    DeviceMatrixChunk::new(&inputs_device[0..memory_size], stride, OFFSET, n);
                let mut outputs_device_matrix = DeviceMatrixChunkMut::new(
                    &mut outputs_device[0..memory_size],
                    stride,
                    OFFSET,
                    n,
                );
                gpu_fn(
                    &inputs_device_matrix,
                    &mut outputs_device_matrix,
                    log_n,
                    transposed_monomials,
                    &stream,
                )
                .unwrap();
                memory_copy_async(
                    &mut outputs_host[0..memory_size],
                    &outputs_device[0..memory_size],
                    &stream,
                )
                .unwrap();
            }
            InOrOutOfPlace::In => {
                memory_copy_async(
                    &mut inputs_device[0..memory_size],
                    &inputs_host[0..memory_size],
                    &stream,
                )
                .unwrap();
                flush_l2();
                let inplace_output_view = &mut inputs_device[0..memory_size];
                let inplace_input_view = unsafe {
                    DeviceSlice::from_raw_parts(
                        inplace_output_view.as_ptr(),
                        inplace_output_view.len(),
                    )
                };
                let inplace_input_view_matrix =
                    DeviceMatrixChunk::new(&inplace_input_view[0..memory_size], stride, OFFSET, n);
                let mut inplace_output_view_matrix = DeviceMatrixChunkMut::new(
                    &mut inplace_output_view[0..memory_size],
                    stride,
                    OFFSET,
                    n,
                );
                gpu_fn(
                    &inplace_input_view_matrix,
                    &mut inplace_output_view_matrix,
                    log_n,
                    transposed_monomials,
                    &stream,
                )
                .unwrap();
                memory_copy_async(
                    &mut outputs_host[0..memory_size],
                    inplace_output_view,
                    &stream,
                )
                .unwrap();
            }
        }

        stream.synchronize().unwrap();

        for col in 0..num_bf_cols {
            let start = (col * stride + OFFSET) as usize;
            let range = start..start + n;
            if transposed_monomials {
                transpose_monomials(&mut outputs_host[range.clone()]);
            }
            bitreverse_enumeration_inplace(&mut outputs_host[range]);
        }

        for ntt in 0..num_bf_cols {
            let start = ntt * stride + OFFSET as usize;
            let xs_range = start..start + n;
            let twiddles = &twiddles[..(n >> 1)];
            let gpu_results = &outputs_host[xs_range.clone()];
            let mut cpu_refs: Vec<BF> = (&inputs_host[xs_range.clone()]).to_vec();
            cpu_fn(&mut cpu_refs, twiddles, log_n);
            for k in 0..n {
                assert_eq!(
                    gpu_results[k], cpu_refs[k],
                    "2^{} ntt {} k {}",
                    log_n, ntt, k
                );
            }
        }
    }
    // ctx.destroy().unwrap();
}

#[cfg(not(no_cuda))]
fn run_monomials_to_evals(
    log_n_range: Range<usize>,
    num_bf_cols: usize,
    mut gpu_fn: impl FnMut(
        &DeviceMatrixChunk<BF>,
        &mut DeviceMatrixChunkMut<BF>,
        usize,
        usize,
        bool,
        &CudaStream,
    ) -> CudaResult<()>,
    in_or_out_of_place: InOrOutOfPlace,
    transposed_monomials: bool,
) {
    let _ctx = DeviceContext::create(12).unwrap();
    let n_max = 1 << (log_n_range.end - 1);
    let worker = Worker::new();
    let stream = CudaStream::default();
    let twiddles = precompute_twiddles_for_fft::<BF, Global, false>(n_max, &worker);

    let mut rng = rand::rng();
    const OFFSET: usize = 0;
    let max_stride: usize = n_max + OFFSET;
    let max_memory_size = (max_stride * num_bf_cols) as usize;
    let flush_l2_size = 1 << 26;
    // Using parallel rng generation, as in the benches, does not reduce runtime noticeably
    let mut inputs_orig_host =
        HostAllocation::<BF>::alloc(max_memory_size, CudaHostAllocFlags::DEFAULT).unwrap();
    inputs_orig_host.fill_with(|| BF::from_nonreduced_u32(rng.random()));
    let mut inputs_host =
        HostAllocation::<BF>::alloc(max_memory_size, CudaHostAllocFlags::DEFAULT).unwrap();
    let mut outputs_host =
        HostAllocation::<BF>::alloc(max_memory_size, CudaHostAllocFlags::DEFAULT).unwrap();
    let flush_l2_host =
        HostAllocation::<BF>::alloc(flush_l2_size, CudaHostAllocFlags::DEFAULT).unwrap();
    let mut inputs_device = DeviceAllocation::<BF>::alloc(max_memory_size).unwrap();
    let mut outputs_device = DeviceAllocation::<BF>::alloc(max_memory_size).unwrap();
    let mut flush_l2_device = DeviceAllocation::<BF>::alloc(1 << 26).unwrap();
    let mut flush_l2 = || {
        memory_copy_async(&mut flush_l2_device[..], &flush_l2_host[..], &stream).unwrap();
    };
    for log_n in log_n_range {
        let coset_factor_power =
            TEST_COSET_INDEX << (OMEGA_LOG_ORDER as usize - log_n - TEST_LOG_LDE_FACTOR);
        let n = (1 << log_n) as usize;
        let stride = n + OFFSET;
        let memory_size = stride * num_bf_cols;

        (&mut inputs_host[0..memory_size]).copy_from_slice(&inputs_orig_host[0..memory_size]);

        for col in 0..num_bf_cols {
            let start = (col * stride + OFFSET) as usize;
            let range = start..start + n;
            if transposed_monomials {
                transpose_monomials(&mut inputs_host[range]);
            }
        }
        memory_copy_async(
            &mut inputs_device[0..memory_size],
            &inputs_host[0..memory_size],
            &stream,
        )
        .unwrap();
        flush_l2();

        match in_or_out_of_place {
            InOrOutOfPlace::Out => {
                let inputs_device_matrix =
                    DeviceMatrixChunk::new(&inputs_device[0..memory_size], stride, OFFSET, n);
                let mut outputs_device_matrix = DeviceMatrixChunkMut::new(
                    &mut outputs_device[0..memory_size],
                    stride,
                    OFFSET,
                    n,
                );
                gpu_fn(
                    &inputs_device_matrix,
                    &mut outputs_device_matrix,
                    log_n,
                    coset_factor_power,
                    transposed_monomials,
                    &stream,
                )
                .unwrap();
                memory_copy_async(
                    &mut outputs_host[0..memory_size],
                    &outputs_device[0..memory_size],
                    &stream,
                )
                .unwrap();
            }
            InOrOutOfPlace::In => {
                let inplace_output_view = &mut inputs_device[0..memory_size];
                let inplace_input_view = unsafe {
                    DeviceSlice::from_raw_parts(
                        inplace_output_view.as_ptr(),
                        inplace_output_view.len(),
                    )
                };
                let inplace_input_view_matrix =
                    DeviceMatrixChunk::new(&inplace_input_view[0..memory_size], stride, OFFSET, n);
                let mut inplace_output_view_matrix = DeviceMatrixChunkMut::new(
                    &mut inplace_output_view[0..memory_size],
                    stride,
                    OFFSET,
                    n,
                );
                gpu_fn(
                    &inplace_input_view_matrix,
                    &mut inplace_output_view_matrix,
                    log_n,
                    coset_factor_power,
                    transposed_monomials,
                    &stream,
                )
                .unwrap();
                memory_copy_async(
                    &mut outputs_host[0..memory_size],
                    inplace_output_view,
                    &stream,
                )
                .unwrap();
            }
        }

        stream.synchronize().unwrap();

        let tau = domain_generator_for_size::<BF>(1u64 << (log_n + TEST_LOG_LDE_FACTOR));
        let mut adjustments = vec![BF::ONE; n];
        distribute_powers_serial(&mut adjustments, BF::ONE, tau.pow(TEST_COSET_INDEX as u32));
        bitreverse_enumeration_inplace(&mut adjustments);
        for ntt in 0..num_bf_cols {
            let start = ntt * stride + OFFSET as usize;
            let xs_range = start..start + n;
            let twiddles = &twiddles[..(n >> 1)];
            let gpu_results = &outputs_host[xs_range.clone()];
            let mut cpu_refs: Vec<BF> = (&inputs_orig_host[xs_range.clone()]).to_vec();
            for (val, adjustment) in cpu_refs.iter_mut().zip(adjustments.iter()) {
                val.mul_assign(adjustment);
            }
            serial_ct_ntt_bitreversed_to_natural(&mut cpu_refs, log_n as u32, twiddles);
            for k in 0..n {
                assert_eq!(
                    gpu_results[k], cpu_refs[k],
                    "2^{} ntt {} k {}",
                    log_n, ntt, k
                );
            }
        }
    }
    // ctx.destroy().unwrap();
}

#[cfg(not(no_cuda))]
fn evals_to_monomials_cpu_fn(inputs: &mut [BF], twiddles: &[BF], _log_n: usize) {
    ifft_natural_to_natural::<BF, BF, BF>(inputs, BF::ONE, twiddles);
}

#[cfg(not(no_cuda))]
fn hypercube_evals_to_monomials_cpu_fn(inputs: &mut [BF], _twiddles: &[BF], log_n: usize) {
    multivariate_hypercube_evals_into_coeffs(inputs, log_n as u32);
    bitreverse_enumeration_inplace(inputs);
}

// These wrappers monomorphize impl arguments of the user-facing API
// so I can pass each wrapper to a run harness as a FnMut generic.
#[cfg(not(no_cuda))]
fn wrap_hypercube_evals_to_monomials_2_pass(
    inputs: &DeviceMatrixChunk<BF>,
    outputs: &mut DeviceMatrixChunkMut<BF>,
    log_n: usize,
    transposed_monomials: bool,
    stream: &CudaStream,
) -> CudaResult<()> {
    hypercube_evals_to_monomials_2_pass(inputs, outputs, log_n, transposed_monomials, stream)
}

#[cfg(not(no_cuda))]
fn wrap_hypercube_evals_to_monomials_3_pass(
    inputs: &DeviceMatrixChunk<BF>,
    outputs: &mut DeviceMatrixChunkMut<BF>,
    log_n: usize,
    transposed_monomials: bool,
    stream: &CudaStream,
) -> CudaResult<()> {
    hypercube_evals_to_monomials_3_pass(inputs, outputs, log_n, transposed_monomials, stream)
}

#[cfg(not(no_cuda))]
fn wrap_evals_to_monomials_2_pass(
    inputs: &DeviceMatrixChunk<BF>,
    outputs: &mut DeviceMatrixChunkMut<BF>,
    log_n: usize,
    transposed_monomials: bool,
    stream: &CudaStream,
) -> CudaResult<()> {
    evals_to_monomials_2_pass(inputs, outputs, log_n, transposed_monomials, stream)
}

#[cfg(not(no_cuda))]
fn wrap_evals_to_monomials_3_pass(
    inputs: &DeviceMatrixChunk<BF>,
    outputs: &mut DeviceMatrixChunkMut<BF>,
    log_n: usize,
    transposed_monomials: bool,
    stream: &CudaStream,
) -> CudaResult<()> {
    evals_to_monomials_3_pass(inputs, outputs, log_n, transposed_monomials, stream)
}

#[cfg(not(no_cuda))]
fn wrap_monomials_to_evals_2_pass(
    inputs: &DeviceMatrixChunk<BF>,
    outputs: &mut DeviceMatrixChunkMut<BF>,
    log_n: usize,
    coset_factor_power: usize,
    transposed_monomials: bool,
    stream: &CudaStream,
) -> CudaResult<()> {
    monomials_to_evals_2_pass(
        inputs,
        outputs,
        log_n,
        coset_factor_power,
        transposed_monomials,
        stream,
    )
}

#[cfg(not(no_cuda))]
fn wrap_monomials_to_evals_3_pass(
    inputs: &DeviceMatrixChunk<BF>,
    outputs: &mut DeviceMatrixChunkMut<BF>,
    log_n: usize,
    coset_factor_power: usize,
    transposed_monomials: bool,
    stream: &CudaStream,
) -> CudaResult<()> {
    monomials_to_evals_3_pass(
        inputs,
        outputs,
        log_n,
        coset_factor_power,
        transposed_monomials,
        stream,
    )
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn test_hypercube_evals_to_monomials_2_pass_out_of_place() {
    run_evals_to_monomials(
        23..25,
        8,
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
        8,
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
        8,
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
        8,
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
        8,
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
        8,
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
        8,
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
        8,
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
        8,
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
        8,
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
        8,
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
        8,
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
        8,
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
        8,
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
        8,
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
        8,
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
        8,
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
        8,
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
        8,
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
        8,
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
        8,
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
        8,
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
        8,
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
        8,
        wrap_monomials_to_evals_2_pass,
        InOrOutOfPlace::In,
        true,
    );
}
