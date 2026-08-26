use std::alloc::Global;

use era_cudart::memory::{memory_copy_async, DeviceAllocation};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use worker::Worker;

use super::{
    hypercube_coeffs_to_evals, hypercube_evals_to_monomial_coeffs, hypercube_evals_to_monomials,
    natural_evals_to_bitreversed_coeffs,
};
use crate::ntt_twiddles::DeviceContext;
use gpu_core::primitives::context::DeviceProperties;
use gpu_core::primitives::field::BF;

/// Lightweight test-local context shim: replaces `ProverContext` for gpu_ntt
/// tests. Uses raw era_cudart allocations and a plain `CudaStream` so the
/// tests have no dep on the prover layer.
struct NttTestContext {
    /// Keeps the NTT twiddle `__constant__` tables alive for the test duration.
    _device_context: DeviceContext,
    stream: CudaStream,
    props: DeviceProperties,
}

impl NttTestContext {
    fn new() -> Self {
        // powers_of_w_coarse_log_count=13 matches the default used in the
        // prover (GMEM_COARSE_LOG_COUNT). Any value in [1, 26] is valid;
        // this one exercises the same table layout as production.
        let _device_context = DeviceContext::create(13).unwrap();
        let stream = CudaStream::create().unwrap();
        let props = DeviceProperties::new().unwrap();
        Self {
            _device_context,
            stream,
            props,
        }
    }

    fn get_exec_stream(&self) -> &CudaStream {
        &self.stream
    }

    fn get_device_properties(&self) -> &DeviceProperties {
        &self.props
    }

    pub(crate) fn device_context(&self) -> &crate::ntt_twiddles::DeviceContext {
        &self._device_context
    }

    /// Allocate `len` elements directly on the device (no pooled allocator).
    fn alloc<T>(&self, len: usize) -> CudaResult<DeviceAllocation<T>> {
        DeviceAllocation::<T>::alloc(len)
    }
}

fn make_context() -> NttTestContext {
    NttTestContext::new()
}

const TEST_LOG_NS: &[usize] = &[1, 2, 3, 4, 5, 6, 8, 10, 12, 14, 16, 18, 20];

#[test]
fn cpu_characterize_hypercube_ordering() {
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
fn hypercube_evals_to_monomial_coeffs_matches_cpu() {
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

        let mut src = context.alloc(n).unwrap();
        let mut dst = context.alloc(n).unwrap();
        memory_copy_async(&mut src, &evals, stream).unwrap();
        hypercube_evals_to_monomial_coeffs(&src, &mut dst, log_n, stream).unwrap();

        let mut actual = vec![BF::ZERO; n];
        memory_copy_async(&mut actual, &dst, stream).unwrap();
        stream.synchronize().unwrap();
        assert_eq!(actual, expected, "log_n={}", log_n);
    }
}

#[test]
#[cfg(not(no_cuda))]
fn hypercube_evals_to_monomials_two_pass_compact_range_matches_cpu() {
    let context = make_context();
    let stream = context.get_exec_stream();
    for log_n in 13usize..=20 {
        let n = 1usize << log_n;
        let evals = (0..n)
            .map(|idx| BF::new((17 + idx * 13) as u32))
            .collect::<Vec<_>>();
        let mut expected = evals.clone();
        multivariate_hypercube_evals_into_coeffs(&mut expected, log_n as u32);

        let mut src = context.alloc(n).unwrap();
        let mut dst = context.alloc(n).unwrap();
        memory_copy_async(&mut src, &evals, stream).unwrap();
        hypercube_evals_to_monomials(
            &src[..],
            &mut dst[..],
            log_n,
            false,
            stream,
            context.get_device_properties(),
        )
        .unwrap();

        let mut actual = vec![BF::ZERO; n];
        memory_copy_async(&mut actual, &dst, stream).unwrap();
        stream.synchronize().unwrap();
        if let Some((row, (actual, expected))) = actual
            .iter()
            .zip(expected.iter())
            .enumerate()
            .find(|(_, (actual, expected))| actual != expected)
        {
            panic!(
                "log_n={log_n} first mismatch at row {row}: actual={actual:?}, expected={expected:?}"
            );
        }
    }
}

#[test]
#[cfg(not(no_cuda))]
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

        let mut src = context.alloc(n).unwrap();
        let mut dst = context.alloc(n).unwrap();
        memory_copy_async(&mut src, &evals, stream).unwrap();
        natural_evals_to_bitreversed_coeffs(&src, &mut dst, log_n, stream).unwrap();

        let mut actual = vec![BF::ZERO; n];
        memory_copy_async(&mut actual, &dst, stream).unwrap();
        stream.synchronize().unwrap();
        assert_eq!(actual, expected, "log_n={}", log_n);
    }
}

// Sole guard for the forward hypercube launcher family; it has no
// production caller. Asserts two independent facts:
//
// 1. ABSOLUTE labeling: the device output equals the pure-CPU forward
//    reference applied to the SAME natural-order array, with no compensating
//    permutation on either side, and is NOT that array's bitreversal.
// 2. RELATIVE labeling-preservation, measured entirely on the device with no
//    CPU oracle at all: `GPU(bitrev(x)) == bitrev(GPU(x))`. That is the
//    property which makes a bitreversal flag on this family meaningless, so it
//    is the guard against such a flag being reintroduced; a kernel that ever
//    became labeling-changing reddens here.
#[test]
#[cfg(not(no_cuda))]
fn hypercube_coeffs_to_evals_is_natural_and_preserves_labeling() {
    let context = make_context();
    let stream = context.get_exec_stream();

    for &log_n in TEST_LOG_NS {
        let n = 1usize << log_n;
        let coeffs = (0..n)
            .map(|idx| BF::new((17 + idx * 13) as u32))
            .collect::<Vec<_>>();

        let mut expected = coeffs.clone();
        multivariate_coeffs_into_hypercube_evals(&mut expected, log_n as u32);
        let mut expected_bitrev = expected.clone();
        fft::bitreverse_enumeration_inplace(&mut expected_bitrev);

        let mut coeffs_bitrev = coeffs.clone();
        fft::bitreverse_enumeration_inplace(&mut coeffs_bitrev);

        let mut src = context.alloc(n).unwrap();
        let mut dst = context.alloc(n).unwrap();

        memory_copy_async(&mut src, &coeffs, stream).unwrap();
        hypercube_coeffs_to_evals(&src, &mut dst, log_n, stream).unwrap();
        let mut actual = vec![BF::ZERO; n];
        memory_copy_async(&mut actual, &dst, stream).unwrap();

        memory_copy_async(&mut src, &coeffs_bitrev, stream).unwrap();
        hypercube_coeffs_to_evals(&src, &mut dst, log_n, stream).unwrap();
        let mut actual_from_bitrev = vec![BF::ZERO; n];
        memory_copy_async(&mut actual_from_bitrev, &dst, stream).unwrap();
        stream.synchronize().unwrap();

        assert_eq!(actual, expected, "log_n={}", log_n);
        if log_n >= 2 {
            // Non-vacuity: the two candidate labelings differ on this data, so
            // the negative control that follows is a real discrimination.
            assert_ne!(expected, expected_bitrev, "log_n={}", log_n);
            assert_ne!(actual, expected_bitrev, "log_n={}", log_n);
        }

        let mut actual_bitrev = actual.clone();
        fft::bitreverse_enumeration_inplace(&mut actual_bitrev);
        assert_eq!(actual_from_bitrev, actual_bitrev, "log_n={}", log_n);
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
fn test_monomials_to_evals_2_pass_out_of_place() {
    run_monomials_to_evals(
        23..25,
        4,
        wrap_monomials_to_evals_2_pass_smem,
        InOrOutOfPlace::Out,
        false,
    );
}

#[test]
#[cfg(not(no_cuda))]
fn test_monomials_to_evals_2_pass_in_place() {
    run_monomials_to_evals(
        23..25,
        4,
        wrap_monomials_to_evals_2_pass_smem,
        InOrOutOfPlace::In,
        false,
    );
}

#[test]
#[cfg(not(no_cuda))]
fn test_monomials_to_evals_2_pass_transposed_monomials_out_of_place() {
    run_monomials_to_evals(
        23..25,
        4,
        wrap_monomials_to_evals_2_pass_smem,
        InOrOutOfPlace::Out,
        true,
    );
}

#[test]
#[cfg(not(no_cuda))]
fn test_monomials_to_evals_2_pass_transposed_monomials_in_place() {
    run_monomials_to_evals(
        23..25,
        4,
        wrap_monomials_to_evals_2_pass_smem,
        InOrOutOfPlace::In,
        true,
    );
}

// The former `compact_parity_test` harness (log_n 4..20) is retired: it oracled
// the strategy-routed forward NTT against the now-removed single-stage radix-2
// per-stage reference path. Its coverage is preserved elsewhere: log_n <= 13 by
// the multi_coset / streaming / DIT parity harnesses (which cross-check against
// the compact kernels called directly), and log_n > 13 by the `host_oracle`
// module (pure-CPU forward-NTT ground truth).

// Parity tests for `bitreversed_monomials_to_natural_evals_multi_coset`: the
// multi-coset entry's per-coset slice of the output must match the
// single-coset path called in a loop. For log_n in [4, 12] the compact 1-pass
// kernel runs all cosets in one launch (`cosets_per_launch = num_cosets`); for
// larger log_n the entry currently falls back to a per-coset loop that
// trivially matches.
#[cfg(not(no_cuda))]
#[allow(dead_code)]
fn run_multi_coset_monomials_to_evals_parity(log_n: usize, num_cosets: usize) {
    let log_lde_factor = num_cosets.trailing_zeros() as usize;
    assert_eq!(1usize << log_lde_factor, num_cosets);
    run_multi_coset_monomials_to_evals_parity_for_range(log_n, log_lde_factor, 0, num_cosets);
}

#[cfg(not(no_cuda))]
#[allow(dead_code)]
fn run_multi_coset_monomials_to_evals_parity_for_range(
    log_n: usize,
    log_lde_factor: usize,
    coset_index_base: usize,
    num_cosets: usize,
) {
    use super::forward::{
        monomials_to_evals_2_pass_compact_initial, monomials_to_evals_compact_1_pass,
    };
    use super::{bitreversed_monomials_to_natural_evals_multi_coset, lde_with_coset_range};
    use crate::ntt_twiddles::OMEGA_LOG_ORDER;
    use gpu_core::primitives::device_structures::{DeviceMatrixChunk, DeviceMatrixChunkMut};

    assert!(num_cosets.is_power_of_two());
    assert!(coset_index_base == 0 || coset_index_base.is_power_of_two());
    assert!(coset_index_base + num_cosets <= (1usize << log_lde_factor));
    const NUM_COLS: usize = 4;

    let context = make_context();
    let stream = context.get_exec_stream();
    let device_props = context.get_device_properties();
    let n = 1usize << log_n;
    let stride = n;
    let cols_size = stride * NUM_COLS;

    let mut inputs_host = vec![BF::ZERO; cols_size];
    for (idx, value) in inputs_host.iter_mut().enumerate() {
        *value = BF::new(23 + (idx as u32).wrapping_mul(41));
    }

    let mut inputs_device = context.alloc(cols_size).unwrap();
    memory_copy_async(&mut inputs_device, &inputs_host, stream).unwrap();

    let total_size = num_cosets * cols_size;
    let mut candidate_device = context.alloc(total_size).unwrap();
    let mut reference_device = context.alloc(total_size).unwrap();

    // DIT-range (log_n in [2, 13]) needs a d-table scratch (len >= N); outside
    // that range the strategy ignores it. A plain cudaMalloc is fine in tests.
    let mut d_scratch = context.alloc(n).unwrap();

    {
        let inputs_matrix = DeviceMatrixChunk::new(&inputs_device[..], stride, 0, n);
        let scratch_opt = if (2..=13).contains(&log_n) {
            Some(&mut d_scratch[..])
        } else {
            None
        };
        if coset_index_base == 0 && num_cosets == (1usize << log_lde_factor) {
            bitreversed_monomials_to_natural_evals_multi_coset(
                &inputs_matrix,
                &mut candidate_device[..],
                log_n,
                log_lde_factor,
                NUM_COLS,
                false,
                context.device_context(),
                scratch_opt,
                stream,
                device_props,
            )
            .unwrap();
        } else {
            lde_with_coset_range(
                &inputs_matrix,
                &mut candidate_device[..],
                log_n,
                log_lde_factor,
                num_cosets,
                coset_index_base,
                NUM_COLS,
                1,
                1,
                context.device_context(),
                scratch_opt,
                stream,
                device_props,
            )
            .unwrap();
        }
    }

    {
        // ORACLE: an INDEPENDENT per-coset baseline. For the DIT range (log_n in
        // [2, 13]) the subject's multi-coset entry routes to the DIT engine, so we
        // must NOT re-enter the DIT path here (that would be circular). The
        // reference mirrors the routing the deleted single-coset entry used:
        //   log_n in [8, 12]  -> 1-pass compact called DIRECTLY;
        //   log_n in [13, 20] -> 2-pass-compact-initial called DIRECTLY (a
        //                        different family from the intermediate/2pc-batched
        //                        candidate — independent for the range tests);
        //   log_n in [2, 7] / [21, 23] -> `lde_with_coset_range` at num_cosets=1,
        //                        which declines the DIT single-pass divisibility
        //                        gate (num_cosets=1) and, for log_n <= 13, never
        //                        takes the lde-intermediate fast path — so it
        //                        dispatches through the strategy to a single-coset
        //                        subwarp/compact (log_n 2-7) or 3-pass (log_n
        //                        21-23) launch, independent of the batched subject.
        // The compact/2pc kernels read twiddles from `__constant__` tables (NOT
        // DitTriangles).
        let coset_factor_shift = (OMEGA_LOG_ORDER as usize - log_n - log_lde_factor) as u32;
        let reference_slice = &mut reference_device[..];
        for coset_offset in 0..num_cosets {
            let coset_index = coset_index_base + coset_offset;
            let chunk_start = coset_offset * cols_size;
            let chunk_end = chunk_start + cols_size;
            let inputs_matrix = DeviceMatrixChunk::new(&inputs_device[..], stride, 0, n);
            if (8..=12).contains(&log_n) {
                let mut ref_chunk = DeviceMatrixChunkMut::new(
                    &mut reference_slice[chunk_start..chunk_end],
                    stride,
                    0,
                    n,
                );
                monomials_to_evals_compact_1_pass(
                    &inputs_matrix,
                    &mut ref_chunk,
                    log_n,
                    coset_index,
                    coset_factor_shift,
                    1,
                    NUM_COLS,
                    NUM_COLS,
                    stream,
                )
                .unwrap();
            } else if (13..=20).contains(&log_n) {
                let mut ref_chunk = DeviceMatrixChunkMut::new(
                    &mut reference_slice[chunk_start..chunk_end],
                    stride,
                    0,
                    n,
                );
                monomials_to_evals_2_pass_compact_initial(
                    &inputs_matrix,
                    &mut ref_chunk,
                    log_n,
                    coset_index,
                    coset_factor_shift,
                    1,
                    NUM_COLS,
                    1,
                    NUM_COLS,
                    stream,
                )
                .unwrap();
            } else {
                lde_with_coset_range(
                    &inputs_matrix,
                    &mut reference_slice[chunk_start..chunk_end],
                    log_n,
                    log_lde_factor,
                    1,
                    coset_index,
                    NUM_COLS,
                    1,
                    1,
                    context.device_context(),
                    None,
                    stream,
                    device_props,
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

    for coset_offset in 0..num_cosets {
        for col in 0..NUM_COLS {
            let base = coset_offset * cols_size + col * stride;
            for k in 0..n {
                assert_eq!(
                    candidate_host[base + k],
                    reference_host[base + k],
                    "log_n={log_n}, log_lde_factor={log_lde_factor}, num_cosets={num_cosets}, coset_index_base={coset_index_base}, coset_offset={coset_offset}, col={col}, k={k}"
                );
            }
        }
    }
}

macro_rules! multi_coset_parity_test {
    ($name:ident, $log_n:expr, $num_cosets:expr) => {
        #[test]
        #[cfg(not(no_cuda))]
        fn $name() {
            run_multi_coset_monomials_to_evals_parity($log_n, $num_cosets);
        }
    };
}

macro_rules! multi_coset_range_parity_test {
    ($name:ident, $log_n:expr, $log_lde_factor:expr, $coset_index_base:expr, $num_cosets:expr) => {
        #[test]
        #[cfg(not(no_cuda))]
        fn $name() {
            run_multi_coset_monomials_to_evals_parity_for_range(
                $log_n,
                $log_lde_factor,
                $coset_index_base,
                $num_cosets,
            );
        }
    };
}

// Multi-coset forward-NTT parity (candidate = production multi-coset entry /
// `lde_with_coset_range`; oracle = the compact / 2pc-compact-initial kernels
// called DIRECTLY, an independent GPU baseline). One representative kept per
// (kernel-family, log_n): the coset count only varies grid batching (guarded by
// `strategy::compact_range_batches_all_cosets_into_one_launch`), so the extra
// coset counts at a given log_n are redundant. Larger log_n (>=13) is
// additionally pinned by the pure-CPU `host_oracle` module.

// Compact 1-pass / subwarp range (log_n 2..12): one rep per log_n.
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_2_cosets_256, 2, 256);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_3_cosets_256, 3, 256);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_4_cosets_4, 4, 4);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_7_cosets_8, 7, 8);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_8_cosets_8, 8, 8);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_11_cosets_16, 11, 16);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_12_cosets_4, 12, 4);
// 2-pass-compact-initial range (log_n 13..20): GPU-vs-GPU batching cross-checks
// (production multi-coset entry vs the direct-2pc baseline) at reps 13/17/19.
// The family is independently oracled against a pure-CPU forward NTT by the
// `host_oracle_2pc_*` set (log_n 13/14/15/16/17/18/19/20); log_n 9/10 in the DIT
// range are covered by dit_engine two_pass + dit_launcher_two_pass.
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_13_cosets_8, 13, 8);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_17_cosets_4, 17, 4);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_19_cosets_2, 19, 2);
// 3-pass range (log_n 21..23): rep at 21; 22/23 subsumed by the pure-CPU
// `monomials_to_evals_3_pass` matrix tests (log_n 21..24).
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_21_cosets_2, 21, 2);
// Range variants (nonzero coset_index_base -> exercise the coset-factor shift).
// Reps at log_n 8/14/18/23. The log_n 15/16/17 cases at coset counts 16/32/64
// are additionally retained to stress the occupancy / grid-batching tuning:
// each log_n is a distinct compiled kernel, and these coset counts drive
// batching configurations (the candidate's lde-intermediate/2pc-batched path
// vs the direct 2pc-compact-initial oracle) that the reps above do not. Their
// correctness is separately pinned by the pure-CPU host_oracle_lde_intermediate
// / host_oracle_2pc sets, so these earn their keep as launch-config coverage.
multi_coset_range_parity_test!(
    multi_coset_monomials_to_evals_log_n_8_cosets_4_base_4,
    8,
    4,
    4,
    4
);
multi_coset_range_parity_test!(
    multi_coset_monomials_to_evals_log_n_18_cosets_8_base_8,
    18,
    9,
    8,
    8
);
multi_coset_range_parity_test!(
    multi_coset_monomials_to_evals_log_n_14_cosets_128_base_128,
    14,
    12,
    128,
    128
);
multi_coset_range_parity_test!(
    multi_coset_monomials_to_evals_log_n_23_cosets_8_base_8,
    23,
    4,
    4,
    4
);
multi_coset_range_parity_test!(
    multi_coset_monomials_to_evals_log_n_17_cosets_16_base_16,
    17,
    10,
    16,
    16
);
multi_coset_range_parity_test!(
    multi_coset_monomials_to_evals_log_n_16_cosets_32_base_32,
    16,
    11,
    32,
    32
);
multi_coset_range_parity_test!(
    multi_coset_monomials_to_evals_log_n_15_cosets_64_base_64,
    15,
    12,
    64,
    64
);

// Host-oracle forward-NTT parity tests. Unlike the parity harnesses above
// (which cross-check one GPU kernel family against ANOTHER GPU path), these
// compare real GPU output against a PURE-CPU ground truth computed by
// `host_forward_ntt_single_coset` (shared with `run_monomials_to_evals`). They
// are the replacement oracle for the 2-pass-compact and lde-intermediate
// forward families before the GPU per-stage reference path is deleted.
//
// Naming: NOT prefixed `cpu_` — these launch GPU kernels and must stay in the
// GPU-serialized nextest group (a `cpu_` path segment opts a test OUT of it).
#[cfg(not(no_cuda))]
mod host_oracle {
    use super::super::forward::monomials_to_evals_2_pass_compact_initial;
    use super::super::{bitreversed_monomials_to_natural_evals_multi_coset, lde_with_coset_range};
    use super::helpers::host_forward_ntt_single_coset;
    use super::make_context;
    use crate::ntt_twiddles::OMEGA_LOG_ORDER;
    use crate::upstream::Field;
    use era_cudart::memory::memory_copy_async;
    use fft::precompute_twiddles_for_fft;
    use gpu_core::primitives::device_structures::{DeviceMatrixChunk, DeviceMatrixChunkMut};
    use gpu_core::primitives::field::BF;
    use rand::rngs::StdRng;
    use rand::{Rng, SeedableRng};
    use std::alloc::Global;
    use worker::Worker;

    /// Which production launcher produces the CANDIDATE (GPU) output.
    #[derive(Clone, Copy)]
    enum Route {
        /// `monomials_to_evals_2_pass_compact_initial` called DIRECTLY. Pins the
        /// 2-pass-compact family at log_n 13, where the forward strategy would
        /// otherwise route to the DIT engine (so a strategy-routed call would
        /// exercise the wrong family).
        Direct2pc,
        /// The production multi-coset entry
        /// `bitreversed_monomials_to_natural_evals_multi_coset` (full coset set,
        /// base 0). For log_n >= 14 the strategy deterministically selects the
        /// 2-pass-compact family (DIT tops out at 13); no d-table scratch needed.
        MultiCosetEntry,
        /// `lde_with_coset_range`, which for log_n in (13, 18] takes the
        /// lde-intermediate fast path unconditionally.
        LdeWithCosetRange,
    }

    /// Drive one forward-NTT case and compare every (coset, column, index) of
    /// the GPU output against the pure-CPU forward NTT.
    ///
    /// Geometry: contiguous coset-major output (num_cols_per_coset_stride ==
    /// num_cols); coset `coset_index_base + offset` occupies
    /// `out[(offset * num_cols + col) * n ..]`. Inputs are randomized with a
    /// fixed seed (reproducible; seed logged in each assert via the message).
    fn run_host_oracle_forward_parity(
        log_n: usize,
        log_lde_factor: usize,
        num_cosets: usize,
        coset_index_base: usize,
        num_cols: usize,
        route: Route,
        seed: u64,
    ) {
        assert!(num_cosets.is_power_of_two() && num_cosets >= 2);
        assert!(coset_index_base + num_cosets <= (1usize << log_lde_factor));
        assert!(log_n + log_lde_factor <= OMEGA_LOG_ORDER as usize);

        let context = make_context();
        let stream = context.get_exec_stream();
        let device_props = context.get_device_properties();
        let n = 1usize << log_n;
        let stride = n; // contiguous: num_cols_per_coset_stride == num_cols.
        let cols_size = stride * num_cols;
        let total_size = num_cosets * cols_size;

        // Randomized, fixed-seed bitreversed monomials. One shared input matrix
        // of `num_cols` columns is fanned out across all output cosets, matching
        // the launcher contract.
        let mut rng = StdRng::seed_from_u64(seed);
        let mut inputs_host = vec![BF::ZERO; cols_size];
        for value in inputs_host.iter_mut() {
            *value = BF::from_nonreduced_u32(rng.random());
        }
        let mut inputs_device = context.alloc(cols_size).unwrap();
        memory_copy_async(&mut inputs_device, &inputs_host, stream).unwrap();

        let mut outputs_device = context.alloc(total_size).unwrap();

        let coset_factor_shift = (OMEGA_LOG_ORDER as usize - log_n - log_lde_factor) as u32;

        {
            let inputs_matrix = DeviceMatrixChunk::new(&inputs_device[..], stride, 0, n);
            match route {
                Route::Direct2pc => {
                    let mut outputs_matrix =
                        DeviceMatrixChunkMut::new(&mut outputs_device[..], stride, 0, n);
                    monomials_to_evals_2_pass_compact_initial(
                        &inputs_matrix,
                        &mut outputs_matrix,
                        log_n,
                        coset_index_base,
                        coset_factor_shift,
                        num_cosets,
                        num_cols,   // num_cols_per_coset (contiguous)
                        num_cosets, // cosets_per_launch: batch every coset
                        num_cols,   // columns_per_launch
                        stream,
                    )
                    .unwrap();
                }
                Route::MultiCosetEntry => {
                    // The entry hardcodes base 0 and the full coset set.
                    assert_eq!(coset_index_base, 0);
                    assert_eq!(num_cosets, 1usize << log_lde_factor);
                    bitreversed_monomials_to_natural_evals_multi_coset(
                        &inputs_matrix,
                        &mut outputs_device[..],
                        log_n,
                        log_lde_factor,
                        num_cols, // num_cols_per_coset_stride (contiguous)
                        false,
                        context.device_context(),
                        None, // log_n >= 14: no DIT, so no d-table scratch
                        stream,
                        device_props,
                    )
                    .unwrap();
                }
                Route::LdeWithCosetRange => {
                    lde_with_coset_range(
                        &inputs_matrix,
                        &mut outputs_device[..],
                        log_n,
                        log_lde_factor,
                        num_cosets,
                        coset_index_base,
                        num_cols, // num_cols_per_coset_stride (contiguous)
                        1,        // occupancy hint numerator
                        1,        // occupancy hint denominator
                        context.device_context(),
                        None, // log_n in (13, 18]: fast path needs no scratch
                        stream,
                        device_props,
                    )
                    .unwrap();
                }
            }
        }

        let mut outputs_host = vec![BF::ZERO; total_size];
        memory_copy_async(&mut outputs_host, &outputs_device, stream).unwrap();
        stream.synchronize().unwrap();

        // PURE-CPU ground truth: one independent forward NTT per (coset, column).
        // No GPU kernel touches the expected side.
        let worker = Worker::new();
        let forward_twiddles = precompute_twiddles_for_fft::<BF, Global, false>(n, &worker);
        let forward_twiddles = &forward_twiddles[..(n >> 1)];

        for coset_offset in 0..num_cosets {
            let coset_index = coset_index_base + coset_offset;
            for col in 0..num_cols {
                let col_monomials = &inputs_host[col * stride..col * stride + n];
                let expected = host_forward_ntt_single_coset(
                    col_monomials,
                    log_n,
                    log_lde_factor,
                    coset_index,
                    forward_twiddles,
                );
                let base = coset_offset * cols_size + col * stride;
                for k in 0..n {
                    assert_eq!(
                        outputs_host[base + k],
                        expected[k],
                        "log_n={log_n}, log_lde_factor={log_lde_factor}, num_cosets={num_cosets}, coset_index_base={coset_index_base}, coset_offset={coset_offset}, col={col}, k={k}, seed={seed:#x}"
                    );
                }
            }
        }
    }

    // 2-pass-compact-initial family (`ab_monomials_to_evals_first_K_stages_compact`
    // + `noninitial_8`).
    //
    // log_n 13: DIRECT call — pins the 2pc family (strategy would route 13 to
    // DIT). Nonzero coset_index_base (2) exercises the coset-factor shift.
    #[test]
    fn host_oracle_2pc_log_n_13_direct_matches() {
        run_host_oracle_forward_parity(13, 2, 2, 2, 2, Route::Direct2pc, 0x2c_13u64);
    }

    // log_n 14 and 20: via the production multi-coset entry (strategy selects the
    // 2pc family for log_n >= 14).
    #[test]
    fn host_oracle_2pc_log_n_14_multi_coset_matches() {
        run_host_oracle_forward_parity(14, 1, 2, 0, 2, Route::MultiCosetEntry, 0x2c_14u64);
    }

    #[test]
    fn host_oracle_2pc_log_n_20_multi_coset_matches() {
        run_host_oracle_forward_parity(20, 1, 2, 0, 1, Route::MultiCosetEntry, 0x2c_20u64);
    }

    // log_n 19: an INDEPENDENT CPU oracle at the top of the 2pc range (the other
    // multi-coset host oracles are 13/14/20). Complements the GPU-vs-GPU
    // `multi_coset_monomials_to_evals_log_n_19_cosets_2` parity case with a
    // pure-CPU forward-NTT ground truth via the production multi-coset entry.
    #[test]
    fn host_oracle_2pc_log_n_19_multi_coset_matches() {
        run_host_oracle_forward_parity(19, 1, 2, 0, 2, Route::MultiCosetEntry, 0x2c_19u64);
    }

    // log_n 15: the ONLY oracle for the 2pc-compact-initial first_7 kernel
    // (`ab_monomials_to_evals_first_7_stages_compact_kernel`). Each stage-count
    // is a DISTINCT compile-time kernel; the multi-coset entry routes log_n 15 to
    // `MonomialsToEvalsFirstCompact { stages: log_n - 8 = 7 }` (DIT tops out at
    // 13, so no DIT and no lde fast path is taken here).
    #[test]
    fn host_oracle_2pc_log_n_15_multi_coset_matches() {
        run_host_oracle_forward_parity(15, 1, 2, 0, 2, Route::MultiCosetEntry, 0x2c_15u64);
    }

    // log_n 16/17/18: the ONLY independent (pure-CPU) oracles for the
    // 2pc-compact-initial first_8/9/10 kernels
    // (`ab_monomials_to_evals_first_{8,9,10}_stages_compact_kernel`, K = log_n -
    // 8). Each stage-count is a DISTINCT compile-time kernel; the multi-coset
    // entry routes each log_n to `MonomialsToEvalsFirstCompact { stages: log_n -
    // 8 }` (DIT tops out at 13, and the lde-intermediate fast path is only
    // reached via `lde_with_coset_range`, a different entry — so neither is taken
    // here). The GPU-vs-GPU `multi_coset_monomials_to_evals_log_n_17_cosets_4`
    // parity case remains a valid batching cross-check alongside the log_n 17
    // oracle here.
    #[test]
    fn host_oracle_2pc_log_n_16_multi_coset_matches() {
        run_host_oracle_forward_parity(16, 1, 2, 0, 2, Route::MultiCosetEntry, 0x2c_16u64);
    }

    #[test]
    fn host_oracle_2pc_log_n_17_multi_coset_matches() {
        run_host_oracle_forward_parity(17, 1, 2, 0, 2, Route::MultiCosetEntry, 0x2c_17u64);
    }

    #[test]
    fn host_oracle_2pc_log_n_18_multi_coset_matches() {
        run_host_oracle_forward_parity(18, 1, 2, 0, 2, Route::MultiCosetEntry, 0x2c_18u64);
    }

    // LDE-intermediate fast path (`ab_lde_first_{6..10}_stages_kernel` +
    // `noninitial_8`) via `lde_with_coset_range`. log_n 14 and 18 lie in
    // (13, 18], so the fast path is taken unconditionally.
    //
    // Coset-tile size: the fast path's grid builder targets FULL occupancy
    // (hints 1/1) and asserts the coset tile is not over-split
    // (`grid_dim_z <= cosets_in_tile`). A 2-coset tile is too small to fill a
    // large GPU at 1/1, so — matching the existing lde-intermediate parity
    // tests — these use a production-scale power-of-two coset tile with a
    // nonzero coset_index_base (which still exercises the coset-factor shift).
    #[test]
    fn host_oracle_lde_intermediate_log_n_14_matches() {
        run_host_oracle_forward_parity(14, 7, 64, 64, 2, Route::LdeWithCosetRange, 0x1de14u64);
    }

    #[test]
    fn host_oracle_lde_intermediate_log_n_18_matches() {
        run_host_oracle_forward_parity(18, 5, 16, 16, 2, Route::LdeWithCosetRange, 0x1de18u64);
    }

    // log_n 15/16/17: the ONLY oracles for the fast-path first_7/8/9 kernels
    // (`ab_lde_first_{7,8,9}_stages_kernel`, K = log_n - 8). log_n in (13, 18]
    // takes the lde-intermediate fast path unconditionally, and each stage-count
    // is a DISTINCT compile-time kernel, so 14/18 do not exercise 7/8/9. The
    // coset tile scales down with log_n (matching 14 -> 64 and 18 -> 16) so the
    // fast-path grid builder does not over-split the tile at occupancy 1/1; each
    // uses the upper coset half, so the nonzero coset_index_base exercises the
    // coset-factor shift.
    #[test]
    fn host_oracle_lde_intermediate_log_n_15_matches() {
        run_host_oracle_forward_parity(15, 7, 64, 64, 2, Route::LdeWithCosetRange, 0x1de15u64);
    }

    #[test]
    fn host_oracle_lde_intermediate_log_n_16_matches() {
        run_host_oracle_forward_parity(16, 6, 32, 32, 2, Route::LdeWithCosetRange, 0x1de16u64);
    }

    #[test]
    fn host_oracle_lde_intermediate_log_n_17_matches() {
        run_host_oracle_forward_parity(17, 5, 16, 16, 2, Route::LdeWithCosetRange, 0x1de17u64);
    }
}

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
    use super::forward::{monomials_to_evals_compact_1_pass, monomials_to_evals_smem_packed};
    use crate::ntt_twiddles::OMEGA_LOG_ORDER;
    use gpu_core::primitives::device_structures::{DeviceMatrixChunk, DeviceMatrixChunkMut};

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
        *value = BF::new(73 + (idx as u32).wrapping_mul(29));
    }
    let mut inputs_device = context.alloc(cols_size).unwrap();
    memory_copy_async(&mut inputs_device, &inputs_host, stream).unwrap();

    let mut candidate_device = context.alloc(total_size).unwrap();
    let mut reference_device = context.alloc(total_size).unwrap();

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
        fn $name() {
            run_smem_packed_vs_compact_parity($log_n, $log_ipb, $num_cosets, $num_cols);
        }
    };
}

// log_n=6, IPB=8: workload >= 8 required.
// (cosets=8, cols=1), (cosets=2, cols=4), (cosets=16, cols=4).
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

// Extend the strategy-driven multi-coset parity sweep to log_n=6 (now routed
// through smem-packed). log_n=8 is already covered by log_n_8_cosets_8 above,
// and the extra coset counts only vary grid batching.
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_6_cosets_8, 6, 8);

// Parity test for the production forward-NTT path on the DIT range (log_n in
// [2, 13]). CANDIDATE = the public multi-coset entry
// `bitreversed_monomials_to_natural_evals_multi_coset`, which routes the DIT
// range through `select_forward_strategy` (DIT where applicable; otherwise the
// non-DIT 1-pass kernel the strategy selects). ORACLE = the compact kernels
// called DIRECTLY (independent baseline: they read `__constant__` twiddle
// tables, NOT DitTriangles): log_n <= 12 -> 1-pass compact; log_n == 13 ->
// 2-pass-compact-initial.
// `log_vpt` is retained for the test matrix shape; routing now chooses the VPT
// variant internally. `num_cols` columns are written back-to-back per coset.
#[cfg(not(no_cuda))]
#[allow(dead_code)]
fn run_streaming_vs_compact_parity(
    log_n: usize,
    log_vpt: usize,
    num_cosets: usize,
    num_cols: usize,
) {
    use super::forward::{
        monomials_to_evals_2_pass_compact_initial, monomials_to_evals_compact_1_pass,
    };
    use super::{bitreversed_monomials_to_natural_evals_multi_coset, lde_with_coset_range};
    use crate::ntt_twiddles::OMEGA_LOG_ORDER;
    use gpu_core::primitives::device_structures::{DeviceMatrixChunk, DeviceMatrixChunkMut};
    let _ = log_vpt;

    let log_lde_factor = num_cosets.trailing_zeros() as usize;
    assert_eq!(1usize << log_lde_factor, num_cosets);
    assert!(
        (2..=13).contains(&log_n),
        "streaming supports log_n in [2, 13]"
    );
    assert!(
        log_vpt == 2 || log_vpt == 3,
        "log_vpt must be 2 (VPT=4) or 3 (VPT=8)"
    );
    assert!(log_n >= log_vpt, "log_n must be >= log_vpt");
    assert!(log_vpt == 3 || log_n <= 12, "VPT=4 requires log_n <= 12");
    let context = make_context();
    let stream = context.get_exec_stream();
    let device_props = context.get_device_properties();
    let n = 1usize << log_n;
    let stride = n;
    let cols_size = stride * num_cols;
    let total_size = num_cosets * cols_size;

    let mut inputs_host = vec![BF::ZERO; cols_size];
    for (idx, value) in inputs_host.iter_mut().enumerate() {
        *value = BF::new(97 + (idx as u32).wrapping_mul(53));
    }
    let mut inputs_device = context.alloc(cols_size).unwrap();
    memory_copy_async(&mut inputs_device, &inputs_host, stream).unwrap();

    let mut candidate_device = context.alloc(total_size).unwrap();
    let mut reference_device = context.alloc(total_size).unwrap();

    let coset_factor_shift = (OMEGA_LOG_ORDER as usize - log_n - log_lde_factor) as u32;

    // CANDIDATE: the public multi-coset entry, which routes the DIT range
    // (log_n in [2, 13]) through `select_forward_strategy` to the DIT engine.
    let mut d_scratch = context.alloc(n).unwrap();
    {
        let inputs_matrix = DeviceMatrixChunk::new(&inputs_device[..], stride, 0, n);
        let scratch_opt = if (2..=13).contains(&log_n) {
            Some(&mut d_scratch[..])
        } else {
            None
        };
        bitreversed_monomials_to_natural_evals_multi_coset(
            &inputs_matrix,
            &mut candidate_device[..],
            log_n,
            log_lde_factor,
            num_cols,
            false,
            context.device_context(),
            scratch_opt,
            stream,
            device_props,
        )
        .unwrap();
    }

    {
        // ORACLE: an INDEPENDENT baseline — the compact kernels called DIRECTLY
        // (they read `__constant__` twiddle tables, NOT DitTriangles), bypassing
        // `select_ntt_strategy` (which now routes the DIT range to the engine
        // under test — calling it here would be circular): log_n <= 12 -> 1-pass
        // compact; log_n == 13 -> 2-pass-compact-initial.
        let reference_slice = &mut reference_device[..];
        for coset_index in 0..num_cosets {
            let chunk_start = coset_index * cols_size;
            let chunk_end = chunk_start + cols_size;
            let inputs_matrix = DeviceMatrixChunk::new(&inputs_device[..], stride, 0, n);
            if (8..=12).contains(&log_n) {
                let mut ref_chunk = DeviceMatrixChunkMut::new(
                    &mut reference_slice[chunk_start..chunk_end],
                    stride,
                    0,
                    n,
                );
                monomials_to_evals_compact_1_pass(
                    &inputs_matrix,
                    &mut ref_chunk,
                    log_n,
                    coset_index,
                    coset_factor_shift,
                    1,
                    num_cols,
                    num_cols,
                    stream,
                )
                .unwrap();
            } else if log_n == 13 {
                let mut ref_chunk = DeviceMatrixChunkMut::new(
                    &mut reference_slice[chunk_start..chunk_end],
                    stride,
                    0,
                    n,
                );
                monomials_to_evals_2_pass_compact_initial(
                    &inputs_matrix,
                    &mut ref_chunk,
                    log_n,
                    coset_index,
                    coset_factor_shift,
                    1,
                    num_cols,
                    1,
                    num_cols,
                    stream,
                )
                .unwrap();
            } else {
                // log_n <= 7: the single-coset multi-coset entry at num_cosets=1.
                // `lde_with_coset_range` with num_cosets=1 declines the DIT
                // single-pass divisibility gate and (log_n <= 13) never takes the
                // lde-intermediate fast path, so it dispatches through the strategy
                // to a single-coset subwarp/compact launch — an independent baseline
                // that never re-enters the DIT engine under test.
                lde_with_coset_range(
                    &inputs_matrix,
                    &mut reference_slice[chunk_start..chunk_end],
                    log_n,
                    log_lde_factor,
                    1,
                    coset_index,
                    num_cols,
                    1,
                    1,
                    context.device_context(),
                    None,
                    stream,
                    device_props,
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
                    "log_n={log_n}, num_cosets={num_cosets}, num_cols={num_cols}, coset={coset_index}, col={col}, k={k}"
                );
            }
        }
    }
}

macro_rules! streaming_v4_parity_test {
    ($name:ident, $log_n:expr, $num_cosets:expr, $num_cols:expr) => {
        #[test]
        #[cfg(not(no_cuda))]
        fn $name() {
            run_streaming_vs_compact_parity($log_n, 2, $num_cosets, $num_cols);
        }
    };
}

macro_rules! streaming_v8_parity_test {
    ($name:ident, $log_n:expr, $num_cosets:expr, $num_cols:expr) => {
        #[test]
        #[cfg(not(no_cuda))]
        fn $name() {
            run_streaming_vs_compact_parity($log_n, 3, $num_cosets, $num_cols);
        }
    };
}

// One representative each (VPT=4 and VPT=8) of the streaming-vs-compact parity
// harness. The DIT range (log_n 2..13) that these route through the production
// multi-coset entry into the DIT engine is covered INDEPENDENTLY per
// (log_n, log_vpt) by the dit_engine parity tests (`dit_single_stream_*` /
// `dit_two_pass_*` vs a compact/lde/host oracle, plus `dit_launcher_*`) and by
// the strategy DIT-route cpu_tests. These anchors keep the end-to-end
// multi-coset-entry -> DIT path exercised at both VPTs.
streaming_v4_parity_test!(streaming_v4_log_n_2_cosets_256, 2, 256, 1);
streaming_v8_parity_test!(streaming_v8_parity_log_n_9_cosets_4, 9, 4, 4);

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
    use super::forward::{monomials_to_evals_compact_1_pass, monomials_to_evals_subwarp};
    use crate::ntt_twiddles::OMEGA_LOG_ORDER;
    use gpu_core::primitives::device_structures::{DeviceMatrixChunk, DeviceMatrixChunkMut};

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
        *value = BF::new(59 + (idx as u32).wrapping_mul(37));
    }
    let mut inputs_device = context.alloc(cols_size).unwrap();
    memory_copy_async(&mut inputs_device, &inputs_host, stream).unwrap();

    let mut candidate_device = context.alloc(total_size).unwrap();
    let mut reference_device = context.alloc(total_size).unwrap();

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

// Parity test for the sub-warp kernel at log_n in {1, 2, 3}: the subwarp
// dispatcher is validated against a PURE-CPU forward NTT
// (`host_forward_ntt_single_coset`) rather than another GPU kernel, so the
// reference is fully independent of the device path under test. The host oracle
// is evaluated once per (coset, col) the subwarp packs into one launch.
#[cfg(not(no_cuda))]
#[allow(dead_code)]
fn run_subwarp_vs_host_parity(
    log_n: usize,
    log_instances_per_block: usize,
    num_cosets: usize,
    num_cols: usize,
) {
    use super::forward::monomials_to_evals_subwarp;
    use super::OMEGA_LOG_ORDER;
    use fft::precompute_twiddles_for_fft;
    use gpu_core::primitives::device_structures::{DeviceMatrixChunk, DeviceMatrixChunkMut};
    use std::alloc::Global;
    use worker::Worker;

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
        *value = BF::new(41 + (idx as u32).wrapping_mul(53));
    }
    let mut inputs_device = context.alloc(cols_size).unwrap();
    memory_copy_async(&mut inputs_device, &inputs_host, stream).unwrap();

    let mut candidate_device = context.alloc(total_size).unwrap();

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
            stream,
        )
        .unwrap();
    }

    let mut candidate_host = vec![BF::ZERO; total_size];
    memory_copy_async(&mut candidate_host, &candidate_device, stream).unwrap();
    stream.synchronize().unwrap();

    // PURE-CPU ground truth: one independent forward NTT per (coset, col). No
    // GPU kernel participates in producing the expected values. `coset_index`
    // ranges over the tile (base 0), matching the subwarp coset-factor mapping.
    let worker = Worker::new();
    let forward_twiddles = precompute_twiddles_for_fft::<BF, Global, false>(n, &worker);
    let forward_twiddles = &forward_twiddles[..(n >> 1)];

    for coset_index in 0..num_cosets {
        for col in 0..num_cols {
            let col_monomials = &inputs_host[col * stride..col * stride + n];
            let expected = host_forward_ntt_single_coset(
                col_monomials,
                log_n,
                log_lde_factor,
                coset_index,
                forward_twiddles,
            );
            let base = coset_index * cols_size + col * stride;
            for k in 0..n {
                assert_eq!(
                    candidate_host[base + k],
                    expected[k],
                    "log_n={log_n}, log_ipb={log_instances_per_block}, num_cosets={num_cosets}, num_cols={num_cols}, coset={coset_index}, col={col}, k={k}"
                );
            }
        }
    }
}

macro_rules! subwarp_vs_host_parity_test {
    ($name:ident, $log_n:expr, $log_ipb:expr, $num_cosets:expr, $num_cols:expr) => {
        #[test]
        #[cfg(not(no_cuda))]
        fn $name() {
            run_subwarp_vs_host_parity($log_n, $log_ipb, $num_cosets, $num_cols);
        }
    };
}

// One IPB_max case per log_n in {1, 2, 3} (subwarp packs `num_cosets` instances
// per block) plus one IPB=1 fallback (BLOCK_THREADS = N, exercising the narrowed
// __shfl_xor_sync warp mask over multiple cosets).
subwarp_vs_host_parity_test!(subwarp_log_n_1_ipb_128_cosets_128_cols_1, 1, 7, 128, 1);
subwarp_vs_host_parity_test!(subwarp_log_n_2_ipb_64_cosets_64_cols_1, 2, 6, 64, 1);
subwarp_vs_host_parity_test!(subwarp_log_n_3_ipb_32_cosets_32_cols_1, 3, 5, 32, 1);
subwarp_vs_host_parity_test!(subwarp_log_n_3_ipb_1_cosets_4_cols_1, 3, 0, 4, 1);

// Extend the strategy-driven multi-coset parity sweep to log_n=1 (the
// multi-coset entry routes through the subwarp dispatch at this size too:
// IPB_max for workload >= IPB_max, IPB=1 for the per-coset reference). log_n
// 2/3 already have reps above; the extra coset counts only vary grid batching.
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_1_cosets_32, 1, 32);

mod dit_engine;
mod helpers;
mod lde_writeback_hybrid;
use crate::upstream::{Field, PrimeField};
#[allow(unused_imports)]
use helpers::*;

/// CPU reference: multilinear coefficients → hypercube evaluations.
/// Ported from `prover::gkr::whir::hypercube_to_monomial` to keep
/// `gpu_ntt` tests free of a `prover` dependency.
fn multivariate_coeffs_into_hypercube_evals<F: Field>(input: &mut [F], size_log2: u32) {
    assert_eq!(input.len(), 1 << size_log2);
    for [a, b] in input.as_chunks_mut::<2>().0.iter_mut() {
        b.add_assign(&*a);
    }
    let mut stride = 2;
    let mut iterations = 2;
    let len = 1 << size_log2;
    for _round in 1..size_log2 {
        let mut i = 0;
        while i < len {
            for _ in 0..iterations {
                let lhs = input[i];
                input[i + stride].add_assign(&lhs);
                i += 1;
            }
            i += iterations;
        }
        stride *= 2;
        iterations *= 2;
    }
}

/// CPU reference: hypercube evaluations → multilinear coefficients.
/// Ported from `prover::gkr::whir::hypercube_to_monomial` to keep
/// `gpu_ntt` tests free of a `prover` dependency.
fn multivariate_hypercube_evals_into_coeffs<F: Field>(input: &mut [F], size_log2: u32) {
    assert_eq!(input.len(), 1 << size_log2);
    let len = 1 << size_log2;
    let mut stride = len / 2;
    let mut iterations = len / 2;
    for _round in 1..size_log2 {
        let mut i = 0;
        while i < len {
            for _ in 0..iterations {
                let lhs = input[i];
                input[i + stride].sub_assign(&lhs);
                i += 1;
            }
            i += iterations;
        }
        stride /= 2;
        iterations /= 2;
    }
    for [a, b] in input.as_chunks_mut::<2>().0.iter_mut() {
        b.sub_assign(&*a);
    }
}

// ---------------------------------------------------------------------------
// Natural-order monomials -> bitreversed-order evals, multi-coset LDE.
// `out_k[p] = f(g_k * omega^rev_n(p))` from NATURAL-labeled coefficients.
// Three independent oracles:
//   A: duality against the old bitrev-monomials -> natural-evals family,
//   B: basis vectors (nothing GPU-derived on the expected side),
//   C: the CPU naive natural->bitreversed CT NTT (`fft` crate).
// ---------------------------------------------------------------------------
#[cfg(not(no_cuda))]
mod natural_to_bitrev {
    use super::super::forward::{
        monomials_to_evals_2_pass_compact_initial, monomials_to_evals_3_pass,
        natural_monomials_to_bitrev_evals_2_pass, natural_monomials_to_bitrev_evals_2_pass_compact,
        natural_monomials_to_bitrev_evals_3_pass,
    };
    use super::super::{
        bitreversed_monomials_to_natural_evals_multi_coset,
        natural_monomials_to_bitreversed_evals_coset_range,
        natural_monomials_to_bitreversed_evals_multi_coset,
    };
    use super::helpers::transpose_monomials;
    use super::{make_context, NttTestContext};
    use crate::ntt_twiddles::OMEGA_LOG_ORDER;
    use crate::upstream::{
        bitreverse_enumeration_inplace, distribute_powers_serial, domain_generator_for_size, Field,
    };
    use era_cudart::memory::memory_copy_async;
    use era_cudart::stream::CudaStream;
    use fft::precompute_twiddles_for_fft;
    use gpu_core::primitives::context::DeviceProperties;
    use gpu_core::primitives::device_structures::{DeviceMatrixChunk, DeviceMatrixChunkMut};
    use gpu_core::primitives::field::BF;
    use rand::rngs::StdRng;
    use rand::{Rng, SeedableRng};
    use std::alloc::Global;
    use worker::Worker;

    /// One test case's geometry. `stride_cols` is the launcher's
    /// `num_cols_per_coset_stride` (>= `num_cols`; larger leaves gaps between
    /// coset slabs).
    #[derive(Clone, Copy, Debug)]
    struct Shape {
        log_n: usize,
        log_lde_factor: usize,
        num_cosets: usize,
        coset_index_base: usize,
        num_cols: usize,
        stride_cols: usize,
        transposed: bool,
    }

    impl Shape {
        fn n(&self) -> usize {
            1usize << self.log_n
        }

        fn output_len(&self) -> usize {
            ((self.num_cosets - 1) * self.stride_cols + self.num_cols) * self.n()
        }

        fn is_full_range(&self) -> bool {
            self.coset_index_base == 0 && self.num_cosets == (1usize << self.log_lde_factor)
        }

        fn coset_factor_shift(&self) -> u32 {
            (OMEGA_LOG_ORDER as usize - self.log_n - self.log_lde_factor) as u32
        }

        /// Coset shift `g_k = tau^k` of the full LDE domain.
        fn coset_factor(&self, coset_offset: usize) -> BF {
            let tau = domain_generator_for_size::<BF>(1u64 << (self.log_n + self.log_lde_factor));
            tau.pow((self.coset_index_base + coset_offset) as u32)
        }

        fn slab(&self, coset_offset: usize, col: usize) -> std::ops::Range<usize> {
            let start = (coset_offset * self.stride_cols + col) * self.n();
            start..start + self.n()
        }
    }

    /// Physical backing for a logical coefficient matrix: every column goes
    /// through the SAME layout function both directions use (identity, or the
    /// 32x32-chunk transposition for the transposed-monomial layout).
    fn layout_columns(logical: &[Vec<BF>], transposed: bool) -> Vec<BF> {
        let mut backing = Vec::with_capacity(logical.len() * logical[0].len());
        for column in logical {
            let mut column = column.clone();
            if transposed {
                transpose_monomials(&mut column);
            }
            backing.extend_from_slice(&column);
        }
        backing
    }

    fn random_columns(shape: &Shape, seed: u64) -> Vec<Vec<BF>> {
        let mut rng = StdRng::seed_from_u64(seed);
        (0..shape.num_cols)
            .map(|_| {
                (0..shape.n())
                    .map(|_| BF::from_nonreduced_u32(rng.random()))
                    .collect()
            })
            .collect()
    }

    fn compare_slices(actual: &[BF], expected: &[BF], what: &str) {
        assert_eq!(actual.len(), expected.len(), "{what}: length mismatch");
        let first = (0..actual.len()).find(|&i| actual[i] != expected[i]);
        if let Some(idx) = first {
            let differing = (0..actual.len())
                .filter(|&i| actual[i] != expected[i])
                .count();
            panic!(
                "{what}: first divergence at row {idx} (0b{idx:b}): actual {:?}, expected {:?} \
                 ({differing} of {} rows differ)",
                actual[idx],
                expected[idx],
                actual.len(),
            );
        }
    }

    fn run_natural_to_bitrev(
        context: &NttTestContext,
        shape: &Shape,
        logical: &[Vec<BF>],
    ) -> Vec<BF> {
        let stream = context.get_exec_stream();
        let n = shape.n();
        let inputs_host = layout_columns(logical, shape.transposed);
        let mut inputs_device = context.alloc(inputs_host.len()).unwrap();
        memory_copy_async(&mut inputs_device, &inputs_host, stream).unwrap();
        let mut outputs_device = context.alloc(shape.output_len()).unwrap();
        {
            let inputs_matrix = DeviceMatrixChunk::new(&inputs_device[..], n, 0, n);
            if shape.is_full_range() {
                natural_monomials_to_bitreversed_evals_multi_coset(
                    &inputs_matrix,
                    &mut outputs_device[..],
                    shape.log_n,
                    shape.log_lde_factor,
                    shape.stride_cols,
                    shape.transposed,
                    context.device_context(),
                    None,
                    stream,
                    context.get_device_properties(),
                )
                .unwrap();
            } else {
                natural_monomials_to_bitreversed_evals_coset_range(
                    &inputs_matrix,
                    &mut outputs_device[..],
                    shape.log_n,
                    shape.log_lde_factor,
                    shape.num_cosets,
                    shape.coset_index_base,
                    shape.stride_cols,
                    shape.transposed,
                    context.device_context(),
                    None,
                    stream,
                    context.get_device_properties(),
                )
                .unwrap();
            }
        }
        let mut outputs_host = vec![BF::ZERO; shape.output_len()];
        memory_copy_async(&mut outputs_host, &outputs_device, stream).unwrap();
        stream.synchronize().unwrap();
        outputs_host
    }

    /// The old family (bitreversed monomials -> natural evals) fed the same
    /// logical coefficients through the same layout function.
    fn run_bitrev_to_natural(
        context: &NttTestContext,
        shape: &Shape,
        logical: &[Vec<BF>],
    ) -> Vec<BF> {
        let stream = context.get_exec_stream();
        let n = shape.n();
        let bitrev_labeled: Vec<Vec<BF>> = logical
            .iter()
            .map(|column| {
                let mut column = column.clone();
                bitreverse_enumeration_inplace(&mut column);
                column
            })
            .collect();
        let inputs_host = layout_columns(&bitrev_labeled, shape.transposed);
        let mut inputs_device = context.alloc(inputs_host.len()).unwrap();
        memory_copy_async(&mut inputs_device, &inputs_host, stream).unwrap();
        let mut outputs_device = context.alloc(shape.output_len()).unwrap();
        {
            let inputs_matrix = DeviceMatrixChunk::new(&inputs_device[..], n, 0, n);
            let mut outputs_matrix = DeviceMatrixChunkMut::new(&mut outputs_device[..], n, 0, n);
            monomials_to_evals_3_pass(
                &inputs_matrix,
                &mut outputs_matrix,
                shape.log_n,
                shape.coset_index_base,
                shape.coset_factor_shift(),
                shape.num_cosets,
                shape.stride_cols,
                shape.num_cosets,
                shape.num_cols,
                shape.transposed,
                stream,
            )
            .unwrap();
        }
        let mut outputs_host = vec![BF::ZERO; shape.output_len()];
        memory_copy_async(&mut outputs_host, &outputs_device, stream).unwrap();
        stream.synchronize().unwrap();
        outputs_host
    }

    /// ORACLE A: `new(natural c)[p] == old(bitrev-labeled c)[rev_n(p)]`, i.e.
    /// the new output is the row-bitreversal of the old one, per virtual
    /// `[coset][column][n]` slice (never across the padded backing).
    fn oracle_a_duality(shape: Shape, seed: u64) {
        let context = make_context();
        let logical = random_columns(&shape, seed);
        let new_outputs = run_natural_to_bitrev(&context, &shape, &logical);
        let old_outputs = run_bitrev_to_natural(&context, &shape, &logical);
        for coset_offset in 0..shape.num_cosets {
            for col in 0..shape.num_cols {
                let range = shape.slab(coset_offset, col);
                let mut expected = old_outputs[range.clone()].to_vec();
                bitreverse_enumeration_inplace(&mut expected);
                compare_slices(
                    &new_outputs[range],
                    &expected,
                    &format!(
                        "oracle A {shape:?} seed={seed:#x} coset_offset={coset_offset} col={col}"
                    ),
                );
            }
        }
    }

    /// ORACLE B: `c = e0` -> every output is ONE; `c = e1` -> `out_k[p] ==
    /// g_k * omega^rev_n(p)`. Column 0 carries e0, column 1 carries e1.
    fn oracle_b_basis_vectors(shape: Shape) {
        assert_eq!(
            shape.num_cols, 2,
            "oracle B uses column 0 = e0, column 1 = e1"
        );
        let context = make_context();
        let n = shape.n();
        let mut e0 = vec![BF::ZERO; n];
        e0[0] = BF::ONE;
        let mut e1 = vec![BF::ZERO; n];
        e1[1] = BF::ONE;
        let outputs = run_natural_to_bitrev(&context, &shape, &[e0, e1]);

        // omega^rev_n(p) for every output row p: natural powers, then
        // bitreversed so index p reads the rev_n(p)-th power.
        let omega = domain_generator_for_size::<BF>(n as u64);
        let mut omega_powers = vec![BF::ONE; n];
        distribute_powers_serial::<BF, BF>(&mut omega_powers, BF::ONE, omega);
        bitreverse_enumeration_inplace(&mut omega_powers);

        for coset_offset in 0..shape.num_cosets {
            let ones = vec![BF::ONE; n];
            compare_slices(
                &outputs[shape.slab(coset_offset, 0)],
                &ones,
                &format!("oracle B (c = e0) {shape:?} coset_offset={coset_offset}"),
            );
            let coset_factor = shape.coset_factor(coset_offset);
            let expected: Vec<BF> = omega_powers
                .iter()
                .map(|p| {
                    let mut v = *p;
                    v.mul_assign(&coset_factor);
                    v
                })
                .collect();
            compare_slices(
                &outputs[shape.slab(coset_offset, 1)],
                &expected,
                &format!("oracle B (c = e1) {shape:?} coset_offset={coset_offset}"),
            );
        }
    }

    /// ORACLE C: pure-CPU ground truth. Scale `c[i] *= g_k^i`, then the naive
    /// natural->bitreversed CT NTT; compare per coset and column.
    fn oracle_c_cpu_naive(shape: Shape, seed: u64) {
        let context = make_context();
        let logical = random_columns(&shape, seed);
        let outputs = run_natural_to_bitrev(&context, &shape, &logical);
        check_vs_cpu_naive(
            &shape,
            &logical,
            &outputs,
            &format!("oracle C {shape:?} seed={seed:#x}"),
        );
    }

    fn check_vs_cpu_naive(shape: &Shape, logical: &[Vec<BF>], outputs: &[BF], what: &str) {
        let n = shape.n();
        let worker = Worker::new();
        let twiddles = precompute_twiddles_for_fft::<BF, Global, false>(n, &worker);
        let twiddles = &twiddles[..(n >> 1)];
        for coset_offset in 0..shape.num_cosets {
            let mut coset_powers = vec![BF::ONE; n];
            distribute_powers_serial::<BF, BF>(
                &mut coset_powers,
                BF::ONE,
                shape.coset_factor(coset_offset),
            );
            for (col, column) in logical.iter().enumerate() {
                let mut expected = column.clone();
                for (value, power) in expected.iter_mut().zip(coset_powers.iter()) {
                    value.mul_assign(power);
                }
                fft::column_major::naive::serial_ct_ntt_natural_to_bitreversed::<BF, BF>(
                    &mut expected,
                    shape.log_n as u32,
                    twiddles,
                );
                compare_slices(
                    &outputs[shape.slab(coset_offset, col)],
                    &expected,
                    &format!("{what} coset_offset={coset_offset} col={col}"),
                );
            }
        }
    }

    const fn shape(
        log_n: usize,
        log_lde_factor: usize,
        num_cosets: usize,
        coset_index_base: usize,
        num_cols: usize,
        stride_cols: usize,
        transposed: bool,
    ) -> Shape {
        Shape {
            log_n,
            log_lde_factor,
            num_cosets,
            coset_index_base,
            num_cols,
            stride_cols,
            transposed,
        }
    }

    #[test]
    fn natural_to_bitrev_duality_matches_old_family() {
        for (shape, seed) in [
            (shape(21, 1, 2, 0, 3, 5, false), 0xa2),
            (shape(21, 1, 2, 0, 3, 5, true), 0xa3),
            (shape(22, 1, 2, 0, 1, 1, true), 0xa4),
            (shape(21, 2, 2, 2, 3, 4, true), 0xa7),
        ] {
            oracle_a_duality(shape, seed);
        }
    }

    #[test]
    fn natural_to_bitrev_basis_vectors_log_n_21() {
        oracle_b_basis_vectors(shape(21, 1, 2, 0, 2, 2, false));
    }

    #[test]
    fn natural_to_bitrev_vs_cpu_naive() {
        for (shape, seed) in [
            (shape(21, 1, 2, 0, 1, 1, false), 0xc1),
            (shape(21, 2, 2, 2, 1, 1, true), 0xc2),
        ] {
            oracle_c_cpu_naive(shape, seed);
        }
    }

    /// The fused natural boundary (hypercube coarse tail + monomial writeback
    /// + coset scale + DIT initial in one launch, over the fine->coarse
    /// pre-tail) must reproduce the unfused sequence bit-exactly: the
    /// multi-coset LDE output AND the materialized natural monomials.
    #[test]
    fn natural_fused_boundary_matches_unfused() {
        use super::super::{
            hypercube_evals_to_monomials, hypercube_to_multi_coset_bitrev_evals_fused,
        };
        for (sh, seed) in [
            (shape(21, 1, 2, 0, 1, 1, false), 0xf1),
            (shape(21, 2, 4, 0, 2, 3, false), 0xf2),
        ] {
            let context = make_context();
            let stream = context.get_exec_stream();
            let n = sh.n();
            let logical = random_columns(&sh, seed);
            let inputs_host = layout_columns(&logical, false);
            let mut inputs_device = context.alloc(inputs_host.len()).unwrap();
            memory_copy_async(&mut inputs_device, &inputs_host, stream).unwrap();

            // Unfused reference: full hypercube iNTT, then the natural LDE.
            let mut ref_monomials_device = context.alloc(sh.num_cols * n).unwrap();
            let mut ref_outputs_device = context.alloc(sh.output_len()).unwrap();
            {
                let inputs_matrix = DeviceMatrixChunk::new(&inputs_device[..], n, 0, n);
                let mut monomials_matrix =
                    DeviceMatrixChunkMut::new(&mut ref_monomials_device[..], n, 0, n);
                hypercube_evals_to_monomials(
                    &inputs_matrix,
                    &mut monomials_matrix,
                    sh.log_n,
                    false,
                    stream,
                    context.get_device_properties(),
                )
                .unwrap();
                let monomials_matrix = DeviceMatrixChunk::new(&ref_monomials_device[..], n, 0, n);
                natural_monomials_to_bitreversed_evals_multi_coset(
                    &monomials_matrix,
                    &mut ref_outputs_device[..],
                    sh.log_n,
                    sh.log_lde_factor,
                    sh.stride_cols,
                    false,
                    context.device_context(),
                    None,
                    stream,
                    context.get_device_properties(),
                )
                .unwrap();
            }

            // Fused arm (monomials are transient in the coset-0 slab; no scratch).
            let mut fused_outputs_device = context.alloc(sh.output_len()).unwrap();
            let fused = {
                let inputs_matrix = DeviceMatrixChunk::new(&inputs_device[..], n, 0, n);
                hypercube_to_multi_coset_bitrev_evals_fused(
                    &inputs_matrix,
                    &mut fused_outputs_device[..],
                    sh.log_n,
                    sh.log_lde_factor,
                    sh.stride_cols,
                    false,
                    None,
                    stream,
                    context.get_device_properties(),
                )
                .unwrap()
            };
            assert!(
                fused,
                "shape {sh:?} must be eligible for the fused boundary"
            );

            let mut ref_outputs = vec![BF::ZERO; sh.output_len()];
            let mut fused_outputs = vec![BF::ZERO; sh.output_len()];
            memory_copy_async(&mut ref_outputs, &ref_outputs_device, stream).unwrap();
            memory_copy_async(&mut fused_outputs, &fused_outputs_device, stream).unwrap();
            stream.synchronize().unwrap();
            compare_slices(&fused_outputs, &ref_outputs, "multi-coset LDE output");
        }
    }

    fn forced_launch_tiling_vs_cpu_naive(
        shape: Shape,
        seed: u64,
        what: &str,
        launch: impl FnOnce(
            &DeviceMatrixChunk<BF>,
            &mut DeviceMatrixChunkMut<BF>,
            &DeviceProperties,
            &CudaStream,
        ),
    ) {
        let context = make_context();
        let stream = context.get_exec_stream();
        let n = shape.n();
        let logical = random_columns(&shape, seed);
        let inputs_host = layout_columns(&logical, shape.transposed);
        let mut inputs_device = context.alloc(inputs_host.len()).unwrap();
        memory_copy_async(&mut inputs_device, &inputs_host, stream).unwrap();
        let mut outputs_device = context.alloc(shape.output_len()).unwrap();
        {
            let inputs_matrix = DeviceMatrixChunk::new(&inputs_device[..], n, 0, n);
            let mut outputs_matrix = DeviceMatrixChunkMut::new(&mut outputs_device[..], n, 0, n);
            launch(
                &inputs_matrix,
                &mut outputs_matrix,
                context.get_device_properties(),
                stream,
            );
        }
        let mut outputs = vec![BF::ZERO; shape.output_len()];
        memory_copy_async(&mut outputs, &outputs_device, stream).unwrap();
        stream.synchronize().unwrap();
        check_vs_cpu_naive(&shape, &logical, &outputs, what);
    }

    /// The launcher's column/coset tiling arithmetic, deterministically: the
    /// strategy picks a single launch for every shape a test box can afford, so
    /// drive the three-pass launcher directly at
    /// `cosets_per_launch = columns_per_launch = 1` (one launch per (col, coset))
    /// and oracle the result against the CPU naive NTT.
    #[test]
    fn natural_to_bitrev_forced_launch_tiling_vs_cpu_naive() {
        let shape = shape(21, 1, 2, 0, 3, 5, false);
        forced_launch_tiling_vs_cpu_naive(
            shape,
            0xc3,
            "forced launch tiling",
            |inputs_matrix, outputs_matrix, device_properties, stream| {
                natural_monomials_to_bitrev_evals_3_pass(
                    inputs_matrix,
                    outputs_matrix,
                    shape.log_n,
                    shape.coset_index_base,
                    shape.coset_factor_shift(),
                    shape.num_cosets,
                    shape.stride_cols,
                    1, // cosets_per_launch
                    1, // columns_per_launch
                    shape.transposed,
                    device_properties,
                    stream,
                )
                .unwrap();
            },
        );
    }

    /// `Entry` routes through the public entry with a synthetic 16 MB L2 (the
    /// real dev-box L2 would pick three-pass); `Direct` calls the two-pass
    /// launcher with forced tiling.
    #[derive(Clone, Copy, Debug)]
    enum TwoPassRoute {
        Entry,
        Direct {
            cosets_per_launch: usize,
            columns_per_launch: usize,
        },
    }

    fn synthetic_tiny_l2_props(context: &NttTestContext) -> DeviceProperties {
        let live = context.get_device_properties();
        DeviceProperties {
            l2_cache_size_bytes: 16 * 1024 * 1024,
            sm_count: live.sm_count,
            compute_capability_major: live.compute_capability_major,
            compute_capability_minor: live.compute_capability_minor,
            max_dynamic_smem_per_block_optin: live.max_dynamic_smem_per_block_optin,
        }
    }

    fn run_natural_to_bitrev_two_pass(
        context: &NttTestContext,
        shape: &Shape,
        logical: &[Vec<BF>],
        route: TwoPassRoute,
    ) -> Vec<BF> {
        let stream = context.get_exec_stream();
        let n = shape.n();
        let inputs_host = layout_columns(logical, shape.transposed);
        let mut inputs_device = context.alloc(inputs_host.len()).unwrap();
        memory_copy_async(&mut inputs_device, &inputs_host, stream).unwrap();
        let mut outputs_device = context.alloc(shape.output_len()).unwrap();
        {
            let inputs_matrix = DeviceMatrixChunk::new(&inputs_device[..], n, 0, n);
            match route {
                TwoPassRoute::Entry => {
                    let props = synthetic_tiny_l2_props(context);
                    let strategy = super::super::select_ntt_strategy(
                        super::super::NttDirection::NaturalToBitrev,
                        shape.log_n,
                        shape.num_cols,
                        shape.num_cosets,
                        &props,
                    )
                    .unwrap();
                    assert!(
                        strategy.passes.len() == 2
                            && matches!(
                                strategy.passes[0].kernel,
                                super::super::NttKernelKind::NaturalToBitrevFirst { .. }
                            ),
                        "synthetic 16 MB L2 must route {shape:?} to the two-pass plan, got {:?}",
                        strategy.passes,
                    );
                    natural_monomials_to_bitreversed_evals_coset_range(
                        &inputs_matrix,
                        &mut outputs_device[..],
                        shape.log_n,
                        shape.log_lde_factor,
                        shape.num_cosets,
                        shape.coset_index_base,
                        shape.stride_cols,
                        shape.transposed,
                        context.device_context(),
                        None,
                        stream,
                        &props,
                    )
                    .unwrap();
                }
                TwoPassRoute::Direct {
                    cosets_per_launch,
                    columns_per_launch,
                } => {
                    let mut outputs_matrix =
                        DeviceMatrixChunkMut::new(&mut outputs_device[..], n, 0, n);
                    natural_monomials_to_bitrev_evals_2_pass(
                        &inputs_matrix,
                        &mut outputs_matrix,
                        shape.log_n,
                        shape.coset_index_base,
                        shape.coset_factor_shift(),
                        shape.num_cosets,
                        shape.stride_cols,
                        cosets_per_launch,
                        columns_per_launch,
                        shape.transposed,
                        stream,
                    )
                    .unwrap();
                }
            }
        }
        let mut outputs_host = vec![BF::ZERO; shape.output_len()];
        memory_copy_async(&mut outputs_host, &outputs_device, stream).unwrap();
        stream.synchronize().unwrap();
        outputs_host
    }

    /// ORACLE A for the two-pass regime: same duality as `oracle_a_duality`,
    /// against the old bitrev-monomials -> natural-evals family.
    fn two_pass_oracle_a_duality(shape: Shape, seed: u64, route: TwoPassRoute) {
        let context = make_context();
        let logical = random_columns(&shape, seed);
        let new_outputs = run_natural_to_bitrev_two_pass(&context, &shape, &logical, route);
        let old_outputs = run_bitrev_to_natural(&context, &shape, &logical);
        for coset_offset in 0..shape.num_cosets {
            for col in 0..shape.num_cols {
                let range = shape.slab(coset_offset, col);
                let mut expected = old_outputs[range.clone()].to_vec();
                bitreverse_enumeration_inplace(&mut expected);
                compare_slices(
                    &new_outputs[range],
                    &expected,
                    &format!(
                        "two-pass oracle A {shape:?} seed={seed:#x} route={route:?} \
                         coset_offset={coset_offset} col={col}"
                    ),
                );
            }
        }
    }

    #[test]
    fn natural_to_bitrev_two_pass_duality_matches_old_family() {
        for (shape, seed) in [
            // Transposed monomials at log_n = 23 (pass-1 phase B): pass 1 resolves the
            // layout on its output rows, so pass 2 sees natural row order.
            (shape(23, 1, 2, 0, 1, 1, true), 0xb2),
            // Transposed monomials at log_n = 24 (pass-1 phase A).
            (shape(24, 1, 2, 0, 1, 1, true), 0xb4),
        ] {
            two_pass_oracle_a_duality(shape, seed, TwoPassRoute::Entry);
        }
    }

    /// ORACLE C for the two-pass regime: pure-CPU ground truth, on the
    /// transposed layout over a non-zero coset base.
    #[test]
    fn natural_to_bitrev_two_pass_vs_cpu_naive_log_n_23_range_base_2_transposed() {
        let shape = shape(23, 2, 2, 2, 1, 1, true);
        let context = make_context();
        let logical = random_columns(&shape, 0xc5);
        let outputs =
            run_natural_to_bitrev_two_pass(&context, &shape, &logical, TwoPassRoute::Entry);
        check_vs_cpu_naive(&shape, &logical, &outputs, "two-pass oracle C");
    }

    /// The two-pass launcher's column / coset tiling loops: one launch per
    /// (column, coset) over a padded output stride and a non-zero coset base.
    #[test]
    fn natural_to_bitrev_two_pass_forced_launch_tiling_log_n_23() {
        two_pass_oracle_a_duality(
            shape(23, 2, 2, 2, 3, 5, true),
            0xb5,
            TwoPassRoute::Direct {
                cosets_per_launch: 1,
                columns_per_launch: 1,
            },
        );
    }

    /// ORACLE A leg for the two-pass-compact range: the OLD family's own
    /// two-pass-compact plan (`first_K_stages_compact` + `noninitial_8`), which
    /// is what covers log_n in [13, 20] on the bitrev-monomials side (the
    /// three-pass forward kernels exist only for log_n in [21, 24]).
    fn run_bitrev_to_natural_two_pass_compact(
        context: &NttTestContext,
        shape: &Shape,
        logical: &[Vec<BF>],
    ) -> Vec<BF> {
        assert!(!shape.transposed);
        let stream = context.get_exec_stream();
        let n = shape.n();
        let bitrev_labeled: Vec<Vec<BF>> = logical
            .iter()
            .map(|column| {
                let mut column = column.clone();
                bitreverse_enumeration_inplace(&mut column);
                column
            })
            .collect();
        let inputs_host = layout_columns(&bitrev_labeled, false);
        let mut inputs_device = context.alloc(inputs_host.len()).unwrap();
        memory_copy_async(&mut inputs_device, &inputs_host, stream).unwrap();
        let mut outputs_device = context.alloc(shape.output_len()).unwrap();
        {
            let inputs_matrix = DeviceMatrixChunk::new(&inputs_device[..], n, 0, n);
            let mut outputs_matrix = DeviceMatrixChunkMut::new(&mut outputs_device[..], n, 0, n);
            monomials_to_evals_2_pass_compact_initial(
                &inputs_matrix,
                &mut outputs_matrix,
                shape.log_n,
                shape.coset_index_base,
                shape.coset_factor_shift(),
                shape.num_cosets,
                shape.stride_cols,
                shape.num_cosets,
                shape.num_cols,
                stream,
            )
            .unwrap();
        }
        let mut outputs_host = vec![BF::ZERO; shape.output_len()];
        memory_copy_async(&mut outputs_host, &outputs_device, stream).unwrap();
        stream.synchronize().unwrap();
        outputs_host
    }

    fn two_pass_compact_oracle_a_duality(shape: Shape, seed: u64) {
        let context = make_context();
        let logical = random_columns(&shape, seed);
        let new_outputs = run_natural_to_bitrev(&context, &shape, &logical);
        let old_outputs = run_bitrev_to_natural_two_pass_compact(&context, &shape, &logical);
        for coset_offset in 0..shape.num_cosets {
            for col in 0..shape.num_cols {
                let range = shape.slab(coset_offset, col);
                let mut expected = old_outputs[range.clone()].to_vec();
                bitreverse_enumeration_inplace(&mut expected);
                compare_slices(
                    &new_outputs[range],
                    &expected,
                    &format!(
                        "two-pass-compact oracle A {shape:?} seed={seed:#x} \
                         coset_offset={coset_offset} col={col}"
                    ),
                );
            }
        }
    }

    #[test]
    fn natural_to_bitrev_two_pass_compact_vs_cpu_naive() {
        for (shape, seed) in [
            // log_n = 20: the only sub-21 base size the commitment layer asks for.
            (shape(20, 1, 2, 0, 1, 1, false), 0xd1),
            (shape(20, 2, 2, 2, 3, 5, false), 0xd2),
            // The bottom of the family's range (K = log_n - 8 = 5 pass-2 stages).
            (shape(13, 1, 2, 0, 3, 3, false), 0xd3),
        ] {
            oracle_c_cpu_naive(shape, seed);
        }
    }

    #[test]
    fn natural_to_bitrev_two_pass_compact_duality_matches_old_family() {
        for (shape, seed) in [
            (shape(20, 1, 2, 0, 1, 1, false), 0xd5),
            (shape(20, 2, 2, 2, 3, 5, false), 0xd6),
        ] {
            two_pass_compact_oracle_a_duality(shape, seed);
        }
    }

    /// The two-pass-compact launcher's column / coset tiling loops: one launch
    /// per (column, coset) over a padded output stride and a non-zero coset
    /// base, oracled against the CPU naive NTT.
    #[test]
    fn natural_to_bitrev_two_pass_compact_forced_launch_tiling_log_n_20() {
        let shape = shape(20, 2, 2, 2, 3, 5, false);
        forced_launch_tiling_vs_cpu_naive(
            shape,
            0xd8,
            "two-pass-compact forced launch tiling",
            |inputs_matrix, outputs_matrix, _device_properties, stream| {
                natural_monomials_to_bitrev_evals_2_pass_compact(
                    inputs_matrix,
                    outputs_matrix,
                    shape.log_n,
                    shape.coset_index_base,
                    shape.coset_factor_shift(),
                    shape.num_cosets,
                    shape.stride_cols,
                    1, // cosets_per_launch
                    1, // columns_per_launch
                    shape.transposed,
                    stream,
                )
                .unwrap();
            },
        );
    }

    /// The transposed-monomial layout has no path in this range: pass 2
    /// exchanges rows inside a 1024-row transposition chunk, and
    /// `log_size_supports_transposed_monomials` is false below log_n = 21, so
    /// the launcher rejects it instead of computing garbage.
    #[test]
    #[should_panic(expected = "transposed_monomials")]
    fn natural_to_bitrev_two_pass_compact_rejects_transposed() {
        let context = make_context();
        let shape = shape(20, 1, 2, 0, 1, 1, true);
        let logical = random_columns(&shape, 0xd7);
        run_natural_to_bitrev(&context, &shape, &logical);
    }
}
