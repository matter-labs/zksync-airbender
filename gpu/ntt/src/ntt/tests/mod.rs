use std::alloc::Global;

use era_cudart::memory::{memory_copy_async, DeviceAllocation};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use worker::Worker;

use super::{hypercube_evals_natural_to_bitreversed_coeffs, natural_evals_to_bitreversed_coeffs};
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

        let mut src = context.alloc(n).unwrap();
        let mut dst = context.alloc(n).unwrap();
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
        wrap_monomials_to_evals_2_pass,
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
        wrap_monomials_to_evals_2_pass,
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
        wrap_monomials_to_evals_2_pass,
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
        wrap_monomials_to_evals_2_pass,
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
        *value = BF::new((23 + (idx as u32).wrapping_mul(41)) as u32);
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
                    false,
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
                    false,
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

// Compact 1-pass range: kernel batches all cosets into one launch.
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_4_cosets_4, 4, 4);
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
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_7_cosets_8, 7, 8);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_8_cosets_32, 8, 32);
// Multi-coset parity over the small-`log_n` range (2..8): the candidate runs
// through the production multi-coset entry (DIT where applicable, else
// subwarp/compact) and is checked against the independent compact baseline.
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_2_cosets_256, 2, 256);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_3_cosets_256, 3, 256);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_4_cosets_128, 4, 128);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_4_cosets_256, 4, 256);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_5_cosets_64, 5, 64);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_6_cosets_32, 6, 32);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_7_cosets_16, 7, 16);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_8_cosets_8, 8, 8);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_11_cosets_16, 11, 16);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_12_cosets_4, 12, 4);
// Strategy-driven parity tests for the two-pass streaming kernel (log_n 9..12)
// and a regression check for the two-pass-compact kernel at log_n=13. The
// `select_forward_strategy` dispatcher routes log_n in [9, 12] through the new
// streaming kernel; log_n=13 falls into `TWO_PASS_COMPACT` and routes to
// `MonomialsToEvalsFirstCompact + NonInitial` (pre-existing).
multi_coset_parity_test!(streaming_log_n_9, 9, 256);
multi_coset_parity_test!(streaming_log_n_10, 10, 128);
multi_coset_parity_test!(streaming_log_n_11, 11, 64);
multi_coset_parity_test!(streaming_log_n_12, 12, 32);
multi_coset_parity_test!(streaming_log_n_13, 13, 16);
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
                        false,
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
                        outputs_host[base + k], expected[k],
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
        run_host_oracle_forward_parity(14, 7, 64, 64, 2, Route::LdeWithCosetRange, 0x1de_14u64);
    }

    #[test]
    fn host_oracle_lde_intermediate_log_n_18_matches() {
        run_host_oracle_forward_parity(18, 5, 16, 16, 2, Route::LdeWithCosetRange, 0x1de_18u64);
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
        *value = BF::new((73 + (idx as u32).wrapping_mul(29)) as u32);
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
        *value = BF::new((97 + (idx as u32).wrapping_mul(53)) as u32);
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
                    false,
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
                    false,
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

// VPT=4 boundary cases (num_cosets == cosets_per_iter = 256 >> (log_n - 2)).
streaming_v4_parity_test!(streaming_v4_log_n_2_cosets_256, 2, 256, 1);
streaming_v4_parity_test!(streaming_v4_log_n_3_cosets_128, 3, 128, 1);
streaming_v4_parity_test!(streaming_v4_log_n_4_cosets_64, 4, 64, 1);
streaming_v4_parity_test!(streaming_v4_log_n_5_cosets_32, 5, 32, 1);
streaming_v4_parity_test!(streaming_v4_log_n_6_cosets_16, 6, 16, 1);
streaming_v4_parity_test!(streaming_v4_log_n_7_cosets_8, 7, 8, 1);
// Multi-iter cases: num_cosets > cosets_per_iter exercises the running shift.
streaming_v4_parity_test!(streaming_v4_log_n_2_cosets_512, 2, 512, 1);
streaming_v4_parity_test!(streaming_v4_log_n_3_cosets_512, 3, 512, 1);
streaming_v4_parity_test!(streaming_v4_log_n_4_cosets_256, 4, 256, 1);
streaming_v4_parity_test!(streaming_v4_log_n_7_cosets_32, 7, 32, 1);
// Multi-column: caller loops over columns externally.
streaming_v4_parity_test!(streaming_v4_log_n_5_cosets_64_cols_4, 5, 64, 4);

// v8 sanity case — single-pass should already cover log_n=8
streaming_v8_parity_test!(streaming_v8_parity_log_n_8_cosets_8, 8, 8, 4);

streaming_v8_parity_test!(streaming_v8_parity_log_n_9_cosets_4, 9, 4, 4);
streaming_v8_parity_test!(streaming_v8_parity_log_n_10_cosets_2, 10, 2, 4);
streaming_v8_parity_test!(streaming_v8_parity_log_n_11_cosets_1, 11, 1, 4);
streaming_v8_parity_test!(streaming_v8_parity_log_n_12_cosets_1, 12, 1, 4);
streaming_v8_parity_test!(streaming_v8_parity_log_n_13_cosets_1, 13, 1, 4);

streaming_v4_parity_test!(streaming_v4_parity_log_n_8_cosets_4, 8, 4, 4);
streaming_v4_parity_test!(streaming_v4_parity_log_n_9_cosets_2, 9, 2, 4);
streaming_v4_parity_test!(streaming_v4_parity_log_n_10_cosets_1, 10, 1, 4);
streaming_v4_parity_test!(streaming_v4_parity_log_n_11_cosets_1, 11, 1, 4);
streaming_v4_parity_test!(streaming_v4_parity_log_n_12_cosets_1, 12, 1, 4);

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
        *value = BF::new((59 + (idx as u32).wrapping_mul(37)) as u32);
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
        *value = BF::new((41 + (idx as u32).wrapping_mul(53)) as u32);
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
            false,
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
                    candidate_host[base + k], expected[k],
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

// Extend the strategy-driven multi-coset parity sweep to log_n in {1, 2, 3}:
// the multi-coset entry now routes through the strategy at these sizes too,
// hitting the subwarp dispatch (IPB_max for workload >= IPB_max, IPB=1 for
// the per-coset reference).
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_1_cosets_32, 1, 32);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_2_cosets_16, 2, 16);
multi_coset_parity_test!(multi_coset_monomials_to_evals_log_n_3_cosets_8, 3, 8);

mod dit_engine;
mod helpers;
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
