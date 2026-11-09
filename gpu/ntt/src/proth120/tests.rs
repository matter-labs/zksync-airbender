use std::alloc::Global;
use std::ops::Range;

use era_cudart::memory::{memory_copy, memory_copy_async, DeviceAllocation};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::device_structures::{DeviceMatrixChunk, DeviceMatrixChunkMut};
use gpu_core::primitives::field::PR;
use rand::{rngs::StdRng, Rng, SeedableRng};

use super::hypercube::hypercube_evals_to_monomials_in_place;
use super::{
    hypercube_evals_to_monomials, lde_coset, pack_hypercubes_to_monomials, update_eq_poly,
    DeviceContext, EqSample,
};
use crate::upstream::{
    domain_generator_for_size, lde_coset_lazy_r8, multivariate_hypercube_evals_into_coeffs_radix4,
    Backend, Field, GenericAllocationPool, Proth120WorkStealingLazyBackend, Twiddles, Worker,
};

const SEED: u64 = 0x9120_0003;
const GUARD: usize = 16;
const SENTINEL: PR = PR {
    0: u128::from_le_bytes([0xAA; 16]),
};

fn random_field(rng: &mut StdRng) -> PR {
    PR::new(rng.random::<u128>() % PR::ORDER)
}

fn random_nonzero(rng: &mut StdRng) -> PR {
    PR::new(1 + rng.random::<u128>() % (PR::ORDER - 1))
}

fn upload<T: Copy>(values: &[T]) -> DeviceAllocation<T> {
    let mut device = DeviceAllocation::<T>::alloc(values.len()).unwrap();
    memory_copy(&mut device, values).unwrap();
    device
}

fn download(values: &DeviceSlice<PR>, stream: &CudaStream) -> Vec<PR> {
    let mut host = vec![PR::ZERO; values.len()];
    memory_copy_async(&mut host, values, stream).unwrap();
    stream.synchronize().unwrap();
    host
}

fn assert_raw_eq(actual: &[PR], expected: &[PR]) {
    assert_eq!(actual.len(), expected.len());
    for (index, (actual, expected)) in actual.iter().zip(expected).enumerate() {
        assert!(actual.0 < PR::ORDER, "noncanonical output at {index}");
        assert_eq!(actual.0, expected.0, "output at {index}");
    }
}

fn assert_unchanged(actual: &[PR], expected: &[PR]) {
    assert_eq!(actual.len(), expected.len());
    for (index, (actual, expected)) in actual.iter().zip(expected).enumerate() {
        assert_eq!(actual.0, expected.0, "changed input at {index}");
        if expected.0 != SENTINEL.0 {
            assert!(actual.0 < PR::ORDER, "noncanonical input at {index}");
        }
    }
}

fn assert_guards(values: &[PR], payload: Range<usize>) {
    assert!(values[..payload.start]
        .iter()
        .all(|value| value.0 == SENTINEL.0));
    assert!(values[payload.end..]
        .iter()
        .all(|value| value.0 == SENTINEL.0));
}

fn assert_matrix_output(actual: &[PR], expected: &[Vec<PR>], rows: usize, stride: usize) {
    for column in 0..expected.len() {
        let start = GUARD + column * stride;
        assert!(actual[start..start + GUARD]
            .iter()
            .all(|value| value.0 == SENTINEL.0));
        assert_raw_eq(
            &actual[start + GUARD..start + GUARD + rows],
            &expected[column],
        );
    }
    assert_guards(actual, GUARD..actual.len() - GUARD);
}

fn guarded_columns(columns: &[Vec<PR>], rows: usize) -> Vec<PR> {
    let stride = rows + GUARD;
    let mut buffer = vec![SENTINEL; columns.len() * stride + 2 * GUARD];
    for (column, values) in columns.iter().enumerate() {
        let start = 2 * GUARD + column * stride;
        buffer[start..start + rows].copy_from_slice(values);
    }
    buffer
}

fn subset_sum_coefficients(values: &[PR]) -> Vec<PR> {
    (0..values.len())
        .map(|mask| {
            let mut coefficient = PR::ZERO;
            let mut subset = mask;
            loop {
                if (mask ^ subset).count_ones().is_multiple_of(2) {
                    coefficient.add_assign(&values[subset]);
                } else {
                    coefficient.sub_assign(&values[subset]);
                }
                if subset == 0 {
                    break;
                }
                subset = (subset - 1) & mask;
            }
            coefficient
        })
        .collect()
}

#[test]
#[cfg(not(no_cuda))]
fn pr_hypercube_cpu_parity() {
    let stream = CudaStream::create().unwrap();
    let mut rng = StdRng::seed_from_u64(SEED);
    let logs = [0, 1, 2, 3, 8, 12, 13, 14, 15, 17, 19, 20];
    for log_n in logs {
        let rows = 1usize << log_n;
        let stride = rows + GUARD;
        let columns: Vec<Vec<PR>> = (0..3)
            .map(|column| {
                (0..rows)
                    .map(|row| match column {
                        0 => PR::ZERO,
                        1 if !row.is_multiple_of(8) => PR::new(PR::ORDER - 1),
                        _ => random_field(&mut rng),
                    })
                    .collect()
            })
            .collect();
        let expected: Vec<Vec<PR>> = columns
            .iter()
            .map(|values| {
                let mut coefficients = values.clone();
                multivariate_hypercube_evals_into_coeffs_radix4(&mut coefficients, log_n);
                if log_n <= 4 {
                    assert_raw_eq(&subset_sum_coefficients(values), &coefficients);
                }
                coefficients
            })
            .collect();
        let input = guarded_columns(&columns, rows);
        let device_input = upload(&input);
        let mut device_output = upload(&vec![SENTINEL; input.len()]);
        let input_matrix = DeviceMatrixChunk::new(
            &device_input[GUARD..input.len() - GUARD],
            stride,
            GUARD,
            rows,
        );
        let mut output_matrix = DeviceMatrixChunkMut::new(
            &mut device_output[GUARD..input.len() - GUARD],
            stride,
            GUARD,
            rows,
        );
        hypercube_evals_to_monomials(&input_matrix, &mut output_matrix, &stream).unwrap();
        assert_matrix_output(&download(&device_output, &stream), &expected, rows, stride);
        assert_unchanged(&download(&device_input, &stream), &input);
        let mut device_values = upload(&input);
        let mut values_matrix = DeviceMatrixChunkMut::new(
            &mut device_values[GUARD..input.len() - GUARD],
            stride,
            GUARD,
            rows,
        );
        hypercube_evals_to_monomials_in_place(&mut values_matrix, &stream).unwrap();
        assert_matrix_output(&download(&device_values, &stream), &expected, rows, stride);
    }
    println!(
        "Proth120 hypercube transform: logs {logs:?}, 3 columns, out of place and in place, 0 mismatches"
    );
}

fn pack_case(
    stream: &CudaStream,
    worker: &Worker,
    rng: &mut StdRng,
    log_rows: u32,
    pack_log2: u32,
    cols: usize,
) -> (DeviceAllocation<PR>, Vec<Vec<PR>>) {
    let rows = 1usize << log_rows;
    let out_rows = rows << pack_log2;
    let out_cols = cols.div_ceil(1 << pack_log2);
    let columns: Vec<Vec<PR>> = (0..cols)
        .map(|_| (0..rows).map(|_| random_field(rng)).collect())
        .collect();
    let evals: Vec<&[PR]> = columns.iter().map(Vec::as_slice).collect();
    let pool = GenericAllocationPool::<PR, PR>::proxy();
    let expected = <Proth120WorkStealingLazyBackend as Backend<PR, PR>>::pack_polys_from_hypercubes_to_monomials(
        &Proth120WorkStealingLazyBackend,
        &evals,
        pack_log2 as usize,
        &pool,
        worker,
    );
    assert_eq!(expected.len(), out_cols);
    let input = guarded_columns(&columns, rows);
    let in_stride = rows + GUARD;
    let out_stride = out_rows + GUARD;
    let output_len = out_cols * out_stride + 2 * GUARD;
    let device_input = upload(&input);
    let mut device_output = upload(&vec![SENTINEL; output_len]);
    let input_matrix = DeviceMatrixChunk::new(
        &device_input[GUARD..input.len() - GUARD],
        in_stride,
        GUARD,
        rows,
    );
    let mut output_matrix = DeviceMatrixChunkMut::new(
        &mut device_output[GUARD..output_len - GUARD],
        out_stride,
        GUARD,
        out_rows,
    );
    pack_hypercubes_to_monomials(&input_matrix, &mut output_matrix, pack_log2, stream).unwrap();
    assert_matrix_output(
        &download(&device_output, stream),
        &expected,
        out_rows,
        out_stride,
    );
    assert_unchanged(&download(&device_input, stream), &input);
    (device_output, expected)
}

#[test]
#[cfg(not(no_cuda))]
fn pr_pack_cpu_parity() {
    let stream = CudaStream::create().unwrap();
    let worker = Worker::new_with_num_threads(8);
    let mut rng = StdRng::seed_from_u64(SEED);
    let shapes = [(3, 5)]
        .into_iter()
        .chain((0..=5).map(|pack_log2| (8, pack_log2)))
        .chain((0..=5).map(|pack_log2| (12, pack_log2)));
    let mut cases = 0;
    for (log_rows, pack_log2) in shapes {
        for cols in [1, 10, 16, 17, 38, 66, 104] {
            pack_case(&stream, &worker, &mut rng, log_rows, pack_log2, cols);
            cases += 1;
        }
    }
    assert_eq!(cases, 91);
    pack_case(&stream, &worker, &mut rng, 1, 17, 100000);
    pack_case(&stream, &worker, &mut rng, 0, 8, 300);
    let ctx = DeviceContext::create().unwrap();
    let (packed, monomials) = pack_case(&stream, &worker, &mut rng, 8, 4, 17);
    let packed_before = download(&packed, &stream);
    let rows = 1usize << 12;
    let stride = rows + GUARD;
    let nu = domain_generator_for_size::<PR>(1u64 << 31);
    let twiddles = Twiddles::<PR, Global>::new(rows, &worker);
    let expected: Vec<Vec<PR>> = monomials
        .iter()
        .map(|values| lde_coset_lazy_r8(values, nu, &twiddles.forward_twiddles[..rows / 2]))
        .collect();
    let mut device_output = upload(&vec![SENTINEL; packed.len()]);
    let device_offset = upload(&[nu]);
    let input_matrix =
        DeviceMatrixChunk::new(&packed[GUARD..packed.len() - GUARD], stride, GUARD, rows);
    let mut output_matrix = DeviceMatrixChunkMut::new(
        &mut device_output[GUARD..packed.len() - GUARD],
        stride,
        GUARD,
        rows,
    );
    lde_coset(
        &ctx,
        &input_matrix,
        &mut output_matrix,
        &device_offset,
        &stream,
    )
    .unwrap();
    assert_matrix_output(&download(&device_output, &stream), &expected, rows, stride);
    assert_unchanged(&download(&packed, &stream), &packed_before);
    assert_raw_eq(&download(&device_offset, &stream), &[nu]);
    println!(
        "Proth120 pack: {cases} shapes + (1,17,100000) + (0,8,300) + packed LDE at nu^1, 0 mismatches"
    );
}

fn eq_product_oracle(eq: &mut [PR], ood: &[EqSample], in_domain: &[EqSample]) {
    let log_n = eq.len().trailing_zeros();
    for sample in ood.iter().chain(in_domain) {
        for (index, value) in eq.iter_mut().enumerate() {
            let mut point = sample.point;
            let mut contribution = sample.weight;
            for bit in 0..log_n {
                let factor = if (index >> bit) & 1 == 1 {
                    point
                } else {
                    let mut complement = PR::ONE;
                    complement.sub_assign(&point);
                    complement
                };
                contribution.mul_assign(&factor);
                point.square();
            }
            value.add_assign(&contribution);
        }
    }
}

fn eq_samples(
    rng: &mut StdRng,
    count: usize,
    point_kind: u32,
    zero_weights: bool,
) -> Vec<EqSample> {
    (0..count)
        .map(|_| EqSample {
            point: match point_kind {
                0 => PR::ZERO,
                1 => PR::ONE,
                _ => random_field(rng),
            },
            weight: if zero_weights {
                PR::ZERO
            } else {
                random_nonzero(rng)
            },
        })
        .collect()
}

fn assert_samples_unchanged(
    actual: &DeviceSlice<EqSample>,
    expected: &[EqSample],
    stream: &CudaStream,
) {
    let mut host = expected.to_vec();
    memory_copy_async(&mut host, actual, stream).unwrap();
    stream.synchronize().unwrap();
    for (actual, expected) in host.iter().zip(expected) {
        assert_raw_eq(
            &[actual.point, actual.weight],
            &[expected.point, expected.weight],
        );
    }
}

#[test]
#[cfg(not(no_cuda))]
fn pr_eq_update_cpu_parity() {
    let stream = CudaStream::create().unwrap();
    let worker = Worker::new_with_num_threads(8);
    let mut rng = StdRng::seed_from_u64(SEED);
    let logs = [0, 1, 2, 3, 8, 9, 10, 11, 12, 16];
    let lists = [(0, 0), (1, 0), (1, 17), (0, 5), (3, 3)];
    let mut cases = 0;
    for log_n in logs {
        let rows = 1usize << log_n;
        for (ood_count, in_count) in lists {
            for point_kind in 0..3 {
                for zero_weights in [true, false] {
                    let ood = eq_samples(&mut rng, ood_count, point_kind, zero_weights);
                    let in_domain = eq_samples(&mut rng, in_count, point_kind, zero_weights);
                    let initial: Vec<PR> = (0..rows).map(|_| random_nonzero(&mut rng)).collect();
                    let mut expected = initial.clone();
                    if log_n >= 2 || ood_count == 1 {
                        let ood_pairs: Vec<_> = ood.iter().map(|s| (s.point, s.weight)).collect();
                        let in_pairs: Vec<_> =
                            in_domain.iter().map(|s| (s.point, s.weight)).collect();
                        <Proth120WorkStealingLazyBackend as Backend<PR, PR>>::update_eq_poly(
                            &Proth120WorkStealingLazyBackend,
                            &mut expected,
                            &ood_pairs,
                            &in_pairs,
                            &worker,
                        );
                    } else {
                        eq_product_oracle(&mut expected, &ood, &in_domain);
                    }
                    let mut guarded = vec![SENTINEL; rows + 2 * GUARD];
                    guarded[GUARD..GUARD + rows].copy_from_slice(&initial);
                    let mut device_eq = upload(&guarded);
                    let device_ood = upload(&ood);
                    let device_in_domain = upload(&in_domain);
                    update_eq_poly(
                        &mut device_eq[GUARD..GUARD + rows],
                        &device_ood,
                        &device_in_domain,
                        &stream,
                    )
                    .unwrap();
                    let actual = download(&device_eq, &stream);
                    assert_guards(&actual, GUARD..GUARD + rows);
                    assert_raw_eq(&actual[GUARD..GUARD + rows], &expected);
                    assert_samples_unchanged(&device_ood, &ood, &stream);
                    assert_samples_unchanged(&device_in_domain, &in_domain, &stream);
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 300);
    println!("Proth120 eq update: logs {logs:?}, {cases} cases, 0 mismatches");
}
