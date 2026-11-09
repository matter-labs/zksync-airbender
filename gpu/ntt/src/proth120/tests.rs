use std::ops::Range;

use era_cudart::memory::{memory_copy, memory_copy_async, DeviceAllocation};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::device_structures::{DeviceMatrixChunk, DeviceMatrixChunkMut};
use gpu_core::primitives::field::PR;
use rand::{rngs::StdRng, Rng, SeedableRng};

use super::hypercube::hypercube_evals_to_monomials_in_place;
use super::{hypercube_evals_to_monomials, pack_hypercubes_to_monomials, update_eq_poly, EqSample};
use crate::upstream::{
    multivariate_hypercube_evals_into_coeffs_radix4, Backend, Field, GenericAllocationPool,
    Proth120WorkStealingLazyBackend, Worker,
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

#[test]
#[cfg(not(no_cuda))]
fn pr_hypercube_cpu_parity() {
    let stream = CudaStream::create().unwrap();
    let mut rng = StdRng::seed_from_u64(SEED);
    // Diagnostic: reduced rows, production base column count.
    let logs = [16];
    for log_n in logs {
        let rows = 1usize << log_n;
        let stride = rows + GUARD;
        let columns: Vec<Vec<PR>> = (0..12)
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
        "Proth120 hypercube transform: logs {logs:?}, 12 columns, out of place and in place, 0 mismatches"
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
    // Wrap packing shape, including the partial final group of columns.
    pack_case(&stream, &worker, &mut rng, 21, 3, 10);
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
    for log_n in [23, 19, 15, 11] {
        let rows = 1usize << log_n;
        let ood = [EqSample {
            point: random_field(&mut rng),
            weight: random_nonzero(&mut rng),
        }];
        let initial: Vec<PR> = (0..rows).map(|_| random_nonzero(&mut rng)).collect();
        let mut expected = initial.clone();
        <Proth120WorkStealingLazyBackend as Backend<PR, PR>>::update_eq_poly(
            &Proth120WorkStealingLazyBackend,
            &mut expected,
            &[(ood[0].point, ood[0].weight)],
            &[],
            &worker,
        );
        let mut guarded = vec![SENTINEL; rows + 2 * GUARD];
        guarded[GUARD..GUARD + rows].copy_from_slice(&initial);
        let mut device_eq = upload(&guarded);
        let device_ood = upload(&ood);
        update_eq_poly(&mut device_eq[GUARD..GUARD + rows], &device_ood, &stream).unwrap();
        let actual = download(&device_eq, &stream);
        assert_guards(&actual, GUARD..GUARD + rows);
        assert_raw_eq(&actual[GUARD..GUARD + rows], &expected);
        assert_samples_unchanged(&device_ood, &ood, &stream);
    }
}
