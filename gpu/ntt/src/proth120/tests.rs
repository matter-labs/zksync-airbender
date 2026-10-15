use std::alloc::Global;
use std::mem::{align_of, size_of};
use std::ops::Range;

use era_cudart::memory::{memory_copy, memory_copy_async, memory_get_info, DeviceAllocation};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::device_structures::{DeviceMatrixChunk, DeviceMatrixChunkMut};
use gpu_core::primitives::field::PR;
use rand::{rngs::StdRng, Rng, SeedableRng};

use super::hypercube::hypercube_evals_to_monomials_in_place;
use super::lde::{lde_coset_chunked, split_table, MAX_COLUMNS_PER_LAUNCH};
use super::pack::{pack_grid_blocks, PACK_BLOCK_THREADS};
use super::{
    convert_coset_leaves, convert_gathered_leaves, hypercube_evals_to_monomials, lde_coset,
    lde_cosets_batched, pack_hypercubes_to_monomials, update_eq_poly, DeviceContext, EqSample,
    TwiddleDescriptor,
};
use crate::upstream::{
    bitreverse_enumeration_inplace, distribute_powers_serial, domain_generator_for_size,
    lde_coset_lazy_r8, lde_coset_lazy_r8_into, multivariate_hypercube_evals_into_coeffs_radix4,
    precompute_twiddles_for_fft, serial_ct_ntt_natural_to_bitreversed, Backend, CosetLeafAccessor,
    ExtCoeffConversion, Field, GenericAllocationPool, Proth120WorkStealingLazyBackend,
    StandardExtCoeffConv, Twiddles, Worker,
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

#[test]
fn cpu_pr_abi_and_dispatch() {
    assert_eq!((size_of::<PR>(), align_of::<PR>()), (16, 16));
    assert_eq!((size_of::<EqSample>(), align_of::<EqSample>()), (32, 16));
    assert_eq!(std::mem::offset_of!(EqSample, point), 0);
    assert_eq!(std::mem::offset_of!(EqSample, weight), 16);
    assert_eq!(
        (
            size_of::<TwiddleDescriptor>(),
            align_of::<TwiddleDescriptor>()
        ),
        (40, 8)
    );
    for log_n in 8..=26 {
        let stages = split_table(log_n);
        assert_eq!(stages.iter().sum::<u32>(), log_n);
        if log_n <= 12 {
            assert_eq!(stages, &[log_n]);
            assert!(((1u32 << log_n) / 4).max(1) <= 1024);
            assert!((1usize << log_n) * size_of::<PR>() <= 65536);
        } else {
            assert!([8, 10, 12].contains(stages.last().unwrap()));
            let mut start = 0;
            for &stage in &stages[..stages.len() - 1] {
                assert!([5, 6, 7, 8].contains(&stage));
                assert!(log_n - start >= 11);
                assert!(1u32 << (log_n - start - 11) <= 32768);
                start += stage;
            }
        }
    }
    for log_n in [7, 27] {
        assert!(std::panic::catch_unwind(|| split_table(log_n)).is_err());
    }
    for (cols, chunks) in [(65535usize, 1usize), (65536, 2), (262144, 5)] {
        assert_eq!(cols.div_ceil(MAX_COLUMNS_PER_LAUNCH), chunks);
    }
    for (log_rows, pack_log2) in [(8, 18), (0, 26)] {
        let rows = 1usize << log_rows;
        let group = 1usize << pack_log2;
        let elements = rows * group;
        assert_eq!(pack_grid_blocks(log_rows, pack_log2), 262144);
        assert_eq!(
            pack_grid_blocks(log_rows, pack_log2) as usize * PACK_BLOCK_THREADS as usize,
            elements
        );
        for index in [0, rows - 1, rows, elements - 1] {
            let column = index >> log_rows;
            let row = index & (rows - 1);
            assert_eq!(column * rows + row, index);
            assert!(column < group);
            assert!(row < rows);
        }
    }
}

#[test]
#[cfg(not(no_cuda))]
fn pr_lde_coset_cpu_parity() {
    let ctx = DeviceContext::create(31).unwrap();
    let stream = CudaStream::create().unwrap();
    let worker = Worker::new_with_num_threads(8);
    let mut rng = StdRng::seed_from_u64(SEED);
    let nu = domain_generator_for_size::<PR>(1u64 << 31);
    let mut cases = 0;
    for log_n in 8..=20 {
        let rows = 1usize << log_n;
        let stride = rows + GUARD;
        let mut input = vec![SENTINEL; 3 * stride + 2 * GUARD];
        let columns: Vec<Vec<PR>> = (0..3)
            .map(|column| {
                (0..rows)
                    .map(|row| match column {
                        0 => PR::ZERO,
                        1 if row % 8 != 0 => PR::new(PR::ORDER - 1),
                        _ => random_field(&mut rng),
                    })
                    .collect()
            })
            .collect();
        for (column, values) in columns.iter().enumerate() {
            let start = 2 * GUARD + column * stride;
            input[start..start + rows].copy_from_slice(values);
        }
        let device_input = upload(&input);
        let twiddles = Twiddles::<PR, Global>::new(rows, &worker);
        let last = (1u32 << (31 - log_n)) - 1;
        let offsets = [
            random_nonzero(&mut rng),
            nu.pow_u128(1),
            nu.pow_u128(last as u128),
            PR::ONE,
        ];
        for offset in offsets {
            let expected: Vec<Vec<PR>> = columns
                .iter()
                .map(|values| {
                    lde_coset_lazy_r8(values, offset, &twiddles.forward_twiddles[..rows / 2])
                })
                .collect();
            if [8, 9, 13, 16].contains(&log_n) {
                for (values, expected) in columns.iter().zip(&expected) {
                    let mut alternate = values.clone();
                    distribute_powers_serial::<PR, PR>(&mut alternate, PR::ONE, offset);
                    serial_ct_ntt_natural_to_bitreversed::<PR, PR>(
                        &mut alternate,
                        log_n,
                        &twiddles.forward_twiddles[..rows / 2],
                    );
                    bitreverse_enumeration_inplace(&mut alternate);
                    assert_raw_eq(&alternate, expected);
                }
            }
            let mut device_output = upload(&vec![SENTINEL; input.len()]);
            let device_offset = upload(&[offset]);
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
            lde_coset_chunked(
                &ctx,
                &input_matrix,
                &mut output_matrix,
                &device_offset,
                2,
                &stream,
            )
            .unwrap();
            let actual = download(&device_output, &stream);
            assert_matrix_output(&actual, &expected, rows, stride);
            assert_unchanged(&download(&device_input, &stream), &input);
            assert_raw_eq(&download(&device_offset, &stream), &[offset]);
            cases += 1;
        }
    }
    assert_eq!(cases, 52);
    println!("Proth120 strided LDE: {cases} matrices, 156 CPU-equal cosets, 0 mismatches");
}

fn batched_case(
    ctx: &DeviceContext,
    stream: &CudaStream,
    input: &[PR],
    log_domain: u32,
    range: Range<u32>,
    twiddles: &[PR],
) -> Vec<PR> {
    let rows = input.len();
    let count = (range.end - range.start) as usize;
    let len = rows * count;
    let mut guarded_input = vec![SENTINEL; rows + 2 * GUARD];
    guarded_input[GUARD..GUARD + rows].copy_from_slice(input);
    let device_input = upload(&guarded_input);
    let mut device_output = upload(&vec![SENTINEL; len + 2 * GUARD]);
    lde_cosets_batched(
        ctx,
        &device_input[GUARD..GUARD + rows],
        log_domain,
        range.clone(),
        &mut device_output[GUARD..GUARD + len],
        stream,
    )
    .unwrap();
    let mut actual = download(&device_output, stream);
    assert_guards(&actual, GUARD..GUARD + len);
    let nu = domain_generator_for_size::<PR>(1u64 << log_domain);
    let mut expected = vec![PR::ZERO; rows];
    for (column, coset) in range.enumerate() {
        lde_coset_lazy_r8_into(input, nu.pow_u128(coset as u128), twiddles, &mut expected);
        assert_raw_eq(
            &actual[GUARD + column * rows..GUARD + (column + 1) * rows],
            &expected,
        );
    }
    assert_unchanged(&download(&device_input, stream), &guarded_input);
    actual.truncate(GUARD + len);
    actual.drain(..GUARD);
    actual
}

#[test]
#[cfg(not(no_cuda))]
fn pr_lde_cosets_batched_cpu_parity() {
    let ctx = DeviceContext::create(31).unwrap();
    let stream = CudaStream::create().unwrap();
    let worker = Worker::new_with_num_threads(8);
    let mut rng = StdRng::seed_from_u64(SEED);
    for log_n in [8, 12, 16, 20] {
        let rows = 1usize << log_n;
        let input: Vec<PR> = (0..rows).map(|_| random_field(&mut rng)).collect();
        let twiddles = precompute_twiddles_for_fft::<PR, Global, false>(rows, &worker);
        let end = 1u32 << (31 - log_n);
        for range in [0..3, end - 2..end, end / 2..end / 2 + 5, 7..7] {
            batched_case(&ctx, &stream, &input, 31, range, &twiddles);
        }
        if log_n == 8 {
            for count in [65536, 262144] {
                batched_case(&ctx, &stream, &input, 31, 0..count, &twiddles);
            }
        }
        let mut adjacent = batched_case(&ctx, &stream, &input, 31, 19..23, &twiddles);
        adjacent.extend(batched_case(&ctx, &stream, &input, 31, 23..27, &twiddles));
        let union = batched_case(&ctx, &stream, &input, 31, 19..27, &twiddles);
        assert_raw_eq(&adjacent, &union);
    }
    println!("Proth120 root31 batches: logs 8/12/16/20, 65536/262144 columns, adjacent ranges, 0 mismatches");
}

#[test]
#[cfg(not(no_cuda))]
fn pr_lde_cosets_batched_wide_context_cpu_parity() {
    let stream = CudaStream::create().unwrap();
    let worker = Worker::new_with_num_threads(8);
    let mut rng = StdRng::seed_from_u64(SEED);
    for (log_max_domain, log_domain) in [(31, 31), (33, 33), (33, 31), (33, 25)] {
        let ctx = DeviceContext::create(log_max_domain).unwrap();
        for log_n in [8, 12] {
            let rows = 1usize << log_n;
            let input: Vec<PR> = (0..rows).map(|_| random_field(&mut rng)).collect();
            let twiddles = precompute_twiddles_for_fft::<PR, Global, false>(rows, &worker);
            let end = 1u32 << (log_domain - log_n);
            for range in [0..2, end - 1..end] {
                let batched =
                    batched_case(&ctx, &stream, &input, log_domain, range.clone(), &twiddles);
                let nu = domain_generator_for_size::<PR>(1u64 << log_domain);
                let device_input = upload(&input);
                for (column, coset) in range.enumerate() {
                    let device_offset = upload(&[nu.pow_u128(coset as u128)]);
                    let mut device_output = upload(&vec![SENTINEL; rows]);
                    lde_coset(
                        &ctx,
                        &DeviceMatrixChunk::new(&device_input[..], rows, 0, rows),
                        &mut DeviceMatrixChunkMut::new(&mut device_output[..], rows, 0, rows),
                        &device_offset,
                        &stream,
                    )
                    .unwrap();
                    assert_raw_eq(
                        &download(&device_output, &stream),
                        &batched[column * rows..(column + 1) * rows],
                    );
                }
            }
        }
    }
    println!("Proth120 batched + single LDE at (L, D) in (31,31) (33,33) (33,31) (33,25): logs 8/12, cosets 0/1/last, 0 mismatches");
}

#[test]
#[cfg(not(no_cuda))]
fn pr_lde_continuous_layout_cpu_parity() {
    let ctx = DeviceContext::create(20).unwrap();
    let stream = CudaStream::create().unwrap();
    let worker = Worker::new_with_num_threads(8);
    let pool = GenericAllocationPool::<PR, PR>::proxy();
    let mut rng = StdRng::seed_from_u64(SEED);
    for (log_n, log_lde) in [(8, 8), (12, 4), (10, 10)] {
        let rows = 1usize << log_n;
        let factor = 1usize << log_lde;
        let input: Vec<PR> = (0..rows).map(|_| random_field(&mut rng)).collect();
        let twiddles = Twiddles::<PR, Global>::new(rows * factor, &worker);
        let (expected, offsets) = <Proth120WorkStealingLazyBackend as Backend<PR, PR>>::lde_ext_poly_from_monomial_form_continuous(
            &Proth120WorkStealingLazyBackend, &input, &twiddles, factor, &pool, &worker,
        );
        let root = domain_generator_for_size::<PR>((rows * factor) as u64);
        assert_eq!(offsets.len(), factor);
        let mut guarded_input = vec![SENTINEL; rows + 2 * GUARD];
        guarded_input[GUARD..GUARD + rows].copy_from_slice(&input);
        let device_input = upload(&guarded_input);
        let mut device_output = upload(&vec![SENTINEL; rows + 2 * GUARD]);
        let mut device_offset = upload(&[PR::ONE]);
        for (coset, offset) in offsets.iter().enumerate() {
            assert_eq!(*offset, root.pow_u128(coset as u128));
            memory_copy(&mut device_offset, &[*offset]).unwrap();
            let input_matrix =
                DeviceMatrixChunk::new(&device_input[GUARD..GUARD + rows], rows, 0, rows);
            let mut output_matrix =
                DeviceMatrixChunkMut::new(&mut device_output[GUARD..GUARD + rows], rows, 0, rows);
            lde_coset(
                &ctx,
                &input_matrix,
                &mut output_matrix,
                &device_offset,
                &stream,
            )
            .unwrap();
            let actual = download(&device_output, &stream);
            assert_guards(&actual, GUARD..GUARD + rows);
            assert_raw_eq(
                &actual[GUARD..GUARD + rows],
                &expected[coset * rows..(coset + 1) * rows],
            );
            assert_raw_eq(&download(&device_offset, &stream), &[*offset]);
        }
        assert_unchanged(&download(&device_input, &stream), &guarded_input);
    }
    println!("Proth120 continuous CPU backend: (8,8)/(12,4)/(10,10), 0 mismatches");
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
                if (mask ^ subset).count_ones() % 2 == 0 {
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
                        1 if row % 8 != 0 => PR::new(PR::ORDER - 1),
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
    let ctx = DeviceContext::create(31).unwrap();
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

fn reverse_bits(value: usize, bits: u32) -> usize {
    if bits == 0 {
        0
    } else {
        value.reverse_bits() >> (usize::BITS - bits)
    }
}

fn natural_coset_leaf(coset: &[PR], log_values: u32, leaf: usize) -> Vec<PR> {
    let values = 1usize << log_values;
    let leaves = coset.len() / values;
    (0..values)
        .map(|slot| coset[leaf + leaves * reverse_bits(slot, log_values)])
        .collect()
}

fn direct_leaf_coefficients(evals: &[PR], x: PR, log_values: u32) -> Vec<PR> {
    let values = evals.len();
    let generator = domain_generator_for_size::<PR>(values as u64);
    let generator_inv = generator.inverse().unwrap();
    let x_inv = x.inverse().unwrap();
    let size_inv = PR::new(values as u128).inverse().unwrap();
    let coefficients: Vec<PR> = (0..values)
        .map(|degree| {
            let mut coefficient = PR::ZERO;
            for (slot, eval) in evals.iter().enumerate() {
                let mut term =
                    generator_inv.pow_u128((reverse_bits(slot, log_values) * degree) as u128);
                term.mul_assign(eval);
                coefficient.add_assign(&term);
            }
            coefficient.mul_assign(&x_inv.pow_u128(degree as u128));
            coefficient.mul_assign(&size_inv);
            coefficient
        })
        .collect();
    for (slot, expected) in evals.iter().enumerate() {
        let mut point = generator.pow_u128(reverse_bits(slot, log_values) as u128);
        point.mul_assign(&x);
        let mut recovered = PR::ZERO;
        for coefficient in coefficients.iter().rev() {
            recovered.mul_assign(&point);
            recovered.add_assign(coefficient);
        }
        assert_raw_eq(&[recovered], &[*expected]);
    }
    coefficients
}

fn leaf_conversion_cases(
    ctx: &DeviceContext,
    stream: &CudaStream,
    rng: &mut StdRng,
    logs: &[u32],
    offsets_for: impl Fn(&mut StdRng, u32) -> Vec<PR>,
) -> usize {
    let worker = Worker::new_with_num_threads(8);
    let mut cases = 0;
    for &log_n in logs {
        let rows = 1usize << log_n;
        let monomials: Vec<PR> = (0..rows).map(|_| random_field(rng)).collect();
        let device_monomials = upload(&monomials);
        let twiddles = precompute_twiddles_for_fft::<PR, Global, false>(rows, &worker);
        let generator = domain_generator_for_size::<PR>(rows as u64);
        for offset in offsets_for(rng, log_n) {
            let device_offset = upload(&[offset]);
            let mut device_coset = upload(&vec![SENTINEL; rows + 2 * GUARD]);
            let input_matrix = DeviceMatrixChunk::new(&device_monomials[..], rows, 0, rows);
            let mut output_matrix =
                DeviceMatrixChunkMut::new(&mut device_coset[GUARD..GUARD + rows], rows, 0, rows);
            lde_coset(
                &ctx,
                &input_matrix,
                &mut output_matrix,
                &device_offset,
                &stream,
            )
            .unwrap();
            let coset = download(&device_coset, &stream);
            assert_guards(&coset, GUARD..GUARD + rows);
            let natural = &coset[GUARD..GUARD + rows];
            assert_raw_eq(natural, &lde_coset_lazy_r8(&monomials, offset, &twiddles));
            assert_raw_eq(&download(&device_monomials, &stream), &monomials);
            for log_values in 0..=4 {
                let values = 1usize << log_values;
                let leaves = rows / values;
                let conv = StandardExtCoeffConv::<PR>::new(rows, values);
                let mut expected = natural.to_vec();
                <StandardExtCoeffConv<PR> as ExtCoeffConversion<PR, PR>>::apply_serial(
                    &conv,
                    &mut expected,
                    offset,
                );
                memory_copy_async(&mut device_coset, &coset, &stream).unwrap();
                convert_coset_leaves(
                    &ctx,
                    &mut device_coset[GUARD..GUARD + rows],
                    log_values,
                    &device_offset,
                    &stream,
                )
                .unwrap();
                let actual = download(&device_coset, &stream);
                assert_guards(&actual, GUARD..GUARD + rows);
                assert_raw_eq(&actual[GUARD..GUARD + rows], &expected);
                let indices = [
                    0,
                    (leaves - 1) as u32,
                    1,
                    (leaves - 1) as u32,
                    0,
                    (leaves / 2) as u32,
                ];
                let device_indices = upload(&indices);
                let gathered: Vec<PR> = indices
                    .iter()
                    .flat_map(|&leaf| natural_coset_leaf(natural, log_values, leaf as usize))
                    .collect();
                let mut guarded = vec![SENTINEL; gathered.len() + 2 * GUARD];
                guarded[GUARD..GUARD + gathered.len()].copy_from_slice(&gathered);
                let mut device_gathered = upload(&guarded);
                convert_gathered_leaves(
                    &ctx,
                    &mut device_gathered[GUARD..GUARD + gathered.len()],
                    &device_indices,
                    log_n,
                    log_values,
                    &device_offset,
                    &stream,
                )
                .unwrap();
                let actual_gathered = download(&device_gathered, &stream);
                assert_guards(&actual_gathered, GUARD..GUARD + gathered.len());
                let accessor = <Proth120WorkStealingLazyBackend as Backend<PR, PR>>::coset_leaves(
                    &Proth120WorkStealingLazyBackend,
                    &conv,
                    natural,
                    offset,
                );
                for (query, &leaf) in indices.iter().enumerate() {
                    let leaf = leaf as usize;
                    let mut cpu_leaf = vec![PR::ZERO; values];
                    accessor.leaf_into(leaf, &mut cpu_leaf);
                    let mut cpu_gathered = gathered[query * values..(query + 1) * values].to_vec();
                    <StandardExtCoeffConv<PR> as ExtCoeffConversion<PR, PR>>::convert_gathered_leaf(
                        &conv,
                        offset.inverse().unwrap(),
                        leaf,
                        &mut cpu_gathered,
                    );
                    let mut x = generator.pow_u128(leaf as u128);
                    x.mul_assign(&offset);
                    let direct = direct_leaf_coefficients(
                        &gathered[query * values..(query + 1) * values],
                        x,
                        log_values,
                    );
                    let gpu_leaf =
                        &actual_gathered[GUARD + query * values..GUARD + (query + 1) * values];
                    assert_raw_eq(gpu_leaf, &cpu_leaf);
                    assert_raw_eq(gpu_leaf, &cpu_gathered);
                    assert_raw_eq(gpu_leaf, &direct);
                    assert_raw_eq(
                        gpu_leaf,
                        &natural_coset_leaf(&actual[GUARD..GUARD + rows], log_values, leaf),
                    );
                }
                let mut actual_indices = indices;
                memory_copy_async(&mut actual_indices, &device_indices, &stream).unwrap();
                stream.synchronize().unwrap();
                assert_eq!(actual_indices, indices);
                let empty_indices = upload::<u32>(&[]);
                let mut empty_gathered = upload(&vec![SENTINEL; 2 * GUARD]);
                convert_gathered_leaves(
                    &ctx,
                    &mut empty_gathered[GUARD..GUARD],
                    &empty_indices,
                    log_n,
                    log_values,
                    &device_offset,
                    &stream,
                )
                .unwrap();
                assert_eq!(
                    download(&empty_gathered, &stream),
                    vec![SENTINEL; 2 * GUARD]
                );
                cases += 1;
            }
            assert_raw_eq(&download(&device_offset, stream), &[offset]);
        }
    }
    cases
}

#[test]
#[cfg(not(no_cuda))]
fn pr_leaf_conversion_cpu_parity() {
    let ctx = DeviceContext::create(31).unwrap();
    let stream = CudaStream::create().unwrap();
    let mut rng = StdRng::seed_from_u64(SEED);
    let nu = domain_generator_for_size::<PR>(1u64 << 31);
    let logs = [8, 12, 16, 20];
    let cases = leaf_conversion_cases(&ctx, &stream, &mut rng, &logs, |rng, _| {
        vec![random_nonzero(rng), nu.pow_u128(19)]
    });
    assert_eq!(cases, 40);
    println!("Proth120 leaf conversion: logs {logs:?}, lv 0..=4, {cases} cases, bulk/gathered/CPU/direct DFT, 0 mismatches");
}

#[test]
#[cfg(not(no_cuda))]
fn pr_leaf_conversion_wide_context_cpu_parity() {
    let ctx = DeviceContext::create(33).unwrap();
    let stream = CudaStream::create().unwrap();
    let mut rng = StdRng::seed_from_u64(SEED);
    let logs = [8, 12];
    for log_domain in [33, 31] {
        let nu = domain_generator_for_size::<PR>(1u64 << log_domain);
        let cases = leaf_conversion_cases(&ctx, &stream, &mut rng, &logs, |_, log_n| {
            vec![nu, nu.pow_u128((1u128 << (log_domain - log_n)) - 1)]
        });
        assert_eq!(cases, 20);
    }
    println!("Proth120 leaf conversion at L = 33, D in {{33, 31}}: logs {logs:?}, lv 0..=4, cosets 1 and last, 0 mismatches");
}

fn host_available_bytes() -> usize {
    let meminfo = std::fs::read_to_string("/proc/meminfo").unwrap();
    let line = meminfo
        .lines()
        .find(|line| line.starts_with("MemAvailable:"))
        .unwrap();
    line.split_whitespace()
        .nth(1)
        .unwrap()
        .parse::<usize>()
        .unwrap()
        * 1024
}

fn require_resources(case: &str, device_bytes: usize, host_bytes: usize) {
    let (free, _) = memory_get_info().unwrap();
    let host = host_available_bytes();
    println!(
        "{case}: requires {device_bytes} device bytes ({free} free) and {host_bytes} host bytes ({host} available)"
    );
    assert!(
        free >= device_bytes,
        "{case}: {device_bytes} device bytes required, {free} free"
    );
    assert!(
        host >= host_bytes,
        "{case}: {host_bytes} host bytes required, {host} available"
    );
}

fn count_mismatches(actual: &[PR], expected: &[PR]) -> usize {
    assert_eq!(actual.len(), expected.len());
    actual
        .iter()
        .zip(expected)
        .filter(|(actual, expected)| actual.0 >= PR::ORDER || actual.0 != expected.0)
        .count()
}

#[test]
#[ignore]
#[cfg(not(no_cuda))]
fn pr_production_lde_parity() {
    let ctx = DeviceContext::create(31).unwrap();
    let stream = CudaStream::create().unwrap();
    let worker = Worker::new_with_num_threads(8);
    let mut rng = StdRng::seed_from_u64(SEED);
    let nu = domain_generator_for_size::<PR>(1u64 << 31);
    for log_n in 15..=26 {
        let rows = 1usize << log_n;
        let bytes = rows * size_of::<PR>();
        let case = format!("Proth120 production LDE log_n {log_n}");
        require_resources(&case, 2 * bytes + 16, 3 * bytes + bytes / 2);
        let k = (1u32 << (31 - log_n)) - 1;
        let offset = nu.pow_u128(k as u128);
        let input: Vec<PR> = (0..rows).map(|_| random_field(&mut rng)).collect();
        let twiddles = precompute_twiddles_for_fft::<PR, Global, false>(rows, &worker);
        let mut expected = vec![PR::ZERO; rows];
        lde_coset_lazy_r8_into(&input, offset, &twiddles, &mut expected);
        drop(twiddles);
        let device_input = upload(&input);
        drop(input);
        let mut device_output = DeviceAllocation::<PR>::alloc(rows).unwrap();
        let device_offset = upload(&[offset]);
        lde_coset(
            &ctx,
            &DeviceMatrixChunk::new(&device_input, rows, 0, rows),
            &mut DeviceMatrixChunkMut::new(&mut device_output, rows, 0, rows),
            &device_offset,
            &stream,
        )
        .unwrap();
        let mut actual = download(&device_output, &stream);
        let coset_mismatches = count_mismatches(&actual, &expected);
        lde_cosets_batched(
            &ctx,
            &device_input,
            31,
            k..k + 1,
            &mut device_output,
            &stream,
        )
        .unwrap();
        memory_copy_async(&mut actual, &device_output, &stream).unwrap();
        stream.synchronize().unwrap();
        let batched_mismatches = count_mismatches(&actual, &expected);
        println!(
            "{case}: offset nu^{k}, lde_coset {coset_mismatches} mismatches, lde_cosets_batched({k}..{}) {batched_mismatches} mismatches",
            k + 1
        );
        assert_eq!((coset_mismatches, batched_mismatches), (0, 0), "{case}");
    }
}

#[test]
#[ignore]
#[cfg(not(no_cuda))]
fn pr_production_batched_parity() {
    let ctx = DeviceContext::create(31).unwrap();
    let stream = CudaStream::create().unwrap();
    let worker = Worker::new_with_num_threads(8);
    let mut rng = StdRng::seed_from_u64(SEED);
    let nu = domain_generator_for_size::<PR>(1u64 << 31);
    for (log_n, count) in [(24, 4u32), (20, 64), (16, 1024), (12, 16384), (8, 262144)] {
        let rows = 1usize << log_n;
        let total = rows * count as usize;
        let bytes = total * size_of::<PR>();
        let row_bytes = rows * size_of::<PR>();
        let case = format!("Proth120 production batched LDE log_n {log_n} x {count} cosets");
        require_resources(
            &case,
            bytes + row_bytes,
            bytes + 2 * row_bytes + row_bytes / 2,
        );
        let input: Vec<PR> = (0..rows).map(|_| random_field(&mut rng)).collect();
        let twiddles = precompute_twiddles_for_fft::<PR, Global, false>(rows, &worker);
        let device_input = upload(&input);
        let mut device_output = DeviceAllocation::<PR>::alloc(total).unwrap();
        let mut actual = vec![PR::ZERO; total];
        let mut expected = vec![PR::ZERO; rows];
        let end = 1u32 << (31 - log_n);
        for start in [3, end - count] {
            lde_cosets_batched(
                &ctx,
                &device_input,
                31,
                start..start + count,
                &mut device_output,
                &stream,
            )
            .unwrap();
            memory_copy_async(&mut actual, &device_output, &stream).unwrap();
            stream.synchronize().unwrap();
            let mut mismatches = 0;
            let mut offset = nu.pow_u128(start as u128);
            for coset in 0..count as usize {
                lde_coset_lazy_r8_into(&input, offset, &twiddles, &mut expected);
                mismatches +=
                    count_mismatches(&actual[coset * rows..(coset + 1) * rows], &expected);
                offset.mul_assign(&nu);
            }
            println!(
                "{case}: range {start}..{}, {mismatches} mismatches",
                start + count
            );
            assert_eq!(mismatches, 0, "{case}, range {start}..{}", start + count);
        }
    }
}

#[test]
#[ignore]
#[cfg(not(no_cuda))]
fn pr_production_pack_parity() {
    let stream = CudaStream::create().unwrap();
    let worker = Worker::new_with_num_threads(8);
    let pool = GenericAllocationPool::<PR, PR>::proxy();
    let mut rng = StdRng::seed_from_u64(SEED);
    for (log_rows, pack_log2, cols) in [(22, 4u32, 16usize), (22, 4, 10), (21, 3, 8), (21, 3, 2)] {
        let rows = 1usize << log_rows;
        let out_rows = rows << pack_log2;
        let input_bytes = cols * rows * size_of::<PR>();
        let output_bytes = out_rows * size_of::<PR>();
        let case = format!(
            "Proth120 production pack 2^{log_rows} x {cols} columns, pack_log2 {pack_log2}"
        );
        require_resources(
            &case,
            input_bytes + output_bytes,
            input_bytes + 2 * output_bytes,
        );
        let columns: Vec<Vec<PR>> = (0..cols)
            .map(|_| (0..rows).map(|_| random_field(&mut rng)).collect())
            .collect();
        let evals: Vec<&[PR]> = columns.iter().map(Vec::as_slice).collect();
        let expected = <Proth120WorkStealingLazyBackend as Backend<PR, PR>>::pack_polys_from_hypercubes_to_monomials(
            &Proth120WorkStealingLazyBackend,
            &evals,
            pack_log2 as usize,
            &pool,
            &worker,
        );
        assert_eq!(expected.len(), 1);
        let mut device_input = DeviceAllocation::<PR>::alloc(cols * rows).unwrap();
        for (column, values) in columns.iter().enumerate() {
            memory_copy(
                &mut device_input[column * rows..(column + 1) * rows],
                values,
            )
            .unwrap();
        }
        drop(evals);
        drop(columns);
        let mut device_output = DeviceAllocation::<PR>::alloc(out_rows).unwrap();
        pack_hypercubes_to_monomials(
            &DeviceMatrixChunk::new(&device_input, rows, 0, rows),
            &mut DeviceMatrixChunkMut::new(&mut device_output, out_rows, 0, out_rows),
            pack_log2,
            &stream,
        )
        .unwrap();
        let actual = download(&device_output, &stream);
        let mismatches = count_mismatches(&actual, &expected[0]);
        println!("{case}: {mismatches} mismatches");
        assert_eq!(mismatches, 0, "{case}");
    }
}

fn horner(coefficients: &[PR], x: PR) -> PR {
    let mut value = PR::ZERO;
    for coefficient in coefficients.iter().rev() {
        value.mul_assign(&x);
        value.add_assign(coefficient);
    }
    value
}

#[test]
#[ignore]
#[cfg(not(no_cuda))]
fn pr_production_eq_leaf_parity() {
    let stream = CudaStream::create().unwrap();
    let worker = Worker::new_with_num_threads(8);
    let mut rng = StdRng::seed_from_u64(SEED);
    let log_n = 26;
    let rows = 1usize << log_n;
    let bytes = rows * size_of::<PR>();
    {
        let case = "Proth120 production eq update 2^26, 1 ood + 17 in-domain samples";
        require_resources(case, bytes + 18 * size_of::<EqSample>(), 2 * bytes);
        let ood = eq_samples(&mut rng, 1, 2, false);
        let in_domain = eq_samples(&mut rng, 17, 2, false);
        let mut expected: Vec<PR> = (0..rows).map(|_| random_nonzero(&mut rng)).collect();
        let mut device_eq = upload(&expected);
        let device_ood = upload(&ood);
        let device_in_domain = upload(&in_domain);
        let ood_pairs: Vec<_> = ood.iter().map(|s| (s.point, s.weight)).collect();
        let in_pairs: Vec<_> = in_domain.iter().map(|s| (s.point, s.weight)).collect();
        <Proth120WorkStealingLazyBackend as Backend<PR, PR>>::update_eq_poly(
            &Proth120WorkStealingLazyBackend,
            &mut expected,
            &ood_pairs,
            &in_pairs,
            &worker,
        );
        update_eq_poly(&mut device_eq, &device_ood, &device_in_domain, &stream).unwrap();
        let actual = download(&device_eq, &stream);
        let mismatches = count_mismatches(&actual, &expected);
        println!("{case}: {mismatches} mismatches");
        assert_eq!(mismatches, 0, "{case}");
    }
    let ctx = DeviceContext::create(31).unwrap();
    let case = "Proth120 production leaf conversion, 2^26 natural coset 31 of the 2^31 domain";
    require_resources(
        case,
        2 * bytes + 16,
        3 * bytes + (rows >> 2) * size_of::<PR>(),
    );
    let monomials: Vec<PR> = (0..rows).map(|_| random_field(&mut rng)).collect();
    let device_monomials = upload(&monomials);
    let mut device_coset = DeviceAllocation::<PR>::alloc(rows).unwrap();
    lde_cosets_batched(
        &ctx,
        &device_monomials,
        31,
        31..32,
        &mut device_coset,
        &stream,
    )
    .unwrap();
    drop(device_monomials);
    let coset = download(&device_coset, &stream);
    let nu = domain_generator_for_size::<PR>(1u64 << 31);
    let offset = nu.pow_u128(31);
    let generator = domain_generator_for_size::<PR>(rows as u64);
    let mut positions = vec![0, rows - 1];
    positions.extend((0..62).map(|_| (rng.random::<u64>() as usize) % rows));
    let horner_mismatches: usize = std::thread::scope(|scope| {
        let handles: Vec<_> = positions
            .chunks(8)
            .map(|chunk| {
                let (monomials, coset) = (&monomials, &coset);
                scope.spawn(move || {
                    chunk
                        .iter()
                        .filter(|&&position| {
                            let mut x = generator.pow_u128(position as u128);
                            x.mul_assign(&offset);
                            let value = horner(monomials, x);
                            coset[position].0 >= PR::ORDER || value.0 != coset[position].0
                        })
                        .count()
                })
            })
            .collect();
        handles
            .into_iter()
            .map(|handle| handle.join().unwrap())
            .sum()
    });
    println!(
        "{case}: Horner check at {} positions, {horner_mismatches} mismatches",
        positions.len()
    );
    assert_eq!(horner_mismatches, 0, "{case}: Horner check");
    drop(monomials);
    let device_offset = upload(&[offset]);
    for log_values in [4, 2] {
        let conv = StandardExtCoeffConv::<PR>::new(rows, 1 << log_values);
        let mut expected = coset.clone();
        <StandardExtCoeffConv<PR> as ExtCoeffConversion<PR, PR>>::apply_serial(
            &conv,
            &mut expected,
            offset,
        );
        drop(conv);
        memory_copy(&mut device_coset, &coset).unwrap();
        convert_coset_leaves(&ctx, &mut device_coset, log_values, &device_offset, &stream).unwrap();
        let actual = download(&device_coset, &stream);
        let mismatches = count_mismatches(&actual, &expected);
        println!("{case}: lv {log_values}, {mismatches} mismatches");
        assert_eq!(mismatches, 0, "{case}, lv {log_values}");
    }
}
