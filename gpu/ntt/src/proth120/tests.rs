use std::alloc::Global;
use std::mem::{align_of, size_of};
use std::ops::Range;

use era_cudart::memory::{memory_copy, memory_copy_async, DeviceAllocation};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::device_structures::{DeviceMatrixChunk, DeviceMatrixChunkMut};
use gpu_core::primitives::field::PR;
use rand::{rngs::StdRng, Rng, SeedableRng};

use super::hypercube::hypercube_evals_to_monomials_in_place;
use super::lde::{lde_coset_chunked, split_table, MAX_COLUMNS_PER_LAUNCH};
use super::pack::{pack_grid_blocks, PACK_BLOCK_THREADS};
use super::{
    hypercube_evals_to_monomials, lde_coset, lde_cosets_batched, pack_hypercubes_to_monomials,
    DeviceContext, TwiddleDescriptor,
};
use crate::upstream::{
    bitreverse_enumeration_inplace, distribute_powers_serial, domain_generator_for_size,
    lde_coset_lazy_r8, lde_coset_lazy_r8_into, multivariate_hypercube_evals_into_coeffs_radix4,
    precompute_twiddles_for_fft, serial_ct_ntt_natural_to_bitreversed, Backend, Field,
    GenericAllocationPool, Proth120WorkStealingLazyBackend, Twiddles, Worker,
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

fn upload(values: &[PR]) -> DeviceAllocation<PR> {
    let mut device = DeviceAllocation::<PR>::alloc(values.len()).unwrap();
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
            assert_eq!(download(&device_input, &stream), input);
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
        range.clone(),
        &mut device_output[GUARD..GUARD + len],
        stream,
    )
    .unwrap();
    let mut actual = download(&device_output, stream);
    assert_guards(&actual, GUARD..GUARD + len);
    let nu = domain_generator_for_size::<PR>(1u64 << 31);
    let mut expected = vec![PR::ZERO; rows];
    for (column, coset) in range.enumerate() {
        lde_coset_lazy_r8_into(input, nu.pow_u128(coset as u128), twiddles, &mut expected);
        assert_raw_eq(
            &actual[GUARD + column * rows..GUARD + (column + 1) * rows],
            &expected,
        );
    }
    assert_eq!(download(&device_input, stream), guarded_input);
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
            batched_case(&ctx, &stream, &input, range, &twiddles);
        }
        if log_n == 8 {
            for count in [65536, 262144] {
                batched_case(&ctx, &stream, &input, 0..count, &twiddles);
            }
        }
        let mut adjacent = batched_case(&ctx, &stream, &input, 19..23, &twiddles);
        adjacent.extend(batched_case(&ctx, &stream, &input, 23..27, &twiddles));
        let union = batched_case(&ctx, &stream, &input, 19..27, &twiddles);
        assert_raw_eq(&adjacent, &union);
    }
    println!("Proth120 root31 batches: logs 8/12/16/20, 65536/262144 columns, adjacent ranges, 0 mismatches");
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
        }
        assert_eq!(download(&device_input, &stream), guarded_input);
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
        assert_eq!(download(&device_input, &stream), input);
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
    assert_eq!(download(&device_input, stream), input);
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
    println!(
        "Proth120 pack: {cases} shapes + (1,17,100000) + (0,8,300) + packed LDE at nu^1, 0 mismatches"
    );
}
