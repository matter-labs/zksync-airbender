use era_cudart::memory::{memory_copy_async, DeviceAllocation};
use era_cudart::stream::CudaStream;

use rand::Rng;

use super::super::hash::{
    hash_leaves, hash_leaves_from_ntt_flat_range_to_staging,
    hash_leaves_from_ntt_flat_range_to_staging_physical, hash_leaves_from_ntt_multi_coset,
    hash_leaves_from_ntt_multi_coset_physical, hash_leaves_from_ntt_multi_coset_to_staging,
    hash_leaves_from_ntt_multi_coset_to_staging_physical, hash_leaves_multi_coset,
    hash_leaves_multi_coset_physical, hash_leaves_physical,
};
use super::super::Digest;
use super::{bitreverse_index, BLOCK_SIZE};
use crate::upstream::{Blake2sState, Field, USE_REDUCED_BLAKE2_ROUNDS};
use gpu_core::primitives::field::BF;
use gpu_ops::simple::set_to_zero;

const SHAPES: [(u32, u32); 5] = [(4, 1), (6, 1), (10, 1), (10, 5), (12, 5)];
const COLS_COUNTS: [usize; 3] = [0, 1, 3];
const COSETS_COUNTS: [usize; 2] = [1, 2];

const NTT_SHAPES: [(u32, u32); 2] = [(6, 1), (10, 5)];
const NTT_COLS_COUNTS: [u32; 2] = [1, 4];
const NTT_LOG_LDE_FACTOR: u32 = 2;

pub(super) fn random_values(len: usize) -> Vec<BF> {
    let mut rng = rand::rng();
    let mut values = vec![BF::ZERO; len];
    values.fill_with(|| BF::from_nonreduced_u32(rng.random()));
    values
}

/// `cudaMalloc(0)` hands back a null pointer that `DeviceAllocation` rejects, so
/// the legal `cols_count == 0` shapes get a one-element backing sliced to zero.
pub(super) fn upload(values: &[BF], stream: &CudaStream) -> DeviceAllocation<BF> {
    let mut device = DeviceAllocation::alloc(values.len().max(1)).unwrap();
    if !values.is_empty() {
        memory_copy_async(&mut device[..values.len()], values, stream).unwrap();
    }
    device
}

/// Permutes every column of every coset slab from natural row order into the
/// bitreversed row order the LSB NTT emits.
pub(super) fn bitreverse_rows(
    values: &[BF],
    cosets_count: usize,
    cols_count: usize,
    log_n: u32,
) -> Vec<BF> {
    let rows_count = 1usize << log_n;
    let coset_stride = cols_count * rows_count;
    let mut result = vec![BF::ZERO; values.len()];
    for coset in 0..cosets_count {
        for col in 0..cols_count {
            let base = coset * coset_stride + col * rows_count;
            for physical in 0..rows_count {
                result[base + physical] = values[base + bitreverse_index(physical, log_n)];
            }
        }
    }
    result
}

/// Host blake2s over the LOGICAL leaf `leaf`: slot `s` of column `col` reads
/// natural row `leaf + rev_b(s) * leaves_count`, absorbed slot-fast.
pub(super) fn host_logical_leaf(
    values: &[BF],
    coset_base: usize,
    rows_count: usize,
    cols_count: usize,
    leaves_count: usize,
    log_values_per_leaf: u32,
    leaf: usize,
) -> Digest {
    let mut input = Vec::with_capacity(cols_count << log_values_per_leaf);
    for col in 0..cols_count {
        for slot in 0..1usize << log_values_per_leaf {
            let row = leaf + bitreverse_index(slot, log_values_per_leaf) * leaves_count;
            input.push(values[coset_base + col * rows_count + row].0);
        }
    }
    let mut state = Blake2sState::new();
    if input.is_empty() {
        return state.state;
    }
    let blocks_count = input.len().div_ceil(BLOCK_SIZE);
    let mut digest = Digest::default();
    for (block_index, chunk) in input.chunks(BLOCK_SIZE).enumerate() {
        let mut block = [0u32; BLOCK_SIZE];
        block[..chunk.len()].copy_from_slice(chunk);
        if block_index + 1 == blocks_count {
            state.absorb_final_block::<USE_REDUCED_BLAKE2_ROUNDS>(&block, chunk.len(), &mut digest);
        } else {
            state.absorb::<USE_REDUCED_BLAKE2_ROUNDS>(&block);
        }
    }
    digest
}

/// `physical[j] == logical[rev_a(j)]` inside every `stride`-spaced coset region.
fn assert_bitreversed_blocks(
    physical: &[Digest],
    logical: &[Digest],
    cosets_count: usize,
    stride: usize,
    leaves_count: usize,
    log_leaves_count: u32,
    label: &str,
) {
    for coset in 0..cosets_count {
        for block in 0..leaves_count {
            let leaf = bitreverse_index(block, log_leaves_count);
            assert_eq!(
                physical[coset * stride + block],
                logical[coset * stride + leaf],
                "{label}: coset {coset} block {block} (logical leaf {leaf})",
            );
        }
    }
}

fn run_multi_coset(
    stream: &CudaStream,
    values: &[BF],
    log_n: u32,
    log_values_per_leaf: u32,
    cols_count: usize,
    cosets_count: usize,
    physical: bool,
) -> Vec<Digest> {
    let rows_count = 1usize << log_n;
    let leaves_count = rows_count >> log_values_per_leaf;
    let values_stride = cols_count * rows_count;
    let results_stride = leaves_count * 2;
    let values_device = upload(values, stream);
    let values_device = &values_device[..values.len()];
    let mut results_device = DeviceAllocation::alloc(results_stride * cosets_count).unwrap();
    set_to_zero(&mut results_device, stream).unwrap();
    if physical {
        hash_leaves_multi_coset_physical(
            values_device,
            &mut results_device,
            log_values_per_leaf,
            cosets_count,
            leaves_count,
            values_stride,
            results_stride,
            cols_count,
            stream,
        )
    } else {
        hash_leaves_multi_coset(
            values_device,
            &mut results_device,
            log_values_per_leaf,
            cosets_count,
            leaves_count,
            values_stride,
            results_stride,
            cols_count,
            stream,
        )
    }
    .unwrap();
    let mut results = vec![Digest::default(); results_stride * cosets_count];
    memory_copy_async(&mut results, &results_device, stream).unwrap();
    stream.synchronize().unwrap();
    results
}

fn run_single_coset(
    stream: &CudaStream,
    values: &[BF],
    log_n: u32,
    log_values_per_leaf: u32,
    physical: bool,
) -> Vec<Digest> {
    let leaves_count = (1usize << log_n) >> log_values_per_leaf;
    let values_device = upload(values, stream);
    let values_device = &values_device[..values.len()];
    let mut results_device = DeviceAllocation::alloc(leaves_count).unwrap();
    set_to_zero(&mut results_device, stream).unwrap();
    if physical {
        hash_leaves_physical(
            values_device,
            &mut results_device,
            log_values_per_leaf,
            stream,
        )
    } else {
        hash_leaves(
            values_device,
            &mut results_device,
            log_values_per_leaf,
            stream,
        )
    }
    .unwrap();
    let mut results = vec![Digest::default(); leaves_count];
    memory_copy_async(&mut results, &results_device, stream).unwrap();
    stream.synchronize().unwrap();
    results
}

#[test]
fn physical_leaf_matches_old_kernel() {
    let stream = CudaStream::default();
    for (log_n, log_values_per_leaf) in SHAPES {
        let log_leaves_count = log_n - log_values_per_leaf;
        let rows_count = 1usize << log_n;
        let leaves_count = rows_count >> log_values_per_leaf;
        for cols_count in COLS_COUNTS {
            for cosets_count in COSETS_COUNTS {
                let natural = random_values(cols_count * rows_count * cosets_count);
                let bitreversed = bitreverse_rows(&natural, cosets_count, cols_count, log_n);
                let label = format!(
                    "multi-coset n={log_n} b={log_values_per_leaf} cols={cols_count} cosets={cosets_count}"
                );
                let logical = run_multi_coset(
                    &stream,
                    &natural,
                    log_n,
                    log_values_per_leaf,
                    cols_count,
                    cosets_count,
                    false,
                );
                let physical = run_multi_coset(
                    &stream,
                    &bitreversed,
                    log_n,
                    log_values_per_leaf,
                    cols_count,
                    cosets_count,
                    true,
                );
                assert_bitreversed_blocks(
                    &physical,
                    &logical,
                    cosets_count,
                    leaves_count * 2,
                    leaves_count,
                    log_leaves_count,
                    &label,
                );
                if cosets_count == 1 {
                    let label =
                        format!("single-coset n={log_n} b={log_values_per_leaf} cols={cols_count}");
                    let logical =
                        run_single_coset(&stream, &natural, log_n, log_values_per_leaf, false);
                    let physical =
                        run_single_coset(&stream, &bitreversed, log_n, log_values_per_leaf, true);
                    assert_bitreversed_blocks(
                        &physical,
                        &logical,
                        1,
                        leaves_count,
                        leaves_count,
                        log_leaves_count,
                        &label,
                    );
                }
            }
        }
    }
}

#[test]
fn physical_leaf_matches_host_oracle() {
    let stream = CudaStream::default();
    for (log_n, log_values_per_leaf) in SHAPES {
        let log_leaves_count = log_n - log_values_per_leaf;
        let rows_count = 1usize << log_n;
        let leaves_count = rows_count >> log_values_per_leaf;
        for cols_count in COLS_COUNTS {
            for cosets_count in COSETS_COUNTS {
                let natural = random_values(cols_count * rows_count * cosets_count);
                let bitreversed = bitreverse_rows(&natural, cosets_count, cols_count, log_n);
                let values_stride = cols_count * rows_count;
                let mut host = Vec::with_capacity(leaves_count * cosets_count);
                for coset in 0..cosets_count {
                    for leaf in 0..leaves_count {
                        host.push(host_logical_leaf(
                            &natural,
                            coset * values_stride,
                            rows_count,
                            cols_count,
                            leaves_count,
                            log_values_per_leaf,
                            leaf,
                        ));
                    }
                }
                let physical = run_multi_coset(
                    &stream,
                    &bitreversed,
                    log_n,
                    log_values_per_leaf,
                    cols_count,
                    cosets_count,
                    true,
                );
                for coset in 0..cosets_count {
                    for block in 0..leaves_count {
                        let leaf = bitreverse_index(block, log_leaves_count);
                        assert_eq!(
                            physical[coset * leaves_count * 2 + block],
                            host[coset * leaves_count + leaf],
                            "host oracle n={log_n} b={log_values_per_leaf} cols={cols_count} \
                             cosets={cosets_count}: coset {coset} block {block} (logical leaf {leaf})",
                        );
                    }
                }
                if cosets_count == 1 {
                    let physical =
                        run_single_coset(&stream, &bitreversed, log_n, log_values_per_leaf, true);
                    for (block, digest) in physical.iter().enumerate() {
                        let leaf = bitreverse_index(block, log_leaves_count);
                        assert_eq!(
                            *digest, host[leaf],
                            "host oracle single-coset n={log_n} b={log_values_per_leaf} \
                             cols={cols_count}: block {block} (logical leaf {leaf})",
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn physical_leaf_from_ntt_matches_old_kernel() {
    let stream = CudaStream::default();
    let cosets_count = 1usize << NTT_LOG_LDE_FACTOR;
    for (log_n, log_values_per_leaf) in NTT_SHAPES {
        let log_leaves_count = log_n - log_values_per_leaf;
        let trace_len = 1u32 << log_n;
        let leaves_count = (1usize << log_n) >> log_values_per_leaf;
        let total_leaves = leaves_count * cosets_count;
        for src_cols_per_coset in NTT_COLS_COUNTS {
            let total_cols = cosets_count * src_cols_per_coset as usize;
            let natural = random_values(total_cols * (1usize << log_n));
            let bitreversed = bitreverse_rows(&natural, 1, total_cols, log_n);
            let mut natural_device = DeviceAllocation::alloc(natural.len()).unwrap();
            let mut bitreversed_device = DeviceAllocation::alloc(bitreversed.len()).unwrap();
            memory_copy_async(&mut natural_device, &natural, &stream).unwrap();
            memory_copy_async(&mut bitreversed_device, &bitreversed, &stream).unwrap();
            let mut logical_device = DeviceAllocation::alloc(total_leaves).unwrap();
            let mut physical_device = DeviceAllocation::alloc(total_leaves).unwrap();
            let mut logical = vec![Digest::default(); total_leaves];
            let mut physical = vec![Digest::default(); total_leaves];
            let label = format!("n={log_n} b={log_values_per_leaf} cols={src_cols_per_coset}");

            for surface in 0..3 {
                set_to_zero(&mut logical_device, &stream).unwrap();
                set_to_zero(&mut physical_device, &stream).unwrap();
                match surface {
                    0 => {
                        hash_leaves_from_ntt_multi_coset(
                            &natural_device,
                            &mut logical_device,
                            log_values_per_leaf,
                            src_cols_per_coset,
                            NTT_LOG_LDE_FACTOR,
                            0,
                            cosets_count,
                            leaves_count,
                            trace_len,
                            &stream,
                        )
                        .unwrap();
                        hash_leaves_from_ntt_multi_coset_physical(
                            &bitreversed_device,
                            &mut physical_device,
                            log_values_per_leaf,
                            src_cols_per_coset,
                            NTT_LOG_LDE_FACTOR,
                            0,
                            cosets_count,
                            leaves_count,
                            trace_len,
                            &stream,
                        )
                        .unwrap();
                    }
                    1 => {
                        hash_leaves_from_ntt_multi_coset_to_staging(
                            &natural_device,
                            &mut logical_device,
                            log_values_per_leaf,
                            src_cols_per_coset,
                            NTT_LOG_LDE_FACTOR,
                            0,
                            cosets_count,
                            leaves_count,
                            trace_len,
                            &stream,
                        )
                        .unwrap();
                        hash_leaves_from_ntt_multi_coset_to_staging_physical(
                            &bitreversed_device,
                            &mut physical_device,
                            log_values_per_leaf,
                            src_cols_per_coset,
                            NTT_LOG_LDE_FACTOR,
                            0,
                            cosets_count,
                            leaves_count,
                            trace_len,
                            &stream,
                        )
                        .unwrap();
                    }
                    _ => {
                        hash_leaves_from_ntt_flat_range_to_staging(
                            &natural_device,
                            &mut logical_device,
                            log_values_per_leaf,
                            src_cols_per_coset,
                            NTT_LOG_LDE_FACTOR,
                            0,
                            total_leaves,
                            leaves_count,
                            trace_len,
                            &stream,
                        )
                        .unwrap();
                        hash_leaves_from_ntt_flat_range_to_staging_physical(
                            &bitreversed_device,
                            &mut physical_device,
                            log_values_per_leaf,
                            src_cols_per_coset,
                            NTT_LOG_LDE_FACTOR,
                            0,
                            total_leaves,
                            leaves_count,
                            trace_len,
                            &stream,
                        )
                        .unwrap();
                    }
                }
                memory_copy_async(&mut logical, &logical_device, &stream).unwrap();
                memory_copy_async(&mut physical, &physical_device, &stream).unwrap();
                stream.synchronize().unwrap();
                assert_bitreversed_blocks(
                    &physical,
                    &logical,
                    cosets_count,
                    leaves_count,
                    leaves_count,
                    log_leaves_count,
                    &format!("from-ntt surface {surface} {label}"),
                );
            }
        }
    }
}
