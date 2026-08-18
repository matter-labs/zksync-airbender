use era_cudart::memory::{memory_copy_async, DeviceAllocation};
use era_cudart::stream::CudaStream;

use itertools::Itertools;
use rand::Rng;

use super::super::*;
use gpu_core::primitives::device_structures::{DeviceMatrix, DeviceMatrixMut};
use gpu_core::primitives::field::BF;
use gpu_core::primitives::utils::LOG_WARP_SIZE;
use gpu_ops::simple::set_to_zero;

use super::{leaf_source_row, random_digest, verify_leaves, verify_nodes};
use crate::upstream::Field;

#[test]
fn blake2s_nodes() {
    const LOG_N: usize = 10;
    const N: usize = 1 << LOG_N;
    let mut values_host = vec![Digest::default(); N * 2];
    values_host.fill_with(random_digest);
    // One layer through the public builder: `results` is sized like `values`,
    // and a single layer fills its first `N` digests.
    let mut results_host = vec![Digest::default(); N * 2];
    let stream = CudaStream::default();
    let mut values_device = DeviceAllocation::alloc(values_host.len()).unwrap();
    let mut results_device = DeviceAllocation::alloc(results_host.len()).unwrap();
    memory_copy_async(&mut values_device, &values_host, &stream).unwrap();
    build_merkle_tree_nodes(&values_device, &mut results_device, 1, &stream).unwrap();
    memory_copy_async(&mut results_host, &results_device, &stream).unwrap();
    stream.synchronize().unwrap();
    verify_nodes(&values_host, &results_host[..N]);
}

fn verify_tree(values: &[Digest], results: &[Digest], layers_count: u32) {
    assert_eq!(values.len(), results.len());
    if layers_count == 0 {
        assert!(results.iter().all(|x| x.iter().all(|&x| x == 0)));
    } else {
        let (nodes, nodes_remaining) = results.split_at(results.len() >> 1);
        verify_nodes(values, nodes);
        verify_tree(nodes, nodes_remaining, layers_count - 1);
    }
}

fn test_merkle_tree(log_n: usize) {
    const VALUES_PER_ROW: usize = 125;
    const LOG_ROWS_PER_HASH: u32 = 1;
    let n = 1 << log_n;
    let layers_count: u32 = (log_n + 1) as u32;
    let mut values_host = vec![BF::ZERO; (n * VALUES_PER_ROW) << LOG_ROWS_PER_HASH];
    let mut rng = rand::rng();
    values_host.fill_with(|| BF::from_nonreduced_u32(rng.random()));
    let mut results_host = vec![Digest::default(); n * 2];
    let stream = CudaStream::default();
    let mut values_device = DeviceAllocation::alloc(values_host.len()).unwrap();
    let mut results_device = DeviceAllocation::alloc(results_host.len()).unwrap();
    set_to_zero(&mut results_device, &stream).unwrap();
    memory_copy_async(&mut values_device, &values_host, &stream).unwrap();
    build_merkle_tree(
        &values_device,
        &mut results_device,
        LOG_ROWS_PER_HASH,
        &stream,
        layers_count,
    )
    .unwrap();
    memory_copy_async(&mut results_host, &results_device, &stream).unwrap();
    stream.synchronize().unwrap();
    let (nodes, nodes_remaining) = results_host.split_at(results_host.len() >> 1);
    verify_leaves(&values_host, nodes, LOG_ROWS_PER_HASH);
    verify_tree(nodes, nodes_remaining, layers_count - 1);
}

#[test]
fn merkle_tree() {
    test_merkle_tree(16);
}

fn test_partial_merkle_tree_multi_coset(
    log_leaves_count: usize,
    log_rows_per_hash: u32,
    cosets_count: usize,
    cols_count: usize,
) {
    let leaves_count = 1usize << log_leaves_count;
    let full_tree_stride = leaves_count * 2;
    let partial_tree_stride = full_tree_stride >> LOG_WARP_SIZE;
    let values_stride = cols_count * (leaves_count << log_rows_per_hash);
    let full_layers_count = (log_leaves_count + 1) as u32;
    let partial_layers_count = full_layers_count - LOG_WARP_SIZE;
    let initialized_partial_len = partial_tree_stride - 1;

    let mut rng = rand::rng();
    let mut values_host = vec![BF::ZERO; values_stride * cosets_count];
    values_host.fill_with(|| BF::from_nonreduced_u32(rng.random()));
    let mut full_tree_host = vec![Digest::default(); full_tree_stride * cosets_count];
    let mut partial_tree_host = vec![Digest::default(); partial_tree_stride * cosets_count];

    let stream = CudaStream::default();
    let mut values_device = DeviceAllocation::alloc(values_host.len()).unwrap();
    let mut full_tree_device = DeviceAllocation::alloc(full_tree_host.len()).unwrap();
    let mut partial_tree_device = DeviceAllocation::alloc(partial_tree_host.len()).unwrap();
    memory_copy_async(&mut values_device, &values_host, &stream).unwrap();
    set_to_zero(&mut full_tree_device, &stream).unwrap();
    set_to_zero(&mut partial_tree_device, &stream).unwrap();

    build_merkle_tree_multi_coset(
        &values_device,
        &mut full_tree_device,
        log_rows_per_hash,
        full_layers_count,
        cosets_count,
        leaves_count,
        values_stride,
        full_tree_stride,
        cols_count,
        &stream,
    )
    .unwrap();
    build_partial_merkle_tree_multi_coset(
        &values_device,
        &mut partial_tree_device,
        log_rows_per_hash,
        partial_layers_count,
        cosets_count,
        &stream,
    )
    .unwrap();

    memory_copy_async(&mut full_tree_host, &full_tree_device, &stream).unwrap();
    memory_copy_async(&mut partial_tree_host, &partial_tree_device, &stream).unwrap();
    stream.synchronize().unwrap();

    for coset in 0..cosets_count {
        let full_start = coset * full_tree_stride + full_tree_stride - partial_tree_stride;
        let partial_start = coset * partial_tree_stride;
        assert_eq!(
            &partial_tree_host[partial_start..partial_start + initialized_partial_len],
            &full_tree_host[full_start..full_start + initialized_partial_len],
        );
    }
}

#[test]
fn partial_merkle_tree_multi_coset_matches_full_tree() {
    test_partial_merkle_tree_multi_coset(6, 0, 1, 3);
    test_partial_merkle_tree_multi_coset(8, 2, 4, 7);
    test_partial_merkle_tree_multi_coset(9, 1, 3, 0);
    test_partial_merkle_tree_multi_coset(9, 1, 3, 2);
}

#[test]
fn gather_leaf_rows() {
    const SRC_LOG_ROWS: usize = 12;
    const SRC_ROWS: usize = 1 << SRC_LOG_ROWS;
    const COLS: usize = 16;
    const LOG_ROWS_PER_LEAF: usize = 2;
    const LEAVES_COUNT: usize = SRC_ROWS >> LOG_ROWS_PER_LEAF;
    const INDEXES_COUNT: usize = 42;
    const DST_ROWS: usize = INDEXES_COUNT << LOG_ROWS_PER_LEAF;
    let mut rng = rand::rng();
    let mut indexes_host = vec![0; INDEXES_COUNT];
    indexes_host.fill_with(|| rng.random_range(0..LEAVES_COUNT as u32));
    let mut values_host = vec![BF::ZERO; SRC_ROWS * COLS];
    values_host.fill_with(|| BF::from_nonreduced_u32(rng.random()));
    let mut results_host = vec![BF::ZERO; DST_ROWS * COLS];
    let stream = CudaStream::default();
    let mut indexes_device = DeviceAllocation::<u32>::alloc(indexes_host.len()).unwrap();
    let mut values_device = DeviceAllocation::<BF>::alloc(values_host.len()).unwrap();
    let mut results_device = DeviceAllocation::<BF>::alloc(results_host.len()).unwrap();
    memory_copy_async(&mut indexes_device, &indexes_host, &stream).unwrap();
    memory_copy_async(&mut values_device, &values_host, &stream).unwrap();
    super::gather_leaf_rows(
        &indexes_device,
        false,
        LOG_ROWS_PER_LEAF as u32,
        &DeviceMatrix::new(&values_device, SRC_ROWS),
        &mut DeviceMatrixMut::new(&mut results_device, DST_ROWS),
        &stream,
    )
    .unwrap();
    memory_copy_async(&mut results_host, &results_device, &stream).unwrap();
    stream.synchronize().unwrap();
    for (i, index) in indexes_host.into_iter().enumerate() {
        let src_leaf = index as usize;
        let dst_row_base = i << LOG_ROWS_PER_LEAF;
        for j in 0..(1 << LOG_ROWS_PER_LEAF) {
            let src_row = leaf_source_row(src_leaf, j, LOG_ROWS_PER_LEAF as u32, LEAVES_COUNT);
            let dst_row = dst_row_base + j;
            for k in 0..COLS {
                let expected = values_host[(k << SRC_LOG_ROWS) + src_row];
                let actual = results_host[(k * DST_ROWS) + dst_row];
                assert_eq!(expected, actual);
            }
        }
    }
}

#[test]
fn gather_merkle_paths() {
    const LOG_LEAVES_COUNT: usize = 12;
    const INDEXES_COUNT: usize = 42;
    const LAYERS_COUNT: usize = LOG_LEAVES_COUNT - 4;
    let mut rng = rand::rng();
    let mut indexes_host = vec![0; INDEXES_COUNT];
    indexes_host.fill_with(|| rng.random_range(0..1u32 << LOG_LEAVES_COUNT));
    let mut values_host = vec![Digest::default(); 1 << (LOG_LEAVES_COUNT + 1)];
    values_host.fill_with(random_digest);
    let mut results_host = vec![Digest::default(); INDEXES_COUNT * LAYERS_COUNT];
    let stream = CudaStream::default();
    let mut indexes_device = DeviceAllocation::alloc(indexes_host.len()).unwrap();
    let mut values_device = DeviceAllocation::alloc(values_host.len()).unwrap();
    let mut results_device = DeviceAllocation::alloc(results_host.len()).unwrap();
    memory_copy_async(&mut indexes_device, &indexes_host, &stream).unwrap();
    memory_copy_async(&mut values_device, &values_host, &stream).unwrap();
    gather_merkle_paths_device(
        &indexes_device,
        &values_device,
        &mut results_device,
        LAYERS_COUNT as u32,
        &stream,
    )
    .unwrap();
    memory_copy_async(&mut results_host, &results_device, &stream).unwrap();
    stream.synchronize().unwrap();
    fn verify_merkle_path(indexes: &[u32], values: &[Digest], results: &[Digest]) {
        let (values, values_next) = values.split_at(values.len() >> 1);
        let (results, results_next) = results.split_at(INDEXES_COUNT);
        for (row_index, &index) in indexes.iter().enumerate() {
            let sibling_index = (index ^ 1) as usize;
            let expected = values[sibling_index];
            let actual = results[row_index];
            assert_eq!(expected, actual);
        }
        if !results_next.is_empty() {
            let indexes_next = indexes.iter().map(|&x| x >> 1).collect_vec();
            verify_merkle_path(&indexes_next, values_next, results_next);
        }
    }
    verify_merkle_path(&indexes_host, &values_host, &results_host);
}
