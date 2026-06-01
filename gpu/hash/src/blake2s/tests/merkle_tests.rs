use era_cudart::memory::{memory_copy_async, DeviceAllocation};

use itertools::Itertools;
use rand::Rng;
use serial_test::serial;

use super::super::*;
use gpu_core::primitives::device_structures::{DeviceMatrix, DeviceMatrixMut};
use gpu_ops::simple::set_to_zero;

use super::{gather_rows, leaf_source_row, random_digest, verify_leaves, verify_nodes};
use crate::upstream::Field;

#[test]
#[serial]
fn leaves() {
    const LOG_N: usize = 10;
    const N: usize = 1 << LOG_N;
    const VALUES_PER_ROW: usize = 125;
    const LOG_ROWS_PER_HASH: u32 = 1;
    let mut values_host = vec![BF::ZERO; (N * VALUES_PER_ROW) << LOG_ROWS_PER_HASH];
    let mut rng = rand::rng();
    values_host.fill_with(|| BF::from_nonreduced_u32(rng.random()));
    let mut results_host = vec![Digest::default(); N];
    let stream = CudaStream::default();
    let mut values_device = DeviceAllocation::alloc(values_host.len()).unwrap();
    let mut results_device = DeviceAllocation::alloc(results_host.len()).unwrap();
    memory_copy_async(&mut values_device, &values_host, &stream).unwrap();
    launch_leaves_kernel(
        &values_device,
        &mut results_device,
        LOG_ROWS_PER_HASH,
        &stream,
    )
    .unwrap();
    memory_copy_async(&mut results_host, &results_device, &stream).unwrap();
    stream.synchronize().unwrap();
    verify_leaves(&values_host, &results_host, LOG_ROWS_PER_HASH);
}

#[test]
#[serial]
fn blake2s_nodes() {
    const LOG_N: usize = 10;
    const N: usize = 1 << LOG_N;
    let mut values_host = vec![Digest::default(); N * 2];
    values_host.fill_with(random_digest);
    let mut results_host = vec![Digest::default(); N];
    let stream = CudaStream::default();
    let mut values_device = DeviceAllocation::alloc(values_host.len()).unwrap();
    let mut results_device = DeviceAllocation::alloc(results_host.len()).unwrap();
    memory_copy_async(&mut values_device, &values_host, &stream).unwrap();
    launch_nodes_kernel(&values_device, &mut results_device, &stream).unwrap();
    memory_copy_async(&mut results_host, &results_device, &stream).unwrap();
    stream.synchronize().unwrap();
    verify_nodes(&values_host, &results_host);
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
        false,
    )
    .unwrap();
    memory_copy_async(&mut results_host, &results_device, &stream).unwrap();
    stream.synchronize().unwrap();
    let (nodes, nodes_remaining) = results_host.split_at(results_host.len() >> 1);
    verify_leaves(&values_host, nodes, LOG_ROWS_PER_HASH);
    verify_tree(nodes, nodes_remaining, layers_count - 1);
}

#[test]
#[serial]
fn merkle_tree_small() {
    test_merkle_tree(8);
}

#[test]
#[serial]
fn merkle_tree_large() {
    test_merkle_tree(16);
}

#[test]
#[serial]
fn test_gather_rows() {
    const SRC_LOG_ROWS: usize = 12;
    const SRC_ROWS: usize = 1 << SRC_LOG_ROWS;
    const COLS: usize = 16;
    const INDEXES_COUNT: usize = 42;
    const LOG_ROWS_PER_INDEX: usize = 1;
    const DST_ROWS: usize = INDEXES_COUNT << LOG_ROWS_PER_INDEX;
    let mut rng = rand::rng();
    let mut indexes_host = vec![0; INDEXES_COUNT];
    indexes_host.fill_with(|| rng.random_range(0..INDEXES_COUNT as u32));
    let mut values_host = vec![BF::ZERO; SRC_ROWS * COLS];
    values_host.fill_with(|| BF::from_nonreduced_u32(rng.random()));
    let mut results_host = vec![BF::ZERO; DST_ROWS * COLS];
    let stream = CudaStream::default();
    let mut indexes_device = DeviceAllocation::<u32>::alloc(indexes_host.len()).unwrap();
    let mut values_device = DeviceAllocation::<BF>::alloc(values_host.len()).unwrap();
    let mut results_device = DeviceAllocation::<BF>::alloc(results_host.len()).unwrap();
    memory_copy_async(&mut indexes_device, &indexes_host, &stream).unwrap();
    memory_copy_async(&mut values_device, &values_host, &stream).unwrap();
    gather_rows(
        &indexes_device,
        false,
        LOG_ROWS_PER_INDEX as u32,
        &DeviceMatrix::new(&values_device, SRC_ROWS),
        &mut DeviceMatrixMut::new(&mut results_device, DST_ROWS),
        &stream,
    )
    .unwrap();
    memory_copy_async(&mut results_host, &results_device, &stream).unwrap();
    stream.synchronize().unwrap();
    for (i, index) in indexes_host.into_iter().enumerate() {
        let src_index = (index as usize) << LOG_ROWS_PER_INDEX;
        let dst_index = i << LOG_ROWS_PER_INDEX;
        for j in 0..1 << LOG_ROWS_PER_INDEX {
            let src_index = src_index + j;
            let dst_index = dst_index + j;
            for k in 0..COLS {
                let expected = values_host[(k << SRC_LOG_ROWS) + src_index];
                let actual = results_host[(k * DST_ROWS) + dst_index];
                assert_eq!(expected, actual);
            }
        }
    }
}

#[test]
#[serial]
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
#[serial]
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

#[test]
#[serial]
fn merkle_tree_cap() {
    const LOG_N: u32 = 10;
    const N: usize = 1 << LOG_N;
    const LOG_CAP_SIZE: u32 = LOG_N - 1;
    const CAP_SIZE: usize = 1 << LOG_CAP_SIZE;
    let mut values_host = vec![Digest::default(); N * 2];
    let mut counter: u32 = 0;
    values_host.fill_with(|| {
        let value = counter;
        counter += 1;
        [value; STATE_SIZE]
    });
    let mut values_device = DeviceAllocation::alloc(values_host.len()).unwrap();
    let stream = CudaStream::create().unwrap();
    memory_copy_async(&mut values_device, &values_host, &stream).unwrap();
    let cap_device = super::merkle_tree_cap(&values_device, LOG_CAP_SIZE);
    let mut cap_host = vec![Digest::default(); CAP_SIZE];
    memory_copy_async(&mut cap_host, cap_device, &stream).unwrap();
    stream.synchronize().unwrap();
    assert_eq!(cap_host.len(), CAP_SIZE);
    assert_eq!(cap_host, values_host[N..3 * N / 2]);
}
