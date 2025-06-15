use era_cudart::cuda_kernel;
use era_cudart::device::{device_get_attribute, get_device};
use era_cudart::execution::{CudaLaunchConfig, Dim3, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart_sys::CudaDeviceAttr;

use crate::device_structures::{
    DeviceMatrixChunkImpl, DeviceMatrixChunkMutImpl, MutPtrAndStride, PtrAndStride,
};
use crate::field::BaseField;
use crate::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};

type BF = BaseField;

pub const RATE: usize = 8;
pub const CAPACITY: usize = 8;
pub const WIDTH: usize = RATE + CAPACITY;

pub type Digest = [BF; CAPACITY];

cuda_kernel!(
    Leaves,
    leaves_kernel,
    values: *const BF,
    results: *mut Digest,
    log_rows_per_hash: u32,
    cols_count: u32,
    count: u32,
);

leaves_kernel!(monolith_leaves_st_kernel);
leaves_kernel!(monolith_leaves_mt_kernel);

#[allow(clippy::too_many_arguments)]
pub fn launch_leaves_generic_kernel(
    kernel_function: LeavesSignature,
    grid_dim: Dim3,
    block_dim: Dim3,
    values: &DeviceSlice<BF>,
    results: &mut DeviceSlice<Digest>,
    log_rows_per_hash: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(RATE, CAPACITY);
    let values_len = values.len();
    let count = results.len();
    assert_eq!(values_len % (count << log_rows_per_hash), 0);
    let values = values.as_ptr();
    let results = results.as_mut_ptr();
    let cols_count = values_len / (count << log_rows_per_hash);
    assert!(cols_count <= u32::MAX as usize);
    let cols_count = cols_count as u32;
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = LeavesArguments::new(values, results, log_rows_per_hash, cols_count, count);
    LeavesFunction(kernel_function).launch(&config, &args)
}

pub fn launch_leaves_st_kernel(
    values: &DeviceSlice<BF>,
    results: &mut DeviceSlice<Digest>,
    log_rows_per_hash: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(RATE, CAPACITY);
    let count = results.len() as u32;
    let kernel_function = monolith_leaves_st_kernel;
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    launch_leaves_generic_kernel(
        kernel_function,
        grid_dim,
        block_dim,
        values,
        results,
        log_rows_per_hash,
        stream,
    )
}

pub fn launch_leaves_mt_kernel(
    values: &DeviceSlice<BF>,
    results: &mut DeviceSlice<Digest>,
    log_rows_per_hash: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(RATE, CAPACITY);
    let count = results.len() as u32;
    let kernel_function = monolith_leaves_mt_kernel;
    assert_eq!((WARP_SIZE * 4) % WIDTH as u32, 0);
    let threads_per_block = WARP_SIZE * 4 / WIDTH as u32;
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(threads_per_block, count);
    let block_dim = (WIDTH as u32, block_dim.x).into();
    launch_leaves_generic_kernel(
        kernel_function,
        grid_dim,
        block_dim,
        values,
        results,
        log_rows_per_hash,
        stream,
    )
}

pub fn launch_leaves_kernel(
    values: &DeviceSlice<BF>,
    results: &mut DeviceSlice<Digest>,
    log_rows_per_hash: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    const MT_BPM: u32 = 9;
    let device_id = get_device()?;
    let mpc = device_get_attribute(CudaDeviceAttr::MultiProcessorCount, device_id)? as u32;
    assert_eq!(RATE, CAPACITY);
    let count = results.len() as u32;
    assert_eq!((WARP_SIZE * 4) % WIDTH as u32, 0);
    let threads_per_block = WARP_SIZE * 4 / WIDTH as u32;
    let (grid_dim, _) = get_grid_block_dims_for_threads_count(threads_per_block, count);
    let launch = if grid_dim.x > MT_BPM * mpc {
        launch_leaves_st_kernel
    } else {
        launch_leaves_mt_kernel
    };
    launch(values, results, log_rows_per_hash, stream)
}

pub fn build_merkle_tree_leaves(
    values: &DeviceSlice<BF>,
    results: &mut DeviceSlice<Digest>,
    log_rows_per_hash: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let values_len = values.len();
    let leaves_count = results.len();
    assert_eq!(values_len % leaves_count, 0);
    launch_leaves_kernel(values, results, log_rows_per_hash, stream)
}

cuda_kernel!(
    Nodes,
    nodes_kernel,
    values: *const Digest,
    results: *mut Digest,
    count: u32,
);

nodes_kernel!(monolith_nodes_st_kernel);
nodes_kernel!(monolith_nodes_mt_kernel);

fn launch_nodes_generic_kernel(
    kernel_function: NodesSignature,
    grid_dim: Dim3,
    block_dim: Dim3,
    values: &DeviceSlice<Digest>,
    results: &mut DeviceSlice<Digest>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(RATE, CAPACITY);
    let values_len = values.len();
    let results_len = results.len();
    assert_eq!(values_len, results_len * 2);
    let values = values.as_ptr();
    let results = results.as_mut_ptr();
    assert!(results_len <= u32::MAX as usize);
    let count = results_len as u32;
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = NodesArguments::new(values, results, count);
    NodesFunction(kernel_function).launch(&config, &args)
}

pub fn launch_nodes_st_kernel(
    values: &DeviceSlice<Digest>,
    results: &mut DeviceSlice<Digest>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(RATE, CAPACITY);
    let count = results.len() as u32;
    let kernel_function = monolith_nodes_st_kernel;
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    launch_nodes_generic_kernel(
        kernel_function,
        grid_dim,
        block_dim,
        values,
        results,
        stream,
    )
}

pub fn launch_nodes_mt_kernel(
    values: &DeviceSlice<Digest>,
    results: &mut DeviceSlice<Digest>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(RATE, CAPACITY);
    let count = results.len() as u32;
    let kernel_function = monolith_nodes_mt_kernel;
    assert_eq!((WARP_SIZE * 4) % WIDTH as u32, 0);
    let threads_per_block = WARP_SIZE * 4 / WIDTH as u32;
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(threads_per_block, count);
    let block_dim = (WIDTH as u32, block_dim.x).into();
    launch_nodes_generic_kernel(
        kernel_function,
        grid_dim,
        block_dim,
        values,
        results,
        stream,
    )
}

pub fn launch_nodes_kernel(
    values: &DeviceSlice<Digest>,
    results: &mut DeviceSlice<Digest>,
    stream: &CudaStream,
) -> CudaResult<()> {
    const MT_BPM: u32 = 10;
    let device_id = get_device()?;
    let mpc = device_get_attribute(CudaDeviceAttr::MultiProcessorCount, device_id)? as u32;
    assert_eq!(RATE, CAPACITY);
    let count = results.len() as u32;
    assert_eq!((WARP_SIZE * 4) % WIDTH as u32, 0);
    let threads_per_block = WARP_SIZE * 4 / WIDTH as u32;
    let (grid_dim, _) = get_grid_block_dims_for_threads_count(threads_per_block, count);
    let launch = if grid_dim.x > MT_BPM * mpc {
        launch_nodes_st_kernel
    } else {
        launch_nodes_mt_kernel
    };
    launch(values, results, stream)
}

pub fn build_merkle_tree_nodes(
    values: &DeviceSlice<Digest>,
    results: &mut DeviceSlice<Digest>,
    layers_count: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    if layers_count == 0 {
        Ok(())
    } else {
        let values_len = values.len();
        let results_len = results.len();
        let layer = values_len.trailing_zeros();
        assert_eq!(values_len, 1 << layer);
        assert_eq!(values_len, results_len);
        let (nodes, nodes_remaining) = results.split_at_mut(results_len >> 1);
        launch_nodes_kernel(values, nodes, stream)?;
        build_merkle_tree_nodes(nodes, nodes_remaining, layers_count - 1, stream)
    }
}

pub fn build_merkle_tree(
    values: &DeviceSlice<BF>,
    results: &mut DeviceSlice<Digest>,
    log_rows_per_hash: u32,
    stream: &CudaStream,
    layers_count: u32,
) -> CudaResult<()> {
    assert_ne!(layers_count, 0);
    let values_len = values.len();
    let results_len = results.len();
    assert_eq!(results_len % 2, 0);
    let leaves_count = results_len / 2;
    assert!(1 << (layers_count - 1) <= leaves_count);
    assert_eq!(values_len % leaves_count, 0);
    let (leaves, nodes) = results.split_at_mut(leaves_count);
    build_merkle_tree_leaves(values, leaves, log_rows_per_hash, stream)?;
    if bit_reverse_leaves {
        bit_reverse_in_place(leaves, stream)?;
    }
    build_merkle_tree_nodes(leaves, nodes, layers_count - 1, stream)
}

cuda_kernel!(
    GatherRows,
    gather_rows_kernel(
        indexes: *const u32,
        indexes_count: u32,
        values: PtrAndStride<BF>,
        results: MutPtrAndStride<BF>,
    )
);

pub fn gather_rows(
    indexes: &DeviceSlice<u32>,
    log_rows_per_index: u32,
    values: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    result: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    stream: &CudaStream,
) -> CudaResult<()> {
    let indexes_len = indexes.len();
    let values_cols = values.cols();
    let result_rows = result.rows();
    let result_cols = result.cols();
    let rows_per_index = 1 << log_rows_per_index;
    assert!(log_rows_per_index < WARP_SIZE);
    assert_eq!(result_cols, values_cols);
    assert_eq!(result_rows, indexes_len << log_rows_per_index);
    assert!(indexes_len <= u32::MAX as usize);
    let indexes_count = indexes_len as u32;
    let (mut grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(WARP_SIZE >> log_rows_per_index, indexes_count);
    let block_dim = (rows_per_index, block_dim.x);
    assert!(result_cols <= u32::MAX as usize);
    grid_dim.y = result_cols as u32;
    let indexes = indexes.as_ptr();
    let values = values.as_ptr_and_stride();
    let result = result.as_mut_ptr_and_stride();
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GatherRowsArguments::new(indexes, indexes_count, values, result);
    GatherRowsFunction::default().launch(&config, &args)
}

cuda_kernel!(
    GatherMerklePaths,
    gather_merkle_paths_kernel(
        indexes: *const u32,
        indexes_count: u32,
        values: *const Digest,
        log_leaves_count: u32,
        results: *mut Digest,
    )
);

pub fn gather_merkle_paths(
    indexes: &DeviceSlice<u32>,
    values: &DeviceSlice<Digest>,
    results: &mut DeviceSlice<Digest>,
    layers_count: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(indexes.len() <= u32::MAX as usize);
    let indexes_count = indexes.len() as u32;
    let values_count = values.len();
    assert!(values_count.is_power_of_two());
    let log_values_count = values_count.trailing_zeros();
    assert_ne!(log_values_count, 0);
    let log_leaves_count = log_values_count - 1;
    assert!(layers_count < log_leaves_count);
    assert_eq!(indexes.len() * layers_count as usize, results.len());
    assert_eq!(WARP_SIZE % CAPACITY as u32, 0);
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(WARP_SIZE / CAPACITY as u32, indexes_count);
    let grid_dim = (grid_dim.x, layers_count);
    let block_dim = (CAPACITY as u32, block_dim.x);
    let indexes = indexes.as_ptr();
    let values = values.as_ptr();
    let result = results.as_mut_ptr();
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args =
        GatherMerklePathsArguments::new(indexes, indexes_count, values, log_leaves_count, result);
    GatherMerklePathsFunction::default().launch(&config, &args)
}

pub fn merkle_tree_cap(values: &DeviceSlice<Digest>, cap_size: usize) -> &DeviceSlice<Digest> {
    assert_ne!(cap_size, 0);
    assert!(cap_size.is_power_of_two());
    let log_cap_size = cap_size.trailing_zeros();
    let values_len = values.len();
    assert_ne!(values_len, 0);
    assert!(values_len.is_power_of_two());
    let log_values_len = values_len.trailing_zeros();
    assert!(log_values_len > log_cap_size);
    let offset = values_len - (1 << (log_cap_size + 1));
    &values[offset..offset + cap_size]
}

#[cfg(test)]
mod tests {
    use era_cudart::memory::{memory_copy, memory_copy_async, DeviceAllocation};
    use field::Field;
    use itertools::Itertools;
    use rand::Rng;
    use serial_test::serial;
    use zksync_airbender::algebra::Mersenne31Field;
    use zksync_airbender::monolith::Monolith;
    use zksync_airbender::prover::merkle_tree::{
        AlgebraicSpongeBasedCompression, CompressionFunction,
    };

    use crate::device_structures::{DeviceMatrix, DeviceMatrixMut};
    use crate::ops_simple::set_to_zero;

    use super::*;

    fn verify_leaves(values: &[BF], results: &[Digest], log_rows_per_hash: u32) {
        let count = results.len();
        let values_len = values.len();
        assert_eq!(values_len % (count << log_rows_per_hash), 0);
        let cols_count = values_len / (count << log_rows_per_hash);
        let rows_count = 1 << log_rows_per_hash;
        type CompressionFunction =
            AlgebraicSpongeBasedCompression<Mersenne31Field, WIDTH, Mersenne31Field>;
        for i in 0..count {
            let mut input = vec![];
            for col in 0..cols_count {
                let offset = (i << log_rows_per_hash) + col * rows_count * count;
                input.extend_from_slice(&values[offset..offset + rows_count]);
            }
            let mut sponge = CompressionFunction::new();
            let expected = sponge.hash_into_leaf(&input);
            let actual = results[i];
            assert_eq!(expected, actual);
        }
    }

    fn verify_nodes(values: &[Digest], results: &[Digest]) {
        let results_len = results.len();
        let values_len = values.len();
        assert_eq!(values_len, results_len * 2);
        values
            .chunks_exact(2)
            .zip(results)
            .for_each(|(input, actual)| {
                let state = input
                    .iter()
                    .flat_map(|&x| x.into_iter())
                    .collect_vec()
                    .try_into()
                    .unwrap();
                let output = <BF as Monolith<WIDTH>>::monolith(state);
                let expected = &output[0..CAPACITY];
                assert_eq!(expected, actual);
            });
    }

    #[allow(clippy::type_complexity)]
    fn test_leaves(
        launch: fn(&DeviceSlice<BF>, &mut DeviceSlice<Digest>, u32, &CudaStream) -> CudaResult<()>,
    ) {
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
        launch(
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

    fn random_digest() -> Digest {
        let mut rng = rand::rng();
        let mut result = Digest::default();
        result.fill_with(|| BF::from_nonreduced_u32(rng.random()));
        result
    }

    fn test_nodes(
        launch: fn(&DeviceSlice<Digest>, &mut DeviceSlice<Digest>, &CudaStream) -> CudaResult<()>,
    ) {
        const LOG_N: usize = 10;
        const N: usize = 1 << LOG_N;
        let mut values_host = vec![Digest::default(); N * 2];
        values_host.fill_with(random_digest);
        let mut results_host = vec![Digest::default(); N];
        let stream = CudaStream::default();
        let mut values_device = DeviceAllocation::alloc(values_host.len()).unwrap();
        let mut results_device = DeviceAllocation::alloc(results_host.len()).unwrap();
        memory_copy_async(&mut values_device, &values_host, &stream).unwrap();
        launch(&values_device, &mut results_device, &stream).unwrap();
        memory_copy_async(&mut results_host, &results_device, &stream).unwrap();
        stream.synchronize().unwrap();
        verify_nodes(&values_host, &results_host);
    }

    #[test]
    #[serial]
    fn monolith_leaves_st() {
        test_leaves(launch_leaves_st_kernel);
    }

    #[test]
    #[serial]
    fn monolith_leaves_mt() {
        test_leaves(launch_leaves_mt_kernel);
    }

    #[test]
    #[serial]
    fn monolith_nodes_st() {
        test_nodes(launch_nodes_st_kernel);
    }

    #[test]
    #[serial]
    fn monolith_nodes_mt() {
        test_nodes(launch_nodes_mt_kernel);
    }

    fn verify_tree(values: &[Digest], results: &[Digest], layers_count: u32) {
        assert_eq!(values.len(), results.len());
        if layers_count == 0 {
            assert!(results.iter().all(|x| x.iter().all(|x| x.is_zero())));
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
    fn merkle_tree_small() {
        test_merkle_tree(8);
    }

    #[test]
    #[ignore]
    fn merkle_tree_large() {
        test_merkle_tree(16);
    }

    #[test]
    fn gather_rows() {
        const SRC_LOG_ROWS: usize = 12;
        const SRC_ROWS: usize = 1 << SRC_LOG_ROWS;
        const COLS: usize = 16;
        const INDEXES_COUNT: usize = 42;
        const LOG_ROWS_PER_INDEX: usize = 1;
        const DST_ROWS: usize = INDEXES_COUNT << LOG_ROWS_PER_INDEX;
        let mut rng = rand::rng();
        let mut indexes_host = vec![0; INDEXES_COUNT];
        indexes_host.fill_with(|| rng.gen_range(0..INDEXES_COUNT as u32));
        let mut values_host = vec![BF::ZERO; SRC_ROWS * COLS];
        values_host.fill_with(|| BF::from_nonreduced_u32(rng.random()));
        let mut results_host = vec![BF::ZERO; DST_ROWS * COLS];
        let stream = CudaStream::default();
        let mut indexes_device = DeviceAllocation::<u32>::alloc(indexes_host.len()).unwrap();
        let mut values_device = DeviceAllocation::<BF>::alloc(values_host.len()).unwrap();
        let mut results_device = DeviceAllocation::<BF>::alloc(results_host.len()).unwrap();
        memory_copy_async(&mut indexes_device, &indexes_host, &stream).unwrap();
        memory_copy_async(&mut values_device, &values_host, &stream).unwrap();
        super::gather_rows(
            &indexes_device,
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
    fn gather_merkle_paths() {
        const LOG_LEAVES_COUNT: usize = 12;
        const INDEXES_COUNT: usize = 42;
        const LAYERS_COUNT: usize = LOG_LEAVES_COUNT - 4;
        let mut rng = rand::rng();
        let mut indexes_host = vec![0; INDEXES_COUNT];
        indexes_host.fill_with(|| rng.gen_range(0..1u32 << LOG_LEAVES_COUNT));
        let mut values_host = vec![Digest::default(); 1 << (LOG_LEAVES_COUNT + 1)];
        values_host.fill_with(random_digest);
        let mut results_host = vec![Digest::default(); INDEXES_COUNT * LAYERS_COUNT];
        let stream = CudaStream::default();
        let mut indexes_device = DeviceAllocation::alloc(indexes_host.len()).unwrap();
        let mut values_device = DeviceAllocation::alloc(values_host.len()).unwrap();
        let mut results_device = DeviceAllocation::alloc(results_host.len()).unwrap();
        memory_copy_async(&mut indexes_device, &indexes_host, &stream).unwrap();
        memory_copy_async(&mut values_device, &values_host, &stream).unwrap();
        super::gather_merkle_paths(
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
    fn merkle_tree_cap() {
        const LOG_N: usize = 10;
        const N: usize = 1 << LOG_N;
        const CAP_SIZE: usize = 1 << (LOG_N - 1);
        let mut values_host = vec![Digest::default(); N * 2];
        let mut counter: u64 = 0;
        values_host.fill_with(|| {
            let value = counter;
            counter += 1;
            [BF::from_nonreduced_u32(value); CAPACITY]
        });
        let mut values_device = DeviceAllocation::alloc(values_host.len()).unwrap();
        memory_copy(&mut values_device, &values_host).unwrap();
        let cap_device = super::merkle_tree_cap(&values_device, CAP_SIZE);
        let mut cap_host = vec![Digest::default(); CAP_SIZE];
        memory_copy(&mut cap_host, cap_device).unwrap();
        assert_eq!(cap_host.len(), CAP_SIZE);
        assert_eq!(cap_host, values_host[N..3 * N / 2]);
    }
}
