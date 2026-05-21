use crate::ops::bit_reverse::bit_reverse_in_place;
use crate::primitives::device_structures::{
    DeviceMatrixChunkImpl, DeviceMatrixChunkMutImpl, MutPtrAndStride, PtrAndStride,
};
use crate::primitives::field::{BF, E4};
use crate::primitives::utils::{get_grid_block_dims_for_threads_count, LOG_WARP_SIZE, WARP_SIZE};
use era_cudart::cuda_kernel;
use era_cudart::device::{device_get_attribute, get_device};
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::memory::memory_set_async;
use era_cudart::occupancy::max_active_blocks_per_multiprocessor;
use era_cudart::result::CudaResult;
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart::stream::CudaStream;
use era_cudart_sys::CudaDeviceAttr;

pub(crate) const STATE_SIZE: usize = 8;

pub(crate) type Digest = [u32; STATE_SIZE];

pub(crate) type DG = Digest;

cuda_kernel!(
    Leaves,
    ab_blake2s_leaves_kernel(
        values: *const BF,
        results: *mut DG,
        log_rows_per_hash: u32,
        cols_count: u32,
        count: u32,
    )
);

pub(crate) fn launch_leaves_kernel(
    values: &DeviceSlice<BF>,
    results: &mut DeviceSlice<DG>,
    log_rows_per_hash: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let values_len = values.len();
    let count = results.len();
    let values = values.as_ptr();
    let results = results.as_mut_ptr();
    assert_eq!(values_len % (count << log_rows_per_hash), 0);
    let cols_count = values_len / (count << log_rows_per_hash);
    assert!(cols_count <= u32::MAX as usize);
    let cols_count = cols_count as u32;
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = LeavesArguments::new(values, results, log_rows_per_hash, cols_count, count);
    LeavesFunction::default().launch(&config, &args)
}

pub(crate) fn build_merkle_tree_leaves(
    values: &DeviceSlice<BF>,
    results: &mut DeviceSlice<DG>,
    log_rows_per_hash: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let values_len = values.len();
    let leaves_count = results.len();
    assert_eq!(values_len % leaves_count, 0);
    launch_leaves_kernel(values, results, log_rows_per_hash, stream)
}

cuda_kernel!(
    LeavesMultiCoset,
    ab_blake2s_leaves_multi_coset_kernel(
        values: *const BF,
        results: *mut DG,
        log_rows_per_hash: u32,
        cols_count: u32,
        log_per_coset_count: u32,
        per_coset_values_stride_bf: u32,
        per_coset_results_stride_digests: u32,
        count: u32,
    )
);

/// Multi-coset variant of `launch_leaves_kernel`: hashes
/// `per_coset_leaves_count * cosets_in_tile` leaves in one launch. Each
/// coset's inputs sit in an independent per-coset slab strided by
/// `per_coset_values_stride_bf`; each coset's outputs sit at offset
/// `coset * per_coset_results_stride_digests` inside `results`. The caller
/// passes the full `results` backing and the kernel addresses each coset's
/// leaves slab via the stride.
pub(crate) fn launch_leaves_kernel_multi_coset(
    values: &DeviceSlice<BF>,
    results: &mut DeviceSlice<DG>,
    log_rows_per_hash: u32,
    cosets_in_tile: usize,
    per_coset_leaves_count: usize,
    per_coset_values_stride_bf: usize,
    per_coset_results_stride_digests: usize,
    cols_count: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(cosets_in_tile >= 1);
    assert!(
        per_coset_leaves_count.is_power_of_two(),
        "per_coset_leaves_count must be a power of two (got {per_coset_leaves_count})"
    );
    let log_per_coset_count = per_coset_leaves_count.trailing_zeros();
    let total_count = per_coset_leaves_count
        .checked_mul(cosets_in_tile)
        .expect("leaves total count overflow");
    // Each coset's input slab must cover cols_count * (per_coset_leaves_count
    // << log_rows_per_hash) BFs starting at `coset * per_coset_values_stride_bf`.
    let per_coset_values_required = cols_count * (per_coset_leaves_count << log_rows_per_hash);
    assert!(per_coset_values_stride_bf >= per_coset_values_required);
    let last_coset_values_end =
        (cosets_in_tile - 1) * per_coset_values_stride_bf + per_coset_values_required;
    assert!(values.len() >= last_coset_values_end);
    // Each coset's output region occupies `per_coset_leaves_count` digests
    // starting at `coset * per_coset_results_stride_digests`.
    assert!(per_coset_results_stride_digests >= per_coset_leaves_count);
    let last_coset_results_end =
        (cosets_in_tile - 1) * per_coset_results_stride_digests + per_coset_leaves_count;
    assert!(results.len() >= last_coset_results_end);
    assert!(cols_count <= u32::MAX as usize);
    assert!(total_count <= u32::MAX as usize);
    assert!(per_coset_values_stride_bf <= u32::MAX as usize);
    assert!(per_coset_results_stride_digests <= u32::MAX as usize);
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(WARP_SIZE * 4, total_count as u32);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = LeavesMultiCosetArguments::new(
        values.as_ptr(),
        results.as_mut_ptr(),
        log_rows_per_hash,
        cols_count as u32,
        log_per_coset_count,
        per_coset_values_stride_bf as u32,
        per_coset_results_stride_digests as u32,
        total_count as u32,
    );
    LeavesMultiCosetFunction::default().launch(&config, &args)
}

cuda_kernel!(Nodes, ab_blake2s_nodes_kernel(values: *const DG, results: *mut DG, count: u32,));

pub(crate) fn launch_nodes_kernel(
    values: &DeviceSlice<DG>,
    results: &mut DeviceSlice<DG>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let values_len = values.len();
    let results_len = results.len();
    assert_eq!(values_len, results_len * 2);
    let values = values.as_ptr();
    let results = results.as_mut_ptr();
    assert!(results_len <= u32::MAX as usize);
    let count = results_len as u32;
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = NodesArguments::new(values, results, count);
    NodesFunction::default().launch(&config, &args)
}

pub(crate) fn build_merkle_tree_nodes(
    values: &DeviceSlice<DG>,
    results: &mut DeviceSlice<DG>,
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

cuda_kernel!(
    NodesMultiCoset,
    ab_blake2s_nodes_multi_coset_kernel(
        values: *const DG,
        results: *mut DG,
        log_per_coset_count: u32,
        per_coset_values_stride_digests: u32,
        per_coset_results_stride_digests: u32,
        count: u32,
    )
);

/// Launch the multi-coset nodes kernel reading from `src_backing` (at
/// `src_offset_in_coset` within each coset's slab of stride
/// `per_coset_src_stride_digests`) and writing to `dst_backing` (at
/// `dst_offset_in_coset` within each coset's slab of stride
/// `per_coset_dst_stride_digests`). When src and dst are the same allocation,
/// use `launch_nodes_kernel_multi_coset_at_offsets` to avoid the aliased
/// `&mut` borrow.
fn launch_nodes_kernel_multi_coset_separate(
    src_backing: &DeviceSlice<DG>,
    dst_backing: &mut DeviceSlice<DG>,
    cosets_in_tile: usize,
    per_coset_src_stride_digests: usize,
    per_coset_dst_stride_digests: usize,
    src_offset_in_coset: usize,
    dst_offset_in_coset: usize,
    output_per_coset_count: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(cosets_in_tile >= 1);
    assert!(
        output_per_coset_count.is_power_of_two(),
        "output_per_coset_count must be a power of two (got {output_per_coset_count})"
    );
    let log_per_coset_count = output_per_coset_count.trailing_zeros();
    let total_count = output_per_coset_count
        .checked_mul(cosets_in_tile)
        .expect("nodes total count overflow");
    let last_src_end = (cosets_in_tile - 1) * per_coset_src_stride_digests
        + src_offset_in_coset
        + output_per_coset_count * 2;
    let last_dst_end = (cosets_in_tile - 1) * per_coset_dst_stride_digests
        + dst_offset_in_coset
        + output_per_coset_count;
    assert!(src_backing.len() >= last_src_end);
    assert!(dst_backing.len() >= last_dst_end);
    assert!(total_count <= u32::MAX as usize);
    assert!(per_coset_src_stride_digests <= u32::MAX as usize);
    assert!(per_coset_dst_stride_digests <= u32::MAX as usize);
    let src_ptr = unsafe { src_backing.as_ptr().add(src_offset_in_coset) };
    let dst_ptr = unsafe { dst_backing.as_mut_ptr().add(dst_offset_in_coset) };
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(WARP_SIZE * 4, total_count as u32);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = NodesMultiCosetArguments::new(
        src_ptr,
        dst_ptr,
        log_per_coset_count,
        per_coset_src_stride_digests as u32,
        per_coset_dst_stride_digests as u32,
        total_count as u32,
    );
    NodesMultiCosetFunction::default().launch(&config, &args)
}

/// Launch the multi-coset nodes kernel against a single backing slab using
/// per-coset src/dst offsets (in digests, relative to each coset's
/// `per_coset_*_stride_digests` slab). Callers express a virtual src/dst view
/// inside the per-coset slabs without re-slicing the backing buffer (which
/// would violate Rust aliasing rules when src and dst sit in the same
/// allocation).
fn launch_nodes_kernel_multi_coset_at_offsets(
    backing: &mut DeviceSlice<DG>,
    cosets_in_tile: usize,
    per_coset_stride_digests: usize,
    src_offset_in_coset: usize,
    dst_offset_in_coset: usize,
    output_per_coset_count: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(cosets_in_tile >= 1);
    assert!(
        output_per_coset_count.is_power_of_two(),
        "output_per_coset_count must be a power of two (got {output_per_coset_count})"
    );
    let log_per_coset_count = output_per_coset_count.trailing_zeros();
    let total_count = output_per_coset_count
        .checked_mul(cosets_in_tile)
        .expect("nodes total count overflow");
    // Validate the largest in-tree offsets stay within the backing.
    let last_src_end = (cosets_in_tile - 1) * per_coset_stride_digests
        + src_offset_in_coset
        + output_per_coset_count * 2;
    let last_dst_end = (cosets_in_tile - 1) * per_coset_stride_digests
        + dst_offset_in_coset
        + output_per_coset_count;
    assert!(backing.len() >= last_src_end);
    assert!(backing.len() >= last_dst_end);
    assert!(total_count <= u32::MAX as usize);
    assert!(per_coset_stride_digests <= u32::MAX as usize);
    // SAFETY: the dispatcher takes a single &mut to `backing` and derives both
    // src and dst pointers from it via offsets. The kernel reads pairs at
    // src_ptr + coset * stride and writes single digests at dst_ptr + coset *
    // stride; src and dst regions across all cosets are disjoint (we never
    // overwrite a digest before reading it) and the per-thread regions never
    // overlap. We cast away the shared borrow only to construct the kernel
    // arg.
    let base = backing.as_mut_ptr();
    let src_ptr = unsafe { base.add(src_offset_in_coset) } as *const DG;
    let dst_ptr = unsafe { base.add(dst_offset_in_coset) };
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(WARP_SIZE * 4, total_count as u32);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = NodesMultiCosetArguments::new(
        src_ptr,
        dst_ptr,
        log_per_coset_count,
        per_coset_stride_digests as u32,
        per_coset_stride_digests as u32,
        total_count as u32,
    );
    NodesMultiCosetFunction::default().launch(&config, &args)
}

/// Iteratively hash up `layers_count` Merkle layers across `cosets_in_tile`
/// trees laid out contiguously in `tree_backing` with stride
/// `per_coset_tree_stride_digests` per tree. The first layer reads from
/// `initial_src_offset_in_coset` (typically the leaves layer at offset 0) and
/// writes to `initial_src_offset_in_coset + initial_src_layer_count_per_coset`.
pub(crate) fn build_merkle_tree_nodes_multi_coset(
    tree_backing: &mut DeviceSlice<DG>,
    layers_count: u32,
    cosets_in_tile: usize,
    per_coset_tree_stride_digests: usize,
    initial_src_offset_in_coset: usize,
    initial_src_layer_count_per_coset: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    let mut src_offset = initial_src_offset_in_coset;
    let mut src_count = initial_src_layer_count_per_coset;
    for _ in 0..layers_count {
        assert_eq!(src_count % 2, 0);
        let output_count_per_coset = src_count / 2;
        let dst_offset = src_offset + src_count;
        launch_nodes_kernel_multi_coset_at_offsets(
            tree_backing,
            cosets_in_tile,
            per_coset_tree_stride_digests,
            src_offset,
            dst_offset,
            output_count_per_coset,
            stream,
        )?;
        src_offset = dst_offset;
        src_count = output_count_per_coset;
    }
    Ok(())
}

/// Multi-coset variant of `build_merkle_tree_nodes` for the partial-tree
/// bottom-hashing case: the first layer's input lives in `src_backing` (a
/// separate allocation, typically the tree_tops slab); subsequent layers hash
/// up inside `dst_backing` (the tree_bottoms slab) starting at offset 0.
pub(crate) fn build_merkle_tree_nodes_multi_coset_from_external_src(
    src_backing: &DeviceSlice<DG>,
    dst_backing: &mut DeviceSlice<DG>,
    layers_count: u32,
    cosets_in_tile: usize,
    per_coset_src_stride_digests: usize,
    per_coset_dst_stride_digests: usize,
    src_offset_in_coset: usize,
    src_layer_count_per_coset: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    if layers_count == 0 {
        return Ok(());
    }
    assert_eq!(src_layer_count_per_coset % 2, 0);
    let first_output_per_coset = src_layer_count_per_coset / 2;
    launch_nodes_kernel_multi_coset_separate(
        src_backing,
        dst_backing,
        cosets_in_tile,
        per_coset_src_stride_digests,
        per_coset_dst_stride_digests,
        src_offset_in_coset,
        /*dst_offset_in_coset=*/ 0,
        first_output_per_coset,
        stream,
    )?;
    build_merkle_tree_nodes_multi_coset(
        dst_backing,
        layers_count - 1,
        cosets_in_tile,
        per_coset_dst_stride_digests,
        /*initial_src_offset_in_coset=*/ 0,
        /*initial_src_layer_count_per_coset=*/ first_output_per_coset,
        stream,
    )
}

/// Multi-coset full merkle tree build. `tree_backing` holds
/// `cosets_in_tile` per-coset tree slabs of `per_coset_tree_stride_digests`
/// digests each (`[coset0_tree | coset1_tree | ...]`). Each coset's tree is
/// of total size `2 * per_coset_leaves_count` digests; this fn writes the
/// leaves layer + `layers_count - 1` node layers, one launch per layer
/// (instead of `cosets_in_tile * layers_count` launches).
pub(crate) fn build_merkle_tree_multi_coset(
    values: &DeviceSlice<BF>,
    tree_backing: &mut DeviceSlice<DG>,
    log_rows_per_hash: u32,
    stream: &CudaStream,
    layers_count: u32,
    cosets_in_tile: usize,
    per_coset_leaves_count: usize,
    per_coset_values_stride_bf: usize,
    per_coset_tree_stride_digests: usize,
    cols_count: usize,
) -> CudaResult<()> {
    assert_ne!(layers_count, 0);
    assert!(cosets_in_tile >= 1);
    assert!(per_coset_leaves_count >= 1 << (layers_count - 1));
    launch_leaves_kernel_multi_coset(
        values,
        tree_backing,
        log_rows_per_hash,
        cosets_in_tile,
        per_coset_leaves_count,
        per_coset_values_stride_bf,
        per_coset_tree_stride_digests,
        cols_count,
        stream,
    )?;
    build_merkle_tree_nodes_multi_coset(
        tree_backing,
        layers_count - 1,
        cosets_in_tile,
        per_coset_tree_stride_digests,
        /*initial_src_offset_in_coset=*/ 0,
        /*initial_src_layer_count_per_coset=*/ per_coset_leaves_count,
        stream,
    )
}

pub(crate) fn build_merkle_tree(
    values: &DeviceSlice<BF>,
    results: &mut DeviceSlice<DG>,
    log_rows_per_hash: u32,
    stream: &CudaStream,
    layers_count: u32,
    bit_reverse_leaves: bool,
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
ab_gather_rows_kernel(
    indexes: *const u32,
    indexes_count: u32,
    bit_reversed_indexes: bool,
    log_rows_count: u32,
    values: PtrAndStride<BF>,
    results: MutPtrAndStride<BF>,
)
);

cuda_kernel!(
    GatherLeafRows,
    ab_gather_leaf_rows_kernel(
        indexes: *const u32,
        indexes_count: u32,
        bit_reversed_indexes: bool,
        log_leaves_count: u32,
        log_rows_per_leaf: u32,
        values: PtrAndStride<BF>,
        results: MutPtrAndStride<BF>,
    )
);

#[cfg(test)]
pub(crate) fn gather_leaf_rows(
    indexes: &DeviceSlice<u32>,
    bit_reverse_indexes: bool,
    log_rows_per_leaf: u32,
    values: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    result: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    stream: &CudaStream,
) -> CudaResult<()> {
    let indexes_len = indexes.len();
    let values_cols = values.cols();
    let values_rows = values.rows();
    assert!(values_rows.is_power_of_two());
    let log_rows_count = values_rows.trailing_zeros();
    assert!(log_rows_count >= log_rows_per_leaf);
    let log_leaves_count = log_rows_count - log_rows_per_leaf;
    let result_rows = result.rows();
    let result_cols = result.cols();
    let rows_per_leaf = 1 << log_rows_per_leaf;
    assert_eq!(result_cols, values_cols);
    assert_eq!(result_rows, indexes_len << log_rows_per_leaf);
    assert!(indexes_len <= u32::MAX as usize);
    let indexes_count = indexes_len as u32;
    let (mut grid_dim, block_dim) = if log_rows_per_leaf < LOG_WARP_SIZE {
        get_grid_block_dims_for_threads_count(
            1 << (LOG_WARP_SIZE - log_rows_per_leaf),
            indexes_count,
        )
    } else {
        (indexes_count.into(), 1.into())
    };
    let block_dim = (rows_per_leaf, block_dim.x);
    assert!(result_cols <= u32::MAX as usize);
    grid_dim.y = result_cols as u32;
    let indexes = indexes.as_ptr();
    let values = values.as_ptr_and_stride();
    let result = result.as_mut_ptr_and_stride();
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GatherLeafRowsArguments::new(
        indexes,
        indexes_count,
        bit_reverse_indexes,
        log_leaves_count,
        log_rows_per_leaf,
        values,
        result,
    );
    GatherLeafRowsFunction::default().launch(&config, &args)
}

cuda_kernel!(
    GatherMerklePaths,
    ab_gather_merkle_paths_kernel(
        indexes: *const u32,
        indexes_count: u32,
        values: *const DG,
        log_leaves_count: u32,
        results: *mut DG,
    )
);

#[cfg(test)]
pub(crate) fn gather_merkle_paths_device(
    indexes: &DeviceSlice<u32>,
    values: &DeviceSlice<DG>,
    results: &mut DeviceSlice<DG>,
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
    // A per-coset cap of size 1 means the query path spans the full coset subtree depth.
    assert!(layers_count <= log_leaves_count);
    assert_eq!(indexes.len() * layers_count as usize, results.len());
    assert_eq!(WARP_SIZE % STATE_SIZE as u32, 0);
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(WARP_SIZE / STATE_SIZE as u32, indexes_count);
    let grid_dim = (grid_dim.x, layers_count);
    let block_dim = (STATE_SIZE as u32, block_dim.x);
    let indexes = indexes.as_ptr();
    let values = values.as_ptr();
    let result = results.as_mut_ptr();
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args =
        GatherMerklePathsArguments::new(indexes, indexes_count, values, log_leaves_count, result);
    GatherMerklePathsFunction::default().launch(&config, &args)
}

cuda_kernel!(
    GatherRowsAndMerklePaths,
    ab_gather_rows_and_merkle_paths_kernel(
        indexes: *const u32,
        indexes_count: u32,
        bit_reverse_indexes: bool,
        values: *const BF,
        log_rows_per_leaf: u32,
        cols_count: u32,
        log_total_leaves_count: u32,
        leaf_values: MutPtrAndStride<BF>,
        tree_bottom: *const Digest,
        layers_count: u32,
        merkle_paths: *mut Digest,
    )
);

cuda_kernel!(
    GatherMerklePathsFromRows,
    ab_gather_merkle_paths_from_rows_kernel(
        indexes: *const u32,
        indexes_count: u32,
        bit_reverse_indexes: bool,
        values: *const BF,
        log_rows_per_leaf: u32,
        cols_count: u32,
        log_total_leaves_count: u32,
        tree_bottom: *const Digest,
        layers_count: u32,
        merkle_paths: *mut Digest,
    )
);

#[cfg(test)]
pub(crate) fn gather_merkle_paths_from_rows(
    indexes: &DeviceSlice<u32>,
    bit_reverse_indexes: bool,
    values: &DeviceSlice<BF>,
    log_rows_per_leaf: u32,
    cols_count: usize,
    tree_bottom: &DeviceSlice<Digest>,
    merkle_paths: &mut DeviceSlice<Digest>,
    layers_count: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let indexes_len = indexes.len();
    let values_len = values.len();
    assert_eq!(values_len % cols_count, 0);
    let log_rows_count = (values_len / cols_count).trailing_zeros();
    assert!(indexes_len <= u32::MAX as usize);
    let indexes_count = indexes_len as u32;
    assert!(layers_count >= LOG_WARP_SIZE);
    assert_eq!(indexes_len * layers_count as usize, merkle_paths.len());
    assert!(cols_count <= u32::MAX as usize);
    let cols_count = cols_count as u32;
    let log_total_leaves_count = log_rows_count as u32 - log_rows_per_leaf;
    let config = CudaLaunchConfig::basic(indexes_count, WARP_SIZE, stream);
    let indexes = indexes.as_ptr();
    let values = values.as_ptr();
    let tree_bottom = tree_bottom.as_ptr();
    let merkle_paths = merkle_paths.as_mut_ptr();
    let args = GatherMerklePathsFromRowsArguments::new(
        indexes,
        indexes_count,
        bit_reverse_indexes,
        values,
        log_rows_per_leaf,
        cols_count,
        log_total_leaves_count,
        tree_bottom,
        layers_count,
        merkle_paths,
    );
    GatherMerklePathsFromRowsFunction::default().launch(&config, &args)
}

// ---------------------------------------------------------------------------
// Phase 3 (WHIR-on-device): slab-write gather variants for base-layer queries.
//
// These variants mirror the existing gather kernels' source addressing but
// write into the proof slab's per-query layout that `parse_whir_proof`
// consumes:
// - `query_indices` (`u32`): tree-space index per query.
// - `query_leaves` (`BF`): row-major per query, `[v0c0, v0c1, ..., v(V-1)c(C-1)]`.
// - `query_paths` (`u32`): query-major, `[layer0_d, layer1_d, ..., layer(L-1)_d]`
//   per query, each digest is `STATE_SIZE` u32 words.
// ---------------------------------------------------------------------------

cuda_kernel!(
    QueryIndexToTreeIndex,
    ab_query_index_to_tree_index_kernel(
        d_query_indexes: *const u32,
        d_out: *mut u32,
        indexes_count: u32,
        log_lde_factor: u32,
        coset_tree_size_log2: u32,
    )
);

pub(crate) fn query_index_to_tree_index(
    d_query_indexes: &DeviceSlice<u32>,
    d_out: &mut DeviceSlice<u32>,
    log_lde_factor: u32,
    coset_tree_size_log2: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let n = d_query_indexes.len();
    assert_eq!(d_out.len(), n);
    assert!(n <= u32::MAX as usize);
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE, n as u32);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = QueryIndexToTreeIndexArguments::new(
        d_query_indexes.as_ptr(),
        d_out.as_mut_ptr(),
        n as u32,
        log_lde_factor,
        coset_tree_size_log2,
    );
    QueryIndexToTreeIndexFunction::default().launch(&config, &args)
}

/// Kernel-arg descriptor for `gather_leaves_for_queries`. One entry per
/// base-field oracle: the consolidated cosets backing pointer, the per-oracle
/// column count, and the slab destination pointer. `columns_count == 0`
/// signals an inactive descriptor slot (the kernel skips the whole oracle).
#[repr(C)]
#[derive(Clone, Copy, Default)]
pub(crate) struct OracleGatherDesc {
    /// `const BF*` consolidated cosets backing for this oracle. Coset `c`
    /// occupies elements `c * (columns_count << log_domain_size) ..
    /// (c + 1) * (columns_count << log_domain_size)`; within each coset the
    /// layout is column-major with stride `1 << log_domain_size`.
    pub cosets_ptr: u64,
    /// Number of base-field columns in this oracle. Set to `0` to mark the
    /// slot inactive — the kernel skips all writes for that oracle.
    pub columns_count: u32,
    /// Padding to keep the descriptor 8-byte aligned across language
    /// boundaries.
    pub _pad: u32,
    /// `BF*` slab destination for this oracle. Layout is query-major:
    /// `slab[q * (rows_per_leaf * columns_count) + v * columns_count + col]`.
    pub slab_dst_ptr: u64,
}

cuda_kernel!(
    GatherLeavesForQueries,
    ab_gather_leaves_for_queries_kernel(
        num_oracles: u32,
        desc0: OracleGatherDesc,
        desc1: OracleGatherDesc,
        desc2: OracleGatherDesc,
        log_lde_factor: u32,
        log_domain_size: u32,
        log_rows_per_leaf: u32,
        query_indexes: *const u32,
        indexes_count: u32,
    )
);

/// Phase 3 (WHIR-on-device, GKR consolidation): gather base-field leaves for
/// all LDE cosets and all active oracles in one launch. The kernel handles the
/// coset filter internally and dispatches oracles via `gridDim.z`.
///
/// `descs[i]` for `i >= num_oracles` (and any active slot with
/// `columns_count == 0`) is skipped. `log_domain_size` is shared across all
/// active oracles (asserted upstream — see WHIR fold schedule). `cosets_ptr`
/// and `slab_dst_ptr` must point at valid device memory for the duration of
/// the call; this wrapper does not retain references.
pub(crate) fn gather_leaves_for_queries(
    descs: &[OracleGatherDesc; 3],
    num_oracles: u32,
    log_lde_factor: u32,
    log_domain_size: u32,
    log_rows_per_leaf: u32,
    query_indexes: &DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(
        num_oracles == 1 || num_oracles == 3,
        "gather_leaves_for_queries supports num_oracles in {{1, 3}}, got {num_oracles}"
    );
    assert!(log_domain_size >= log_rows_per_leaf);
    let indexes_len = query_indexes.len();
    assert!(indexes_len <= u32::MAX as usize);
    let indexes_count = indexes_len as u32;
    // Assert unused desc slots are zeroed (defense against caller misuse).
    for i in (num_oracles as usize)..3 {
        assert_eq!(
            descs[i].cosets_ptr, 0,
            "inactive desc slot {i} must have cosets_ptr == 0"
        );
        assert_eq!(
            descs[i].columns_count, 0,
            "inactive desc slot {i} must have columns_count == 0"
        );
        assert_eq!(
            descs[i].slab_dst_ptr, 0,
            "inactive desc slot {i} must have slab_dst_ptr == 0"
        );
    }
    // Max columns_count across the active descriptors. Must be >= 1 (the
    // launch needs a non-empty gridDim.y); zero-column oracles are skipped
    // by the kernel internally, but at least one active oracle must have
    // columns to do useful work.
    let max_cols = (0..num_oracles as usize)
        .map(|i| descs[i].columns_count)
        .max()
        .unwrap_or(0);
    assert!(
        max_cols >= 1,
        "gather_leaves_for_queries requires at least one active oracle with columns_count >= 1"
    );
    let rows_per_leaf = 1u32 << log_rows_per_leaf;
    let (mut grid_dim, block_dim) = if log_rows_per_leaf < LOG_WARP_SIZE {
        get_grid_block_dims_for_threads_count(
            1 << (LOG_WARP_SIZE - log_rows_per_leaf),
            indexes_count,
        )
    } else {
        (indexes_count.into(), 1.into())
    };
    let block_dim = (rows_per_leaf, block_dim.x);
    grid_dim.y = max_cols;
    let grid_dim = (grid_dim.x, grid_dim.y, num_oracles);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GatherLeavesForQueriesArguments::new(
        num_oracles,
        descs[0],
        descs[1],
        descs[2],
        log_lde_factor,
        log_domain_size,
        log_rows_per_leaf,
        query_indexes.as_ptr(),
        indexes_count,
    );
    GatherLeavesForQueriesFunction::default().launch(&config, &args)
}

cuda_kernel!(
    GatherMerklePathsFullForQueries,
    ab_gather_merkle_paths_full_for_queries_kernel(
        query_indexes: *const u32,
        indexes_count: u32,
        log_lde_factor: u32,
        stride_per_coset_in_digests: u32,
        consolidated_tree: *const DG,
        log_leaves_count: u32,
        layers_count: u32,
        slab_dst: *mut u32,
    )
);

/// Phase 3 (WHIR-on-device, Step 3 consolidation): single-launch Full-tree
/// merkle-path gather across all LDE cosets for one oracle. The kernel
/// resolves the per-coset segment internally via `coset = q & lde_mask`.
///
/// The consolidated tree backing stores cosets in NATURAL order: coset `c`
/// occupies `consolidated_tree[c * stride_per_coset_in_digests ..
/// (c + 1) * stride_per_coset_in_digests]`. For Full mode,
/// `stride_per_coset_in_digests = 2 * leaves_count` (= `1 << (log_leaves_count
/// + 1)`), matching `TreesHolder::Full` indexing in
/// `prover/trace/holder/mod.rs`. `log_leaves_count` is per-coset (NOT whole
/// tree); the wrapper derives it from `stride_per_coset_in_digests`.
pub(crate) fn gather_merkle_paths_full_for_queries(
    query_indexes: &DeviceSlice<u32>,
    log_lde_factor: u32,
    stride_per_coset_in_digests: u32,
    consolidated_tree: &DeviceSlice<DG>,
    slab_dst: &mut DeviceSlice<u32>,
    layers_count: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(query_indexes.len() <= u32::MAX as usize);
    let indexes_count = query_indexes.len() as u32;
    // stride_per_coset_in_digests == 2 * leaves_count for Full mode.
    assert!(
        stride_per_coset_in_digests >= 2 && stride_per_coset_in_digests.is_power_of_two(),
        "stride_per_coset_in_digests must be a power of two >= 2 (got {stride_per_coset_in_digests})"
    );
    let log_stride = stride_per_coset_in_digests.trailing_zeros();
    let log_leaves_count = log_stride - 1;
    assert!(layers_count <= log_leaves_count);
    let lde_factor = 1usize << log_lde_factor;
    assert_eq!(
        consolidated_tree.len(),
        lde_factor * stride_per_coset_in_digests as usize,
        "consolidated_tree length must equal lde_factor * stride_per_coset_in_digests"
    );
    // Kernel computes src_index in u32 (coset_offset + layer_offset + ...).
    // Guard against silent overflow.
    let total_u32_words =
        (lde_factor as u64) * (stride_per_coset_in_digests as u64) * (STATE_SIZE as u64);
    assert!(
        total_u32_words <= u32::MAX as u64,
        "consolidated tree u32-word footprint ({total_u32_words}) exceeds u32::MAX; kernel would overflow"
    );
    assert_eq!(
        slab_dst.len(),
        query_indexes.len() * layers_count as usize * STATE_SIZE
    );
    assert_eq!(WARP_SIZE % STATE_SIZE as u32, 0);
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(WARP_SIZE / STATE_SIZE as u32, indexes_count);
    let grid_dim = (grid_dim.x, layers_count);
    let block_dim = (STATE_SIZE as u32, block_dim.x);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GatherMerklePathsFullForQueriesArguments::new(
        query_indexes.as_ptr(),
        indexes_count,
        log_lde_factor,
        stride_per_coset_in_digests,
        consolidated_tree.as_ptr(),
        log_leaves_count,
        layers_count,
        slab_dst.as_mut_ptr(),
    );
    GatherMerklePathsFullForQueriesFunction::default().launch(&config, &args)
}

/// Kernel-arg descriptor for `gather_merkle_paths_partial_for_queries`. One
/// entry per base-field oracle: the consolidated cosets backing pointer (for
/// on-the-fly bottom-layer hashing), the consolidated partial-tree backing
/// pointer (for upper-layer walks), the per-oracle column count, and the slab
/// destination pointer. `columns_count == 0` signals an inactive descriptor
/// slot (the kernel skips the whole oracle).
#[repr(C)]
#[derive(Clone, Copy, Default)]
pub(crate) struct OraclePartialPathDesc {
    /// `const BF*` consolidated cosets backing for this oracle. Coset `c`
    /// occupies elements `c * (columns_count << log_domain_size) ..
    /// (c + 1) * (columns_count << log_domain_size)`; within each coset the
    /// layout is column-major with stride `1 << log_domain_size`.
    pub cosets_ptr: u64,
    /// `const u32*` consolidated partial-tree backing for this oracle.
    /// Coset `c` occupies digest words `c * stride_per_coset_in_digests *
    /// STATE_SIZE .. (c + 1) * stride_per_coset_in_digests * STATE_SIZE`.
    pub partial_tree_ptr: u64,
    /// Number of base-field columns in this oracle. Set to `0` to mark the
    /// slot inactive — the kernel skips all writes for that oracle.
    pub columns_count: u32,
    /// Padding to keep the descriptor 8-byte aligned across language
    /// boundaries.
    pub _pad: u32,
    /// `u32*` slab destination for this oracle. Layout is query-major:
    /// `slab[q * layers_count * STATE_SIZE + layer * STATE_SIZE + word]`.
    pub slab_dst_ptr: u64,
}

cuda_kernel!(
    GatherMerklePathsPartialForQueries,
    ab_gather_merkle_paths_partial_for_queries_kernel(
        num_oracles: u32,
        desc0: OraclePartialPathDesc,
        desc1: OraclePartialPathDesc,
        desc2: OraclePartialPathDesc,
        log_lde_factor: u32,
        log_rows_per_leaf: u32,
        log_total_leaves_count: u32,
        stride_per_coset_in_digests: u32,
        layers_count: u32,
        query_indexes: *const u32,
        indexes_count: u32,
    )
);

/// Phase 3 (WHIR-on-device, GKR consolidation): single-launch Partial-tree
/// merkle-path gather across all LDE cosets and all active oracles.
///
/// For each query, the kernel hashes the first `LOG_WARP_SIZE` layers on the
/// fly from the per-oracle BF cosets backing (via warp-shuffle compression),
/// then walks the upper layers in the per-oracle partial-tree backing.
///
/// `descs[i]` for `i >= num_oracles` (and any active slot with
/// `columns_count == 0`) is skipped. `log_rows_per_leaf` and
/// `log_total_leaves_count` are shared across all active oracles (asserted
/// upstream — see WHIR fold schedule). The `cosets_ptr`, `partial_tree_ptr`,
/// and `slab_dst_ptr` fields must point at valid device memory for the
/// duration of the call; this wrapper does not retain references.
pub(crate) fn gather_merkle_paths_partial_for_queries(
    descs: &[OraclePartialPathDesc; 3],
    num_oracles: u32,
    log_lde_factor: u32,
    log_rows_per_leaf: u32,
    log_total_leaves_count: u32,
    stride_per_coset_in_digests: u32,
    layers_count: u32,
    query_indexes: &DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(
        num_oracles == 1 || num_oracles == 3,
        "gather_merkle_paths_partial_for_queries supports num_oracles in {{1, 3}}, got {num_oracles}"
    );
    assert!(layers_count >= LOG_WARP_SIZE);
    assert!(log_total_leaves_count >= LOG_WARP_SIZE);
    let indexes_len = query_indexes.len();
    assert!(indexes_len <= u32::MAX as usize);
    let indexes_count = indexes_len as u32;
    // Per-coset partial-tree length in digests for `TreesHolder::Partial`:
    // `1 << (log_total_leaves_count + 1 - LOG_WARP_SIZE)`.
    let expected_stride = 1u32 << (log_total_leaves_count + 1 - LOG_WARP_SIZE);
    assert_eq!(
        stride_per_coset_in_digests, expected_stride,
        "stride_per_coset_in_digests ({stride_per_coset_in_digests}) must equal 1 << (log_total_leaves_count + 1 - LOG_WARP_SIZE) ({expected_stride})"
    );
    // Assert unused desc slots are zeroed (defense against caller misuse).
    for i in (num_oracles as usize)..3 {
        assert_eq!(
            descs[i].cosets_ptr, 0,
            "inactive desc slot {i} must have cosets_ptr == 0"
        );
        assert_eq!(
            descs[i].partial_tree_ptr, 0,
            "inactive desc slot {i} must have partial_tree_ptr == 0"
        );
        assert_eq!(
            descs[i].columns_count, 0,
            "inactive desc slot {i} must have columns_count == 0"
        );
        assert_eq!(
            descs[i].slab_dst_ptr, 0,
            "inactive desc slot {i} must have slab_dst_ptr == 0"
        );
    }
    let grid_dim = (indexes_count, num_oracles);
    let block_dim = WARP_SIZE;
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GatherMerklePathsPartialForQueriesArguments::new(
        num_oracles,
        descs[0],
        descs[1],
        descs[2],
        log_lde_factor,
        log_rows_per_leaf,
        log_total_leaves_count,
        stride_per_coset_in_digests,
        layers_count,
        query_indexes.as_ptr(),
        indexes_count,
    );
    GatherMerklePathsPartialForQueriesFunction::default().launch(&config, &args)
}

pub(crate) fn merkle_tree_cap(
    values: &DeviceSlice<DG>,
    log_tree_cap_size: u32,
) -> &DeviceSlice<DG> {
    let values_len = values.len();
    assert_ne!(values_len, 0);
    assert!(values_len.is_power_of_two());
    let log_values_len = values_len.trailing_zeros();
    assert!(log_values_len > log_tree_cap_size);
    let offset = values_len - (1 << (log_tree_cap_size + 1));
    &values[offset..offset + (1 << log_tree_cap_size)]
}

cuda_kernel!(Blake2SPow, ab_blake2s_pow_kernel(seed: *const u32, bits_count: u32, max_nonce: u64, result: *mut u64));

cuda_kernel!(
    GatherTreeCaps,
    ab_gather_tree_caps_kernel(
        src_ptrs: *const u64,
        dst: *mut u32,
        cap_words_per_coset: u32,
        coset_count: u32
    )
);

/// Maximum coset count the inline `gather_tree_caps_inline` kernel-arg
/// descriptor can hold. Sized for headroom — production lde_factor is
/// typically ≤ 4.
pub(crate) const GKR_GATHER_TREE_CAPS_MAX_COSETS: usize = 32;

/// Kernel-arg descriptor for `gather_tree_caps_inline`. Consolidated form:
/// a single base pointer plus per-coset stride lets the kernel gather every
/// per-coset cap region from one contiguous tree backing. The kernel folds
/// the natural→bit-reversed coset reindex (`stage1_pos = bitreverse(
/// natural_idx, log_lde_factor)`) so the destination layout matches the
/// legacy stage1 ordering.
#[repr(C)]
#[derive(Clone, Copy, Default)]
pub(crate) struct GpuGatherTreeCapsDesc {
    /// Number of source cosets to gather (= `1 << log_lde_factor`).
    pub coset_count: u32,
    /// Number of u32 words gathered per source coset.
    pub cap_words_per_coset: u32,
    /// Stride between per-coset segments in the source backing, in u32 words.
    /// The kernel reads `base_ptr + natural_idx * stride_per_coset_in_u32_words`
    /// for coset `natural_idx`.
    pub stride_per_coset_in_u32_words: u32,
    /// `log2(coset_count)`. Used to bit-reverse `natural_idx` into the
    /// destination cap-region slot.
    pub log_lde_factor: u32,
    /// Source backing base pointer treated as `const u32 *`.
    pub base_ptr: u64,
}

const _: () = {
    assert!(
        std::mem::size_of::<GpuGatherTreeCapsDesc>() <= 32 * 1024,
        "GpuGatherTreeCapsDesc must fit under the 32 KB inline kernel-arg ceiling"
    );
};

cuda_kernel!(
    GatherTreeCapsInline,
    ab_gather_tree_caps_inline_kernel(desc: GpuGatherTreeCapsDesc, dst: *mut u32)
);

/// Maximum source addresses the `gather_e_addresses` kernel-arg descriptor
/// can hold. See [`crate::prover::gkr::gkr_address_audit_helpers::GKR_GATHER_MAX_ADDRESSES`]
/// for the rationale; the audit panics if any future circuit exceeds this.
pub(crate) const GKR_GATHER_MAX_ADDRESSES: usize = 1280;

/// Kernel-arg descriptor for `gather_e_addresses`. Inline form: passed by
/// value as `__grid_constant__` data.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuGatherEAddressesDesc {
    /// Number of populated entries in `src_ptrs`.
    pub num_addresses: u32,
    /// Number of E4 elements gathered per source address.
    pub elements_per_addr: u32,
    /// Source device pointers (one per address). Each is treated as a
    /// `const u32 *` referring to `elements_per_addr * 4` u32 words.
    pub src_ptrs: [u64; GKR_GATHER_MAX_ADDRESSES],
}

impl Default for GpuGatherEAddressesDesc {
    fn default() -> Self {
        Self {
            num_addresses: 0,
            elements_per_addr: 0,
            src_ptrs: [0u64; GKR_GATHER_MAX_ADDRESSES],
        }
    }
}

const _: () = {
    assert!(
        std::mem::size_of::<GpuGatherEAddressesDesc>() <= 32 * 1024,
        "GpuGatherEAddressesDesc must fit under the 32 KB inline kernel-arg ceiling"
    );
};

cuda_kernel!(
    GatherEAddresses,
    ab_gather_e_addresses_kernel(desc: GpuGatherEAddressesDesc, dst: *mut u32)
);

cuda_kernel!(
    TranscriptCommitInitial,
    ab_transcript_commit_initial_kernel(seed_out: *mut u32, input: *const u32, input_len: u32)
);

/// Maximum number of input chunks the chunked transcript-commit kernel-arg
/// descriptor can hold. The pre-WHIR transcript pack feeds 5 chunks
/// (canonical-top-bits + external_challenges + setup cap + memory cap +
/// witness cap); 8 leaves headroom without any meaningful kernel-arg cost.
pub(crate) const GKR_CHUNKED_COMMIT_MAX_CHUNKS: usize = 8;

/// Kernel-arg descriptor for `transcript_commit_initial_chunked`. Streams
/// Blake2s over the logical concatenation of `num_chunks` device-resident
/// u32 buffers in one kernel launch (no host-side concat staging).
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuChunkedInputDesc {
    /// Number of populated entries in `src_ptrs` and `chunk_lens`.
    pub num_chunks: u32,
    /// Padding to keep the `u64` array 8-byte aligned across language
    /// boundaries.
    pub _pad: u32,
    /// Source device pointers (one per chunk). Each is treated as a
    /// `const u32 *` of length `chunk_lens[i]`.
    pub src_ptrs: [u64; GKR_CHUNKED_COMMIT_MAX_CHUNKS],
    /// Per-chunk u32 word counts.
    pub chunk_lens: [u32; GKR_CHUNKED_COMMIT_MAX_CHUNKS],
}

impl Default for GpuChunkedInputDesc {
    fn default() -> Self {
        Self {
            num_chunks: 0,
            _pad: 0,
            src_ptrs: [0u64; GKR_CHUNKED_COMMIT_MAX_CHUNKS],
            chunk_lens: [0u32; GKR_CHUNKED_COMMIT_MAX_CHUNKS],
        }
    }
}

const _: () = {
    assert!(
        std::mem::size_of::<GpuChunkedInputDesc>() <= 32 * 1024,
        "GpuChunkedInputDesc must fit under the 32 KB inline kernel-arg ceiling"
    );
};

cuda_kernel!(
    TranscriptCommitInitialChunked,
    ab_transcript_commit_initial_chunked_kernel(desc: GpuChunkedInputDesc, seed_out: *mut u32)
);

cuda_kernel!(
    TranscriptCommit,
    ab_transcript_commit_kernel(seed_io: *mut u32, input: *const u32, input_len: u32)
);

cuda_kernel!(
    TranscriptSqueeze,
    ab_transcript_squeeze_kernel(seed_io: *mut u32, output: *mut u32, output_len: u32)
);

cuda_kernel!(
    TranscriptSqueezeE4,
    ab_transcript_squeeze_e4_kernel(seed_io: *mut u32, output_e4: *mut E4, count: u32)
);

/// Gather `coset_count` cap regions, each `cap_words_per_coset` u32 words
/// long, from the consolidated tree backing pointed to by `base_ptr` into
/// `dst[0..coset_count * cap_words_per_coset]`. Per-coset source segments
/// are at stride `stride_per_coset_in_u32_words`. The kernel writes coset
/// `natural_idx` to `dst[bitreverse(natural_idx, log_lde_factor) * cap_words..]`
/// so the destination layout matches the legacy stage1 ordering used by
/// `read_per_coset_caps_synchronously`.
///
/// Inline form of `gather_tree_caps`: the descriptor rides as kernel-arg
/// data (`__grid_constant__`), so callers (e.g. `TraceHolder::commit_all`)
/// avoid an H2D for the source pointer table.
pub(crate) fn gather_tree_caps_inline(
    base_ptr: *const u32,
    coset_count: u32,
    cap_words_per_coset: u32,
    stride_per_coset_in_u32_words: u32,
    log_lde_factor: u32,
    dst: &mut DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(coset_count > 0);
    assert!(cap_words_per_coset > 0);
    assert!(stride_per_coset_in_u32_words >= cap_words_per_coset);
    assert_eq!(coset_count, 1u32 << log_lde_factor);
    assert!(
        (coset_count as usize) <= GKR_GATHER_TREE_CAPS_MAX_COSETS,
        "gather_tree_caps descriptor has {} cosets; exceeds GKR_GATHER_TREE_CAPS_MAX_COSETS = {}. \
         Raise the constant in ops/blake2s.rs (and the matching native constant) if a \
         future workload needs more.",
        coset_count,
        GKR_GATHER_TREE_CAPS_MAX_COSETS,
    );
    assert_eq!(
        dst.len(),
        (coset_count as usize) * (cap_words_per_coset as usize),
        "gather_tree_caps_inline dst length must match coset_count * cap_words_per_coset",
    );
    let desc = GpuGatherTreeCapsDesc {
        coset_count,
        cap_words_per_coset,
        stride_per_coset_in_u32_words,
        log_lde_factor,
        base_ptr: base_ptr as u64,
    };
    let threads_per_block = std::cmp::min(cap_words_per_coset, 256u32);
    let config = CudaLaunchConfig::basic(coset_count, threads_per_block, stream);
    let args = GatherTreeCapsInlineArguments::new(desc, dst.as_mut_ptr());
    GatherTreeCapsInlineFunction::default().launch(&config, &args)
}

/// Gather `src_ptrs.len()` E4 evaluation regions (each `elements_per_addr`
/// E4 values long) from the device pointers in `src_ptrs` into the contiguous
/// `dst[0..src_ptrs.len()*elements_per_addr]`. The caller orders `src_ptrs`
/// (host slice) to match the desired output address sequence (typically the
/// BTreeMap key order of the per-layer transcript inputs). The pointer table
/// is passed by value as kernel-arg data; production callers must respect
/// `GKR_GATHER_MAX_ADDRESSES`.
pub(crate) fn gather_e_addresses(
    src_ptrs: &[u64],
    dst: &mut DeviceSlice<E4>,
    elements_per_addr: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let num_addresses = src_ptrs.len();
    assert!(num_addresses > 0);
    assert!(elements_per_addr > 0);
    assert!(
        num_addresses <= GKR_GATHER_MAX_ADDRESSES,
        "gather descriptor has {} addresses; exceeds GKR_GATHER_MAX_ADDRESSES = {}. \
         Raise the constant in gkr_address_audit.rs after re-running the audit.",
        num_addresses,
        GKR_GATHER_MAX_ADDRESSES,
    );
    assert_eq!(
        dst.len(),
        num_addresses * elements_per_addr as usize,
        "gather_e_addresses dst length must match num_addresses * elements_per_addr",
    );
    let mut desc = GpuGatherEAddressesDesc::default();
    desc.num_addresses = num_addresses as u32;
    desc.elements_per_addr = elements_per_addr;
    desc.src_ptrs[..num_addresses].copy_from_slice(src_ptrs);
    // Each E4 = 4 u32 words; cap thread count to a reasonable warp multiple.
    let words_per_addr = elements_per_addr.saturating_mul(4);
    let threads_per_block = std::cmp::min(words_per_addr, 64u32);
    let config = CudaLaunchConfig::basic(num_addresses as u32, threads_per_block, stream);
    let args = GatherEAddressesArguments::new(desc, dst.as_mut_ptr() as *mut u32);
    GatherEAddressesFunction::default().launch(&config, &args)
}

/// Chunked variant of [`transcript_commit_initial`]: computes
/// `seed = Blake2s(chunk_0 || chunk_1 || ... || chunk_{N-1})` from the IV without
/// requiring the host to first concatenate the chunks into a single contiguous
/// device buffer. `seed` must be exactly `STATE_SIZE` u32 words; written.
/// `chunks` are `(device pointer, u32 length)` pairs covering the logical
/// transcript prefix in order. Producing the same digest as the single-buffer
/// kernel is covered by `transcript_commit_initial_chunked_parity_*`.
pub(crate) fn transcript_commit_initial_chunked(
    seed: &mut DeviceSlice<u32>,
    chunks: &[(*const u32, u32)],
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(seed.len(), STATE_SIZE);
    let num_chunks = chunks.len();
    assert!(
        num_chunks <= GKR_CHUNKED_COMMIT_MAX_CHUNKS,
        "transcript_commit_initial_chunked: {num_chunks} chunks exceeds GKR_CHUNKED_COMMIT_MAX_CHUNKS = {GKR_CHUNKED_COMMIT_MAX_CHUNKS}",
    );
    let mut desc = GpuChunkedInputDesc::default();
    desc.num_chunks = num_chunks as u32;
    for (i, (ptr, len)) in chunks.iter().enumerate() {
        desc.src_ptrs[i] = *ptr as u64;
        desc.chunk_lens[i] = *len;
    }
    let seed_ptr = seed.as_mut_ptr();
    let config = CudaLaunchConfig::basic(1u32, 1u32, stream);
    let args = TranscriptCommitInitialChunkedArguments::new(desc, seed_ptr);
    TranscriptCommitInitialChunkedFunction::default().launch(&config, &args)
}

/// Device-side `commit_with_seed`: computes `new_seed = Blake2s(old_seed || input)`.
///
/// `seed` must be exactly `STATE_SIZE` u32 words. Updated in place.
/// `input` contains the field-element data to absorb.
pub(crate) fn transcript_commit(
    seed: &mut DeviceSlice<u32>,
    input: &DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(seed.len(), STATE_SIZE);
    let seed_ptr = seed.as_mut_ptr();
    let input_ptr = input.as_ptr();
    let input_len = input.len() as u32;
    let config = CudaLaunchConfig::basic(1u32, 1u32, stream);
    let args = TranscriptCommitArguments::new(seed_ptr, input_ptr, input_len);
    TranscriptCommitFunction::default().launch(&config, &args)
}

/// Device-side `draw_randomness`: expands the seed into `output.len()` u32 words.
///
/// The first `STATE_SIZE` words of `output` are the seed itself (no hashing).
/// If more than `STATE_SIZE` words are requested, additional chunks are produced
/// by iteratively hashing the seed. `seed` is updated in place when
/// `output.len() > STATE_SIZE`.
///
/// `output.len()` must be a positive multiple of `STATE_SIZE`.
pub(crate) fn transcript_squeeze(
    seed: &mut DeviceSlice<u32>,
    output: &mut DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(seed.len(), STATE_SIZE);
    let output_len = output.len();
    assert!(output_len > 0);
    assert_eq!(output_len % STATE_SIZE, 0);
    let seed_ptr = seed.as_mut_ptr();
    let output_ptr = output.as_mut_ptr();
    let config = CudaLaunchConfig::basic(1u32, 1u32, stream);
    let args = TranscriptSqueezeArguments::new(seed_ptr, output_ptr, output_len as u32);
    TranscriptSqueezeFunction::default().launch(&config, &args)
}

/// Device-side `draw_random_field_els::<BF, E4>(seed, count)`. Produces `count` E4 challenges
/// in Montgomery form by squeezing raw u32 words from `seed` and applying per-limb
/// `from_raw_repr_with_reduction`. `seed` is updated in place to the post-draw state.
pub(crate) fn transcript_squeeze_e4(
    seed: &mut DeviceSlice<u32>,
    output: &mut DeviceSlice<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(seed.len(), STATE_SIZE);
    let count = output.len();
    assert!(count > 0);
    assert!(count <= u32::MAX as usize);
    let seed_ptr = seed.as_mut_ptr();
    let output_ptr = output.as_mut_ptr();
    let config = CudaLaunchConfig::basic(1u32, 1u32, stream);
    let args = TranscriptSqueezeE4Arguments::new(seed_ptr, output_ptr, count as u32);
    TranscriptSqueezeE4Function::default().launch(&config, &args)
}

pub(crate) fn blake2s_pow(
    seed: &DeviceSlice<u32>,
    bits_count: u32,
    max_nonce: u64,
    result: &mut DeviceVariable<u64>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(seed.len(), STATE_SIZE);
    unsafe {
        memory_set_async(result.transmute_mut(), 0xff, stream)?;
    }
    const BLOCK_SIZE: u32 = WARP_SIZE * 4;
    let device_id = get_device()?;
    let mpc = device_get_attribute(CudaDeviceAttr::MultiProcessorCount, device_id)?;
    let kernel_function = Blake2SPowFunction::default();
    let max_blocks = max_active_blocks_per_multiprocessor(&kernel_function, BLOCK_SIZE as i32, 0)?;
    let num_blocks = (mpc * max_blocks) as u32;
    let config = CudaLaunchConfig::basic(num_blocks, BLOCK_SIZE, stream);
    let seed = seed.as_ptr();
    let result = result.as_mut_ptr();
    let args = Blake2SPowArguments {
        seed,
        bits_count,
        max_nonce,
        result,
    };
    kernel_function.launch(&config, &args)
}
mod gkr_ops;

pub(crate) use gkr_ops::{
    assemble_query_indexes, backward_new_claims_linear, backward_new_claims_two_var,
    backward_sumcheck_round_update, build_combined_claim, whir_fold_round_update,
};

#[cfg(test)]
mod tests;
