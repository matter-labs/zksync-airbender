use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::device_structures::{DeviceMatrixChunkImpl, DeviceMatrixChunkMutImpl};
use gpu_core::primitives::device_structures::{MutPtrAndStride, PtrAndStride};
use gpu_core::primitives::field::BF;
#[cfg(test)]
use gpu_core::primitives::field::E4;
use gpu_core::primitives::utils::LOG_WARP_SIZE;
use gpu_core::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
use gpu_ops::bit_reverse::bit_reverse_in_place;

pub const STATE_SIZE: usize = 8;

pub type Digest = [u32; STATE_SIZE];

pub type DG = Digest;

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

pub fn launch_leaves_kernel(
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

pub fn build_merkle_tree_leaves(
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
pub fn launch_leaves_kernel_multi_coset(
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

cuda_kernel!(
    LeavesFromNttMultiCoset,
    ab_blake2s_leaves_from_ntt_multi_coset_kernel(
        ntt_output: *const BF,
        results: *mut DG,
        log_values_per_leaf: u32,
        src_cols_per_coset: u32,
        log_lde_factor: u32,
        coset_index_base: u32,
        per_coset_count: u32,
        log_per_coset_count: u32,
        trace_len: u32,
        count: u32,
    )
);

/// Hashes `cosets_in_tile * per_coset_leaves_count` WHIR leaves in one launch,
/// reading the natural multi-coset NTT output and writing digests at the
/// flat-tree leaf positions today's `pack_rows_for_whir_leaves_multi_coset` +
/// `launch_leaves_kernel_multi_coset` pipeline produces. The output tree
/// backing layout is unchanged: digest for natural coset `C`, leaf `i` lives
/// at `results[(bitreverse(C, log_lde_factor) * per_coset_leaves_count + i) *
/// STATE_SIZE]`.
///
/// `ntt_output` logical shape: rows = `trace_len`, cols =
/// `cosets_in_tile * src_cols_per_coset`, coset-major outer (`col /
/// src_cols_per_coset = coset_in_tile`), column-major within each coset. The
/// total backing length must be at least `cosets_in_tile * trace_len *
/// src_cols_per_coset` BFs.
pub fn launch_leaves_kernel_from_ntt_multi_coset(
    ntt_output: &DeviceSlice<BF>,
    results: &mut DeviceSlice<DG>,
    log_values_per_leaf: u32,
    src_cols_per_coset: u32,
    log_lde_factor: u32,
    coset_index_base: u32,
    cosets_in_tile: usize,
    per_coset_leaves_count: usize,
    trace_len: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(cosets_in_tile >= 1);
    assert!(
        per_coset_leaves_count.is_power_of_two(),
        "per_coset_leaves_count must be a power of two (got {per_coset_leaves_count})"
    );
    assert!(src_cols_per_coset >= 1);
    assert!(trace_len.is_power_of_two());
    assert!(trace_len >= 1 << log_values_per_leaf);
    let log_per_coset_count = per_coset_leaves_count.trailing_zeros();
    assert_eq!(
        1usize << log_per_coset_count,
        trace_len as usize >> log_values_per_leaf,
        "per_coset_leaves_count must equal trace_len / values_per_leaf"
    );
    let total_count = per_coset_leaves_count
        .checked_mul(cosets_in_tile)
        .expect("leaves total count overflow");
    assert!(total_count <= u32::MAX as usize);
    let required_ntt_bf = (trace_len as usize) * (src_cols_per_coset as usize) * cosets_in_tile;
    assert!(ntt_output.len() >= required_ntt_bf);
    assert!(results.len() >= total_count);
    assert!(coset_index_base as usize + cosets_in_tile <= 1usize << log_lde_factor);
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(WARP_SIZE * 4, total_count as u32);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = LeavesFromNttMultiCosetArguments::new(
        ntt_output.as_ptr(),
        results.as_mut_ptr(),
        log_values_per_leaf,
        src_cols_per_coset,
        log_lde_factor,
        coset_index_base,
        per_coset_leaves_count as u32,
        log_per_coset_count,
        trace_len,
        total_count as u32,
    );
    LeavesFromNttMultiCosetFunction::default().launch(&config, &args)
}

cuda_kernel!(Nodes, ab_blake2s_nodes_kernel(values: *const DG, results: *mut DG, count: u32,));

pub fn launch_nodes_kernel(
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

pub fn build_merkle_tree_nodes(
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
pub fn build_merkle_tree_nodes_multi_coset(
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
pub fn build_merkle_tree_nodes_multi_coset_from_external_src(
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
pub fn build_merkle_tree_multi_coset(
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

pub fn build_merkle_tree(
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

#[doc(hidden)]
pub fn gather_leaf_rows(
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

#[doc(hidden)]
pub fn gather_merkle_paths_device(
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

#[doc(hidden)]
pub fn gather_merkle_paths_from_rows(
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

pub fn query_index_to_tree_index(
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

pub fn merkle_tree_cap(values: &DeviceSlice<DG>, log_tree_cap_size: u32) -> &DeviceSlice<DG> {
    let values_len = values.len();
    assert_ne!(values_len, 0);
    assert!(values_len.is_power_of_two());
    let log_values_len = values_len.trailing_zeros();
    assert!(log_values_len > log_tree_cap_size);
    let offset = values_len - (1 << (log_tree_cap_size + 1));
    &values[offset..offset + (1 << log_tree_cap_size)]
}
mod gather;
mod transcript;

pub use gather::*;
pub use transcript::*;

#[cfg(test)]
mod tests;
