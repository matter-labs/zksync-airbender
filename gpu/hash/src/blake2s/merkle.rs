//! Blake2s Merkle-tree construction: node (2→1 digest) hashing and the
//! single-launch-per-layer multi-coset tree builders used by the prover's
//! commit paths.

use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::field::BF;
use gpu_core::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};

use super::hash::{hash_leaves, hash_leaves_multi_coset};
use super::{checked_u32, Digest};

cuda_kernel!(
    Nodes,
    ab_blake2s_nodes_kernel(values: *const Digest, results: *mut Digest, count: u32)
);

pub(super) fn hash_nodes(
    values: &DeviceSlice<Digest>,
    results: &mut DeviceSlice<Digest>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let values_len = values.len();
    let results_len = results.len();
    assert_eq!(values_len, results_len * 2);
    let values = values.as_ptr();
    let results = results.as_mut_ptr();
    let count = checked_u32(results_len);
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = NodesArguments::new(values, results, count);
    NodesFunction::default().launch(&config, &args)
}

/// Hash `layers_count` node layers up from the `values` layer, writing each
/// successive (halving) layer contiguously into `results`.
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
        hash_nodes(values, nodes, stream)?;
        build_merkle_tree_nodes(nodes, nodes_remaining, layers_count - 1, stream)
    }
}

cuda_kernel!(
    NodesMultiCoset,
    ab_blake2s_nodes_multi_coset_kernel(
        values: *const Digest,
        results: *mut Digest,
        log_per_coset_count: u32,
        per_coset_values_stride_digests: u32,
        per_coset_results_stride_digests: u32,
        count: u32,
    )
);

/// Launch the multi-coset nodes kernel against a single backing slab using
/// per-coset src/dst offsets (in digests, relative to each coset's
/// `per_coset_stride_digests` slab). Callers express a virtual src/dst view
/// inside the per-coset slabs without re-slicing the backing buffer (which
/// would violate Rust aliasing rules when src and dst sit in the same
/// allocation).
fn launch_nodes_kernel_multi_coset_at_offsets(
    backing: &mut DeviceSlice<Digest>,
    cosets_in_tile: usize,
    per_coset_stride_digests: usize,
    src_offset_in_coset: usize,
    dst_offset_in_coset: usize,
    output_per_coset_count: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    // Per-coset containment: each coset's read/write window must fit inside
    // its own slab — the aggregate end checks below cannot see a window that
    // spills into the next coset's slab.
    let src_window_end = src_offset_in_coset
        .checked_add(output_per_coset_count * 2)
        .expect("src window overflow");
    let dst_window_end = dst_offset_in_coset
        .checked_add(output_per_coset_count)
        .expect("dst window overflow");
    assert!(src_window_end <= per_coset_stride_digests);
    assert!(dst_window_end <= per_coset_stride_digests);
    // Same-backing launch: the write window must not overlap the read window
    // within a slab (containment above already separates distinct cosets).
    assert!(
        dst_offset_in_coset >= src_window_end || src_offset_in_coset >= dst_window_end,
        "src/dst windows overlap within the per-coset slab"
    );
    let last_src_end = (cosets_in_tile - 1)
        .checked_mul(per_coset_stride_digests)
        .and_then(|x| x.checked_add(src_window_end))
        .expect("src extent overflow");
    let last_dst_end = (cosets_in_tile - 1)
        .checked_mul(per_coset_stride_digests)
        .and_then(|x| x.checked_add(dst_window_end))
        .expect("dst extent overflow");
    assert!(backing.len() >= last_src_end);
    assert!(backing.len() >= last_dst_end);
    // SAFETY: both src and dst pointers derive from a single &mut to
    // `backing`, offset per coset by the same stride. The containment asserts
    // above confine every coset's read window and write window to its own
    // slab, and the disjointness assert proves the two windows never overlap
    // within a slab — so no digest is read and written concurrently. The
    // shared borrow is cast away only to construct the kernel arg.
    let base = backing.as_mut_ptr();
    let src_ptr = unsafe { base.add(src_offset_in_coset) } as *const Digest;
    let dst_ptr = unsafe { base.add(dst_offset_in_coset) };
    assert!(
        output_per_coset_count.is_power_of_two(),
        "output_per_coset_count must be a power of two (got {output_per_coset_count})"
    );
    let total_count = checked_u32(
        output_per_coset_count
            .checked_mul(cosets_in_tile)
            .expect("nodes total count overflow"),
    );
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, total_count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = NodesMultiCosetArguments::new(
        src_ptr,
        dst_ptr,
        output_per_coset_count.trailing_zeros(),
        checked_u32(per_coset_stride_digests),
        checked_u32(per_coset_stride_digests),
        total_count,
    );
    NodesMultiCosetFunction::default().launch(&config, &args)
}

/// Iteratively hash up `layers_count` Merkle layers across `cosets_in_tile`
/// trees laid out contiguously in `tree_backing` with stride
/// `per_coset_tree_stride_digests` per tree. The first layer reads from
/// `initial_src_offset_in_coset` (typically the leaves layer at offset 0) and
/// writes to `initial_src_offset_in_coset + initial_src_layer_count_per_coset`.
fn build_merkle_tree_nodes_multi_coset(
    tree_backing: &mut DeviceSlice<Digest>,
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

cuda_kernel!(
    PartialTreeMultiCoset,
    ab_blake2s_partial_tree_multi_coset_kernel(
        values: *const BF,
        tree_backing: *mut Digest,
        log_rows_per_hash: u32,
        cols_count: u32,
        log_per_coset_count: u32,
        per_coset_values_stride_bf: u32,
        per_coset_tree_stride_digests: u32,
        count: u32,
    )
);

/// `values` is exact `[coset][column][row]` storage without padding. Each tree
/// slab has `leaves / 16` digests and is filled `[level 5 | level 6 | ...]`.
pub fn build_partial_merkle_tree_multi_coset(
    values: &DeviceSlice<BF>,
    tree_backing: &mut DeviceSlice<Digest>,
    log_rows_per_hash: u32,
    layers_count: u32,
    cosets_in_tile: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    const THREADS_PER_BLOCK: u32 = 256;
    const LEAVES_PER_BLOCK: u32 = 512;
    const REDUCTION_LAYERS: u32 = WARP_SIZE.trailing_zeros();

    assert_ne!(layers_count, 0);
    assert!(cosets_in_tile >= 1);
    assert!(log_rows_per_hash < 32);
    assert_eq!(tree_backing.len() % cosets_in_tile, 0);
    let per_coset_tree_stride_digests = tree_backing.len() / cosets_in_tile;
    assert!(per_coset_tree_stride_digests.is_power_of_two());
    let per_coset_leaves_count = per_coset_tree_stride_digests << (REDUCTION_LAYERS - 1);
    assert!(layers_count <= per_coset_tree_stride_digests.trailing_zeros());
    let boundary_roots_per_coset = per_coset_leaves_count >> REDUCTION_LAYERS;
    assert_eq!(values.len() % cosets_in_tile, 0);
    let per_coset_values_stride_bf = values.len() / cosets_in_tile;
    let rows_per_coset = per_coset_leaves_count
        .checked_mul(1usize << log_rows_per_hash)
        .expect("partial tree rows count overflow");
    assert_eq!(per_coset_values_stride_bf % rows_per_coset, 0);
    let cols_count = per_coset_values_stride_bf / rows_per_coset;

    let total_leaves = checked_u32(
        per_coset_leaves_count
            .checked_mul(cosets_in_tile)
            .expect("partial tree leaves count overflow"),
    );
    let mut config = CudaLaunchConfig::basic(
        total_leaves.div_ceil(LEAVES_PER_BLOCK),
        THREADS_PER_BLOCK,
        stream,
    );
    config.dynamic_smem_bytes = LEAVES_PER_BLOCK as usize * core::mem::size_of::<Digest>();
    let args = PartialTreeMultiCosetArguments::new(
        values.as_ptr(),
        tree_backing.as_mut_ptr(),
        log_rows_per_hash,
        checked_u32(cols_count),
        per_coset_leaves_count.trailing_zeros(),
        checked_u32(per_coset_values_stride_bf),
        checked_u32(per_coset_tree_stride_digests),
        total_leaves,
    );
    PartialTreeMultiCosetFunction::default().launch(&config, &args)?;
    build_merkle_tree_nodes_multi_coset(
        tree_backing,
        layers_count - 1,
        cosets_in_tile,
        per_coset_tree_stride_digests,
        0,
        boundary_roots_per_coset,
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
    tree_backing: &mut DeviceSlice<Digest>,
    log_rows_per_hash: u32,
    layers_count: u32,
    cosets_in_tile: usize,
    per_coset_leaves_count: usize,
    per_coset_values_stride_bf: usize,
    per_coset_tree_stride_digests: usize,
    cols_count: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_ne!(layers_count, 0);
    assert!(cosets_in_tile >= 1);
    assert!(per_coset_leaves_count >= 1 << (layers_count - 1));
    hash_leaves_multi_coset(
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

/// Single-coset full tree build from a flat values matrix. Production commits
/// go through the multi-coset builders above; this is a test-reference reader
/// kept for downstream parity tests (circuit_prover's TraceHolder cache-mode
/// tests rebuild trees with it), like the `#[doc(hidden)]` gather helpers.
#[doc(hidden)]
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
    hash_leaves(values, leaves, log_rows_per_hash, stream)?;
    build_merkle_tree_nodes(leaves, nodes, layers_count - 1, stream)
}
