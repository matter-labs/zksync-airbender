//! Blake2s Merkle-tree construction: the fused node tower (many Merkle layers
//! per launch) and the multi-coset tree builders used by the prover's commit
//! paths.

use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::field::BF;
use gpu_core::primitives::utils::WARP_SIZE;

use super::hash::{hash_leaves, hash_leaves_multi_coset};
use super::{checked_u32, Digest};

cuda_kernel!(
    NodesTower,
    ab_blake2s_nodes_tower_multi_coset_kernel(
        src: *const Digest,
        dst: *mut Digest,
        layers: u32,
        log_blocks_per_coset: u32,
        stride_digests: u32,
        src_count_per_coset: u32,
    )
);

/// Layers one tower launch folds. A block owns one subtree and emits one digest
/// per thread at layer 0, so it runs `1 << (LAYERS - 1)` threads over
/// `1 << LAYERS` source digests, with that many digests of shared memory.
const NODES_TOWER_MAX_LAYERS: u32 = 10;

/// Digests a `layers`-deep tower writes over a `src_count`-digest source layer.
fn tower_output_count(src_count: usize, layers: u32) -> usize {
    src_count - (src_count >> layers)
}

/// Offset, relative to the tower's first output layer, of the last layer it
/// writes — i.e. where the next tower's source layer begins.
fn tower_last_layer_offset(src_count: usize, layers: u32) -> usize {
    tower_output_count(src_count, layers - 1)
}

fn launch_nodes_tower(
    src: *const Digest,
    dst: *mut Digest,
    layers: u32,
    cosets_in_tile: usize,
    stride_digests: usize,
    src_count_per_coset: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(src_count_per_coset.is_power_of_two());
    assert!((1..=src_count_per_coset.trailing_zeros()).contains(&layers));
    let threads = 1u32 << (layers - 1);
    let blocks_per_coset = src_count_per_coset >> layers;
    let grid = checked_u32(blocks_per_coset * cosets_in_tile);
    let mut config = CudaLaunchConfig::basic(grid, threads, stream);
    config.dynamic_smem_bytes = threads as usize * core::mem::size_of::<Digest>();
    let args = NodesTowerArguments::new(
        src,
        dst,
        layers,
        blocks_per_coset.trailing_zeros(),
        checked_u32(stride_digests),
        checked_u32(src_count_per_coset),
    );
    NodesTowerFunction::default().launch(&config, &args)
}

/// Tower launch against a single backing slab, using per-coset src/dst offsets.
/// Callers express a virtual src/dst view inside the per-coset slabs without
/// re-slicing the backing buffer (which would violate Rust aliasing rules when
/// src and dst sit in the same allocation).
fn launch_nodes_tower_in_backing(
    backing: &mut DeviceSlice<Digest>,
    cosets_in_tile: usize,
    per_coset_stride_digests: usize,
    src_offset_in_coset: usize,
    dst_offset_in_coset: usize,
    src_count_per_coset: usize,
    layers: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    // Per-coset containment: each coset's read/write window must fit inside
    // its own slab — the aggregate end checks below cannot see a window that
    // spills into the next coset's slab.
    let src_window_end = src_offset_in_coset
        .checked_add(src_count_per_coset)
        .expect("src window overflow");
    let dst_window_end = dst_offset_in_coset
        .checked_add(tower_output_count(src_count_per_coset, layers))
        .expect("dst window overflow");
    assert!(src_window_end <= per_coset_stride_digests);
    assert!(dst_window_end <= per_coset_stride_digests);
    // The write window must not overlap the read window within a slab
    // (containment above already separates distinct cosets).
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
    launch_nodes_tower(
        src_ptr,
        dst_ptr,
        layers,
        cosets_in_tile,
        per_coset_stride_digests,
        src_count_per_coset,
        stream,
    )
}

fn tower_step_layers(remaining: u32, src_count: usize) -> u32 {
    let layers = remaining
        .min(NODES_TOWER_MAX_LAYERS)
        .min(src_count.trailing_zeros());
    assert!(
        layers >= 1,
        "source layer too small for another Merkle layer"
    );
    layers
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
        return Ok(());
    }
    let values_len = values.len();
    let results_len = results.len();
    assert!(values_len.is_power_of_two());
    assert_eq!(values_len, results_len);
    // The first tower's source layer lives outside `results`; every later one
    // reads a layer it already wrote.
    let layers = tower_step_layers(layers_count, values_len);
    launch_nodes_tower(
        values.as_ptr(),
        results.as_mut_ptr(),
        layers,
        1,
        0,
        values_len,
        stream,
    )?;
    let mut src_offset = tower_last_layer_offset(values_len, layers);
    let mut src_count = values_len >> layers;
    let mut remaining = layers_count - layers;
    while remaining > 0 {
        let layers = tower_step_layers(remaining, src_count);
        let dst_offset = src_offset + src_count;
        launch_nodes_tower_in_backing(
            results,
            1,
            results_len,
            src_offset,
            dst_offset,
            src_count,
            layers,
            stream,
        )?;
        src_offset = dst_offset + tower_last_layer_offset(src_count, layers);
        src_count >>= layers;
        remaining -= layers;
    }
    Ok(())
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
    let mut remaining = layers_count;
    while remaining > 0 {
        let layers = tower_step_layers(remaining, src_count);
        let dst_offset = src_offset + src_count;
        launch_nodes_tower_in_backing(
            tree_backing,
            cosets_in_tile,
            per_coset_tree_stride_digests,
            src_offset,
            dst_offset,
            src_count,
            layers,
            stream,
        )?;
        src_offset = dst_offset + tower_last_layer_offset(src_count, layers);
        src_count >>= layers;
        remaining -= layers;
    }
    Ok(())
}

/// Node-only seam over an ALREADY-POPULATED source layer in `tree_backing`,
/// forwarding verbatim to [`build_merkle_tree_nodes_multi_coset`]. Callers that
/// write (and permute) their own leaves layer cannot use
/// [`build_merkle_tree_multi_coset`], which re-hashes leaves first and would
/// overwrite it.
#[doc(hidden)]
pub fn build_merkle_tree_nodes_multi_coset_over_existing_layer(
    tree_backing: &mut DeviceSlice<Digest>,
    layers_count: u32,
    cosets_in_tile: usize,
    per_coset_tree_stride_digests: usize,
    initial_src_offset_in_coset: usize,
    initial_src_layer_count_per_coset: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    build_merkle_tree_nodes_multi_coset(
        tree_backing,
        layers_count,
        cosets_in_tile,
        per_coset_tree_stride_digests,
        initial_src_offset_in_coset,
        initial_src_layer_count_per_coset,
        stream,
    )
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

cuda_kernel!(
    PartialTreeMultiCosetPhysical,
    ab_blake2s_partial_tree_multi_coset_physical_kernel(
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

/// LSB sibling of [`build_partial_merkle_tree_multi_coset`]: `values` is the
/// same exact `[coset][column][row]` storage, but in BITREVERSED row order.
/// The tree backing it writes is byte-identical to the natural-order builder's.
pub fn build_partial_merkle_tree_multi_coset_physical(
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
    // A CTA reduces one contiguous run of 512 LOGICAL leaves, and the physical
    // block translation below is only coset-local for a CTA that stays inside
    // one coset.
    assert!(
        per_coset_leaves_count.trailing_zeros() >= LEAVES_PER_BLOCK.trailing_zeros(),
        "each 512-leaf CTA must stay inside one coset ({per_coset_leaves_count} leaves per coset)"
    );
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
    let args = PartialTreeMultiCosetPhysicalArguments::new(
        values.as_ptr(),
        tree_backing.as_mut_ptr(),
        log_rows_per_hash,
        checked_u32(cols_count),
        per_coset_leaves_count.trailing_zeros(),
        checked_u32(per_coset_values_stride_bf),
        checked_u32(per_coset_tree_stride_digests),
        total_leaves,
    );
    PartialTreeMultiCosetPhysicalFunction::default().launch(&config, &args)?;
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
