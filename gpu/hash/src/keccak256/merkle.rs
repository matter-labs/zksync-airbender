use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::field::PR;
use gpu_core::primitives::utils::LOG_WARP_SIZE;

use super::hash::{leaf_shape, leaf_tile, LeafShape, LeafTile};
use super::{
    assert_no_overlap, checked_product, checked_u64, grid_dim, tile_extent, Digest, BLOCK_THREADS,
};

const MAX_SKIP_BOTTOM: u32 = 10;
const DIRECT_SKIP_BOTTOM: u32 = 8;
const PARTIAL_ROOTS_THREADS: u32 = 256;

pub fn retained_layer_offset(log_leaves: u32, skip_bottom: u32, layer: u32) -> usize {
    assert!(
        log_leaves <= 31,
        "keccak256::retained_layer_offset: log_leaves <= 31"
    );
    assert!(
        skip_bottom <= layer && layer <= log_leaves,
        "keccak256::retained_layer_offset: skip_bottom <= layer <= log_leaves"
    );
    let leaves = 1usize << log_leaves;
    2 * (leaves >> skip_bottom) - 2 * (leaves >> layer)
}

pub fn top_nodes_layer_offset(log_lde: u32, layer: u32) -> usize {
    assert!(
        log_lde <= 31,
        "keccak256::top_nodes_layer_offset: log_lde <= 31"
    );
    assert!(
        layer >= 1 && layer <= log_lde,
        "keccak256::top_nodes_layer_offset: 1 <= layer <= log_lde"
    );
    let cosets = 1usize << log_lde;
    cosets - (cosets >> (layer - 1))
}

pub(super) struct PartialTreeShape {
    pub(super) leaves: LeafShape,
    pub(super) retained_per_coset: usize,
}

pub(super) fn partial_tree_shape(
    name: &str,
    log_domain: u32,
    log_values_per_leaf: u32,
    columns: u32,
    skip_bottom: u32,
) -> PartialTreeShape {
    let leaves = leaf_shape(name, log_domain, log_values_per_leaf, columns);
    assert!(
        skip_bottom <= leaves.log_leaves,
        "keccak256::{name}: skip_bottom <= log_domain - log_values_per_leaf"
    );
    assert!(
        skip_bottom <= MAX_SKIP_BOTTOM,
        "keccak256::{name}: skip_bottom <= 10"
    );
    let retained_per_coset = 2 * (leaves.leaves >> skip_bottom) - 1;
    PartialTreeShape {
        leaves,
        retained_per_coset,
    }
}

pub fn partial_coset_tree_scratch_len(
    log_domain: u32,
    log_values_per_leaf: u32,
    skip_bottom: u32,
) -> usize {
    let shape = partial_tree_shape(
        "partial_coset_tree_scratch_len",
        log_domain,
        log_values_per_leaf,
        1,
        skip_bottom,
    );
    if skip_bottom <= LOG_WARP_SIZE {
        0
    } else {
        shape.leaves.leaves >> LOG_WARP_SIZE
    }
}

pub(super) struct PartialTreeTile {
    pub(super) leaves: LeafTile,
    pub(super) retained_stride: u64,
}

pub(super) fn partial_tree_tile(
    name: &str,
    shape: &PartialTreeShape,
    values_len: usize,
    cosets_in_tile: u32,
    values_stride: usize,
    retained_stride: usize,
    retained_len: usize,
) -> PartialTreeTile {
    let leaves = leaf_tile(
        name,
        &shape.leaves,
        values_len,
        cosets_in_tile,
        values_stride,
    );
    let retained_extent = tile_extent(
        name,
        cosets_in_tile,
        retained_stride,
        shape.retained_per_coset,
    );
    assert!(
        retained_len >= retained_extent,
        "keccak256::{name}: retained.len() >= (cosets_in_tile - 1) * retained_stride + 2 * (leaves >> skip_bottom) - 1"
    );
    PartialTreeTile {
        leaves,
        retained_stride: checked_u64(name, retained_stride),
    }
}

pub(super) fn top_tree_log_lde(
    name: &str,
    roots_len: usize,
    cap_log: u32,
    nodes_len: usize,
) -> u32 {
    assert!(
        roots_len.is_power_of_two(),
        "keccak256::{name}: roots.len() is a power of two"
    );
    let log_lde = roots_len.trailing_zeros();
    assert!(log_lde <= 31, "keccak256::{name}: log_lde <= 31");
    assert!(cap_log <= log_lde, "keccak256::{name}: cap_log <= log_lde");
    assert_eq!(
        nodes_len,
        roots_len - (1usize << cap_log),
        "keccak256::{name}: nodes.len() == roots.len() - 2^cap_log"
    );
    log_lde
}

cuda_kernel!(
    PartialRoots,
    ab_keccak256_partial_roots_kernel(
        values: *const PR,
        log_domain: u32,
        log_v: u32,
        columns: u32,
        skip_bottom: u32,
        cosets_in_tile: u32,
        values_stride: u64,
        retained_stride: u64,
        retained: *mut Digest,
    )
);

cuda_kernel!(
    ReduceRoots,
    ab_keccak256_reduce_roots_kernel(
        src: *const Digest,
        count: u64,
        reduction_layers: u32,
        dst: *mut Digest,
    )
);

cuda_kernel!(
    Nodes,
    ab_keccak256_nodes_kernel(
        src: *const Digest,
        count: u64,
        cosets_in_tile: u32,
        src_stride: u64,
        dst_stride: u64,
        dst: *mut Digest,
    )
);

cuda_kernel!(
    GatherCap,
    ab_keccak256_gather_cap_kernel(src: *const Digest, count: u64, dst: *mut Digest)
);

fn launch_nodes(
    name: &str,
    src: *const Digest,
    count: usize,
    cosets_in_tile: u32,
    src_stride: u64,
    dst_stride: u64,
    dst: *mut Digest,
    stream: &CudaStream,
) -> CudaResult<()> {
    let grid = grid_dim(
        name,
        checked_product(name, cosets_in_tile as usize, count),
        BLOCK_THREADS,
    );
    let args = NodesArguments::new(
        src,
        checked_u64(name, count),
        cosets_in_tile,
        src_stride,
        dst_stride,
        dst,
    );
    let config = CudaLaunchConfig::basic(grid, BLOCK_THREADS, stream);
    NodesFunction::default().launch(&config, &args)
}

pub fn build_partial_coset_tree(
    values: &DeviceSlice<PR>,
    log_domain: u32,
    log_values_per_leaf: u32,
    columns: u32,
    skip_bottom: u32,
    retained: &mut DeviceSlice<Digest>,
    stream: &CudaStream,
) -> CudaResult<()> {
    const NAME: &str = "build_partial_coset_tree";
    assert!(
        skip_bottom <= DIRECT_SKIP_BOTTOM,
        "keccak256::{NAME}: skip_bottom <= 8; use build_partial_coset_tree_with_scratch"
    );
    build_partial_coset_tree_impl(
        NAME,
        values,
        log_domain,
        log_values_per_leaf,
        columns,
        skip_bottom,
        retained,
        None,
        stream,
    )
}

pub fn build_partial_coset_tree_with_scratch(
    values: &DeviceSlice<PR>,
    log_domain: u32,
    log_values_per_leaf: u32,
    columns: u32,
    skip_bottom: u32,
    retained: &mut DeviceSlice<Digest>,
    scratch: &mut DeviceSlice<Digest>,
    stream: &CudaStream,
) -> CudaResult<()> {
    build_partial_coset_tree_impl(
        "build_partial_coset_tree_with_scratch",
        values,
        log_domain,
        log_values_per_leaf,
        columns,
        skip_bottom,
        retained,
        Some(scratch),
        stream,
    )
}

fn build_partial_coset_tree_impl(
    name: &str,
    values: &DeviceSlice<PR>,
    log_domain: u32,
    log_values_per_leaf: u32,
    columns: u32,
    skip_bottom: u32,
    retained: &mut DeviceSlice<Digest>,
    scratch: Option<&mut DeviceSlice<Digest>>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let shape = partial_tree_shape(name, log_domain, log_values_per_leaf, columns, skip_bottom);
    assert_eq!(
        values.len(),
        shape.leaves.coset_values,
        "keccak256::{name}: values.len() == columns << log_domain"
    );
    assert_eq!(
        retained.len(),
        shape.retained_per_coset,
        "keccak256::{name}: retained.len() == 2 * (leaves >> skip_bottom) - 1"
    );
    build_partial_coset_trees_impl(
        name,
        values,
        log_domain,
        log_values_per_leaf,
        columns,
        skip_bottom,
        1,
        values.len(),
        retained.len(),
        retained,
        scratch,
        stream,
    )
}

pub fn build_partial_coset_trees_multi_coset(
    values: &DeviceSlice<PR>,
    log_domain: u32,
    log_values_per_leaf: u32,
    columns: u32,
    skip_bottom: u32,
    cosets_in_tile: u32,
    values_stride: usize,
    retained_stride: usize,
    retained: &mut DeviceSlice<Digest>,
    stream: &CudaStream,
) -> CudaResult<()> {
    const NAME: &str = "build_partial_coset_trees_multi_coset";
    assert!(
        skip_bottom <= DIRECT_SKIP_BOTTOM,
        "keccak256::{NAME}: skip_bottom <= 8; use build_partial_coset_trees_multi_coset_with_scratch"
    );
    build_partial_coset_trees_impl(
        NAME,
        values,
        log_domain,
        log_values_per_leaf,
        columns,
        skip_bottom,
        cosets_in_tile,
        values_stride,
        retained_stride,
        retained,
        None,
        stream,
    )
}

pub fn build_partial_coset_trees_multi_coset_with_scratch(
    values: &DeviceSlice<PR>,
    log_domain: u32,
    log_values_per_leaf: u32,
    columns: u32,
    skip_bottom: u32,
    cosets_in_tile: u32,
    values_stride: usize,
    retained_stride: usize,
    retained: &mut DeviceSlice<Digest>,
    scratch: &mut DeviceSlice<Digest>,
    stream: &CudaStream,
) -> CudaResult<()> {
    build_partial_coset_trees_impl(
        "build_partial_coset_trees_multi_coset_with_scratch",
        values,
        log_domain,
        log_values_per_leaf,
        columns,
        skip_bottom,
        cosets_in_tile,
        values_stride,
        retained_stride,
        retained,
        Some(scratch),
        stream,
    )
}

fn build_partial_coset_trees_impl(
    name: &str,
    values: &DeviceSlice<PR>,
    log_domain: u32,
    log_values_per_leaf: u32,
    columns: u32,
    skip_bottom: u32,
    cosets_in_tile: u32,
    values_stride: usize,
    retained_stride: usize,
    retained: &mut DeviceSlice<Digest>,
    scratch: Option<&mut DeviceSlice<Digest>>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let shape = partial_tree_shape(name, log_domain, log_values_per_leaf, columns, skip_bottom);
    let tile = partial_tree_tile(
        name,
        &shape,
        values.len(),
        cosets_in_tile,
        values_stride,
        retained_stride,
        retained.len(),
    );
    assert_no_overlap(name, values, retained);
    if let Some(scratch) = scratch.as_deref() {
        assert_no_overlap(name, values, scratch);
        assert_no_overlap(name, retained, scratch);
    }
    if skip_bottom <= LOG_WARP_SIZE || (scratch.is_none() && skip_bottom <= DIRECT_SKIP_BOTTOM) {
        let args = PartialRootsArguments::new(
            values.as_ptr(),
            log_domain,
            log_values_per_leaf,
            columns,
            skip_bottom,
            cosets_in_tile,
            tile.leaves.values_stride,
            tile.retained_stride,
            retained.as_mut_ptr(),
        );
        let grid = grid_dim(name, tile.leaves.threads, PARTIAL_ROOTS_THREADS);
        let config = CudaLaunchConfig::basic(grid, PARTIAL_ROOTS_THREADS, stream);
        PartialRootsFunction::default().launch(&config, &args)?;
    } else {
        let scratch = scratch.expect("deep partial tree builder requires explicit scratch");
        let scratch_len = shape.leaves.leaves >> LOG_WARP_SIZE;
        assert!(
            scratch.len() >= scratch_len,
            "keccak256::{name}: scratch.len() >= leaves >> 5"
        );
        let roots = shape.leaves.leaves >> skip_bottom;
        let roots_grid = grid_dim(name, shape.leaves.leaves, PARTIAL_ROOTS_THREADS);
        let reduce_grid = grid_dim(name, scratch_len, BLOCK_THREADS);
        for coset in 0..cosets_in_tile as usize {
            let args = PartialRootsArguments::new(
                unsafe { values.as_ptr().add(coset * values_stride) },
                log_domain,
                log_values_per_leaf,
                columns,
                LOG_WARP_SIZE,
                1,
                tile.leaves.values_stride,
                checked_u64(name, scratch_len),
                scratch.as_mut_ptr(),
            );
            PartialRootsFunction::default().launch(
                &CudaLaunchConfig::basic(roots_grid, PARTIAL_ROOTS_THREADS, stream),
                &args,
            )?;
            let args = ReduceRootsArguments::new(
                scratch.as_ptr(),
                checked_u64(name, roots),
                skip_bottom - LOG_WARP_SIZE,
                unsafe { retained.as_mut_ptr().add(coset * retained_stride) },
            );
            ReduceRootsFunction::default().launch(
                &CudaLaunchConfig::basic(reduce_grid, BLOCK_THREADS, stream),
                &args,
            )?;
        }
    }
    retained_layers(
        name,
        shape.leaves.log_leaves,
        skip_bottom,
        cosets_in_tile,
        tile.retained_stride,
        retained.as_mut_ptr(),
        stream,
    )
}

fn retained_layers(
    name: &str,
    log_leaves: u32,
    skip_bottom: u32,
    cosets_in_tile: u32,
    retained_stride: u64,
    base: *mut Digest,
    stream: &CudaStream,
) -> CudaResult<()> {
    for layer in skip_bottom..log_leaves {
        let src = retained_layer_offset(log_leaves, skip_bottom, layer);
        let dst = retained_layer_offset(log_leaves, skip_bottom, layer + 1);
        launch_nodes(
            name,
            unsafe { base.add(src) },
            1usize << (log_leaves - layer - 1),
            cosets_in_tile,
            retained_stride,
            retained_stride,
            unsafe { base.add(dst) },
            stream,
        )?;
    }
    Ok(())
}

// Layers skip_bottom + 1..=log_leaves of `cosets_in_tile` retained trees whose layer skip_bottom
// is in place (retained[coset * retained_stride + subtree]).
pub fn build_retained_layers(
    log_leaves: u32,
    skip_bottom: u32,
    cosets_in_tile: u32,
    retained_stride: usize,
    retained: &mut DeviceSlice<Digest>,
    stream: &CudaStream,
) -> CudaResult<()> {
    const NAME: &str = "build_retained_layers";
    let per_coset = retained_layer_offset(log_leaves, skip_bottom, log_leaves) + 1;
    assert!(
        retained.len() >= tile_extent(NAME, cosets_in_tile, retained_stride, per_coset),
        "keccak256::{NAME}: retained.len() >= (cosets_in_tile - 1) * retained_stride + retained per coset"
    );
    retained_layers(
        NAME,
        log_leaves,
        skip_bottom,
        cosets_in_tile,
        checked_u64(NAME, retained_stride),
        retained.as_mut_ptr(),
        stream,
    )
}

// The retained trees (layers skip_bottom..=log_leaves, `retained_stride` apart) of `cosets` coset
// trees whose depth-`node_depth` nodes are in `nodes` (coset-major, 2^(log_leaves - node_depth) per
// coset): layers node_depth + 1..skip_bottom alternate through `scratch` (at least nodes.len() / 2)
// and the head of `nodes`, which is overwritten; layer skip_bottom lands in `retained`.
#[allow(clippy::too_many_arguments)]
pub fn build_retained_from_nodes(
    nodes: &mut DeviceSlice<Digest>,
    node_depth: u32,
    log_leaves: u32,
    skip_bottom: u32,
    cosets: u32,
    scratch: &mut DeviceSlice<Digest>,
    retained: &mut DeviceSlice<Digest>,
    retained_stride: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    build_retained_bottom_from_nodes(
        nodes,
        node_depth,
        log_leaves,
        skip_bottom,
        cosets,
        scratch,
        retained,
        retained_stride,
        stream,
    )?;
    retained_layers(
        "build_retained_from_nodes",
        log_leaves,
        skip_bottom,
        cosets,
        checked_u64("build_retained_from_nodes", retained_stride),
        retained.as_mut_ptr(),
        stream,
    )
}

// `build_retained_from_nodes` up to layer skip_bottom; the layers above it are left to
// `build_retained_layers`.
#[allow(clippy::too_many_arguments)]
pub fn build_retained_bottom_from_nodes(
    nodes: &mut DeviceSlice<Digest>,
    node_depth: u32,
    log_leaves: u32,
    skip_bottom: u32,
    cosets: u32,
    scratch: &mut DeviceSlice<Digest>,
    retained: &mut DeviceSlice<Digest>,
    retained_stride: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    const NAME: &str = "build_retained_bottom_from_nodes";
    assert!(
        node_depth < skip_bottom && skip_bottom <= log_leaves && log_leaves <= 31,
        "keccak256::{NAME}: node_depth < skip_bottom <= log_leaves <= 31"
    );
    let per_coset_nodes = 1usize << (log_leaves - node_depth);
    assert_eq!(
        Some(nodes.len()),
        (cosets as usize).checked_mul(per_coset_nodes),
        "keccak256::{NAME}: nodes.len() == cosets << (log_leaves - node_depth)"
    );
    assert!(
        skip_bottom == node_depth + 1 || scratch.len() >= nodes.len() / 2,
        "keccak256::{NAME}: scratch.len() >= nodes.len() / 2"
    );
    let per_coset = retained_layer_offset(log_leaves, skip_bottom, log_leaves) + 1;
    assert!(
        retained.len() >= tile_extent(NAME, cosets, retained_stride, per_coset),
        "keccak256::{NAME}: retained.len() >= (cosets - 1) * retained_stride + retained per coset"
    );
    assert_no_overlap(NAME, nodes, scratch);
    assert_no_overlap(NAME, nodes, retained);
    assert_no_overlap(NAME, scratch, retained);
    for layer in node_depth + 1..=skip_bottom {
        let count = 1usize << (log_leaves - layer);
        let input = if (layer - node_depth) % 2 == 1 {
            nodes.as_ptr()
        } else {
            scratch.as_ptr()
        };
        let (output, dst_stride) = if layer == skip_bottom {
            (retained.as_mut_ptr(), checked_u64(NAME, retained_stride))
        } else if (layer - node_depth) % 2 == 1 {
            (scratch.as_mut_ptr(), checked_u64(NAME, count))
        } else {
            (nodes.as_mut_ptr(), checked_u64(NAME, count))
        };
        launch_nodes(
            NAME,
            input,
            count,
            cosets,
            checked_u64(NAME, 2 * count),
            dst_stride,
            output,
            stream,
        )?;
    }
    Ok(())
}

// `layers` binary-tree layers above the digests in `src` (one node launch per layer): the last
// layer goes to `dst` (src.len() >> layers digests), the layers between alternate through
// `scratch` (at least src.len() / 2 digests when layers >= 2) and the head of `src`, which is
// overwritten.
pub fn reduce_digest_layers(
    src: &mut DeviceSlice<Digest>,
    layers: u32,
    scratch: &mut DeviceSlice<Digest>,
    dst: &mut DeviceSlice<Digest>,
    stream: &CudaStream,
) -> CudaResult<()> {
    const NAME: &str = "reduce_digest_layers";
    assert!(
        (1..=MAX_SKIP_BOTTOM).contains(&layers),
        "keccak256::{NAME}: 1 <= layers <= 10"
    );
    let count = src.len();
    assert_eq!(
        Some(count),
        dst.len().checked_mul(1 << layers),
        "keccak256::{NAME}: src.len() == dst.len() << layers"
    );
    assert!(
        layers == 1 || scratch.len() >= count / 2,
        "keccak256::{NAME}: scratch.len() >= src.len() / 2"
    );
    assert_no_overlap(NAME, src, dst);
    assert_no_overlap(NAME, src, scratch);
    assert_no_overlap(NAME, scratch, dst);
    for layer in 1..=layers {
        let (input, output) = match (layer % 2, layer == layers) {
            (1, true) => (src.as_ptr(), dst.as_mut_ptr()),
            (1, false) => (src.as_ptr(), scratch.as_mut_ptr()),
            (_, true) => (scratch.as_ptr(), dst.as_mut_ptr()),
            (_, false) => (scratch.as_ptr(), src.as_mut_ptr()),
        };
        launch_nodes(NAME, input, count >> layer, 1, 0, 0, output, stream)?;
    }
    Ok(())
}

// Roots of every 2^layers consecutive digests of `src` (1 <= layers <= 5), e.g. the depth-10
// subtree roots of a coset from its depth-8 sub-roots.
pub fn reduce_digests(
    src: &DeviceSlice<Digest>,
    layers: u32,
    dst: &mut DeviceSlice<Digest>,
    stream: &CudaStream,
) -> CudaResult<()> {
    const NAME: &str = "reduce_digests";
    assert!(
        (1..=LOG_WARP_SIZE).contains(&layers),
        "keccak256::{NAME}: 1 <= layers <= 5"
    );
    assert_eq!(
        Some(src.len()),
        dst.len().checked_mul(1 << layers),
        "keccak256::{NAME}: src.len() == dst.len() << layers"
    );
    assert_no_overlap(NAME, src, dst);
    let args = ReduceRootsArguments::new(
        src.as_ptr(),
        checked_u64(NAME, dst.len()),
        layers,
        dst.as_mut_ptr(),
    );
    let grid = grid_dim(NAME, src.len(), BLOCK_THREADS);
    ReduceRootsFunction::default()
        .launch(&CudaLaunchConfig::basic(grid, BLOCK_THREADS, stream), &args)
}

pub fn build_top_tree(
    roots: &DeviceSlice<Digest>,
    cap_log: u32,
    nodes: &mut DeviceSlice<Digest>,
    stream: &CudaStream,
) -> CudaResult<()> {
    const NAME: &str = "build_top_tree";
    let log_lde = top_tree_log_lde(NAME, roots.len(), cap_log, nodes.len());
    assert_no_overlap(NAME, roots, nodes);
    let base = nodes.as_mut_ptr();
    for layer in 1..=log_lde - cap_log {
        let src = if layer == 1 {
            roots.as_ptr()
        } else {
            unsafe { base.add(top_nodes_layer_offset(log_lde, layer - 1)) as *const Digest }
        };
        let dst = unsafe { base.add(top_nodes_layer_offset(log_lde, layer)) };
        launch_nodes(NAME, src, roots.len() >> layer, 1, 0, 0, dst, stream)?;
    }
    Ok(())
}

pub fn gather_tree_cap(
    leaves: &DeviceSlice<Digest>,
    nodes: &DeviceSlice<Digest>,
    cap_log: u32,
    out: &mut DeviceSlice<Digest>,
    stream: &CudaStream,
) -> CudaResult<()> {
    const NAME: &str = "gather_tree_cap";
    let log_lde = top_tree_log_lde(NAME, leaves.len(), cap_log, nodes.len());
    let cap = 1usize << cap_log;
    assert_eq!(
        out.len(),
        cap,
        "keccak256::gather_tree_cap: out.len() == 2^cap_log"
    );
    assert_no_overlap(NAME, leaves, out);
    assert_no_overlap(NAME, nodes, out);
    let src = if cap_log == log_lde {
        leaves.as_ptr()
    } else {
        nodes[nodes.len() - cap..].as_ptr()
    };
    let args = GatherCapArguments::new(src, checked_u64(NAME, cap), out.as_mut_ptr());
    let config = CudaLaunchConfig::basic(grid_dim(NAME, cap, BLOCK_THREADS), BLOCK_THREADS, stream);
    GatherCapFunction::default().launch(&config, &args)
}
