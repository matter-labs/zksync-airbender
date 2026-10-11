use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::field::PR;

use super::hash::{leaf_shape, leaf_tile, LeafShape, LeafTile};
use super::{
    assert_no_overlap, checked_product, checked_u64, grid_dim, tile_extent, Digest, BLOCK_THREADS,
};

const MAX_SKIP_BOTTOM: u32 = 5;
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
        "keccak256::{name}: skip_bottom <= 5"
    );
    let retained_per_coset = 2 * (leaves.leaves >> skip_bottom) - 1;
    PartialTreeShape {
        leaves,
        retained_per_coset,
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
    let shape = partial_tree_shape(NAME, log_domain, log_values_per_leaf, columns, skip_bottom);
    assert_eq!(
        values.len(),
        shape.leaves.coset_values,
        "keccak256::build_partial_coset_tree: values.len() == columns << log_domain"
    );
    assert_eq!(
        retained.len(),
        shape.retained_per_coset,
        "keccak256::build_partial_coset_tree: retained.len() == 2 * (leaves >> skip_bottom) - 1"
    );
    build_partial_coset_trees_multi_coset(
        values,
        log_domain,
        log_values_per_leaf,
        columns,
        skip_bottom,
        1,
        values.len(),
        retained.len(),
        retained,
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
    let shape = partial_tree_shape(NAME, log_domain, log_values_per_leaf, columns, skip_bottom);
    let tile = partial_tree_tile(
        NAME,
        &shape,
        values.len(),
        cosets_in_tile,
        values_stride,
        retained_stride,
        retained.len(),
    );
    assert_no_overlap(NAME, values, retained);
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
    let grid = grid_dim(NAME, tile.leaves.threads, PARTIAL_ROOTS_THREADS);
    let config = CudaLaunchConfig::basic(grid, PARTIAL_ROOTS_THREADS, stream);
    PartialRootsFunction::default().launch(&config, &args)?;
    let log_leaves = shape.leaves.log_leaves;
    let base = retained.as_mut_ptr();
    for layer in skip_bottom..log_leaves {
        let src = retained_layer_offset(log_leaves, skip_bottom, layer);
        let dst = retained_layer_offset(log_leaves, skip_bottom, layer + 1);
        launch_nodes(
            NAME,
            unsafe { base.add(src) },
            shape.leaves.leaves >> (layer + 1),
            cosets_in_tile,
            tile.retained_stride,
            tile.retained_stride,
            unsafe { base.add(dst) },
            stream,
        )?;
    }
    Ok(())
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
