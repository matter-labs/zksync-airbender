use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use gpu_core::primitives::field::PR;
use gpu_core::primitives::nvtx::scoped_range;
use gpu_hash::keccak256::{
    build_retained_bottom_from_nodes, build_retained_layers, launch_open_paths, open_paths_depth,
    reduce_digest_layers, retained_layer_offset, Digest,
};
use gpu_ntt::proth120::{
    launch_suffix_micro, lde_coset_slot, CosetSource, DeviceContext, Dispatch, ScaleArgs,
    SuffixShape, TwiddleDescriptor,
};

#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct LeafSinkArgs {
    tile: *const PR,
    out: *mut Digest,
    tile_coset_stride: u64,
    out_coset_stride: u64,
    log_a: u32,
    log_r: u32,
    skip_bottom: u32,
    first_tile: u32,
    log_n: u32,
    log_domain: u32,
    k0: u32,
    reserved: u32,
}

const _: () = assert!(size_of::<LeafSinkArgs>() == 64);

cuda_kernel_signature_arguments_and_function!(
    pub(crate) LeafSink,
    args: LeafSinkArgs, descriptor: TwiddleDescriptor,
);
macro_rules! leaf_sink_kernel {
    ($name:ident) => {
        cuda_kernel_declaration!($name(args: LeafSinkArgs, descriptor: TwiddleDescriptor,));
    };
}
leaf_sink_kernel!(ab_pr_leaf_sink_1_2_3_commit_kernel);
leaf_sink_kernel!(ab_pr_leaf_sink_2_1_3_commit_kernel);
leaf_sink_kernel!(ab_pr_leaf_sink_7_2_3_commit_kernel);
leaf_sink_kernel!(ab_pr_leaf_sink_13_1_3_commit_kernel);
leaf_sink_kernel!(ab_pr_leaf_sink_1_3_5_coefficient_tree_kernel);
leaf_sink_kernel!(ab_pr_leaf_sink_1_4_5_coefficient_tree_kernel);
leaf_sink_kernel!(ab_pr_leaf_sink_1_3_5_residue_tree_kernel);
leaf_sink_kernel!(ab_pr_leaf_sink_1_4_5_residue_tree_kernel);

#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct LeafOpenArgs {
    gate: *const u32,
    coset: *const u32,
    queries: *const u32,
    leaves: *mut PR,
    paths: *mut Digest,
    count: u32,
    log_lde: u32,
    depth: u32,
    reserved: u32,
}

const _: () = assert!(size_of::<LeafOpenArgs>() == 56);

cuda_kernel_signature_arguments_and_function!(
    pub(crate) LeafOpen,
    args: LeafSinkArgs, open: LeafOpenArgs, descriptor: TwiddleDescriptor,
);
macro_rules! leaf_open_kernel {
    ($name:ident) => {
        cuda_kernel_declaration!(
            $name(args: LeafSinkArgs, open: LeafOpenArgs, descriptor: TwiddleDescriptor,)
        );
    };
}
leaf_open_kernel!(ab_pr_leaf_sink_1_2_3_open_kernel);
leaf_open_kernel!(ab_pr_leaf_sink_2_1_3_open_kernel);
leaf_open_kernel!(ab_pr_leaf_sink_7_2_3_open_kernel);
leaf_open_kernel!(ab_pr_leaf_sink_13_1_3_open_kernel);

fn leaf_open_function(columns: u32, log_v: u32) -> Option<LeafOpenFunction> {
    Some(LeafOpenFunction(match (columns, log_v) {
        (1, 2) => ab_pr_leaf_sink_1_2_3_open_kernel,
        (2, 1) => ab_pr_leaf_sink_2_1_3_open_kernel,
        (7, 2) => ab_pr_leaf_sink_7_2_3_open_kernel,
        (13, 1) => ab_pr_leaf_sink_13_1_3_open_kernel,
        _ => return None,
    }))
}

// Commit hashes the coset evaluations; CoefficientTree hashes each leaf converted to its
// coefficients (WHIR oracles) with the coset k0 + launch coset of the 2^log_domain codeword.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SinkMode {
    Commit,
    CoefficientTree { log_domain: u32, k0: u32 },
}

// The sink's in-block tree depth: the Commit sink stops at depth-3 nodes (32 per block, the layers
// above are full-width node launches, `reduce_digest_layers`); the coefficient-tree sink builds its
// whole skip_bottom-5 subtrees.
pub fn sink_tree_depth(mode: &SinkMode, skip_bottom: u32) -> u32 {
    match mode {
        SinkMode::Commit => 3,
        SinkMode::CoefficientTree { .. } => skip_bottom,
    }
}

// CoefficientTree leaves come from the residue-tree kernels (the group before its last log_v stages,
// unscaled by the coset power); the converting kernels (last log_v stages, then the leaf conversion)
// are the reference.
fn leaf_sink_function(
    columns: u32,
    log_v: u32,
    tree_depth: u32,
    mode: &SinkMode,
    converted: bool,
) -> Option<LeafSinkFunction> {
    let commit = matches!(mode, SinkMode::Commit);
    Some(LeafSinkFunction(
        match (columns, log_v, tree_depth, commit, converted) {
            (1, 2, 3, true, _) => ab_pr_leaf_sink_1_2_3_commit_kernel,
            (2, 1, 3, true, _) => ab_pr_leaf_sink_2_1_3_commit_kernel,
            (7, 2, 3, true, _) => ab_pr_leaf_sink_7_2_3_commit_kernel,
            (13, 1, 3, true, _) => ab_pr_leaf_sink_13_1_3_commit_kernel,
            (1, 3, 5, false, false) => ab_pr_leaf_sink_1_3_5_residue_tree_kernel,
            (1, 4, 5, false, false) => ab_pr_leaf_sink_1_4_5_residue_tree_kernel,
            (1, 3, 5, false, true) => ab_pr_leaf_sink_1_3_5_coefficient_tree_kernel,
            (1, 4, 5, false, true) => ab_pr_leaf_sink_1_4_5_coefficient_tree_kernel,
            _ => return None,
        },
    ))
}

// Commit: depth-3 sink nodes, then at least one node layer up to skip_bottom; coefficient tree:
// whole skip_bottom-5 subtrees in the block.
fn supported_skip_bottom(mode: &SinkMode, skip_bottom: u32) -> bool {
    match mode {
        SinkMode::Commit => (4..=10).contains(&skip_bottom),
        SinkMode::CoefficientTree { .. } => skip_bottom == 5,
    }
}

pub fn has_leaf_sink(shape: &SuffixShape, mode: &SinkMode) -> bool {
    supported_skip_bottom(mode, shape.skip_bottom)
        && leaf_sink_function(
            shape.columns,
            shape.log_v,
            sink_tree_depth(mode, shape.skip_bottom),
            mode,
            false,
        )
        .is_some()
}

const MAX_GRID_Z: u32 = 1 << 16;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct SinkLaunch {
    pub(crate) grid: (u32, u32, u32),
    pub(crate) tree_depth: u32,
    pub(crate) tile_coset_stride: usize,
}

// Host checks of one sink launch, every span in checked arithmetic.
#[allow(clippy::too_many_arguments)]
pub(crate) fn sink_launch(
    log_max_domain: u32,
    shape: &SuffixShape,
    mode: &SinkMode,
    tiles_len: usize,
    first_tile: u32,
    tile_count: u32,
    cosets: u32,
    out_len: usize,
    out_coset_stride: usize,
) -> SinkLaunch {
    let tree_depth = sink_tree_depth(mode, shape.skip_bottom);
    assert!(
        leaf_sink_function(shape.columns, shape.log_v, tree_depth, mode, false).is_some(),
        "leaf sink: no kernel for {} columns, log_v {}, skip_bottom {}, {mode:?}",
        shape.columns,
        shape.log_v,
        shape.skip_bottom
    );
    assert!(
        supported_skip_bottom(mode, shape.skip_bottom),
        "leaf sink: skip_bottom {} outside 4..=10 (Commit) / 5 (CoefficientTree)",
        shape.skip_bottom
    );
    assert!(
        (6..=8).contains(&shape.r) && shape.log_v < shape.r,
        "leaf sink: r {} outside 6..=8 or not above log_v",
        shape.r
    );
    assert!(
        shape.log_n <= log_max_domain,
        "leaf sink: log_n {} exceeds context log_max_domain {log_max_domain}",
        shape.log_n
    );
    assert!(
        shape.log_n >= shape.r && shape.log_a() >= shape.skip_bottom,
        "leaf sink: skip_bottom {} above log_a",
        shape.skip_bottom
    );
    let log_block_leaves = shape.skip_bottom + shape.r - shape.log_v;
    assert!(
        log_block_leaves >= 8,
        "leaf sink: a tile holds fewer than 256 leaves"
    );
    if let SinkMode::CoefficientTree { log_domain, k0 } = *mode {
        assert!(
            shape.log_n <= log_domain && log_domain <= log_max_domain,
            "leaf sink: log_domain {log_domain} outside {}..={log_max_domain}",
            shape.log_n
        );
        assert!(
            u64::from(k0) + u64::from(cosets) <= 1u64 << (log_domain - shape.log_n),
            "leaf sink: cosets out of range"
        );
    }
    assert!(
        (1..MAX_GRID_Z).contains(&cosets),
        "leaf sink: cosets must be in 1..2^16"
    );
    assert!(
        tile_count >= 1
            && u64::from(first_tile) + u64::from(tile_count) <= shape.tiles_per_coset() as u64,
        "leaf sink: tiles out of range"
    );
    let overflow = || panic!("leaf sink: span overflow");
    let tile_coset_stride = (tile_count as usize)
        .checked_mul(shape.tile_len())
        .unwrap_or_else(overflow);
    let tiles_span = (cosets as usize)
        .checked_mul(tile_coset_stride)
        .unwrap_or_else(overflow);
    assert_eq!(tiles_len, tiles_span, "leaf sink: tiles length");
    let items = 1usize << (shape.log_n - shape.log_v - tree_depth);
    assert!(
        cosets == 1 || out_coset_stride >= items,
        "leaf sink: out coset stride below the items of a coset"
    );
    let out_span = (cosets as usize - 1)
        .checked_mul(out_coset_stride)
        .and_then(|offset| offset.checked_add(items))
        .unwrap_or_else(overflow);
    assert!(
        out_len >= out_span,
        "leaf sink: out shorter than its coset span"
    );
    let blocks = 1u64 << (log_block_leaves - 8);
    let grid_x = u64::from(tile_count) * blocks;
    assert!(grid_x < 1 << 31, "leaf sink: grid.x overflow");
    SinkLaunch {
        grid: (grid_x as u32, 1, cosets),
        tree_depth,
        tile_coset_stride,
    }
}

// The sink of tiles [first_tile, first_tile + tile_count) of `cosets` suffix-micro outputs
// (`launch_suffix_micro` layout): the last log_v stages, the leaf hashes and the in-block layers;
// writes the depth-`sink_tree_depth` nodes of launch coset z at
// out[z * out_coset_stride + node index in the coset tree].
#[allow(clippy::too_many_arguments)]
pub fn launch_sink(
    ctx: &DeviceContext,
    tiles: &DeviceSlice<PR>,
    shape: &SuffixShape,
    first_tile: u32,
    tile_count: u32,
    cosets: u32,
    mode: SinkMode,
    out: &mut DeviceSlice<Digest>,
    out_coset_stride: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    launch_leaf_sink(
        ctx,
        tiles,
        shape,
        first_tile,
        tile_count,
        cosets,
        mode,
        out,
        out_coset_stride,
        false,
        stream,
    )
}

// `launch_sink` with the converting CoefficientTree kernels (the reference of the residue-tree ones).
#[cfg(test)]
#[allow(clippy::too_many_arguments)]
pub(crate) fn launch_sink_converted(
    ctx: &DeviceContext,
    tiles: &DeviceSlice<PR>,
    shape: &SuffixShape,
    first_tile: u32,
    tile_count: u32,
    cosets: u32,
    mode: SinkMode,
    out: &mut DeviceSlice<Digest>,
    out_coset_stride: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    launch_leaf_sink(
        ctx,
        tiles,
        shape,
        first_tile,
        tile_count,
        cosets,
        mode,
        out,
        out_coset_stride,
        true,
        stream,
    )
}

#[allow(clippy::too_many_arguments)]
fn launch_leaf_sink(
    ctx: &DeviceContext,
    tiles: &DeviceSlice<PR>,
    shape: &SuffixShape,
    first_tile: u32,
    tile_count: u32,
    cosets: u32,
    mode: SinkMode,
    out: &mut DeviceSlice<Digest>,
    out_coset_stride: usize,
    converted: bool,
    stream: &CudaStream,
) -> CudaResult<()> {
    let launch = sink_launch(
        ctx.log_max_domain(),
        shape,
        &mode,
        tiles.len(),
        first_tile,
        tile_count,
        cosets,
        out.len(),
        out_coset_stride,
    );
    let tiles_range =
        tiles.as_ptr() as usize..tiles.as_ptr() as usize + tiles.len() * size_of::<PR>();
    let out_range = out.as_ptr() as usize..out.as_ptr() as usize + out.len() * size_of::<Digest>();
    assert!(
        tiles_range.end <= out_range.start || out_range.end <= tiles_range.start,
        "leaf sink: tiles/out overlap"
    );
    let (log_domain, k0) = match mode {
        SinkMode::Commit => (shape.log_n, 0),
        SinkMode::CoefficientTree { log_domain, k0 } => (log_domain, k0),
    };
    let args = LeafSinkArgs {
        tile: tiles.as_ptr(),
        out: out.as_mut_ptr(),
        tile_coset_stride: launch.tile_coset_stride as u64,
        out_coset_stride: out_coset_stride as u64,
        log_a: shape.log_a(),
        log_r: shape.r,
        skip_bottom: shape.skip_bottom,
        first_tile,
        log_n: shape.log_n,
        log_domain,
        k0,
        reserved: 0,
    };
    let function = leaf_sink_function(
        shape.columns,
        shape.log_v,
        launch.tree_depth,
        &mode,
        converted,
    )
    .unwrap();
    function.launch(
        &CudaLaunchConfig::basic(launch.grid, 256, stream),
        &LeafSinkArguments::new(args, ctx.descriptor()),
    )
}

// Scratch of `commit_coset`: one batch of suffix tiles, the coset's depth-3 sink nodes and the
// half-size scratch of the layers above them (the coset's prefix output is the monomials' length).
pub fn commit_coset_scratch_lens(plan: &Dispatch, shape: &SuffixShape) -> (usize, usize, usize) {
    let nodes = 1usize
        << (shape.log_n - shape.log_v - sink_tree_depth(&SinkMode::Commit, shape.skip_bottom));
    (plan.tiles_per_batch * shape.tile_len(), nodes, nodes / 2)
}

// The retained tree of coset k (layers skip_bottom..=h, `retained_layer_offset` layout) of the
// coset LDE of `columns` monomial columns of 2^log_n rows: chunked prefix with the coset scale,
// per batch of tiles the suffix micro and the Commit sink, then the node layers up to the top.
#[allow(clippy::too_many_arguments)]
pub fn commit_coset(
    ctx: &DeviceContext,
    monomials: &DeviceSlice<PR>,
    plan: &Dispatch,
    shape: &SuffixShape,
    coset: u32,
    log_domain: u32,
    prefix: &mut DeviceSlice<PR>,
    tiles: &mut DeviceSlice<PR>,
    nodes: &mut DeviceSlice<Digest>,
    node_scratch: &mut DeviceSlice<Digest>,
    retained: &mut DeviceSlice<Digest>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let h = shape.log_n - shape.log_v;
    let sb = shape.skip_bottom;
    assert_eq!(
        (tiles.len(), nodes.len(), node_scratch.len()),
        commit_coset_scratch_lens(plan, shape),
        "commit_coset: scratch lengths"
    );
    assert_eq!(
        retained.len(),
        retained_layer_offset(h, sb, h) + 1,
        "commit_coset: retained length"
    );
    {
        let _r = scoped_range(Some("ab"), "packed.commit.prefix");
        lde_coset_slot(
            ctx,
            monomials,
            prefix,
            shape.columns as usize,
            plan.prefix.as_ref().expect("commit_coset: no prefix plan"),
            ScaleArgs {
                coset: CosetSource::Constant(coset),
                log_domain,
            },
            stream,
        )?;
    }
    let _r = scoped_range(Some("ab"), "packed.commit.suffix");
    let column_len = (shape.columns as usize) << shape.log_n;
    let tiles_per_coset = shape.tiles_per_coset();
    let nodes_len = nodes.len();
    for first in (0..tiles_per_coset).step_by(plan.tiles_per_batch) {
        let count = plan.tiles_per_batch.min(tiles_per_coset - first);
        let batch = &mut tiles[..count * shape.tile_len()];
        launch_suffix_micro(
            ctx,
            prefix,
            column_len,
            batch,
            shape,
            first as u32,
            count as u32,
            1,
            None,
            stream,
        )?;
        launch_sink(
            ctx,
            batch,
            shape,
            first as u32,
            count as u32,
            1,
            SinkMode::Commit,
            nodes,
            nodes_len,
            stream,
        )?;
    }
    let bottom = 1usize << (h - sb);
    reduce_digest_layers(
        nodes,
        sb - sink_tree_depth(&SinkMode::Commit, sb),
        node_scratch,
        &mut retained[..bottom],
        stream,
    )?;
    build_retained_layers(h, sb, 1, retained.len(), retained, stream)
}

// One openings slot of the touched-coset plan: its coset and active flag (one u32 each, device).
#[derive(Clone, Copy)]
pub struct OpenSlot<'a> {
    pub coset: &'a DeviceSlice<u32>,
    pub active: &'a DeviceSlice<u32>,
}

// The openings of one Commit tree: queries (query = leaf << log_lde | physical coset), leaf
// values [query][slot'][column] and paths [query][depth], depth = h + log_lde - cap_log.
pub struct OpenQueries<'a> {
    pub queries: &'a DeviceSlice<u32>,
    pub log_lde: u32,
    pub cap_log: u32,
    pub leaves: &'a mut DeviceSlice<PR>,
    pub paths: &'a mut DeviceSlice<Digest>,
}

pub fn has_open_sink(shape: &SuffixShape) -> bool {
    (8..=10).contains(&shape.skip_bottom)
        && has_leaf_sink(shape, &SinkMode::Commit)
        && leaf_open_function(shape.columns, shape.log_v).is_some()
}

// The open sink of one batch of tiles for one slot: blocks whose depth-skip_bottom subtree holds a
// query of the slot's coset hash their leaves into the slot's depth-3 `nodes` and write the
// queried leaves and path layers 0..2; the others return.
#[allow(clippy::too_many_arguments)]
fn launch_open_sink(
    ctx: &DeviceContext,
    tiles: &DeviceSlice<PR>,
    shape: &SuffixShape,
    first_tile: u32,
    tile_count: u32,
    slot: OpenSlot,
    open: &mut OpenQueries,
    nodes: &mut DeviceSlice<Digest>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let launch = sink_launch(
        ctx.log_max_domain(),
        shape,
        &SinkMode::Commit,
        tiles.len(),
        first_tile,
        tile_count,
        1,
        nodes.len(),
        nodes.len(),
    );
    let h = shape.log_n - shape.log_v;
    let depth = (h + open.log_lde)
        .checked_sub(open.cap_log)
        .expect("leaf open: cap_log above the tree depth");
    let count = open.queries.len();
    assert!(
        has_open_sink(shape),
        "leaf open: no open sink for {shape:?}"
    );
    assert!(
        (1..=1024).contains(&count) && open.log_lde <= 12,
        "leaf open: 1 <= queries <= 1024, log_lde <= 12"
    );
    assert_eq!(
        nodes.len(),
        1 << (h - 3),
        "leaf open: nodes.len() == leaves / 8"
    );
    assert_eq!(
        open.leaves.len(),
        count * ((shape.columns as usize) << shape.log_v),
        "leaf open: leaves.len() == Q * columns * 2^log_v"
    );
    assert_eq!(
        open.paths.len(),
        count * depth as usize,
        "leaf open: paths.len() == Q * depth"
    );
    assert!(
        slot.coset.len() == 1 && slot.active.len() == 1,
        "leaf open: slot coset and active are one u32"
    );
    let args = LeafSinkArgs {
        tile: tiles.as_ptr(),
        out: nodes.as_mut_ptr(),
        tile_coset_stride: launch.tile_coset_stride as u64,
        out_coset_stride: nodes.len() as u64,
        log_a: shape.log_a(),
        log_r: shape.r,
        skip_bottom: shape.skip_bottom,
        first_tile,
        log_n: shape.log_n,
        log_domain: shape.log_n,
        k0: 0,
        reserved: 0,
    };
    let open_args = LeafOpenArgs {
        gate: slot.active.as_ptr(),
        coset: slot.coset.as_ptr(),
        queries: open.queries.as_ptr(),
        leaves: open.leaves.as_mut_ptr(),
        paths: open.paths.as_mut_ptr(),
        count: count as u32,
        log_lde: open.log_lde,
        depth,
        reserved: 0,
    };
    leaf_open_function(shape.columns, shape.log_v)
        .unwrap()
        .launch(
            &CudaLaunchConfig::basic(launch.grid, 256, stream),
            &LeafOpenArguments::new(args, open_args, ctx.descriptor()),
        )
}

// Scratch of `open_coset_slot`: one batch of suffix tiles and the slot's depth-3 nodes (the
// prefix output is the monomials' length).
pub fn open_coset_slot_scratch_lens(plan: &Dispatch, shape: &SuffixShape) -> (usize, usize) {
    (
        plan.tiles_per_batch * shape.tile_len(),
        1usize << (shape.log_n - shape.log_v - 3),
    )
}

// The openings in one slot of the touched-coset plan (every launch gated by the slot's active
// flag): the chunked prefix of the slot's coset, per batch of tiles the suffix micro and the open
// sink, then the path layers above the sink from its depth-3 nodes and the coset's retained tree
// (`retained_all`, `retained_stride` per coset).
#[allow(clippy::too_many_arguments)]
pub fn open_coset_slot(
    ctx: &DeviceContext,
    monomials: &DeviceSlice<PR>,
    plan: &Dispatch,
    shape: &SuffixShape,
    slot: OpenSlot,
    log_domain: u32,
    retained_all: &DeviceSlice<Digest>,
    retained_stride: usize,
    open: &mut OpenQueries,
    prefix: &mut DeviceSlice<PR>,
    tiles: &mut DeviceSlice<PR>,
    nodes: &mut DeviceSlice<Digest>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(
        (tiles.len(), nodes.len()),
        open_coset_slot_scratch_lens(plan, shape),
        "open_coset_slot: scratch lengths"
    );
    open_paths_depth(
        nodes.len(),
        retained_all.len(),
        retained_stride,
        open.log_lde,
        shape.log_n - shape.log_v,
        shape.skip_bottom,
        open.cap_log,
        open.queries.len(),
        open.paths.len(),
    );
    lde_coset_slot(
        ctx,
        monomials,
        prefix,
        shape.columns as usize,
        plan.prefix
            .as_ref()
            .expect("open_coset_slot: no prefix plan"),
        ScaleArgs {
            coset: CosetSource::Slot {
                coset: slot.coset,
                active: slot.active,
            },
            log_domain,
        },
        stream,
    )?;
    let column_len = (shape.columns as usize) << shape.log_n;
    let tiles_per_coset = shape.tiles_per_coset();
    for first in (0..tiles_per_coset).step_by(plan.tiles_per_batch) {
        let count = plan.tiles_per_batch.min(tiles_per_coset - first);
        let batch = &mut tiles[..count * shape.tile_len()];
        launch_suffix_micro(
            ctx,
            prefix,
            column_len,
            batch,
            shape,
            first as u32,
            count as u32,
            1,
            Some(slot.active),
            stream,
        )?;
        launch_open_sink(
            ctx,
            batch,
            shape,
            first as u32,
            count as u32,
            slot,
            open,
            nodes,
            stream,
        )?;
    }
    launch_open_paths(
        nodes,
        retained_all,
        retained_stride,
        slot.coset,
        slot.active,
        open.queries,
        open.log_lde,
        shape.log_n - shape.log_v,
        shape.skip_bottom,
        open.cap_log,
        open.paths,
        stream,
    )
}

// Upper bound of one suffix batch of a coefficient tree (cosets x tiles), the L2-resident tile set.
pub const COEFFICIENT_BATCH_BYTES: usize = 32 << 20;

// (cosets, tiles per coset) of one suffix batch of a coefficient tree: whole cosets while a coset's
// tiles fit the batch, else one coset and as many tiles as fit.
pub fn coefficient_batch(shape: &SuffixShape, cosets: usize) -> (usize, usize) {
    let tile_bytes = shape.tile_len() * size_of::<PR>();
    let tiles = shape.tiles_per_coset();
    let coset_bytes = tiles * tile_bytes;
    if coset_bytes <= COEFFICIENT_BATCH_BYTES {
        (
            (COEFFICIENT_BATCH_BYTES / coset_bytes).min(cosets).max(1),
            tiles,
        )
    } else {
        (1, (COEFFICIENT_BATCH_BYTES / tile_bytes).clamp(1, tiles))
    }
}

pub fn coefficient_tiles_len(shape: &SuffixShape, cosets: usize) -> usize {
    let (batch_cosets, batch_tiles) = coefficient_batch(shape, cosets);
    batch_cosets * batch_tiles * shape.tile_len()
}

// The retained trees (layers skip_bottom..=h, `retained_per_coset` apart) of cosets k0..k0 + cosets
// of a coefficient-tree oracle (one monomial column, codeword 2^log_domain): the batched chunked
// prefix of all the cosets into `prefix` (cosets x 2^log_n), then per suffix batch of
// `coefficient_batch` the suffix micro and the CoefficientTree sink, then the layers above.
#[allow(clippy::too_many_arguments)]
pub fn commit_coefficient_cosets(
    ctx: &DeviceContext,
    monomials: &DeviceSlice<PR>,
    plan: &Dispatch,
    shape: &SuffixShape,
    log_domain: u32,
    k0: u32,
    cosets: usize,
    prefix: &mut DeviceSlice<PR>,
    tiles: &mut DeviceSlice<PR>,
    retained: &mut DeviceSlice<Digest>,
    retained_per_coset: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    let rows = 1usize << shape.log_n;
    let h = shape.log_n - shape.log_v;
    assert_eq!(
        shape.columns, 1,
        "commit_coefficient_cosets: one monomial column"
    );
    assert_eq!(
        prefix.len(),
        cosets * rows,
        "commit_coefficient_cosets: prefix length"
    );
    assert_eq!(
        tiles.len(),
        coefficient_tiles_len(shape, cosets),
        "commit_coefficient_cosets: tiles length"
    );
    assert_eq!(
        retained_per_coset,
        retained_layer_offset(h, shape.skip_bottom, h) + 1,
        "commit_coefficient_cosets: retained per coset"
    );
    assert_eq!(
        retained.len(),
        cosets * retained_per_coset,
        "commit_coefficient_cosets: retained length"
    );
    {
        let _r = scoped_range(Some("ab"), "whir.commit.prefix");
        lde_coset_slot(
            ctx,
            monomials,
            prefix,
            cosets,
            plan.prefix
                .as_ref()
                .expect("commit_coefficient_cosets: no prefix plan"),
            ScaleArgs {
                coset: CosetSource::Batched { k0 },
                log_domain,
            },
            stream,
        )?;
    }
    let _r = scoped_range(Some("ab"), "whir.commit.suffix");
    let (batch_cosets, batch_tiles) = coefficient_batch(shape, cosets);
    let tiles_per_coset = shape.tiles_per_coset();
    for first_coset in (0..cosets).step_by(batch_cosets) {
        let coset_count = batch_cosets.min(cosets - first_coset);
        for first_tile in (0..tiles_per_coset).step_by(batch_tiles) {
            let tile_count = batch_tiles.min(tiles_per_coset - first_tile);
            let batch = &mut tiles[..coset_count * tile_count * shape.tile_len()];
            launch_suffix_micro(
                ctx,
                &prefix[first_coset * rows..],
                rows,
                batch,
                shape,
                first_tile as u32,
                tile_count as u32,
                coset_count as u32,
                None,
                stream,
            )?;
            launch_sink(
                ctx,
                batch,
                shape,
                first_tile as u32,
                tile_count as u32,
                coset_count as u32,
                SinkMode::CoefficientTree {
                    log_domain,
                    k0: k0 + first_coset as u32,
                },
                &mut retained[first_coset * retained_per_coset..],
                retained_per_coset,
                stream,
            )?;
        }
    }
    build_retained_layers(
        h,
        shape.skip_bottom,
        cosets as u32,
        retained_per_coset,
        retained,
        stream,
    )
}

cuda_kernel_signature_arguments_and_function!(
    pub(crate) ResidueSink,
    monomials: *const PR,
    leaves: *mut Digest,
    k0: u32,
    cosets: u32,
    log_domain: u32,
    descriptor: TwiddleDescriptor,
);
macro_rules! residue_sink_kernel {
    ($name:ident) => {
        cuda_kernel_declaration!(
            $name(
                monomials: *const PR,
                leaves: *mut Digest,
                k0: u32,
                cosets: u32,
                log_domain: u32,
                descriptor: TwiddleDescriptor,
            )
        );
    };
}
residue_sink_kernel!(ab_pr_residue_sink_8_4_kernel);
residue_sink_kernel!(ab_pr_residue_sink_11_3_kernel);
residue_sink_kernel!(ab_pr_residue_sink_11_4_kernel);

// The residue-sink kernel and its cosets per block.
fn residue_sink_function(
    log_n: u32,
    log_v: u32,
    skip_bottom: u32,
) -> Option<(ResidueSinkFunction, u32)> {
    let (function, cosets): (ResidueSinkSignature, u32) = match (log_n, log_v, skip_bottom) {
        (8, 4, 4) => (ab_pr_residue_sink_8_4_kernel, 8),
        (11, 3, 5) => (ab_pr_residue_sink_11_3_kernel, 1),
        (11, 4, 5) => (ab_pr_residue_sink_11_4_kernel, 1),
        _ => return None,
    };
    Some((ResidueSinkFunction(function), cosets))
}

pub fn has_residue_sink(log_n: u32, log_v: u32, skip_bottom: u32) -> bool {
    residue_sink_function(log_n, log_v, skip_bottom).is_some()
}

// Leaf digests per residue chunk: a chunk's leaves and their first node layer stay L2-resident.
const RESIDUE_CHUNK_LEAVES: usize = 1 << 20;

fn residue_chunk_cosets(log_n: u32, log_v: u32, skip_bottom: u32, cosets: usize) -> usize {
    let Some((_, cosets_per_block)) = residue_sink_function(log_n, log_v, skip_bottom) else {
        panic!(
            "residue sink: no kernel for log_n {log_n}, log_v {log_v}, skip_bottom {skip_bottom}"
        )
    };
    cosets.min((RESIDUE_CHUNK_LEAVES >> (log_n - log_v)).max(cosets_per_block as usize))
}

// Digests of scratch `commit_residue_cosets` needs for `cosets` cosets: a chunk's leaves and, when
// skip_bottom >= 2, half as many again.
pub fn residue_scratch_len(log_n: u32, log_v: u32, skip_bottom: u32, cosets: usize) -> usize {
    let leaves = residue_chunk_cosets(log_n, log_v, skip_bottom, cosets)
        .checked_mul(1 << (log_n - log_v))
        .expect("residue sink: scratch length overflow");
    if skip_bottom >= 2 {
        leaves + leaves / 2
    } else {
        leaves
    }
}

// The retained trees (layers skip_bottom..=h, `retained_per_coset` apart) of cosets k0..k0 + cosets
// of a small coefficient-tree oracle (one monomial column of 2^log_n, codeword 2^log_domain),
// nothing materialized: with f = sum_r X^r P_r(X^V), each leaf's slots are P_r at its point, so a
// block evaluates the V residue polynomials on whole cosets in shared memory and hashes the leaves;
// per L2-sized chunk, node launches build the layers above.
#[allow(clippy::too_many_arguments)]
pub fn commit_residue_cosets(
    ctx: &DeviceContext,
    monomials: &DeviceSlice<PR>,
    log_n: u32,
    log_v: u32,
    skip_bottom: u32,
    log_domain: u32,
    k0: u32,
    cosets: usize,
    scratch: &mut DeviceSlice<Digest>,
    retained: &mut DeviceSlice<Digest>,
    retained_per_coset: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    let Some((function, cosets_per_block)) = residue_sink_function(log_n, log_v, skip_bottom)
    else {
        panic!(
            "residue sink: no kernel for log_n {log_n}, log_v {log_v}, skip_bottom {skip_bottom}"
        )
    };
    let h = log_n - log_v;
    assert_eq!(
        monomials.len(),
        1 << log_n,
        "residue sink: monomials length"
    );
    assert!(
        log_n <= log_domain && log_domain <= ctx.log_max_domain(),
        "residue sink: log_domain {log_domain} outside {log_n}..={}",
        ctx.log_max_domain()
    );
    assert!(cosets >= 1, "residue sink: no cosets");
    assert!(
        u64::from(k0) + cosets as u64 <= 1u64 << (log_domain - log_n),
        "residue sink: cosets out of range"
    );
    assert_eq!(
        retained_per_coset,
        retained_layer_offset(h, skip_bottom, h) + 1,
        "residue sink: retained per coset"
    );
    assert_eq!(
        Some(retained.len()),
        cosets.checked_mul(retained_per_coset),
        "residue sink: retained length"
    );
    assert_eq!(
        scratch.len(),
        residue_scratch_len(log_n, log_v, skip_bottom, cosets),
        "residue sink: scratch length"
    );
    assert!(
        (scratch.as_ptr() as usize).is_multiple_of(16),
        "residue sink: scratch must be 16-byte aligned"
    );
    let chunk = residue_chunk_cosets(log_n, log_v, skip_bottom, cosets);
    let (leaves, rest) = scratch.split_at_mut(chunk << h);
    for c0 in (0..cosets).step_by(chunk) {
        let count = chunk.min(cosets - c0);
        let leaves = &mut leaves[..count << h];
        let grid = u32::try_from(count.div_ceil(cosets_per_block as usize))
            .ok()
            .filter(|&grid| grid < 1 << 31)
            .expect("residue sink: grid.x overflow");
        function.launch(
            &CudaLaunchConfig::basic(grid, 256, stream),
            &ResidueSinkArguments::new(
                monomials.as_ptr(),
                leaves.as_mut_ptr(),
                k0 + c0 as u32,
                count as u32,
                log_domain,
                ctx.descriptor(),
            ),
        )?;
        build_retained_bottom_from_nodes(
            leaves,
            0,
            h,
            skip_bottom,
            count as u32,
            rest,
            &mut retained[c0 * retained_per_coset..(c0 + count) * retained_per_coset],
            retained_per_coset,
            stream,
        )?;
    }
    build_retained_layers(
        h,
        skip_bottom,
        cosets as u32,
        retained_per_coset,
        retained,
        stream,
    )
}
