use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use gpu_core::primitives::field::PR;
use gpu_hash::keccak256::Digest;
use gpu_ntt::proth120::{DeviceContext, SuffixShape, TwiddleDescriptor};

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

fn leaf_sink_function(
    columns: u32,
    log_v: u32,
    tree_depth: u32,
    mode: &SinkMode,
) -> Option<LeafSinkFunction> {
    let commit = matches!(mode, SinkMode::Commit);
    Some(LeafSinkFunction(
        match (columns, log_v, tree_depth, commit) {
            (1, 2, 3, true) => ab_pr_leaf_sink_1_2_3_commit_kernel,
            (2, 1, 3, true) => ab_pr_leaf_sink_2_1_3_commit_kernel,
            (7, 2, 3, true) => ab_pr_leaf_sink_7_2_3_commit_kernel,
            (13, 1, 3, true) => ab_pr_leaf_sink_13_1_3_commit_kernel,
            (1, 3, 5, false) => ab_pr_leaf_sink_1_3_5_coefficient_tree_kernel,
            (1, 4, 5, false) => ab_pr_leaf_sink_1_4_5_coefficient_tree_kernel,
            _ => return None,
        },
    ))
}

pub fn has_leaf_sink(shape: &SuffixShape, mode: &SinkMode) -> bool {
    leaf_sink_function(
        shape.columns,
        shape.log_v,
        sink_tree_depth(mode, shape.skip_bottom),
        mode,
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
        leaf_sink_function(shape.columns, shape.log_v, tree_depth, mode).is_some(),
        "leaf sink: no kernel for {} columns, log_v {}, skip_bottom {}, {mode:?}",
        shape.columns,
        shape.log_v,
        shape.skip_bottom
    );
    assert!(
        match mode {
            SinkMode::Commit => (8..=10).contains(&shape.skip_bottom),
            SinkMode::CoefficientTree { .. } => shape.skip_bottom == 5,
        },
        "leaf sink: skip_bottom {} outside 8..=10 (Commit) / 5 (CoefficientTree)",
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
    let function =
        leaf_sink_function(shape.columns, shape.log_v, launch.tree_depth, &mode).unwrap();
    function.launch(
        &CudaLaunchConfig::basic(launch.grid, 256, stream),
        &LeafSinkArguments::new(args, ctx.descriptor()),
    )
}
