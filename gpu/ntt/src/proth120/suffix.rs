use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use gpu_core::primitives::field::PR;

use super::context::{DeviceContext, TwiddleDescriptor};
use super::prefix::Dispatch;
use super::{validate_disjoint, validate_slice};

#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct SuffixTileArgs {
    prefix: *const PR,
    tile: *mut PR,
    prefix_column_stride: u64,
    prefix_coset_stride: u64,
    tile_coset_stride: u64,
    log_a: u32,
    skip_bottom: u32,
    first_tile: u32,
    columns: u32,
}

const _: () = assert!(core::mem::size_of::<SuffixTileArgs>() == 56);

cuda_kernel_signature_arguments_and_function!(
    pub(crate) SuffixMicro,
    args: SuffixTileArgs, descriptor: TwiddleDescriptor,
);
macro_rules! suffix_micro_kernel {
    ($name:ident) => {
        cuda_kernel_declaration!($name(args: SuffixTileArgs, descriptor: TwiddleDescriptor,));
    };
}
suffix_micro_kernel!(ab_pr_dit_suffix_micro_6_1_kernel);
suffix_micro_kernel!(ab_pr_dit_suffix_micro_6_2_kernel);
suffix_micro_kernel!(ab_pr_dit_suffix_micro_6_3_kernel);
suffix_micro_kernel!(ab_pr_dit_suffix_micro_6_4_kernel);
suffix_micro_kernel!(ab_pr_dit_suffix_micro_7_1_kernel);
suffix_micro_kernel!(ab_pr_dit_suffix_micro_7_2_kernel);
suffix_micro_kernel!(ab_pr_dit_suffix_micro_7_3_kernel);
suffix_micro_kernel!(ab_pr_dit_suffix_micro_7_4_kernel);
suffix_micro_kernel!(ab_pr_dit_suffix_micro_8_1_kernel);
suffix_micro_kernel!(ab_pr_dit_suffix_micro_8_2_kernel);
suffix_micro_kernel!(ab_pr_dit_suffix_micro_8_3_kernel);
suffix_micro_kernel!(ab_pr_dit_suffix_micro_8_4_kernel);

fn suffix_micro_function(r: u32, log_v: u32) -> SuffixMicroFunction {
    SuffixMicroFunction(match (r, log_v) {
        (6, 1) => ab_pr_dit_suffix_micro_6_1_kernel,
        (6, 2) => ab_pr_dit_suffix_micro_6_2_kernel,
        (6, 3) => ab_pr_dit_suffix_micro_6_3_kernel,
        (6, 4) => ab_pr_dit_suffix_micro_6_4_kernel,
        (7, 1) => ab_pr_dit_suffix_micro_7_1_kernel,
        (7, 2) => ab_pr_dit_suffix_micro_7_2_kernel,
        (7, 3) => ab_pr_dit_suffix_micro_7_3_kernel,
        (7, 4) => ab_pr_dit_suffix_micro_7_4_kernel,
        (8, 1) => ab_pr_dit_suffix_micro_8_1_kernel,
        (8, 2) => ab_pr_dit_suffix_micro_8_2_kernel,
        (8, 3) => ab_pr_dit_suffix_micro_8_3_kernel,
        (8, 4) => ab_pr_dit_suffix_micro_8_4_kernel,
        _ => panic!("Proth120 suffix: no micro kernel for r {r}, log_v {log_v}"),
    })
}

// Suffix geometry of one packed or WHIR oracle (spec section 2): after the a = log_n - r prefix
// stages, component g is the run of 2^r values at prefix block bitrev_a(g); tile G holds components
// [G * 2^sb, (G + 1) * 2^sb) of every column, i.e. 2^(r - v) complete subtrees of 2^sb leaves.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SuffixShape {
    pub log_n: u32,
    pub r: u32,
    pub log_v: u32,
    pub skip_bottom: u32,
    pub columns: u32,
}

impl SuffixShape {
    pub fn new(
        dispatch: &Dispatch,
        log_n: u32,
        log_v: u32,
        skip_bottom: u32,
        columns: u32,
    ) -> Self {
        assert!(
            !dispatch.small,
            "Proth120 suffix: Small shapes have no suffix tiles"
        );
        let shape = Self {
            log_n,
            r: dispatch.r,
            log_v,
            skip_bottom,
            columns,
        };
        assert_eq!(shape.tiles_per_coset(), dispatch.tiles_per_coset);
        shape
    }

    pub fn log_a(&self) -> u32 {
        self.log_n - self.r
    }

    pub fn tiles_per_coset(&self) -> usize {
        1 << (self.log_a() - self.skip_bottom)
    }

    pub fn subtrees_per_tile(&self) -> usize {
        1 << (self.r - self.log_v)
    }

    // Elements of one tile of all columns: [column][f_lo][w][2^v].
    pub fn tile_len(&self) -> usize {
        (self.columns as usize) << (self.skip_bottom + self.r)
    }
}

const COMPONENT_BLOCK_VALUES: u32 = 1 << 10;
const MAX_GRID_YZ: u32 = 1 << 16;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct SuffixLaunch {
    pub(crate) grid: (u32, u32, u32),
    pub(crate) tile_coset_stride: usize,
}

// Host checks of one suffix micro launch, every span in checked arithmetic.
#[allow(clippy::too_many_arguments)]
pub(crate) fn suffix_launch(
    log_max_domain: u32,
    shape: &SuffixShape,
    prefix_len: usize,
    prefix_coset_stride: usize,
    tiles_len: usize,
    first_tile: u32,
    tile_count: u32,
    cosets: u32,
) -> SuffixLaunch {
    assert!(
        (6..=8).contains(&shape.r) && (1..=4).contains(&shape.log_v) && shape.log_v < shape.r,
        "Proth120 suffix: no micro kernel for r {}, log_v {}",
        shape.r,
        shape.log_v
    );
    assert!(
        shape.log_n <= log_max_domain,
        "Proth120 suffix: log_n {} exceeds context log_max_domain {log_max_domain}",
        shape.log_n
    );
    assert!(
        shape.log_n >= shape.r && shape.log_a() >= shape.skip_bottom,
        "Proth120 suffix: skip_bottom {} above log_a",
        shape.skip_bottom
    );
    let components_per_block = COMPONENT_BLOCK_VALUES >> shape.r;
    assert!(
        shape.skip_bottom < u32::BITS && (1u32 << shape.skip_bottom) >= components_per_block,
        "Proth120 suffix: skip_bottom below a block of components"
    );
    assert!(
        (1..MAX_GRID_YZ).contains(&shape.columns) && (1..MAX_GRID_YZ).contains(&cosets),
        "Proth120 suffix: columns and cosets must be in 1..2^16"
    );
    assert!(
        tile_count >= 1
            && u64::from(first_tile) + u64::from(tile_count) <= shape.tiles_per_coset() as u64,
        "Proth120 suffix: tiles out of range"
    );
    let overflow = || panic!("Proth120 suffix: span overflow");
    let column_len = (shape.columns as usize)
        .checked_mul(1usize << shape.log_n)
        .unwrap_or_else(overflow);
    assert!(
        cosets == 1 || prefix_coset_stride >= column_len,
        "Proth120 suffix: prefix coset stride below the columns of a coset"
    );
    let prefix_span = (cosets as usize - 1)
        .checked_mul(prefix_coset_stride)
        .and_then(|offset| offset.checked_add(column_len))
        .unwrap_or_else(overflow);
    assert!(
        prefix_len >= prefix_span,
        "Proth120 suffix: prefix shorter than its coset span"
    );
    let tile_coset_stride = (tile_count as usize)
        .checked_mul(shape.tile_len())
        .unwrap_or_else(overflow);
    let tiles_span = (cosets as usize)
        .checked_mul(tile_coset_stride)
        .unwrap_or_else(overflow);
    assert_eq!(tiles_len, tiles_span, "Proth120 suffix: tiles length");
    let blocks = ((1u32 << shape.skip_bottom) / components_per_block)
        .checked_mul(tile_count)
        .filter(|&blocks| blocks < 1 << 31)
        .unwrap_or_else(|| panic!("Proth120 suffix: grid.x overflow"));
    SuffixLaunch {
        grid: (blocks, shape.columns, cosets),
        tile_coset_stride,
    }
}

// The suffix micro of tiles [first_tile, first_tile + tiles) of `cosets` coset prefixes
// (prefix coset c at c * prefix_coset_stride, columns at stride 2^log_n) into `tiles` laid out
// [coset][tile][column][f_lo][w][2^v], the coset stride being tiles * tile_len.
#[allow(clippy::too_many_arguments)]
pub fn launch_suffix_micro(
    ctx: &DeviceContext,
    prefix: &DeviceSlice<PR>,
    prefix_coset_stride: usize,
    tiles: &mut DeviceSlice<PR>,
    shape: &SuffixShape,
    first_tile: u32,
    tile_count: u32,
    cosets: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let launch = suffix_launch(
        ctx.log_max_domain(),
        shape,
        prefix.len(),
        prefix_coset_stride,
        tiles.len(),
        first_tile,
        tile_count,
        cosets,
    );
    let prefix_range = validate_slice(prefix, "Proth120 suffix prefix");
    let tiles_range = validate_slice(tiles, "Proth120 suffix tiles");
    validate_disjoint(
        &prefix_range,
        &tiles_range,
        "Proth120 suffix: prefix/tiles overlap",
    );
    let config = CudaLaunchConfig::basic(launch.grid, 256, stream);
    let args = SuffixTileArgs {
        prefix: prefix.as_ptr(),
        tile: tiles.as_mut_ptr(),
        prefix_column_stride: 1u64 << shape.log_n,
        prefix_coset_stride: prefix_coset_stride as u64,
        tile_coset_stride: launch.tile_coset_stride as u64,
        log_a: shape.log_a(),
        skip_bottom: shape.skip_bottom,
        first_tile,
        columns: shape.columns,
    };
    suffix_micro_function(shape.r, shape.log_v)
        .launch(&config, &SuffixMicroArguments::new(args, ctx.descriptor()))
}
