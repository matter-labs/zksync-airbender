use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use gpu_core::primitives::device_structures::{MutPtrAndStride, PtrAndStride};
use gpu_core::primitives::field::PR;

use super::context::{DeviceContext, TwiddleDescriptor};
use super::lde::{
    naturalize, set_max_dynamic_smem, ChunkMap, DitPolicy, TransformPass, TransformPolicy,
    MAX_COLUMNS_PER_LAUNCH,
};
use super::{validate_context_log, validate_disjoint, validate_slice};

#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct CosetScale {
    coset: *const u32,
    k0: u32,
    batched: u32,
    log_domain: u32,
    reserved: u32,
}

const _: () = {
    assert!(core::mem::size_of::<CosetScale>() == 24);
    assert!(core::mem::offset_of!(CosetScale, k0) == 8);
    assert!(core::mem::offset_of!(CosetScale, log_domain) == 16);
};

cuda_kernel_signature_arguments_and_function!(
    pub(crate) DitScaled,
    inputs: PtrAndStride<PR>, outputs: MutPtrAndStride<PR>, descriptor: TwiddleDescriptor,
    log_n: u32, start_stage: u32, map: ChunkMap, scale: CosetScale,
);
macro_rules! dit_scaled_kernel {
    ($name:ident) => {
        cuda_kernel_declaration!($name(
            inputs: PtrAndStride<PR>, outputs: MutPtrAndStride<PR>, descriptor: TwiddleDescriptor,
            log_n: u32, start_stage: u32, map: ChunkMap, scale: CosetScale,
        ));
    };
}
dit_scaled_kernel!(ab_pr_dit_nonfinal_5_stages_scaled_kernel);
dit_scaled_kernel!(ab_pr_dit_nonfinal_6_stages_scaled_kernel);
dit_scaled_kernel!(ab_pr_dit_nonfinal_7_stages_scaled_kernel);
dit_scaled_kernel!(ab_pr_dit_nonfinal_8_stages_scaled_kernel);
dit_scaled_kernel!(ab_pr_dit_nonfinal_5_stages_narrow_scaled_kernel);
dit_scaled_kernel!(ab_pr_dit_nonfinal_6_stages_narrow_scaled_kernel);
dit_scaled_kernel!(ab_pr_dit_nonfinal_7_stages_narrow_scaled_kernel);

fn dit_scaled_function(pass: &PrefixPass) -> DitScaledFunction {
    DitScaledFunction(match (pass.stages, pass.narrow) {
        (5, false) => ab_pr_dit_nonfinal_5_stages_scaled_kernel,
        (6, false) => ab_pr_dit_nonfinal_6_stages_scaled_kernel,
        (7, false) => ab_pr_dit_nonfinal_7_stages_scaled_kernel,
        (8, false) => ab_pr_dit_nonfinal_8_stages_scaled_kernel,
        (5, true) => ab_pr_dit_nonfinal_5_stages_narrow_scaled_kernel,
        (6, true) => ab_pr_dit_nonfinal_6_stages_narrow_scaled_kernel,
        (7, true) => ab_pr_dit_nonfinal_7_stages_narrow_scaled_kernel,
        _ => panic!("Proth120 prefix: no scaled first pass for {pass:?}"),
    })
}

// Logical coset k of the scale offset_k = w_D^k: by value, from device memory (openings), or
// k0 + the launch's column index when the columns of a launch are consecutive cosets.
#[derive(Clone, Copy)]
pub enum CosetSource<'a> {
    Constant(u32),
    Device(&'a DeviceSlice<u32>),
    Batched { k0: u32 },
}

#[derive(Clone, Copy)]
pub struct ScaleArgs<'a> {
    pub coset: CosetSource<'a>,
    pub log_domain: u32,
}

#[derive(Clone, Copy)]
pub(crate) struct FirstPassScale<'a> {
    pub(crate) descriptor: TwiddleDescriptor,
    pub(crate) scale: ScaleArgs<'a>,
}

impl ScaleArgs<'_> {
    fn native(&self, column: usize) -> CosetScale {
        let (coset, k0, batched) = match self.coset {
            CosetSource::Constant(k) => (std::ptr::null(), k, 0),
            CosetSource::Device(slot) => {
                assert_eq!(
                    slot.len(),
                    1,
                    "Proth120 prefix: device coset must be one u32"
                );
                (slot.as_ptr(), 0, 0)
            }
            CosetSource::Batched { k0 } => (
                std::ptr::null(),
                k0.checked_add(u32::try_from(column).unwrap())
                    .expect("Proth120 prefix: batched coset overflow"),
                1,
            ),
        };
        CosetScale {
            coset,
            k0,
            batched,
            log_domain: self.log_domain,
            reserved: 0,
        }
    }
}

pub(crate) const MAX_CHUNK_BYTES: usize = 32 << 20;
pub(crate) const MIN_CHUNK_BYTES: usize = 1 << 20;
pub(crate) const MAX_TILE_BYTES: usize = 32 << 20;
pub(crate) const MAX_LOG_MAX_DOMAIN: u32 = 33;

// Half of the device L2: the working set at which the BabyBear NTT's measured per-NTT cost
// minimum landed on both the 96 MiB and the 128 MiB parts (`ntt::strategy`).
pub fn l2_working_set_budget(l2_cache_size_bytes: usize) -> usize {
    l2_cache_size_bytes / 2
}

const LOG_TILE_LANES: u32 = 3;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct PrefixPass {
    pub(crate) start: u32,
    pub(crate) stages: u32,
    pub(crate) narrow: bool,
}

impl PrefixPass {
    pub(crate) fn tile_bits(&self) -> u32 {
        if self.narrow {
            self.stages
        } else {
            8
        }
    }

    pub(crate) fn transform_pass(&self) -> TransformPass {
        if self.narrow {
            TransformPass::NonfinalNarrow(self.stages)
        } else {
            TransformPass::Nonfinal(self.stages)
        }
    }

    pub(crate) fn threads(&self) -> u32 {
        1 << (self.tile_bits() + LOG_TILE_LANES - 2)
    }

    pub(crate) fn y_bits(&self, log_n: u32) -> u32 {
        log_n - self.start - self.tile_bits() - LOG_TILE_LANES
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChunkPlan {
    pub(crate) log_n: u32,
    pub(crate) cols_per_chunk: usize,
    pub(crate) strips: u32,
    pub(crate) strip_blocks: u32,
    pub(crate) strip_domain_bits: u32,
    pub(crate) passes: Vec<PrefixPass>,
}

impl ChunkPlan {
    pub fn log_n(&self) -> u32 {
        self.log_n
    }

    pub fn stages(&self) -> u32 {
        self.passes.iter().map(|p| p.stages).sum()
    }

    pub(crate) fn chunk_bytes(&self) -> usize {
        let column = size_of::<PR>() << self.log_n;
        if self.strips == 1 {
            column * self.cols_per_chunk
        } else {
            (column >> self.strip_domain_bits) * self.strip_blocks as usize
        }
    }

    pub(crate) fn map(&self, strip: u32) -> ChunkMap {
        ChunkMap {
            strip_base: strip * self.strip_blocks,
            strip_blocks: self.strip_blocks,
            strip_domain_bits: self.strip_domain_bits,
        }
    }

    pub(crate) fn grid_y(&self, pass: &PrefixPass) -> u32 {
        (1u32 << (pass.y_bits(self.log_n) - self.strip_domain_bits)) * self.strip_blocks
    }

    #[cfg(test)]
    pub(crate) fn launches_per_column_group(&self) -> usize {
        self.passes.len() * self.strips as usize
    }
}

// Groups of prefix stages from {5, 6, 7, 8}: one pass when it fits, else two passes with the
// largest first group, else three passes with a narrow last 5 and the first two balanced.
pub(crate) fn prefix_groups(stages: u32) -> Option<Vec<(u32, bool)>> {
    match stages {
        5..=8 => Some(vec![(stages, false)]),
        10..=16 => {
            let first = (stages - 5).min(8);
            let last = stages - first;
            Some(vec![(first, false), (last, last == 5)])
        }
        17..=21 => {
            let rest = stages - 5;
            Some(vec![
                (rest.div_ceil(2), false),
                (rest / 2, false),
                (5, true),
            ])
        }
        _ => None,
    }
}

// The same groups with every pass of at most 7 stages narrow (2^stages tiles per block).
pub(crate) fn narrow_groups(groups: &[(u32, bool)]) -> Vec<(u32, bool)> {
    groups
        .iter()
        .map(|&(stages, _)| (stages, stages <= 7))
        .collect()
}

pub(crate) fn chunk_plan(
    log_n: u32,
    groups: &[(u32, bool)],
    chunk_bytes: usize,
) -> Option<ChunkPlan> {
    assert!(
        chunk_bytes.is_power_of_two(),
        "Proth120 prefix: chunk bytes must be a power of two"
    );
    let mut start = 0;
    let mut passes = Vec::with_capacity(groups.len());
    for &(stages, narrow) in groups {
        if !(5..=8).contains(&stages) || narrow && stages == 8 {
            return None;
        }
        let pass = PrefixPass {
            start,
            stages,
            narrow,
        };
        if log_n < start + pass.tile_bits() + LOG_TILE_LANES {
            return None;
        }
        passes.push(pass);
        start += stages;
    }
    let last = *passes.last()?;
    if start >= log_n {
        return None;
    }
    let column = size_of::<PR>() << log_n;
    if column <= chunk_bytes {
        return Some(ChunkPlan {
            log_n,
            cols_per_chunk: chunk_bytes / column,
            strips: 1,
            strip_blocks: 1,
            strip_domain_bits: 0,
            passes,
        });
    }
    let strip_domain_bits = last.y_bits(log_n);
    let per_strip = column >> strip_domain_bits;
    if per_strip > chunk_bytes {
        return None;
    }
    let strip_blocks = (chunk_bytes / per_strip) as u32;
    Some(ChunkPlan {
        log_n,
        cols_per_chunk: 1,
        strips: (1u32 << strip_domain_bits) / strip_blocks,
        strip_blocks,
        strip_domain_bits,
        passes,
    })
}

// Per-coset stage split of a packed or WHIR oracle: the L2-chunked prefix of a = log_n - r
// stages, then suffix tiles of 2^skip_bottom components x 2^r values x all columns, consumed
// `tiles_per_batch` at a time (Small: one block per column when log_n <= 12). Chunk and batch
// sizes follow from the device L2 working-set budget; when the budget cannot hold them the same
// kernels run with smaller or no L2 residency (`*_resident == false`), with identical output.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Dispatch {
    pub small: bool,
    pub r: u32,
    pub tile_bytes: usize,
    pub tiles_per_coset: usize,
    pub tiles_per_batch: usize,
    pub prefix: Option<ChunkPlan>,
    pub prefix_working_set: usize,
    pub suffix_working_set: usize,
    pub prefix_resident: bool,
    pub suffix_resident: bool,
    pub l2_budget: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DispatchError {
    Unsupported,
}

pub(crate) fn twiddle_bytes(log_max_domain: u32) -> usize {
    let low = log_max_domain.div_ceil(2);
    2 * size_of::<PR>() * ((1 << low) + (1 << (log_max_domain - low)))
}

// Depth-8 sub-roots of one coset, kept by base/setup commits (skip_bottom > 8).
pub(crate) fn subroot_bytes(log_n: u32, log_v: u32, skip_bottom: u32) -> usize {
    if skip_bottom > 8 {
        32 << (log_n - log_v - 8)
    } else {
        0
    }
}

fn dispatch_with_budget(
    log_n: u32,
    columns: usize,
    log_v: u32,
    skip_bottom: u32,
    l2_budget: usize,
) -> Option<Dispatch> {
    if log_n <= 12 {
        return Some(Dispatch {
            small: true,
            r: log_n,
            tile_bytes: columns.checked_mul(size_of::<PR>() << log_n)?,
            tiles_per_coset: 1,
            tiles_per_batch: 1,
            prefix: None,
            prefix_working_set: 0,
            suffix_working_set: 0,
            prefix_resident: true,
            suffix_resident: true,
            l2_budget,
        });
    }
    let fixed = twiddle_bytes(MAX_LOG_MAX_DOMAIN) + subroot_bytes(log_n, log_v, skip_bottom);
    for r in [8, 7, 6] {
        let a = log_n - r;
        let tile_bytes = columns.checked_mul(size_of::<PR>() << (skip_bottom + r))?;
        if a < skip_bottom || r < log_v || tile_bytes > MAX_TILE_BYTES {
            continue;
        }
        let Some(groups) = prefix_groups(a) else {
            continue;
        };
        let tiles_per_coset = 1usize << (a - skip_bottom);
        let Some(tiles_per_batch) = (1..=tiles_per_coset.min(2))
            .rev()
            .find(|t| t * tile_bytes + fixed <= l2_budget)
        else {
            continue;
        };
        let plan = (MIN_CHUNK_BYTES.ilog2()..=MAX_CHUNK_BYTES.ilog2())
            .rev()
            .filter_map(|log_chunk| chunk_plan(log_n, &groups, 1 << log_chunk))
            .find(|plan| 2 * plan.chunk_bytes() + fixed <= l2_budget);
        let Some(plan) = plan else {
            continue;
        };
        return Some(Dispatch {
            small: false,
            r,
            tile_bytes,
            tiles_per_coset,
            tiles_per_batch,
            prefix_working_set: 2 * plan.chunk_bytes() + fixed,
            suffix_working_set: tiles_per_batch * tile_bytes + fixed,
            prefix: Some(plan),
            prefix_resident: true,
            suffix_resident: true,
            l2_budget,
        });
    }
    None
}

// Below the budget: the largest r with a valid geometry, the smallest closed strip that still
// fits the whole L2, else one full-grid launch per pass; one suffix tile per batch.
fn dispatch_degraded(
    log_n: u32,
    columns: usize,
    log_v: u32,
    skip_bottom: u32,
    l2_cache_size_bytes: usize,
) -> Option<Dispatch> {
    let l2_budget = l2_working_set_budget(l2_cache_size_bytes);
    let fixed = twiddle_bytes(MAX_LOG_MAX_DOMAIN) + subroot_bytes(log_n, log_v, skip_bottom);
    let column = size_of::<PR>() << log_n;
    for r in [8, 7, 6] {
        let a = log_n - r;
        let tile_bytes = columns.checked_mul(size_of::<PR>() << (skip_bottom + r))?;
        if a < skip_bottom || r < log_v || tile_bytes > MAX_TILE_BYTES {
            continue;
        }
        let Some(groups) = prefix_groups(a) else {
            continue;
        };
        let full_grid = chunk_plan(log_n, &groups, column)?;
        let plan = (MIN_CHUNK_BYTES.ilog2()..=MAX_CHUNK_BYTES.ilog2())
            .filter_map(|log_chunk| chunk_plan(log_n, &groups, 1 << log_chunk))
            .find(|plan| 2 * plan.chunk_bytes() + fixed <= l2_cache_size_bytes)
            .unwrap_or(full_grid);
        let prefix_working_set = 2 * plan.chunk_bytes() + fixed;
        let suffix_working_set = tile_bytes + fixed;
        return Some(Dispatch {
            small: false,
            r,
            tile_bytes,
            tiles_per_coset: 1 << (a - skip_bottom),
            tiles_per_batch: 1,
            prefix: Some(plan),
            prefix_working_set,
            suffix_working_set,
            prefix_resident: prefix_working_set <= l2_budget,
            suffix_resident: suffix_working_set <= l2_budget,
            l2_budget,
        });
    }
    None
}

pub fn dispatch(
    log_n: u32,
    columns: usize,
    log_v: u32,
    skip_bottom: u32,
    l2_cache_size_bytes: usize,
) -> Result<Dispatch, DispatchError> {
    if !(8..=26).contains(&log_n)
        || columns == 0
        || !(1..=4).contains(&log_v)
        || skip_bottom > log_n - log_v
    {
        return Err(DispatchError::Unsupported);
    }
    let l2_budget = l2_working_set_budget(l2_cache_size_bytes);
    dispatch_with_budget(log_n, columns, log_v, skip_bottom, l2_budget)
        .or_else(|| dispatch_degraded(log_n, columns, log_v, skip_bottom, l2_cache_size_bytes))
        .ok_or(DispatchError::Unsupported)
}

pub(crate) fn launch_prefix_chunked<P: TransformPolicy>(
    policy: &P,
    source: PtrAndStride<PR>,
    target: MutPtrAndStride<PR>,
    cols: usize,
    plan: &ChunkPlan,
    first_pass_scale: Option<FirstPassScale>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let group = plan.cols_per_chunk.min(MAX_COLUMNS_PER_LAUNCH);
    let scaled = first_pass_scale.map(|first| {
        let pass = plan.passes[0];
        assert_eq!(
            pass.start, 0,
            "Proth120 prefix: the scaled pass must be the first pass"
        );
        (first, dit_scaled_function(&pass))
    });
    let output_source = PtrAndStride::new(target.ptr as *const PR, target.stride);
    let functions: Vec<_> = plan
        .passes
        .iter()
        .map(|pass| policy.function(pass.transform_pass()))
        .collect();
    for column in (0..cols).step_by(group) {
        let chunk = (cols - column).min(group);
        let offset = |stride: usize| {
            column
                .checked_mul(stride)
                .expect("Proth120 prefix: column offset overflow")
        };
        let input = PtrAndStride::new(
            unsafe { source.ptr.add(offset(source.stride)) },
            source.stride,
        );
        let in_place = PtrAndStride::new(
            unsafe { output_source.ptr.add(offset(target.stride)) },
            target.stride,
        );
        let output = MutPtrAndStride::new(
            unsafe { target.ptr.add(offset(target.stride)) },
            target.stride,
        );
        for strip in 0..plan.strips {
            let map = plan.map(strip);
            for (pass, function) in plan.passes.iter().zip(&functions) {
                let grid_y = plan.grid_y(pass);
                assert!(grid_y <= 65535, "Proth120 prefix: grid.y exceeds 65535");
                let config = CudaLaunchConfig::basic(
                    (1u32 << pass.start, grid_y, chunk as u32),
                    pass.threads(),
                    stream,
                );
                let input = if pass.start == 0 { input } else { in_place };
                match &scaled {
                    Some((first, function)) if pass.start == 0 => function.launch(
                        &config,
                        &DitScaledArguments::new(
                            input,
                            output,
                            first.descriptor,
                            plan.log_n,
                            0,
                            map,
                            first.scale.native(column),
                        ),
                    )?,
                    _ => function.launch(
                        &config,
                        &policy.arguments(input, output, plan.log_n, pass.start, map),
                    )?,
                }
            }
        }
    }
    Ok(())
}

fn validate_coset(scale: &ScaleArgs, log_n: u32, cosets: usize, log_max_domain: u32) {
    assert!(
        log_n <= scale.log_domain && scale.log_domain <= log_max_domain,
        "Proth120 prefix: log_domain {} outside {log_n}..={log_max_domain}",
        scale.log_domain
    );
    let limit = 1u64 << (scale.log_domain - log_n);
    match scale.coset {
        CosetSource::Constant(k) => assert!(
            u64::from(k) < limit,
            "Proth120 prefix: coset {k} out of range"
        ),
        CosetSource::Batched { k0 } => assert!(
            u64::from(k0) + cosets as u64 <= limit,
            "Proth120 prefix: batched cosets out of range"
        ),
        CosetSource::Device(_) => {}
    }
}

// The first `plan.stages()` stages of the coset LDE of `cols` monomial columns of 2^log_n rows,
// coefficient i scaled by offset_k^i in the first pass; output stays in the network's order.
// With `CosetSource::Batched` the output columns are cosets k0.. of one monomial column.
pub fn lde_coset_slot(
    ctx: &DeviceContext,
    monomials: &DeviceSlice<PR>,
    prefix_out: &mut DeviceSlice<PR>,
    cols: usize,
    plan: &ChunkPlan,
    scale: ScaleArgs,
    stream: &CudaStream,
) -> CudaResult<()> {
    let rows = 1usize << plan.log_n;
    let len = cols
        .checked_mul(rows)
        .expect("Proth120 prefix: length overflow");
    let batched = matches!(scale.coset, CosetSource::Batched { .. });
    assert_eq!(
        monomials.len(),
        if batched { rows } else { len },
        "Proth120 prefix: monomial length"
    );
    assert_eq!(prefix_out.len(), len, "Proth120 prefix: output length");
    let input_range = validate_slice(monomials, "Proth120 prefix input");
    let output_range = validate_slice(prefix_out, "Proth120 prefix output");
    validate_disjoint(
        &input_range,
        &output_range,
        "Proth120 prefix: input/output overlap",
    );
    validate_context_log(ctx, plan.log_n);
    validate_coset(
        &scale,
        plan.log_n,
        if batched { cols } else { 1 },
        ctx.log_max_domain(),
    );
    launch_prefix_chunked(
        &DitPolicy(ctx.descriptor()),
        PtrAndStride::new(monomials.as_ptr(), if batched { 0 } else { rows }),
        MutPtrAndStride::new(prefix_out.as_mut_ptr(), rows),
        cols,
        plan,
        Some(FirstPassScale {
            descriptor: ctx.descriptor(),
            scale,
        }),
        stream,
    )
}

// Reference completion of a prefix output: the remaining stages as one final pass, then the
// natural-order permutation (the `NaturalEvaluations` layout of `lde_coset`).
pub fn lde_finish_reference(
    ctx: &DeviceContext,
    values: &mut DeviceSlice<PR>,
    cols: usize,
    plan: &ChunkPlan,
    stream: &CudaStream,
) -> CudaResult<()> {
    let log_n = plan.log_n;
    let start = plan.stages();
    let stages = log_n - start;
    assert!(
        has_reference_finish(plan),
        "Proth120 prefix: no final kernel for {stages} stages"
    );
    let rows = 1usize << log_n;
    let len = cols
        .checked_mul(rows)
        .expect("Proth120 prefix: length overflow");
    assert_eq!(values.len(), len, "Proth120 prefix: finish length");
    validate_slice(values, "Proth120 prefix finish values");
    validate_context_log(ctx, log_n);
    let policy = DitPolicy(ctx.descriptor());
    let function = policy.function(TransformPass::Final(stages));
    let bytes = size_of::<PR>() << stages;
    if stages >= 10 {
        set_max_dynamic_smem(&function, bytes)?;
    }
    let target = MutPtrAndStride::new(values.as_mut_ptr(), rows);
    let source = PtrAndStride::new(target.ptr as *const PR, rows);
    for column in (0..cols).step_by(MAX_COLUMNS_PER_LAUNCH) {
        let chunk = (cols - column).min(MAX_COLUMNS_PER_LAUNCH);
        let offset = column * rows;
        let mut config =
            CudaLaunchConfig::basic((1u32 << start, chunk as u32), 1u32 << (stages - 2), stream);
        config.dynamic_smem_bytes = bytes;
        function.launch(
            &config,
            &policy.arguments(
                PtrAndStride::new(unsafe { source.ptr.add(offset) }, rows),
                MutPtrAndStride::new(unsafe { target.ptr.add(offset) }, rows),
                log_n,
                start,
                ChunkMap::FULL,
            ),
        )?;
    }
    naturalize(target, log_n, cols, MAX_COLUMNS_PER_LAUNCH, stream)
}

pub fn has_reference_finish(plan: &ChunkPlan) -> bool {
    [8, 10, 12].contains(&(plan.log_n - plan.stages()))
}
