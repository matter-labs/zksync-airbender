use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::device_structures::{MutPtrAndStride, PtrAndStride};
use gpu_core::primitives::field::PR;

use super::lde::{ChunkMap, TransformPass, TransformPolicy, MAX_COLUMNS_PER_LAUNCH};

pub(crate) const L2_CHUNK_BYTES: usize = 16 << 20;
pub(crate) const MAX_TILE_BYTES: usize = 32 << 20;
pub(crate) const L2_WORKING_SET_BYTES: usize = 64 << 20;
pub(crate) const MAX_LOG_MAX_DOMAIN: u32 = 33;

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
pub(crate) struct ChunkPlan {
    pub(crate) log_n: u32,
    pub(crate) cols_per_chunk: usize,
    pub(crate) strips: u32,
    pub(crate) strip_blocks: u32,
    pub(crate) strip_domain_bits: u32,
    pub(crate) passes: Vec<PrefixPass>,
}

impl ChunkPlan {
    pub(crate) fn stages(&self) -> u32 {
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
        if !(5..=8).contains(&stages) || narrow && stages != 5 {
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Dispatch {
    pub(crate) small: bool,
    pub(crate) r: u32,
    pub(crate) tile_bytes: usize,
    pub(crate) tiles_per_coset: usize,
    pub(crate) prefix: Option<ChunkPlan>,
    pub(crate) prefix_working_set: usize,
    pub(crate) suffix_working_set: usize,
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

pub(crate) fn dispatch(
    log_n: u32,
    columns: usize,
    log_v: u32,
    skip_bottom: u32,
) -> Option<Dispatch> {
    if !(8..=26).contains(&log_n)
        || columns == 0
        || !(1..=4).contains(&log_v)
        || skip_bottom > log_n - log_v
    {
        return None;
    }
    if log_n <= 12 {
        return Some(Dispatch {
            small: true,
            r: log_n,
            tile_bytes: columns.checked_mul(size_of::<PR>() << log_n)?,
            tiles_per_coset: 1,
            prefix: None,
            prefix_working_set: 0,
            suffix_working_set: 0,
        });
    }
    let twiddles = twiddle_bytes(MAX_LOG_MAX_DOMAIN);
    let subroots = subroot_bytes(log_n, log_v, skip_bottom);
    for r in [8, 7, 6] {
        let a = log_n - r;
        let tile_bytes = columns.checked_mul(size_of::<PR>() << (skip_bottom + r))?;
        if a < skip_bottom || r < log_v || tile_bytes > MAX_TILE_BYTES {
            continue;
        }
        let Some(plan) = prefix_groups(a).and_then(|g| chunk_plan(log_n, &g, L2_CHUNK_BYTES))
        else {
            continue;
        };
        let tiles_per_coset = 1usize << (a - skip_bottom);
        let prefix_working_set = 2 * plan.chunk_bytes() + twiddles + subroots;
        let suffix_working_set = tiles_per_coset.min(2) * tile_bytes + twiddles + subroots;
        if prefix_working_set.max(suffix_working_set) > L2_WORKING_SET_BYTES {
            continue;
        }
        return Some(Dispatch {
            small: false,
            r,
            tile_bytes,
            tiles_per_coset,
            prefix: Some(plan),
            prefix_working_set,
            suffix_working_set,
        });
    }
    None
}

pub(crate) fn launch_prefix_chunked<P: TransformPolicy>(
    policy: &P,
    source: PtrAndStride<PR>,
    target: MutPtrAndStride<PR>,
    cols: usize,
    plan: &ChunkPlan,
    stream: &CudaStream,
) -> CudaResult<()> {
    let group = plan.cols_per_chunk.min(MAX_COLUMNS_PER_LAUNCH);
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
                function.launch(
                    &config,
                    &policy.arguments(input, output, plan.log_n, pass.start, map),
                )?;
            }
        }
    }
    Ok(())
}
