//! Device allocations, descriptor upload and the LDE pass.

use era_cudart::event::{elapsed_time, CudaEvent};
use era_cudart::memory::{memory_copy, DeviceAllocation};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;

use crate::abi::*;
use crate::cache::CachePlan;
use crate::domain::lde_matrix;
use crate::geometry::Geometry;
use crate::kernels;
use crate::reference;
use crate::synth::SynthProgram;

/// Backing classes: one tap allocation and one coset allocation each.
pub const CLASS_BF: usize = 0;
pub const CLASS_E4: usize = 1;
pub const CLASSES: usize = 2;
/// `u32` words per field element of each class.
pub const CLASS_WORDS: [usize; CLASSES] = [1, 4];

pub fn class_index(source_class: u8) -> usize {
    match source_class {
        UNISKIP_SRC_BF_GLOBAL => CLASS_BF,
        UNISKIP_SRC_E4_GLOBAL => CLASS_E4,
        other => panic!("source class {other} has no backing"),
    }
}

/// Where a window sits inside its class backing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WindowPlacement {
    pub class: usize,
    pub columns: u32,
    /// Field-element offset of the window inside its class backing.
    pub offset: u64,
}

/// ALLOCATION LAYOUT. The windows of one field class share a single tap backing
/// (and an identically shaped coset backing), packed in window order; a window
/// occupies `columns * UNISKIP_TAPS * 2^log_rows` field elements. The init
/// generator's index is the ABSOLUTE element index inside that backing, so
/// `reference.rs` must go through this type rather than the `(window, column)`
/// view — two windows of the same class would otherwise generate identical data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Layout {
    pub log_rows: u32,
    pub rows: u64,
    pub windows: [WindowPlacement; UNISKIP_WINDOWS],
    /// Field elements in each class's tap (and coset) backing.
    pub class_elements: [u64; CLASSES],
}

impl Layout {
    pub fn new(program: &SynthProgram, geometry: &Geometry) -> Self {
        let mut class_elements = [0u64; CLASSES];
        let mut windows = [WindowPlacement {
            class: CLASS_BF,
            columns: 0,
            offset: 0,
        }; UNISKIP_WINDOWS];
        for (w, placement) in windows.iter_mut().enumerate() {
            let spec = program.windows[w];
            let class = class_index(spec.kind.source_class());
            *placement = WindowPlacement {
                class,
                columns: spec.columns,
                offset: class_elements[class],
            };
            class_elements[class] +=
                u64::from(spec.columns) * UNISKIP_TAPS as u64 * geometry.logical_rows;
        }
        Self {
            log_rows: geometry.log_rows,
            rows: geometry.logical_rows,
            windows,
            class_elements,
        }
    }

    /// Byte offset of a window inside its class backing. E4 ALIGNMENT INVARIANT:
    /// the device `load<e4>` reinterprets to `uint4 *`, so every e4 base must be
    /// 16-byte aligned. Offsets count whole field elements, so an e4 window's byte
    /// offset is a multiple of 16, and `cudaMalloc` aligns the backing itself to
    /// far more than that.
    pub fn window_byte_offset(&self, window: usize) -> usize {
        let placement = self.windows[window];
        placement.offset as usize * CLASS_WORDS[placement.class] * size_of::<u32>()
    }

    /// Field elements of one column's 16-plane block.
    pub fn column_elements(&self) -> u64 {
        UNISKIP_TAPS as u64 * self.rows
    }

    /// Element index of `(window, column)`'s block inside its class backing.
    pub fn column_base(&self, window: usize, column: usize) -> u64 {
        self.windows[window].offset + column as u64 * self.column_elements()
    }

    /// Words of each class's backing (both tap and coset).
    pub fn class_words(&self, class: usize) -> usize {
        self.class_elements[class] as usize * CLASS_WORDS[class]
    }

    /// Bytes of the tap backings of both classes; the coset backings match.
    pub fn backing_bytes(&self) -> u64 {
        (0..CLASSES)
            .map(|class| self.class_words(class) as u64 * size_of::<u32>() as u64)
            .sum()
    }
}

/// Grid shape of the coset LDE. `Cell` is the v1 shape — one thread per
/// (job, cell, row), so a row's 16 taps are re-read once per coset cell. `Row` is the
/// intra-thread reshape — one thread per (job, row), per (job, row, limb) for `e4` —
/// which reads each tap once and emits all 16 cells. Both write the same bytes, so
/// they are interchangeable for every consumer and for validation.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, clap::ValueEnum)]
pub enum LdeShape {
    Cell,
    #[default]
    Row,
}

impl LdeShape {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Cell => "cell",
            Self::Row => "row",
        }
    }
}

/// Where the coset cells come from. `Unfused` materializes them in a separate LDE
/// stage and the eval kernel reads them back — the v1 pass. `FusedRecompute` drops
/// both the LDE launches and the coset backing: the accessor extends the source's
/// 16 taps on read. `FusedCached` adds a fixed shared-memory assignment on top of it,
/// so the planned sources' coset slabs are produced once per 32-row tile instead of
/// once per reference. All three produce the same `q`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, clap::ValueEnum)]
pub enum EvalMode {
    #[default]
    Unfused,
    FusedRecompute,
    FusedCached,
}

impl EvalMode {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Unfused => "unfused",
            Self::FusedRecompute => "fused-recompute",
            Self::FusedCached => "fused-cached",
        }
    }

    /// Whether the pass writes a coset backing at all.
    pub fn materializes_coset(self) -> bool {
        self == Self::Unfused
    }

    /// Whether the pass reads the shared-memory cache plan.
    pub fn uses_cache(self) -> bool {
        self == Self::FusedCached
    }
}

/// Which four of the 32 cells a warp owns. `Block` is the v1 map (warp `w` takes
/// cells `4w..4w+3`, so warps 0-3 are all-H and warps 4-7 all-coset); `Interleave`
/// gives warp `w` the cells `{w, w+8, w+16, w+24}`, two of each. Fused modes only —
/// it exists to spread the recompute across all eight warps.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, clap::ValueEnum)]
pub enum CellMap {
    #[default]
    Block,
    Interleave,
}

impl CellMap {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Block => "block",
            Self::Interleave => "interleave",
        }
    }
}

/// The shape knobs of one pass. `lde_shape` applies to [`EvalMode::Unfused`] only
/// and `cell_map` to the fused modes only; `main` rejects the other combinations.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PassConfig {
    pub mode: EvalMode,
    pub lde_shape: LdeShape,
    pub cell_map: CellMap,
}

/// The timed stages of one pass, in execution order.
pub const STAGES: [&str; 4] = ["lde", "eval", "finalize", "fold"];

/// Device time of one pass, from the CUDA events the pass records.
#[derive(Clone, Copy, Debug)]
pub struct StageTimes {
    pub stage_ms: [f32; STAGES.len()],
    pub total_ms: f32,
}

/// COMPULSORY traffic of one pass: every distinct byte a stage must read or write
/// at least once. Real DRAM traffic is never below this and is usually above it —
/// the eval kernel issues one load per operand reference, and the LDE re-reads its
/// input once per coset cell — so `bytes / time` is a LOWER bound on the bandwidth
/// a stage is achieving, not an upper one.
#[derive(Clone, Copy, Debug)]
pub struct PassBytes {
    pub stage: [u64; STAGES.len()],
    pub total: u64,
}

/// A class-pair LDE launch (`bf`, `e4`), or `None` in a mode with no LDE stage.
type LdeLaunch = fn(&UniskipVmDesc, &DeviceSlice<u16>, usize, &CudaStream) -> CudaResult<()>;
type EvalLaunch = fn(&UniskipVmDesc, u32, &CudaStream) -> CudaResult<()>;

pub struct Harness {
    pub layout: Layout,
    pub desc: UniskipVmDesc,
    geometry: Geometry,
    seed: u32,
    flat_eq: bool,
    config: PassConfig,
    lde: Option<[LdeLaunch; CLASSES]>,
    eval: EvalLaunch,
    taps: [DeviceAllocation<u32>; CLASSES],
    /// One unused word per class in a fused mode — see [`EvalMode::materializes_coset`].
    cosets: [DeviceAllocation<u32>; CLASSES],
    #[allow(dead_code)] // referenced by desc.eq_low
    eq_low: DeviceAllocation<u32>,
    partials: DeviceAllocation<u32>,
    q: DeviceAllocation<u32>,
    /// One `e4` per (source, row), at `source * rows + row`.
    folded: DeviceAllocation<u32>,
    jobs: [DeviceAllocation<u16>; CLASSES],
    job_counts: [usize; CLASSES],
    stream: CudaStream,
    /// `STAGES.len() + 1` markers: one before the first stage, one after each.
    events: Vec<CudaEvent>,
}

impl Harness {
    /// Allocate the backings, upload the program, the LDE matrix and the coefficient
    /// bank, and run the init kernels over the taps and the eq tables. `flat_eq`
    /// forces every eq entry to ONE — the `--validate-flat-eq` debug mode, which
    /// isolates the term VM from the eq composition on both sides. `config` picks the
    /// source-resolution mode and the grid shapes; none of them changes `q`. `plan` is
    /// the shared-memory assignment, applied to the wire only in a caching mode.
    pub fn new(
        program: &SynthProgram,
        geometry: &Geometry,
        seed: u32,
        flat_eq: bool,
        config: PassConfig,
        plan: &CachePlan,
    ) -> CudaResult<Self> {
        let layout = Layout::new(program, geometry);
        let stream = CudaStream::create()?;

        // `alloc(0)` has no valid device pointer; a class with no columns still gets
        // a one-word backing so the base records stay dereferenceable-but-unused.
        let alloc_words =
            |class: usize| DeviceAllocation::<u32>::alloc(layout.class_words(class).max(1));
        let mut taps = [alloc_words(CLASS_BF)?, alloc_words(CLASS_E4)?];
        // A fused mode never reads a coset element, so it allocates no coset backing:
        // this is the 1x-backing memory saving the mode exists for. Its base records
        // are NULLED below rather than pointed at the placeholder, so a stray coset
        // read faults instead of returning garbage.
        let cosets = if config.mode.materializes_coset() {
            [alloc_words(CLASS_BF)?, alloc_words(CLASS_E4)?]
        } else {
            [
                DeviceAllocation::<u32>::alloc(1)?,
                DeviceAllocation::<u32>::alloc(1)?,
            ]
        };

        let mut job_ids: [Vec<u16>; CLASSES] = [Vec::new(), Vec::new()];
        for (id, rec) in program.sources.iter().enumerate() {
            job_ids[class_index(rec.source_class)].push(id as u16);
        }
        let job_counts = [job_ids[CLASS_BF].len(), job_ids[CLASS_E4].len()];
        // The job lists ARE the used-column map: one source per column of every
        // window, so the LDE covers each backing exactly once and no coset element
        // is left at its uninitialized value.
        let total_columns: u32 = layout.windows.iter().map(|w| w.columns).sum();
        assert_eq!(
            program.sources.len() as u32,
            total_columns,
            "the source table must cover every column of every window exactly once"
        );
        let mut jobs = [
            DeviceAllocation::<u16>::alloc(job_counts[CLASS_BF].max(1))?,
            DeviceAllocation::<u16>::alloc(job_counts[CLASS_E4].max(1))?,
        ];
        for class in 0..CLASSES {
            if job_counts[class] > 0 {
                memory_copy(&mut jobs[class][..job_counts[class]], &job_ids[class][..])?;
            }
        }

        // The allocation carries the whole derived-table init space; `eq_low` is its
        // tail slice, so no two derived tables hold identical data (see
        // `reference::UNISKIP_EQ_LOW_INIT_BASE`).
        let eq_low_offset = reference::UNISKIP_EQ_LOW_INIT_BASE as usize * CLASS_WORDS[CLASS_E4];
        let eq_low_words = eq_low_offset + geometry.eq_low_len() * CLASS_WORDS[CLASS_E4];
        let mut eq_low = DeviceAllocation::<u32>::alloc(eq_low_words)?;

        let mut partials =
            DeviceAllocation::<u32>::alloc(geometry.partials as usize * CLASS_WORDS[CLASS_E4])?;
        let q = DeviceAllocation::<u32>::alloc(UNISKIP_CELLS * CLASS_WORDS[CLASS_E4])?;
        let folded = DeviceAllocation::<u32>::alloc(
            program.sources.len() * geometry.logical_rows as usize * CLASS_WORDS[CLASS_E4],
        )?;

        let mut desc = UniskipVmDesc {
            record_count: program.program.len() as u32,
            num_sources: program.sources.len() as u32,
            log_rows: geometry.log_rows,
            eq_sizes: UniskipEqSizes {
                high: [geometry.eq_sizes.0, geometry.eq_sizes.1],
                low: geometry.eq_sizes.2,
            },
            eq_low: eq_low.as_ptr() as u64 + (eq_low_offset * size_of::<u32>()) as u64,
            partials: partials.as_mut_ptr() as u64,
            immediates: program.immediates_canonical.map(reference::to_device_bf),
            ..Default::default()
        };
        desc.program[..program.program.len()].copy_from_slice(&program.program);
        desc.source[..program.sources.len()].copy_from_slice(&program.sources);
        // The plan reaches the device on the wire (`cache_slot` per record) and as the
        // inverse unit -> source table below. A non-caching mode leaves every record at
        // the sentinel and uploads an empty table, so no kernel can read a stale slot.
        let fill = if config.mode.uses_cache() {
            assert_eq!(
                plan.source_slot.len(),
                program.sources.len(),
                "the cache plan was lowered from a different program"
            );
            for (rec, &slot) in desc.source[..program.sources.len()]
                .iter_mut()
                .zip(plan.source_slot.iter())
            {
                rec.cache_slot = slot;
            }
            plan.fill
        } else {
            [UNISKIP_CACHE_FILL_NONE; UNISKIP_CACHE_UNITS]
        };
        for window in 0..UNISKIP_WINDOWS {
            let class = layout.windows[window].class;
            let byte_offset = layout.window_byte_offset(window) as u64;
            desc.tap_bases[window] = UniskipBaseRecord {
                base: taps[class].as_ptr() as u64 + byte_offset,
            };
            desc.coset_bases[window] = UniskipBaseRecord {
                base: if config.mode.materializes_coset() {
                    cosets[class].as_ptr() as u64 + byte_offset
                } else {
                    0
                },
            };
        }

        kernels::upload_lde_matrix(&reference::flat_lde_matrix(&lde_matrix()))?;
        kernels::upload_eq_high(&reference::eq_high_words(seed, flat_eq))?;
        kernels::upload_coeff_bank(&reference::coeff_bank_words(seed))?;
        kernels::upload_fold_weights(&reference::fold_weight_words(seed))?;
        kernels::upload_cache_fill(&fill)?;
        kernels::init_bf(&mut taps[CLASS_BF], seed, &stream)?;
        kernels::init_e4(&mut taps[CLASS_E4], seed, &stream)?;
        kernels::init_e4(&mut eq_low, seed, &stream)?;
        stream.synchronize()?;

        if flat_eq {
            let ones: Vec<u32> =
                std::iter::repeat_n(reference::e4_one_words(), geometry.eq_low_len())
                    .flatten()
                    .collect();
            memory_copy(
                &mut eq_low[eq_low_offset..eq_low_offset + ones.len()],
                &ones[..],
            )?;
        }

        let mut events = Vec::with_capacity(STAGES.len() + 1);
        for _ in 0..=STAGES.len() {
            events.push(CudaEvent::create()?);
        }

        // Mode dispatch is resolved ONCE, here: the pass itself is two function
        // pointers, so neither arm carries the other's branch.
        let lde = match config.mode {
            EvalMode::Unfused => Some(match config.lde_shape {
                LdeShape::Cell => [kernels::lde_bf as LdeLaunch, kernels::lde_e4 as LdeLaunch],
                LdeShape::Row => [
                    kernels::lde_bf_row as LdeLaunch,
                    kernels::lde_e4_row as LdeLaunch,
                ],
            }),
            EvalMode::FusedRecompute | EvalMode::FusedCached => None,
        };
        let eval: EvalLaunch = match (config.mode, config.cell_map) {
            (EvalMode::Unfused, _) => kernels::eval,
            (EvalMode::FusedRecompute, CellMap::Block) => kernels::eval_fused,
            (EvalMode::FusedRecompute, CellMap::Interleave) => kernels::eval_fused_interleave,
            (EvalMode::FusedCached, CellMap::Block) => kernels::eval_fused_cached,
            (EvalMode::FusedCached, CellMap::Interleave) => kernels::eval_fused_cached_interleave,
        };

        Ok(Self {
            layout,
            desc,
            geometry: *geometry,
            seed,
            flat_eq,
            config,
            lde,
            eval,
            taps,
            cosets,
            eq_low,
            partials,
            q,
            folded,
            jobs,
            job_counts,
            stream,
            events,
        })
    }

    /// One coset LDE pass over both field classes, in the configured grid shape —
    /// nothing at all in a fused mode, where the accessor absorbs it.
    pub fn run_lde(&self) -> CudaResult<()> {
        let Some([bf, e4]) = self.lde else {
            return Ok(());
        };
        bf(
            &self.desc,
            &self.jobs[CLASS_BF],
            self.job_counts[CLASS_BF],
            &self.stream,
        )?;
        e4(
            &self.desc,
            &self.jobs[CLASS_E4],
            self.job_counts[CLASS_E4],
            &self.stream,
        )
    }

    /// One fold pass over both field classes, at the round challenge the fold
    /// weights were uploaded for.
    pub fn run_fold(&mut self) -> CudaResult<()> {
        kernels::fold_bf(
            &self.desc,
            &self.jobs[CLASS_BF],
            self.job_counts[CLASS_BF],
            &mut self.folded,
            &self.stream,
        )?;
        kernels::fold_e4(
            &self.desc,
            &self.jobs[CLASS_E4],
            self.job_counts[CLASS_E4],
            &mut self.folded,
            &self.stream,
        )
    }

    /// One full uniskip pass: coset LDE, the 32-cell eval, the reduction of the
    /// block partials into `q`, then the fold at the round challenge. Every pass
    /// records the stage events, warmup included, so a timed pass and an untimed
    /// one are the same work.
    pub fn run_pass(&mut self) -> CudaResult<()> {
        self.events[0].record(&self.stream)?;
        self.run_lde()?;
        self.events[1].record(&self.stream)?;
        (self.eval)(&self.desc, self.geometry.blocks, &self.stream)?;
        self.events[2].record(&self.stream)?;
        kernels::finalize(
            &self.partials,
            self.geometry.blocks,
            &mut self.q,
            &self.stream,
        )?;
        self.events[3].record(&self.stream)?;
        self.run_fold()?;
        self.events[4].record(&self.stream)
    }

    pub fn synchronize(&self) -> CudaResult<()> {
        self.stream.synchronize()
    }

    pub fn config(&self) -> PassConfig {
        self.config
    }

    /// Device bytes the pass holds in its tap and coset backings.
    pub fn backing_bytes_resident(&self) -> u64 {
        let backing = self.layout.backing_bytes();
        backing + u64::from(self.config.mode.materializes_coset()) * backing
    }

    /// Device time of the last pass, in [`STAGES`] order. Only valid once the pass
    /// has completed — call [`Self::synchronize`] first.
    pub fn stage_times(&self) -> CudaResult<StageTimes> {
        let mut stage_ms = [0f32; STAGES.len()];
        for (stage, ms) in stage_ms.iter_mut().enumerate() {
            *ms = elapsed_time(&self.events[stage], &self.events[stage + 1])?;
        }
        Ok(StageTimes {
            stage_ms,
            total_ms: elapsed_time(&self.events[0], &self.events[STAGES.len()])?,
        })
    }

    /// Compulsory traffic of one pass, in [`STAGES`] order — see [`PassBytes`]. A
    /// fused mode has no LDE stage and its eval reads the tap backing only, so its
    /// floor is one backing lighter in each of the two stages.
    pub fn pass_bytes(&self) -> PassBytes {
        let e4_bytes = CLASS_WORDS[CLASS_E4] as u64 * size_of::<u32>() as u64;
        let backing = self.layout.backing_bytes();
        let partials = self.geometry.partials * e4_bytes;
        let folded = u64::from(self.desc.num_sources) * self.layout.rows * e4_bytes;
        let coset = u64::from(self.config.mode.materializes_coset()) * backing;
        let stage = [
            2 * coset,
            backing + coset + partials,
            partials + UNISKIP_CELLS as u64 * e4_bytes,
            backing + folded,
        ];
        PassBytes {
            stage,
            total: stage.iter().sum(),
        }
    }

    /// The 32 evaluations the last pass produced, four `u32` limbs per cell.
    pub fn download_q(&self) -> CudaResult<Vec<u32>> {
        let mut host = vec![0u32; UNISKIP_CELLS * CLASS_WORDS[CLASS_E4]];
        memory_copy(&mut host[..], &self.q[..])?;
        Ok(host)
    }

    /// Compare all 32 cells against the full CPU oracle, bit-exact.
    pub fn validate_q(&self, program: &SynthProgram) -> CudaResult<Result<(), String>> {
        let actual = self.download_q()?;
        let expected = reference::eval_q(program, &self.geometry, self.seed, self.flat_eq);
        Ok(reference::check_q(&expected, &actual))
    }

    fn download_column(
        &self,
        backing: &[DeviceAllocation<u32>; CLASSES],
        window: usize,
        column: usize,
    ) -> CudaResult<Vec<u32>> {
        let class = self.layout.windows[window].class;
        let words = CLASS_WORDS[class];
        let start = self.layout.column_base(window, column) as usize * words;
        let len = self.layout.column_elements() as usize * words;
        let mut host = vec![0u32; len];
        memory_copy(&mut host[..], &backing[class][start..start + len])?;
        Ok(host)
    }

    /// Compare the first and last used column of every window — taps and all 16
    /// coset cells — against the host reference, bit-exact. Only meaningful where the
    /// coset is materialized; a fused mode has no buffer to check and leans on the
    /// `q` oracle, which addresses all 32 cells.
    pub fn validate_lde(&self) -> CudaResult<Result<(), String>> {
        assert!(
            self.config.mode.materializes_coset(),
            "validate_lde needs a materialized coset"
        );
        for window in 0..UNISKIP_WINDOWS {
            let columns = self.layout.windows[window].columns as usize;
            let checked: Vec<usize> = match columns {
                0 => Vec::new(),
                1 => vec![0],
                _ => vec![0, columns - 1],
            };
            for column in checked {
                let rec = self.desc.source[..self.desc.num_sources as usize]
                    .iter()
                    .copied()
                    .find(|r| addr_window(r.addr) == window && addr_column(r.addr) == column)
                    .expect("every window column is a source record");
                let taps = self.download_column(&self.taps, window, column)?;
                let coset = self.download_column(&self.cosets, window, column)?;
                let label = format!("window {window} column {column}");
                if let Err(e) = reference::check_column(
                    &self.layout,
                    self.seed,
                    window,
                    rec,
                    &taps,
                    &coset,
                    &label,
                ) {
                    return Ok(Err(e));
                }
            }
        }
        Ok(Ok(()))
    }

    /// The first and last used column of a field class, in backing order. Fewer
    /// than two entries if the class holds fewer than two columns.
    fn class_edge_sources(&self, class: usize) -> Vec<(usize, UniskipSourceRecord)> {
        let mut of_class: Vec<(usize, UniskipSourceRecord)> = self.desc.source
            [..self.desc.num_sources as usize]
            .iter()
            .copied()
            .enumerate()
            .filter(|(_, rec)| class_index(rec.source_class) == class)
            .collect();
        of_class.sort_by_key(|(_, rec)| {
            self.layout
                .column_base(addr_window(rec.addr), addr_column(rec.addr))
        });
        match of_class.len() {
            0 => Vec::new(),
            1 => vec![of_class[0]],
            n => vec![of_class[0], of_class[n - 1]],
        }
    }

    /// Rows the fold check samples: the two ends plus a few interior rows.
    fn sample_rows(&self) -> Vec<u64> {
        let rows = self.layout.rows;
        let mut sampled = vec![0, 1, rows / 3, rows / 2, rows - 1];
        sampled.sort_unstable();
        sampled.dedup();
        sampled
    }

    /// Compare the folded values of the first and last used column of both field
    /// classes, at sampled rows, against the host fold — bit-exact. Sampled rather
    /// than exhaustive: the fold output is one `e4` per (source, row), so a full
    /// download is the size of the whole tap backing.
    pub fn validate_fold(&self) -> CudaResult<Result<(), String>> {
        let words = CLASS_WORDS[CLASS_E4];
        let rows = self.sample_rows();
        for class in 0..CLASSES {
            for (id, rec) in self.class_edge_sources(class) {
                let mut host = vec![0u32; rows.len() * words];
                for (i, &row) in rows.iter().enumerate() {
                    let start = (id as u64 * self.layout.rows + row) as usize * words;
                    memory_copy(
                        &mut host[i * words..(i + 1) * words],
                        &self.folded[start..start + words],
                    )?;
                }
                let label = format!(
                    "source {id} (window {} column {})",
                    addr_window(rec.addr),
                    addr_column(rec.addr)
                );
                if let Err(e) =
                    reference::fold_check(&self.layout, self.seed, rec, &rows, &host, &label)
                {
                    return Ok(Err(e));
                }
            }
        }
        Ok(Ok(()))
    }
}

#[cfg(test)]
mod cpu_tests {
    use super::*;
    use crate::synth::{generate, Census, SYNTH_E4_WINDOW};

    #[test]
    fn cpu_layout_tiles_backings() {
        let geometry = Geometry::new(10).unwrap();
        let program = generate(5, Census::default()).unwrap();
        let layout = Layout::new(&program, &geometry);

        let mut expected = [0u64; CLASSES];
        for window in 0..UNISKIP_WINDOWS {
            let placement = layout.windows[window];
            assert_eq!(
                placement.class,
                class_index(program.windows[window].kind.source_class())
            );
            assert_eq!(placement.offset, expected[placement.class]);
            expected[placement.class] += u64::from(placement.columns) * layout.column_elements();
            // E4 alignment invariant: a `uint4` load needs a 16-byte-aligned base.
            if placement.class == CLASS_E4 {
                assert_eq!(layout.window_byte_offset(window) % 16, 0);
            }
        }
        assert_eq!(layout.class_elements, expected);
        assert_eq!(layout.windows[SYNTH_E4_WINDOW].class, CLASS_E4);

        // Column blocks tile their backing exactly once, with no gaps.
        let mut seen = std::collections::HashSet::new();
        for window in 0..UNISKIP_WINDOWS {
            let placement = layout.windows[window];
            for column in 0..placement.columns as usize {
                let base = layout.column_base(window, column);
                for element in base..base + layout.column_elements() {
                    assert!(seen.insert((placement.class, element)));
                }
            }
        }
        assert_eq!(seen.len() as u64, layout.class_elements.iter().sum::<u64>());
    }
}
