//! Device allocations, descriptor upload and the LDE pass.

use era_cudart::memory::{memory_copy, DeviceAllocation};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;

use crate::abi::*;
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
}

pub struct Harness {
    pub layout: Layout,
    pub desc: UniskipVmDesc,
    seed: u32,
    taps: [DeviceAllocation<u32>; CLASSES],
    cosets: [DeviceAllocation<u32>; CLASSES],
    #[allow(dead_code)] // referenced by desc.eq_low; the eval kernel reads it in Task 4.
    eq_low: DeviceAllocation<u32>,
    jobs: [DeviceAllocation<u16>; CLASSES],
    job_counts: [usize; CLASSES],
    stream: CudaStream,
}

impl Harness {
    /// Allocate the backings, upload the program and the LDE matrix, and run the
    /// init kernels over the taps and the eq tables.
    pub fn new(program: &SynthProgram, geometry: &Geometry, seed: u32) -> CudaResult<Self> {
        let layout = Layout::new(program, geometry);
        let stream = CudaStream::create()?;

        // `alloc(0)` has no valid device pointer; a class with no columns still gets
        // a one-word backing so the base records stay dereferenceable-but-unused.
        let alloc_words =
            |class: usize| DeviceAllocation::<u32>::alloc(layout.class_words(class).max(1));
        let mut taps = [alloc_words(CLASS_BF)?, alloc_words(CLASS_E4)?];
        let cosets = [alloc_words(CLASS_BF)?, alloc_words(CLASS_E4)?];

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

        let eq_low_words = geometry.eq_low_len() * CLASS_WORDS[CLASS_E4];
        let mut eq_low = DeviceAllocation::<u32>::alloc(eq_low_words)?;

        let mut desc = UniskipVmDesc {
            record_count: program.program.len() as u32,
            num_sources: program.sources.len() as u32,
            log_rows: geometry.log_rows,
            eq_sizes: UniskipEqSizes {
                high: [geometry.eq_sizes.0, geometry.eq_sizes.1],
                low: geometry.eq_sizes.2,
            },
            eq_low: eq_low.as_ptr() as u64,
            immediates: program.immediates_canonical.map(reference::to_device_bf),
            ..Default::default()
        };
        desc.program[..program.program.len()].copy_from_slice(&program.program);
        desc.source[..program.sources.len()].copy_from_slice(&program.sources);
        for window in 0..UNISKIP_WINDOWS {
            let class = layout.windows[window].class;
            let byte_offset = layout.window_byte_offset(window) as u64;
            desc.tap_bases[window] = UniskipBaseRecord {
                base: taps[class].as_ptr() as u64 + byte_offset,
            };
            desc.coset_bases[window] = UniskipBaseRecord {
                base: cosets[class].as_ptr() as u64 + byte_offset,
            };
        }

        kernels::upload_lde_matrix(&reference::flat_lde_matrix(&lde_matrix()))?;
        kernels::upload_eq_high(&reference::eq_high_words(seed))?;
        kernels::init_bf(&mut taps[CLASS_BF], seed, &stream)?;
        kernels::init_e4(&mut taps[CLASS_E4], seed, &stream)?;
        kernels::init_e4(&mut eq_low, seed, &stream)?;
        stream.synchronize()?;

        Ok(Self {
            layout,
            desc,
            seed,
            taps,
            cosets,
            eq_low,
            jobs,
            job_counts,
            stream,
        })
    }

    /// One coset LDE pass over both field classes.
    pub fn run_lde(&self) -> CudaResult<()> {
        kernels::lde_bf(
            &self.desc,
            &self.jobs[CLASS_BF],
            self.job_counts[CLASS_BF],
            &self.stream,
        )?;
        kernels::lde_e4(
            &self.desc,
            &self.jobs[CLASS_E4],
            self.job_counts[CLASS_E4],
            &self.stream,
        )
    }

    pub fn synchronize(&self) -> CudaResult<()> {
        self.stream.synchronize()
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
    /// coset cells — against the host reference, bit-exact.
    pub fn validate_lde(&self) -> CudaResult<Result<(), String>> {
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
