use std::marker::PhantomData;
use std::ops::{Deref, DerefMut, Range};
use std::sync::Arc;

use super::{fields, section, ProofLayoutPr, ProofSlabPr};
use crate::upstream::{ProverConfig, PR};
use era_cudart::slice::{CudaSlice, CudaSliceMut, DeviceSlice};
use gpu_core::primitives::context::DeviceAllocation;
use gpu_hash::keccak256::Digest;

#[derive(Clone)]
pub struct WhirBaseOpeningsLayoutPr {
    pub leaves: Range<usize>,
    pub paths: Range<usize>,
    pub tree_indexes: Range<usize>,
}
#[derive(Clone)]
pub struct WhirIntermediateLayoutPr {
    pub cap: Range<usize>,
    pub openings: WhirBaseOpeningsLayoutPr,
}
#[derive(Clone)]
pub struct WhirProofLayoutPr {
    pub memory: WhirBaseOpeningsLayoutPr,
    pub setup: WhirBaseOpeningsLayoutPr,
    pub intermediate: Vec<WhirIntermediateLayoutPr>,
    pub memory_cap: Range<usize>,
    pub ood_samples: Range<usize>,
    pub sumcheck_polys: Range<usize>,
    pub pow_nonces: Range<usize>,
    pub final_monomials: Range<usize>,
    pub batched_opening: Range<usize>,
}

fn product(a: usize, b: usize) -> usize {
    a.checked_mul(b).expect("Proth120 WHIR proof size overflow")
}
fn digests(cursor: &mut usize, count: usize) -> Range<usize> {
    section(cursor, product(count, size_of::<Digest>()))
}
fn openings(
    cursor: &mut usize,
    queries: usize,
    values: usize,
    columns: usize,
    depth: usize,
) -> WhirBaseOpeningsLayoutPr {
    WhirBaseOpeningsLayoutPr {
        leaves: fields(cursor, product(product(queries, values), columns)),
        paths: digests(cursor, product(queries, depth)),
        tree_indexes: section(cursor, product(queries, size_of::<u32>())),
    }
}

impl WhirProofLayoutPr {
    pub(super) fn new(
        cursor: &mut usize,
        config: &ProverConfig,
        memory_columns: usize,
        setup_columns: usize,
    ) -> Self {
        let schedule = &config.whir_schedule;
        let folds = schedule.fold_steps();
        let queries = schedule.queries_per_round();
        let lde = schedule.intermediate_lde_factors();
        let cap_log = config.cap_size.trailing_zeros() as usize;
        let mut log_n = config.whir_message_size_log2();
        let base_depth = log_n + config.lde_factor().trailing_zeros() as usize - folds[0] - cap_log;
        let memory = openings(
            cursor,
            queries[0],
            1 << folds[0],
            memory_columns,
            base_depth,
        );
        let setup = openings(cursor, queries[0], 1 << folds[0], setup_columns, base_depth);
        let mut intermediate = Vec::with_capacity(folds.len() - 1);
        for round in 0..folds.len() - 1 {
            log_n -= folds[round];
            let depth = log_n + lde[round].trailing_zeros() as usize - folds[round + 1] - cap_log;
            intermediate.push(WhirIntermediateLayoutPr {
                cap: digests(cursor, 1 << cap_log),
                openings: openings(cursor, queries[round + 1], 1 << folds[round + 1], 1, depth),
            });
        }
        log_n -= folds.last().copied().unwrap();
        Self {
            memory,
            setup,
            intermediate,
            memory_cap: digests(cursor, 1 << cap_log),
            ood_samples: fields(cursor, folds.len() - 1),
            sumcheck_polys: fields(cursor, product(folds.iter().sum(), 3)),
            pow_nonces: section(cursor, product(folds.len(), size_of::<u64>())),
            final_monomials: fields(cursor, 1 << log_n),
            batched_opening: fields(cursor, 1),
        }
    }

    pub(super) fn ranges(&self) -> Vec<Range<usize>> {
        let mut ranges = Vec::new();
        let mut add = |o: &WhirBaseOpeningsLayoutPr| {
            ranges.extend([o.leaves.clone(), o.paths.clone(), o.tree_indexes.clone()])
        };
        add(&self.memory);
        add(&self.setup);
        for o in &self.intermediate {
            ranges.push(o.cap.clone());
            ranges.extend([
                o.openings.leaves.clone(),
                o.openings.paths.clone(),
                o.openings.tree_indexes.clone(),
            ]);
        }
        ranges.extend([
            self.memory_cap.clone(),
            self.ood_samples.clone(),
            self.sumcheck_polys.clone(),
            self.pow_nonces.clone(),
            self.final_monomials.clone(),
            self.batched_opening.clone(),
        ]);
        ranges
    }

    pub(super) fn parse<'a>(&self, bytes: &'a [u8]) -> WhirProofFieldsPr<'a> {
        fn values<'a, T>(bytes: &'a [u8], range: &Range<usize>) -> &'a [T] {
            assert!(range.end <= bytes.len() && range.start <= range.end);
            assert_eq!(range.len() % size_of::<T>(), 0);
            let pointer = bytes.as_ptr().wrapping_add(range.start);
            assert_eq!(pointer as usize % align_of::<T>(), 0);
            // SAFETY: the slab is initialized by the completed D2H; bounds,
            // alignment and element size are checked above. T is PR/u32/u64/Digest.
            unsafe { std::slice::from_raw_parts(pointer.cast(), range.len() / size_of::<T>()) }
        }
        fn pr<'a>(bytes: &'a [u8], range: &Range<usize>) -> &'a [PR] {
            let values = values::<PR>(bytes, range);
            assert!(
                values.iter().all(|v| v.0 < PR::ORDER),
                "Proth120 WHIR proof field is noncanonical"
            );
            values
        }
        let base = |layout: &WhirBaseOpeningsLayoutPr| WhirBaseOpeningsFieldsPr {
            leaves: pr(bytes, &layout.leaves),
            paths: values(bytes, &layout.paths),
            tree_indexes: values(bytes, &layout.tree_indexes),
        };
        WhirProofFieldsPr {
            memory: base(&self.memory),
            setup: base(&self.setup),
            intermediate: self
                .intermediate
                .iter()
                .map(|layout| WhirIntermediateFieldsPr {
                    cap: values(bytes, &layout.cap),
                    openings: base(&layout.openings),
                })
                .collect(),
            memory_cap: values(bytes, &self.memory_cap),
            ood_samples: pr(bytes, &self.ood_samples),
            sumcheck_polys: pr(bytes, &self.sumcheck_polys),
            pow_nonces: values(bytes, &self.pow_nonces),
            final_monomials: pr(bytes, &self.final_monomials),
        }
    }
}

pub struct WhirBaseOpeningsFieldsPr<'a> {
    pub leaves: &'a [PR],
    pub paths: &'a [Digest],
    pub tree_indexes: &'a [u32],
}
pub struct WhirIntermediateFieldsPr<'a> {
    pub cap: &'a [Digest],
    pub openings: WhirBaseOpeningsFieldsPr<'a>,
}
pub struct WhirProofFieldsPr<'a> {
    pub memory: WhirBaseOpeningsFieldsPr<'a>,
    pub setup: WhirBaseOpeningsFieldsPr<'a>,
    pub intermediate: Vec<WhirIntermediateFieldsPr<'a>>,
    pub memory_cap: &'a [Digest],
    pub ood_samples: &'a [PR],
    pub sumcheck_polys: &'a [PR],
    pub pow_nonces: &'a [u64],
    pub final_monomials: &'a [PR],
}

/// A disjoint proof region retaining its slab through the last scheduled writer.
/// Used by the WHIR crate; device contents are opaque on the scheduling thread.
pub struct ProofSlabSlicePr<T> {
    backing: Arc<DeviceAllocation<PR>>,
    range: Range<usize>,
    _marker: PhantomData<T>,
}
impl<T> Deref for ProofSlabSlicePr<T> {
    type Target = DeviceSlice<T>;
    fn deref(&self) -> &Self::Target {
        // SAFETY: construction bounds/alignment-checks this live slab region;
        // the Arc retains it, and the returned view is not dereferenced on host.
        unsafe {
            DeviceSlice::from_raw_parts(
                self.backing
                    .as_ptr()
                    .cast::<u8>()
                    .add(self.range.start)
                    .cast(),
                self.range.len() / size_of::<T>(),
            )
        }
    }
}
impl<T> DerefMut for ProofSlabSlicePr<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: same region as deref; WHIR owns its disjoint output views.
        unsafe {
            DeviceSlice::from_raw_parts_mut(
                self.backing
                    .as_ptr()
                    .cast::<u8>()
                    .add(self.range.start)
                    .cast_mut()
                    .cast(),
                self.range.len() / size_of::<T>(),
            )
        }
    }
}
impl<T> CudaSlice<T> for ProofSlabSlicePr<T> {
    unsafe fn as_slice(&self) -> &[T] {
        DeviceSlice::<T>::as_slice(self)
    }
}
impl<T> CudaSliceMut<T> for ProofSlabSlicePr<T> {
    unsafe fn as_mut_slice(&mut self) -> &mut [T] {
        DeviceSlice::<T>::as_mut_slice(self)
    }
}

/// The apex hands the WHIR crate one target; views only cover its output ranges.
pub struct WhirProofTargetPr {
    pub backing: Arc<DeviceAllocation<PR>>,
    pub layout: Arc<ProofLayoutPr>,
}
impl<T> ProofSlabSlicePr<T> {
    /// Used across the crate boundary by the WHIR output builder; its layout
    /// assigns disjoint regions, and each view retains the common allocation.
    pub fn new(backing: Arc<DeviceAllocation<PR>>, range: Range<usize>) -> Self {
        assert!(
            size_of::<T>() > 0
                && range.start <= range.end
                && range.end <= backing.len() * size_of::<PR>()
        );
        assert_eq!(
            backing.as_ptr().cast::<u8>().wrapping_add(range.start) as usize % align_of::<T>(),
            0
        );
        assert_eq!(range.len() % size_of::<T>(), 0);
        Self {
            backing,
            range,
            _marker: PhantomData,
        }
    }
}
impl ProofSlabPr {
    pub fn whir_target(&mut self) -> WhirProofTargetPr {
        WhirProofTargetPr {
            backing: Arc::clone(&self.backing),
            layout: Arc::clone(&self.layout),
        }
    }
}
