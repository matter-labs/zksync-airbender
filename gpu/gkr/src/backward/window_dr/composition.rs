use std::collections::BTreeSet;
use std::sync::Arc;

use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::E4;
use gpu_gkr_compiler::DrWindowInputProjection;
use gpu_prover_context::ProverContext;

use crate::backward::{make_eq_sizes, GkrEqSizes};
use crate::{DrWindowLayerProgram, GpuGKRStorage};

use super::binding::{
    bind_dr_window_continuations, resolve_storage_e4, DrContinuationFactoredEqScratch,
    DrContinuationFactoredEqView, DrWindowBindError, DrWindowContinuationArena,
    DrWindowContinuationLaunch, DrWindowLaunch,
};

#[derive(Clone, Copy)]
pub(crate) struct DrWindowPassEqView {
    pub(crate) eq_low: *const E4,
    pub(crate) eq_sizes: GkrEqSizes,
}

impl DrWindowPassEqView {
    pub(crate) fn new(eq_low: *const E4, eq_sizes: GkrEqSizes) -> Self {
        Self { eq_low, eq_sizes }
    }
}

// SAFETY: the view is retained only by a layer plan that also owns the
// allocation, and the pointer is forwarded only to stream-ordered kernels.
unsafe impl Send for DrWindowPassEqView {}
unsafe impl Sync for DrWindowPassEqView {}

pub(crate) struct DrWindowPassEqState {
    pub(crate) eq_low: DeviceAllocation<E4>,
    pub(crate) eq_sizes: GkrEqSizes,
    pub(crate) build_offset: usize,
}

impl DrWindowPassEqState {
    pub(crate) fn as_view(&self) -> DrWindowPassEqView {
        DrWindowPassEqView::new(self.eq_low.as_ptr(), self.eq_sizes)
    }
}

/// Keeps every raw canonical input backing alive until its last queued reader
/// has been enqueued. The canonical source list itself is the layer program's
/// input projection.
pub(crate) struct DrWindowRawInputKeepalive {
    backings: Vec<Arc<DeviceAllocation<E4>>>,
}

impl DrWindowRawInputKeepalive {
    pub(crate) fn from_projection<B>(
        storage: &GpuGKRStorage<B, E4>,
        projection: &DrWindowInputProjection,
    ) -> Result<Self, DrWindowBindError> {
        let mut seen = BTreeSet::new();
        let mut backings = Vec::new();
        for &address in projection.canonical_sources() {
            let backing = Arc::clone(resolve_storage_e4(storage, address)?.backing);
            if seen.insert(Arc::as_ptr(&backing) as usize) {
                backings.push(backing);
            }
        }
        Ok(Self { backings })
    }

    pub(crate) fn canonical_source_pointers<B>(
        &self,
        storage: &GpuGKRStorage<B, E4>,
        projection: &DrWindowInputProjection,
    ) -> Result<Vec<*const E4>, DrWindowBindError> {
        projection
            .canonical_sources()
            .iter()
            .copied()
            .map(|address| {
                let resolved = resolve_storage_e4(storage, address)?;
                assert!(
                    self.backings
                        .iter()
                        .any(|backing| Arc::ptr_eq(backing, resolved.backing)),
                    "the prepared raw-input keepalive must own the resolved backing",
                );
                let stride = 1usize.checked_shl(resolved.log2_stride).ok_or(
                    DrWindowBindError::ArenaGeometryOverflow {
                        log2_stride: resolved.log2_stride,
                        poly_count: resolved.poly_index + 1,
                    },
                )?;
                let offset = resolved.poly_index.checked_mul(stride).ok_or(
                    DrWindowBindError::ArenaGeometryOverflow {
                        log2_stride: resolved.log2_stride,
                        poly_count: resolved.poly_index + 1,
                    },
                )?;
                // SAFETY: `resolve_storage_e4` returns the exact live backing,
                // stride, and polynomial index retained by this keepalive.
                Ok(unsafe { resolved.backing.as_ptr().add(offset) })
            })
            .collect()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DrWindowContinuationParity {
    Even,
    Odd,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DrWindowContinuationPlannedSource {
    Raw,
    Arena(DrWindowContinuationParity),
}

/// One continuation pass, fully determined by the layer width and its start
/// round. Every other quantity is derived on demand, so no pass carries a
/// mutable cumulative drain from one record into the next.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct DrWindowContinuationPassGeometry {
    pub(crate) folding_steps: usize,
    pub(crate) start_round: usize,
}

impl DrWindowContinuationPassGeometry {
    pub(crate) fn new(folding_steps: usize, start_round: usize) -> Result<Self, DrWindowBindError> {
        if start_round < 3 || !start_round.is_multiple_of(3) || start_round + 3 >= folding_steps {
            return Err(DrWindowBindError::InvalidContinuationBoundary {
                folding_steps,
                start_round,
            });
        }
        Ok(Self {
            folding_steps,
            start_round,
        })
    }

    fn pass_index(self) -> usize {
        (self.start_round - 3) / 3
    }

    pub(crate) fn destination(self) -> DrWindowContinuationParity {
        if self.pass_index().is_multiple_of(2) {
            DrWindowContinuationParity::Even
        } else {
            DrWindowContinuationParity::Odd
        }
    }

    /// Pass 0 reads raw storage; every later pass reads the previous pass's
    /// destination, which is the opposite parity of its own.
    pub(crate) fn source(self) -> DrWindowContinuationPlannedSource {
        if self.pass_index() == 0 {
            return DrWindowContinuationPlannedSource::Raw;
        }
        DrWindowContinuationPlannedSource::Arena(match self.destination() {
            DrWindowContinuationParity::Even => DrWindowContinuationParity::Odd,
            DrWindowContinuationParity::Odd => DrWindowContinuationParity::Even,
        })
    }

    pub(crate) fn log2_stride(self) -> u32 {
        (self.folding_steps + 1 - self.start_round) as u32
    }

    pub(crate) fn challenge_offset(self) -> usize {
        self.start_round + 3
    }

    pub(crate) fn challenge_count(self) -> usize {
        self.folding_steps - self.challenge_offset()
    }

    pub(crate) fn eq_entry_sizes(self) -> GkrEqSizes {
        make_eq_sizes(self.challenge_count())
    }
}

/// Build exactly the continuation prefix already landed in the layer hook.
/// The caller supplies both W' and the tail-entry round so composition cannot
/// silently introduce a competing policy calculation.
pub(crate) fn plan_dr_window_continuations(
    folding_steps: usize,
    landed_window_count: usize,
    landed_entry_round: usize,
) -> Result<Vec<DrWindowContinuationPassGeometry>, DrWindowBindError> {
    if landed_window_count > 4 || landed_entry_round != 3 + 3 * landed_window_count {
        return Err(DrWindowBindError::ContinuationPlanMismatch {
            window_count: landed_window_count,
            entry_round: landed_entry_round,
        });
    }
    (0..landed_window_count)
        .map(|pass_index| DrWindowContinuationPassGeometry::new(folding_steps, 3 + 3 * pass_index))
        .collect()
}

/// Resolve the exact logical stride published by the final continuation.
/// A parity arena retains its larger first-use owner geometry, so selecting
/// the owner stride here would cross polynomial boundaries on reused arenas.
fn validate_dr_window_final_publication_stride(
    owner_log2_stride: u32,
    planned_log2_stride: u32,
) -> Result<usize, DrWindowBindError> {
    if owner_log2_stride < planned_log2_stride {
        return Err(DrWindowBindError::FinalPublicationStrideMismatch {
            owner_log2_stride,
            planned_log2_stride,
        });
    }
    Ok(1usize << planned_log2_stride)
}

#[derive(Default)]
pub(crate) struct DrWindowContinuationArenaOwners {
    pub(crate) even: Option<DrWindowContinuationArena>,
    pub(crate) odd: Option<DrWindowContinuationArena>,
}

impl DrWindowContinuationArenaOwners {
    pub(crate) fn get(
        &self,
        parity: DrWindowContinuationParity,
    ) -> Option<&DrWindowContinuationArena> {
        match parity {
            DrWindowContinuationParity::Even => self.even.as_ref(),
            DrWindowContinuationParity::Odd => self.odd.as_ref(),
        }
    }
}

/// One immutable continuation launch and the exact Eq state observed at its
/// entry and after its one tail fold.
pub(crate) struct DrWindowContinuationPass {
    pub(crate) geometry: DrWindowContinuationPassGeometry,
    pub(crate) launch: DrWindowContinuationLaunch,
    pub(crate) eq_entry: DrContinuationFactoredEqView,
}

/// The prepared R0 producer and the owners it keeps alive until the layer's
/// final queued consumer. R0's Eq state remains pass-local: later continuation
/// evaluators allocate a distinct Eq view and do not mutate it.
pub(crate) struct DrWindowLayerPreparationHook {
    pub(crate) r0_launch: DrWindowLaunch,
    pub(crate) continuation_window_count: usize,
    pub(crate) megakernel_entry_round: usize,
    pub(crate) r0_eq: DrWindowPassEqState,
    pub(crate) raw_inputs: DrWindowRawInputKeepalive,
    pub(crate) partials_capacity: usize,
}

impl DrWindowLayerPreparationHook {
    pub(crate) fn new(
        r0_launch: DrWindowLaunch,
        continuation_window_count: usize,
        megakernel_entry_round: usize,
        r0_eq: DrWindowPassEqState,
        raw_inputs: DrWindowRawInputKeepalive,
        partials_capacity: usize,
    ) -> Self {
        assert_eq!(
            megakernel_entry_round,
            3 + 3 * continuation_window_count,
            "the preflighted DR execution plan must use width-three boundaries",
        );
        assert!(
            megakernel_entry_round < r0_launch.folding_steps,
            "the recursive tail must own at least one round",
        );
        Self {
            r0_launch,
            continuation_window_count,
            megakernel_entry_round,
            r0_eq,
            raw_inputs,
            partials_capacity,
        }
    }

    /// Bind every continuation pass on top of the prepared R0 producer.
    pub(crate) fn activate<B>(
        self,
        program: &DrWindowLayerProgram,
        storage: &GpuGKRStorage<B, E4>,
        claim_point: *const E4,
        context: &ProverContext,
    ) -> Result<DrWindowLayerCompositionHook, DrWindowBindError> {
        let mut hook = DrWindowLayerCompositionHook {
            prepared: self,
            continuation_launches: Vec::new(),
            continuation_eq: None,
            continuation_arenas: DrWindowContinuationArenaOwners::default(),
        };
        bind_dr_window_continuations(&mut hook, program, storage, claim_point, context)?;
        Ok(hook)
    }
}

/// Whole-layer owner handed to D1/DR-cont once the continuation passes are
/// bound on top of the prepared R0 producer.
pub(crate) struct DrWindowLayerCompositionHook {
    pub(crate) prepared: DrWindowLayerPreparationHook,
    /// Stream-ordered continuation descriptors. Each record snapshots its own
    /// Eq entry and one-fold boundary rather than sharing mutable drain state.
    pub(crate) continuation_launches: Vec<DrWindowContinuationPass>,
    /// Exactly one DR-owned three-group Eq allocation when W'>0.
    pub(crate) continuation_eq: Option<DrContinuationFactoredEqScratch>,
    /// First-use-sized even/odd arena owners. Their `Rc` allocations keep all
    /// raw pointers in the launch descriptors alive through the final queued
    /// consumer.
    pub(crate) continuation_arenas: DrWindowContinuationArenaOwners,
}

impl DrWindowLayerCompositionHook {
    /// Canonical input pointers at the exact state consumed by the recursive
    /// tail. With W'=0 the megakernel performs the first three folds from raw
    /// storage. Otherwise it consumes the last continuation's destination;
    /// the megakernel itself folds that pass's three pending challenges.
    pub(crate) fn megakernel_source_pointers<B>(
        &self,
        program: &DrWindowLayerProgram,
        storage: &GpuGKRStorage<B, E4>,
    ) -> Result<Vec<*const E4>, DrWindowBindError> {
        let projection = program.input_projection();
        let canonical_count = projection.canonical_sources().len();
        if let Some(last) = self.continuation_launches.last() {
            let arena = self
                .continuation_arenas
                .get(last.geometry.destination())
                .expect("the final continuation destination must remain owned");
            assert_eq!(arena.poly_count(), canonical_count);
            let binding = arena.binding();
            // Parity owners retain their first-use (largest) geometry. A later
            // same-parity pass reuses the base with a smaller logical stride,
            // which is recorded on that immutable pass rather than the owner.
            let stride = validate_dr_window_final_publication_stride(
                binding.log2_stride,
                last.geometry.log2_stride(),
            )?;
            Ok((0..canonical_count)
                .map(|poly_idx| {
                    // SAFETY: the arena owns `canonical_count * stride` E4
                    // cells and remains live through every queued consumer.
                    unsafe { binding.base.cast::<E4>().add(poly_idx * stride) }
                })
                .collect())
        } else {
            self.prepared
                .raw_inputs
                .canonical_source_pointers(storage, projection)
        }
    }
}
