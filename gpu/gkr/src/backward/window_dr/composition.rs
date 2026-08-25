// Task 6 consumes the R0 hook; D1/DR-cont extends it with continuation state.
#![allow(dead_code)]

use std::collections::BTreeSet;
use std::sync::Arc;

use era_cudart::result::CudaResult;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::E4;
use gpu_gkr_compiler::{DrWindowInputProjection, DrWindowProgram};
use gpu_prover_context::ProverContext;

use crate::backward::kernels::record_active_eq_slot_fold;
use crate::backward::{make_eq_sizes, GkrEqSizes, GKR_EQ_GROUP_TABLE_LEN};
use crate::upstream::GKRAddress;
use crate::GpuGKRStorage;

use super::binding::{
    bind_dr_window_continuations, dr_window_partials_len, resolve_storage_e4,
    DrContinuationFactoredEqScratch, DrContinuationFactoredEqView, DrWindowBindError,
    DrWindowContinuationArena, DrWindowContinuationLaunch, DrWindowLaunch,
};

#[derive(Clone, Copy)]
pub(crate) struct DrWindowPassEqView {
    pub(crate) eq_low: *const E4,
    pub(crate) eq_sizes: GkrEqSizes,
    pub(crate) build_offset: usize,
}

impl DrWindowPassEqView {
    pub(crate) fn new(eq_low: *const E4, eq_sizes: GkrEqSizes, build_offset: usize) -> Self {
        Self {
            eq_low,
            eq_sizes,
            build_offset,
        }
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
    pub(crate) fn allocate(
        context: &ProverContext,
        build_offset: usize,
        challenge_count: usize,
    ) -> CudaResult<Self> {
        Ok(Self {
            eq_low: context.alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::Top)?,
            eq_sizes: make_eq_sizes(challenge_count),
            build_offset,
        })
    }

    pub(crate) fn as_view(&self) -> DrWindowPassEqView {
        DrWindowPassEqView::new(self.eq_low.as_ptr(), self.eq_sizes, self.build_offset)
    }
}

pub(crate) struct DrWindowRawInputKeepalive {
    pub(crate) canonical_sources: Vec<GKRAddress>,
    pub(crate) backings: Vec<Arc<DeviceAllocation<E4>>>,
}

impl DrWindowRawInputKeepalive {
    pub(crate) fn from_projection<B>(
        storage: &GpuGKRStorage<B, E4>,
        projection: &DrWindowInputProjection,
    ) -> Result<Self, DrWindowBindError> {
        let owner = build_raw_input_owner(projection, |address| {
            resolve_storage_e4(storage, address).map(|resolved| Arc::clone(resolved.backing))
        })?;
        Ok(Self {
            canonical_sources: owner.canonical_sources,
            backings: owner.backings,
        })
    }

    fn canonical_source_pointers<B>(
        &self,
        storage: &GpuGKRStorage<B, E4>,
    ) -> Result<Vec<*const E4>, DrWindowBindError> {
        self.canonical_sources
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

pub(super) struct DrWindowRawInputOwner<T> {
    pub(super) canonical_sources: Vec<GKRAddress>,
    pub(super) backings: Vec<Arc<T>>,
}

pub(super) fn build_raw_input_owner<T, Error>(
    projection: &DrWindowInputProjection,
    mut resolve: impl FnMut(GKRAddress) -> Result<Arc<T>, Error>,
) -> Result<DrWindowRawInputOwner<T>, Error> {
    let canonical_sources = projection.canonical_sources().to_vec();
    let mut seen = BTreeSet::new();
    let mut backings = Vec::new();
    for &address in &canonical_sources {
        let backing = resolve(address)?;
        if seen.insert(Arc::as_ptr(&backing) as usize) {
            backings.push(backing);
        }
    }
    Ok(DrWindowRawInputOwner {
        canonical_sources,
        backings,
    })
}

pub(crate) fn continuation_window_count(folding_steps: usize) -> usize {
    (folding_steps.saturating_sub(4) / 3).min(4)
}

pub(crate) fn megakernel_entry_round(folding_steps: usize) -> usize {
    3 + 3 * continuation_window_count(folding_steps)
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

/// Allocation-neutral geometry for one continuation pass. The Eq entry and
/// boundary descriptors are both immutable: consumers must never carry a
/// mutable cumulative drain from one record into the next.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct DrWindowContinuationPassGeometry {
    pub(crate) pass_index: usize,
    pub(crate) start_round: usize,
    pub(crate) source: DrWindowContinuationPlannedSource,
    pub(crate) destination: DrWindowContinuationParity,
    pub(crate) per_poly_len: usize,
    pub(crate) log2_stride: u32,
    pub(crate) eq_entry_sizes: GkrEqSizes,
    pub(crate) one_fold_boundary_sizes: GkrEqSizes,
    pub(crate) challenge_offset: usize,
    pub(crate) challenge_count: usize,
    pub(crate) partials_len: usize,
}

pub(crate) fn dr_window_continuation_pass_geometry(
    folding_steps: usize,
    start_round: usize,
) -> Result<DrWindowContinuationPassGeometry, DrWindowBindError> {
    if start_round < 3 || start_round % 3 != 0 || start_round + 3 >= folding_steps {
        return Err(DrWindowBindError::InvalidContinuationBoundary {
            folding_steps,
            start_round,
        });
    }
    let pass_index = (start_round - 3) / 3;
    let log2_stride = folding_steps + 1 - start_round;
    let challenge_offset = start_round + 3;
    let challenge_count = folding_steps - challenge_offset;
    let eq_entry_sizes = make_eq_sizes(challenge_count);
    let mut one_fold_boundary_sizes = eq_entry_sizes;
    record_active_eq_slot_fold(&mut one_fold_boundary_sizes);
    let destination = if pass_index % 2 == 0 {
        DrWindowContinuationParity::Even
    } else {
        DrWindowContinuationParity::Odd
    };
    let source = if pass_index == 0 {
        DrWindowContinuationPlannedSource::Raw
    } else {
        DrWindowContinuationPlannedSource::Arena(if pass_index % 2 == 0 {
            DrWindowContinuationParity::Odd
        } else {
            DrWindowContinuationParity::Even
        })
    };
    Ok(DrWindowContinuationPassGeometry {
        pass_index,
        start_round,
        source,
        destination,
        per_poly_len: 1usize << log2_stride,
        log2_stride: log2_stride as u32,
        eq_entry_sizes,
        one_fold_boundary_sizes,
        challenge_offset,
        challenge_count,
        partials_len: dr_window_partials_len(folding_steps - start_round),
    })
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
        .map(|pass_index| dr_window_continuation_pass_geometry(folding_steps, 3 + 3 * pass_index))
        .collect()
}

/// Resolve the exact logical stride published by the final continuation.
/// A parity arena retains its larger first-use owner geometry, so selecting
/// the owner stride here would cross polynomial boundaries on reused arenas.
pub(crate) fn validate_dr_window_final_publication_stride(
    owner_log2_stride: u32,
    planned_log2_stride: u32,
    planned_per_poly_len: usize,
    selected_log2_stride: u32,
) -> Result<usize, DrWindowBindError> {
    let expected = 1usize.checked_shl(planned_log2_stride);
    if owner_log2_stride < planned_log2_stride
        || selected_log2_stride != planned_log2_stride
        || expected != Some(planned_per_poly_len)
    {
        return Err(DrWindowBindError::FinalPublicationStrideMismatch {
            owner_log2_stride,
            planned_log2_stride,
            planned_per_poly_len,
            selected_log2_stride,
        });
    }
    Ok(planned_per_poly_len)
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
    pub(crate) one_fold_boundary_sizes: GkrEqSizes,
}

/// Whole-layer owner handed to D1/DR-cont after the R0 producer is prepared.
/// R0's Eq state remains pass-local: later continuation evaluators allocate a
/// distinct Eq view and do not mutate this persistent tail state.
pub(crate) struct DrWindowLayerCompositionHook {
    pub(crate) r0_launch: DrWindowLaunch,
    pub(crate) continuation_window_count: usize,
    pub(crate) megakernel_entry_round: usize,
    pub(crate) continuation_readiness: DrWindowContinuationReadiness,
    pub(crate) r0_eq: DrWindowPassEqState,
    pub(crate) raw_inputs: DrWindowRawInputKeepalive,
    pub(crate) partials_capacity: usize,
    /// Immutable producer program retained for continuation batch assembly.
    pub(crate) continuation_program: DrWindowProgram,
    /// Immutable canonical input-only publication map for every continuation.
    pub(crate) continuation_projection: DrWindowInputProjection,
    /// Stream-ordered continuation descriptors. Each record snapshots its own
    /// Eq entry and one-fold boundary rather than sharing mutable drain state.
    pub(crate) continuation_launches: Vec<DrWindowContinuationPass>,
    /// Exactly one DR-owned three-group Eq allocation when W'>0.
    pub(crate) continuation_eq: Option<DrContinuationFactoredEqScratch>,
    /// First-use-sized even/odd arena owners. Their `Arc` allocations keep all
    /// raw pointers in the launch descriptors alive through the final queued
    /// consumer.
    pub(crate) continuation_arenas: DrWindowContinuationArenaOwners,
    /// Explicit allocation keepalives mirror the parity owners so later hook
    /// reshaping cannot shorten the lifetime of already queued descriptors.
    /// Cloning these `Arc`s never allocates another device backing.
    pub(crate) continuation_keepalives: Vec<Arc<DeviceAllocation<E4>>>,
}

impl DrWindowLayerCompositionHook {
    pub(crate) fn new(
        r0_launch: DrWindowLaunch,
        r0_eq: DrWindowPassEqState,
        raw_inputs: DrWindowRawInputKeepalive,
        partials_capacity: usize,
        continuation_program: DrWindowProgram,
        continuation_projection: DrWindowInputProjection,
    ) -> Self {
        let folding_steps = r0_launch.folding_steps;
        Self {
            r0_launch,
            continuation_window_count: continuation_window_count(folding_steps),
            megakernel_entry_round: megakernel_entry_round(folding_steps),
            continuation_readiness: DrWindowContinuationReadiness::Disabled,
            r0_eq,
            raw_inputs,
            partials_capacity,
            continuation_program,
            continuation_projection,
            continuation_launches: Vec::new(),
            continuation_eq: None,
            continuation_arenas: DrWindowContinuationArenaOwners::default(),
            continuation_keepalives: Vec::new(),
        }
    }

    /// Canonical input pointers at the exact state consumed by the recursive
    /// tail. With W'=0 the megakernel performs the first three folds from raw
    /// storage. Otherwise it consumes the last continuation's destination;
    /// the megakernel itself folds that pass's three pending challenges.
    pub(crate) fn megakernel_source_pointers<B>(
        &self,
        storage: &GpuGKRStorage<B, E4>,
    ) -> Result<Vec<*const E4>, DrWindowBindError> {
        let canonical_count = self.continuation_projection.canonical_sources().len();
        assert_eq!(self.raw_inputs.canonical_sources.len(), canonical_count);
        if let Some(last) = self.continuation_launches.last() {
            let arena = self
                .continuation_arenas
                .get(last.geometry.destination)
                .expect("the final continuation destination must remain owned");
            assert_eq!(arena.poly_count(), canonical_count);
            let binding = arena.binding();
            // Parity owners retain their first-use (largest) geometry. A later
            // same-parity pass reuses the base with a smaller logical stride,
            // which is recorded on that immutable pass rather than the owner.
            let stride = validate_dr_window_final_publication_stride(
                binding.log2_stride,
                last.geometry.log2_stride,
                last.geometry.per_poly_len,
                last.geometry.log2_stride,
            )?;
            Ok((0..canonical_count)
                .map(|poly_idx| {
                    // SAFETY: the arena owns `canonical_count * stride` E4
                    // cells and remains live through every queued consumer.
                    unsafe { binding.base.cast::<E4>().add(poly_idx * stride) }
                })
                .collect())
        } else {
            self.raw_inputs.canonical_source_pointers(storage)
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DrWindowContinuationReadiness {
    Disabled,
    ProducerReady,
}

pub(crate) fn dr_window_continuation_readiness(
    options: crate::GkrBackwardOptions,
    strategy: crate::BackwardExecutionStrategy,
    bundle_ready: bool,
) -> Result<DrWindowContinuationReadiness, crate::DrWindowContinuationPreflightError> {
    if !options.windowed_dr_continuations {
        return Ok(DrWindowContinuationReadiness::Disabled);
    }
    if strategy != crate::BackwardExecutionStrategy::WindowedR0 {
        return Err(crate::DrWindowContinuationPreflightError::RequiresWindowedSchedule);
    }
    if !options.windowed_dr {
        return Err(crate::DrWindowContinuationPreflightError::IncompleteChain {
            windowed_r0: false,
            continuations: true,
            recursive_tail: false,
        });
    }
    if !bundle_ready {
        return Err(crate::DrWindowContinuationPreflightError::BundleNotReady);
    }
    Ok(DrWindowContinuationReadiness::ProducerReady)
}

/// Task 6 preparation retained until the complete-chain launch is bound. It
/// owns the common round Eq allocation while round scratch keeps only the same
/// launch pointer; the partials owner remains in the enclosing layer plan.
pub(crate) struct DrWindowLayerPreparationHook {
    pub(crate) r0_launch: DrWindowLaunch,
    pub(crate) continuation_window_count: usize,
    pub(crate) megakernel_entry_round: usize,
    pub(crate) continuation_readiness: DrWindowContinuationReadiness,
    pub(crate) r0_eq: DrWindowPassEqState,
    pub(crate) raw_inputs: DrWindowRawInputKeepalive,
    pub(crate) required_future_partials_len: usize,
    pub(crate) continuation_program: DrWindowProgram,
    pub(crate) continuation_projection: DrWindowInputProjection,
}

impl DrWindowLayerPreparationHook {
    pub(crate) fn new(
        r0_launch: DrWindowLaunch,
        r0_eq: DrWindowPassEqState,
        raw_inputs: DrWindowRawInputKeepalive,
        required_future_partials_len: usize,
        continuation_program: DrWindowProgram,
        continuation_projection: DrWindowInputProjection,
    ) -> Self {
        let folding_steps = r0_launch.folding_steps;
        Self {
            r0_launch,
            continuation_window_count: continuation_window_count(folding_steps),
            megakernel_entry_round: megakernel_entry_round(folding_steps),
            continuation_readiness: DrWindowContinuationReadiness::Disabled,
            r0_eq,
            raw_inputs,
            required_future_partials_len,
            continuation_program,
            continuation_projection,
        }
    }

    pub(crate) fn activate<B>(
        self,
        storage: &GpuGKRStorage<B, E4>,
        claim_point: *const E4,
        context: &ProverContext,
    ) -> Result<DrWindowLayerCompositionHook, DrWindowBindError> {
        assert_eq!(
            self.continuation_readiness,
            DrWindowContinuationReadiness::ProducerReady,
            "production activation requires the preflighted continuation chain",
        );
        let mut hook = DrWindowLayerCompositionHook::new(
            self.r0_launch,
            self.r0_eq,
            self.raw_inputs,
            self.required_future_partials_len,
            self.continuation_program,
            self.continuation_projection,
        );
        bind_dr_window_continuations(&mut hook, storage, claim_point, context)?;
        Ok(hook)
    }

    pub(crate) fn configure_continuation_readiness(
        &mut self,
        options: crate::GkrBackwardOptions,
        strategy: crate::BackwardExecutionStrategy,
        bundle_ready: bool,
    ) -> Result<(), crate::DrWindowContinuationPreflightError> {
        self.continuation_readiness =
            dr_window_continuation_readiness(options, strategy, bundle_ready)?;
        Ok(())
    }
}
