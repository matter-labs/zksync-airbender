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

use crate::backward::{make_eq_sizes, GkrEqSizes, GKR_EQ_GROUP_TABLE_LEN};
use crate::upstream::GKRAddress;
use crate::GpuGKRStorage;

use super::binding::{
    resolve_storage_e4, DrWindowBindError, DrWindowLaunch, DrWindowR0Preparation,
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

/// Whole-layer owner handed to D1/DR-cont after the R0 producer is prepared.
/// R0's Eq state remains pass-local: later continuation evaluators allocate a
/// distinct Eq view and do not mutate this persistent tail state.
pub(crate) struct DrWindowLayerCompositionHook {
    pub(crate) r0_launch: DrWindowLaunch,
    pub(crate) continuation_window_count: usize,
    pub(crate) megakernel_entry_round: usize,
    pub(crate) r0_eq: DrWindowPassEqState,
    pub(crate) raw_inputs: DrWindowRawInputKeepalive,
    pub(crate) partials_capacity: usize,
    /// Immutable producer program retained for continuation batch assembly.
    pub(crate) continuation_program: DrWindowProgram,
    /// Immutable canonical input-only publication map for every continuation.
    pub(crate) continuation_projection: DrWindowInputProjection,
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
            r0_eq,
            raw_inputs,
            partials_capacity,
            continuation_program,
            continuation_projection,
        }
    }
}

/// Allocation-neutral Task 6 preparation retained for a future complete-chain
/// launch. The non-owning Eq view borrows the common round scratch; no runtime
/// partials pointer or launch-ready descriptor is retained here.
pub(crate) struct DrWindowLayerPreparationHook {
    pub(crate) r0: DrWindowR0Preparation,
    pub(crate) continuation_window_count: usize,
    pub(crate) megakernel_entry_round: usize,
    pub(crate) r0_eq: DrWindowPassEqView,
    pub(crate) raw_inputs: DrWindowRawInputKeepalive,
    pub(crate) required_future_partials_len: usize,
}

impl DrWindowLayerPreparationHook {
    pub(crate) fn new(
        r0: DrWindowR0Preparation,
        r0_eq: DrWindowPassEqView,
        raw_inputs: DrWindowRawInputKeepalive,
    ) -> Self {
        let folding_steps = r0.folding_steps;
        let required_future_partials_len = r0.required_future_partials_len;
        Self {
            r0,
            continuation_window_count: continuation_window_count(folding_steps),
            megakernel_entry_round: megakernel_entry_round(folding_steps),
            r0_eq,
            raw_inputs,
            required_future_partials_len,
        }
    }
}
