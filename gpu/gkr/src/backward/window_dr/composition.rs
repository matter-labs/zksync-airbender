// Task 4 consumes the R0 eq/keepalive owners; D1/DR-cont extends composition.
#![allow(dead_code)]

use std::collections::BTreeSet;
use std::sync::Arc;

use era_cudart::result::CudaResult;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::E4;
use gpu_gkr_compiler::DrWindowInputProjection;
use gpu_prover_context::ProverContext;

use crate::backward::{make_eq_sizes, GkrEqSizes, GKR_EQ_GROUP_TABLE_LEN};
use crate::upstream::GKRAddress;
use crate::GpuGKRStorage;

use super::binding::{resolve_storage_e4, DrWindowBindError};

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
