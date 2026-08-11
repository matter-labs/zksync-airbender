use std::collections::BTreeMap;

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;

use super::kernels::{ClaimBufferLayout, DeviceClaimPointAndBatching};
use crate::upstream::GKRAddress;
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::context::{DeviceAllocation, UnsafeMutAccessor};
use gpu_core::primitives::field::E4;
use gpu_prover_context::ProverContext;

#[doc(hidden)]
#[derive(Debug, PartialEq, Eq)]
pub struct GKRBackwardStageSnapshot {
    pub layer_idx: usize,
    pub claim_point: Vec<E4>,
    pub batching_challenge: E4,
    pub claims: BTreeMap<GKRAddress, E4>,
}

#[doc(hidden)]
#[derive(Default)]
pub struct GKRBackwardStageSnapshotSink {
    snapshots: Vec<GKRBackwardStageSnapshot>,
}

impl GKRBackwardStageSnapshotSink {
    pub fn into_snapshots(self) -> Vec<GKRBackwardStageSnapshot> {
        self.snapshots
    }
}

pub(super) fn schedule_stage_snapshot(
    layer_idx: usize,
    point_and_batching: &DeviceClaimPointAndBatching,
    claims: &DeviceAllocation<E4>,
    claim_layout: &ClaimBufferLayout,
    output: UnsafeMutAccessor<GKRBackwardStageSnapshotSink>,
    callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
) -> CudaResult<()> {
    assert_eq!(claims.len(), claim_layout.claim_count());
    let stream = context.get_exec_stream();
    let mut point_host = unsafe { context.alloc_host_uninit_slice(point_and_batching.len()) };
    let mut claims_host = unsafe { context.alloc_host_uninit_slice(claims.len()) };
    memory_copy_async(
        &mut point_host,
        point_and_batching.slice(0, point_and_batching.len()),
        stream,
    )?;
    memory_copy_async(&mut claims_host, claims, stream)?;

    let point_host = point_host.get_accessor();
    let claims_host = claims_host.get_accessor();
    let addresses = claim_layout.addresses.clone();
    callbacks.schedule(
        move || {
            let point_and_batching = unsafe { point_host.get() };
            let (&batching_challenge, claim_point) = point_and_batching
                .split_last()
                .expect("stage snapshot must contain a batching challenge");
            let claims = addresses
                .iter()
                .copied()
                .zip(unsafe { claims_host.get() }.iter().copied())
                .collect();
            unsafe { output.get_mut() }
                .snapshots
                .push(GKRBackwardStageSnapshot {
                    layer_idx,
                    claim_point: claim_point.to_vec(),
                    batching_challenge,
                    claims,
                });
        },
        stream,
    )
}
