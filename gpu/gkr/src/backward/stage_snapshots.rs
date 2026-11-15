use std::collections::BTreeMap;

use era_cudart::{memory::memory_copy_async, result::CudaResult, slice::DeviceSlice};
use gpu_core::primitives::{callbacks::Callbacks, context::UnsafeMutAccessor, field::E4};
use gpu_prover_context::ProverContext;

use crate::{backward::kernels::ClaimBufferLayout, upstream::GKRAddress};

#[doc(hidden)]
#[derive(Debug, PartialEq, Eq)]
pub struct GKRBackwardStageSnapshot<F = E4> {
    pub layer_idx: usize,
    pub claim_point: Vec<F>,
    pub batching_challenge: F,
    pub claims: BTreeMap<GKRAddress, F>,
}

#[doc(hidden)]
#[derive(Default)]
pub struct GKRBackwardStageSnapshotSink<F = E4> {
    snapshots: Vec<GKRBackwardStageSnapshot<F>>,
}

impl<F> GKRBackwardStageSnapshotSink<F> {
    pub fn into_snapshots(self) -> Vec<GKRBackwardStageSnapshot<F>> {
        self.snapshots
    }
}

pub(crate) fn schedule_stage_snapshot_fields<F: Copy + Send + Sync + 'static>(
    layer_idx: usize,
    point_and_batching: &DeviceSlice<F>,
    claims: &DeviceSlice<F>,
    claim_layout: &ClaimBufferLayout,
    output: UnsafeMutAccessor<GKRBackwardStageSnapshotSink<F>>,
    callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
) -> CudaResult<()> {
    assert_eq!(claims.len(), claim_layout.claim_count());
    let stream = context.get_exec_stream();
    let mut point_host = unsafe { context.alloc_host_uninit_slice(point_and_batching.len()) };
    let mut claims_host = unsafe { context.alloc_host_uninit_slice(claims.len()) };
    memory_copy_async(&mut point_host, point_and_batching, stream)?;
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
