use era_cudart::result::CudaResult;
use gpu_core::primitives::{
    callbacks::Callbacks,
    context::{DeviceAllocation, UnsafeMutAccessor},
    field::E4,
};
use gpu_prover_context::ProverContext;

use crate::{
    baby_bear::backward::kernels::DeviceClaimPointAndBatching,
    backward::{kernels::ClaimBufferLayout, stage_snapshots::*},
};

pub(super) fn schedule_stage_snapshot(
    layer_idx: usize,
    point_and_batching: &DeviceClaimPointAndBatching,
    claims: &DeviceAllocation<E4>,
    claim_layout: &ClaimBufferLayout,
    output: UnsafeMutAccessor<GKRBackwardStageSnapshotSink>,
    callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
) -> CudaResult<()> {
    schedule_stage_snapshot_fields(
        layer_idx,
        point_and_batching.slice(0, point_and_batching.len()),
        claims,
        claim_layout,
        output,
        callbacks,
        context,
    )
}
