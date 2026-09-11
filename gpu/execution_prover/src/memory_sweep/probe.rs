// Ported from dev's memory_sweep/probe.rs: normal target placement plus
// reversed placement for the largest follower's complete production inputs.
use crate::messages::GpuWorkRequest;
use crate::upstream::{DefaultTreeConstructor, GKRProof, MerkleTreeCapVarLength};
use crate::workers::gpu::{
    enqueue_phase_two, finish_sweep_memory, finish_sweep_proof,
    schedule_phase_one_with_policy_override,
};
use crate::A;
use era_cudart::result::CudaResult;
use gpu_circuit_prover::proof::memory_policy::ProofMemoryPolicy;
use gpu_core::primitives::field::{BF, E4};
use gpu_prover_context::ProverContext;
use std::hash::{Hash, Hasher};

pub(super) fn drain(context: &ProverContext) -> CudaResult<()> {
    context.get_h2d_stream().synchronize()?;
    context.get_exec_stream().synchronize()?;
    context.get_side_stream().synchronize()
}

pub(super) fn commit_memory(
    device_id: i32,
    context: &ProverContext,
    request: GpuWorkRequest<A>,
) -> CudaResult<Vec<MerkleTreeCapVarLength>> {
    let result = (|| {
        let phase = schedule_phase_one_with_policy_override(
            device_id,
            context,
            request,
            Some(Default::default()),
        )?;
        finish_sweep_memory(enqueue_phase_two(device_id, context, phase)?)
    })();
    drain(context)?;
    result
}

/// Cross-check the factory's largest-follower accounting against real input
/// transfers. This diagnostic is outside all timed proof ranges.
pub(super) fn input_footprint(
    device_id: i32,
    context: &ProverContext,
    request: GpuWorkRequest<A>,
) -> CudaResult<usize> {
    let before = context.get_used_mem_current();
    let phase = schedule_phase_one_with_policy_override(
        device_id,
        context,
        request,
        Some(Default::default()),
    );
    drain(context)?;
    let phase = phase?;
    let bytes = context.get_used_mem_current() - before;
    drop(phase);
    Ok(bytes)
}

pub(super) struct Sample {
    pub elapsed_ms: f32,
    pub fingerprint: u64,
}

pub(super) fn run_case(
    device_id: i32,
    context: &mut ProverContext,
    target_request: GpuWorkRequest<A>,
    target_override: Option<ProofMemoryPolicy>,
    follower_request: GpuWorkRequest<A>,
) -> CudaResult<(Sample, ProofMemoryPolicy)> {
    // On pool OOM, queued operations must finish before freed arena ranges can
    // be reused. The runner retains PreparedCircuit host inputs throughout.
    context.set_reversed_allocation_placement(false);
    let target = schedule_phase_one_with_policy_override(
        device_id,
        context,
        target_request,
        target_override,
    );
    let target = match target {
        Ok(target) => target,
        Err(e) => {
            drain(context)?;
            return Err(e);
        }
    };
    let policy = target.policy();
    // Complete the target H2D before an enqueue error can release tiny
    // scheduler-owned pinned sources. Follower H2D still overlaps the proof.
    context.get_h2d_stream().synchronize()?;
    context.set_reversed_allocation_placement(true);
    // The follower is never proved; its policy only has to be admissible, so
    // the sweep pins the default while replay exercises production selection.
    let follower_override = target_override.map(|_| ProofMemoryPolicy::default());
    let follower = schedule_phase_one_with_policy_override(
        device_id,
        context,
        follower_request,
        follower_override,
    );
    context.set_reversed_allocation_placement(false);
    let result = match &follower {
        Ok(_) => enqueue_phase_two(device_id, context, target).and_then(finish_sweep_proof),
        Err(error) => {
            drain(context)?;
            drop(target);
            Err(*error)
        }
    };
    // The follower is not proved: target.finish() alone does not join its H2D.
    drain(context)?;
    drop(follower);
    result.map(|(proof, elapsed_ms)| {
        (
            Sample {
                elapsed_ms,
                fingerprint: fingerprint(&proof),
            },
            policy,
        )
    })
}

fn fingerprint(proof: &GKRProof<BF, E4, DefaultTreeConstructor>) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    serde_json::to_vec(proof)
        .expect("serializable proof")
        .hash(&mut hasher);
    hasher.finish()
}
