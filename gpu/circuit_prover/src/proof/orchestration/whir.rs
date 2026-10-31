use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;

use crate::proof::memory_policy::ProofMemoryPolicy;
use crate::upstream::{BaseCommitmentGeometry, GKRCircuitArtifact, WhirSchedule};
use gpu_core::primitives::context::{DeviceAllocation, UnsafeAccessor};
use gpu_core::primitives::field::{BF, E4};
use gpu_gkr::backward::GpuGKRBackwardScheduledExecution;
use gpu_gkr::base_layer_claims::{
    schedule_prepare_base_layer_claims_with_sources, GpuGKRBaseLayerClaimsScheduledExecution,
    ScheduledBaseLayerClaimsState,
};
use gpu_gkr::proof_layout::ProofLayout;
use gpu_gkr::setup::GpuGKRSetupTransfer;
use gpu_gkr::stage1::GpuGKRStage1Output;
use gpu_prover_context::ProverContext;
use gpu_trace::trace::holder::TraceHolder;
use gpu_whir::fold::{schedule_gpu_whir_fold_with_sources, GpuWhirFoldScheduledExecution};

pub(in crate::proof) struct WhirPhaseResult {
    pub(in crate::proof) base_layer_claims_scheduled: GpuGKRBaseLayerClaimsScheduledExecution,
    pub(in crate::proof) base_layer_claims_shared_state:
        UnsafeAccessor<ScheduledBaseLayerClaimsState>,
    pub(in crate::proof) whir_scheduled: GpuWhirFoldScheduledExecution,
}

pub(in crate::proof) fn schedule_whir_phase<'a>(
    compiled_circuit: &GKRCircuitArtifact<BF>,
    base_geometry: BaseCommitmentGeometry,
    whir_schedule: &WhirSchedule,
    setup_transfer: &mut Option<GpuGKRSetupTransfer<'a>>,
    synthetic_setup_trace_holder: &mut Option<TraceHolder<BF>>,
    stage1_output: &mut GpuGKRStage1Output,
    backward_scheduled: &mut GpuGKRBackwardScheduledExecution,
    proof_slab: &DeviceAllocation<E4>,
    proof_layout: &ProofLayout,
    batching_pow_bits: u32,
    memory_policy: ProofMemoryPolicy,
    context: &ProverContext,
) -> CudaResult<WhirPhaseResult> {
    let setup_trace_holder = setup_transfer
        .as_ref()
        .map(|setup| &setup.trace_holder)
        .unwrap_or_else(|| {
            synthetic_setup_trace_holder
                .as_ref()
                .expect("setup-less proof path must materialize a synthetic setup holder")
        });
    let final_claim_addresses = backward_scheduled.final_claim_addresses().to_vec();
    let (final_device_seed, final_device_claim_point) =
        backward_scheduled.final_device_seed_and_claim_point_mut();
    let base_layer_claims_scheduled = schedule_prepare_base_layer_claims_with_sources(
        compiled_circuit.layers[0].clone(),
        final_device_claim_point,
        // Layer-1 incoming claim addresses are schedule-time-known (the
        // `ClaimBufferLayout` built when backward staged its final claims),
        // so the base-layer extras plan is built without a host claim map.
        &final_claim_addresses,
        setup_trace_holder,
        &stage1_output.memory_trace_holder,
        &stage1_output.witness_trace_holder,
        stage1_output.merged_witness_offset,
        proof_slab,
        proof_layout,
        final_device_seed,
        context,
    )?;
    let base_layer_claims_shared_state = base_layer_claims_scheduled.shared_state_handle();
    let setup_trace_holder = setup_transfer
        .as_mut()
        .map(|setup| &mut setup.trace_holder)
        .unwrap_or_else(|| synthetic_setup_trace_holder.as_mut().unwrap());
    setup_trace_holder.defer_materialization_until_queries(memory_policy.setup);
    stage1_output
        .memory_trace_holder
        .defer_materialization_until_queries(memory_policy.memory);

    let (seed, logical_point) = backward_scheduled.final_device_seed_and_claim_point_mut();
    schedule_base_commitment_handoff(
        base_geometry,
        logical_point,
        seed,
        proof_slab,
        proof_layout,
        batching_pow_bits,
        context,
    )?;
    // SAFETY: these slab regions were initialized by the handoff on exec and
    // remain live through the WHIR scheduler and terminal readback.
    let (point_ptr, point_len) = unsafe {
        proof_layout.whir_original_evaluation_point_device_mut(proof_slab.as_ptr() as *mut u8)
    };
    let point = unsafe { DeviceSlice::from_raw_parts_mut(point_ptr, point_len) };
    let (batching_ptr, batching_len) =
        unsafe { proof_layout.whir_batching_challenge_device_mut(proof_slab.as_ptr() as *mut u8) };
    let batching_challenge_device =
        unsafe { DeviceSlice::from_raw_parts(batching_ptr, batching_len) };
    let whir_scheduled = {
        let setup_trace_holder = if let Some(setup_transfer) = setup_transfer.as_mut() {
            &mut setup_transfer.trace_holder
        } else {
            synthetic_setup_trace_holder
                .as_mut()
                .expect("setup-less proof path must materialize a synthetic setup holder")
        };
        let (final_device_seed_mut, _claim_point) =
            backward_scheduled.final_device_seed_and_claim_point_mut();
        let folding_pow_bits: Vec<u32> = whir_schedule
            .internal_rounds
            .iter()
            .map(|round| round.folding_pow_bits)
            .collect();
        let ood_pow_bits: Vec<u32> = whir_schedule
            .internal_rounds
            .iter()
            .map(|round| round.ood_pow_bits)
            .collect();
        schedule_gpu_whir_fold_with_sources(
            &mut stage1_output.memory_trace_holder,
            &mut stage1_output.witness_trace_holder,
            setup_trace_holder,
            point,
            final_device_seed_mut,
            batching_challenge_device,
            whir_schedule.base_lde_factor(),
            whir_schedule.fold_steps(),
            whir_schedule.queries_per_round(),
            whir_schedule.intermediate_lde_factors(),
            whir_schedule.queries_pow_bits_per_round(),
            &folding_pow_bits,
            &ood_pow_bits,
            whir_schedule.cap_size,
            u32::try_from(base_geometry.message_size_log2()).expect("message log2 exceeds u32"),
            true, // use_hypercube_evals_for_batching
            proof_slab,
            proof_layout,
            context,
        )?
    };

    Ok(WhirPhaseResult {
        base_layer_claims_scheduled,
        base_layer_claims_shared_state,
        whir_scheduled,
    })
}

/// Device-only boundary shared by proof orchestration and protocol parity tests.
/// Physical packing extends the logical point; virtual packing adds no draw.
pub(crate) fn schedule_base_commitment_handoff(
    base_geometry: BaseCommitmentGeometry,
    logical_point: &DeviceSlice<E4>,
    seed: &mut DeviceSlice<u32>,
    proof_slab: &DeviceAllocation<E4>,
    proof_layout: &ProofLayout,
    batching_pow_bits: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    // SAFETY: the point and logical/packed claim ranges are disjoint, aligned
    // slab regions. All device readers/writers are ordered on exec and the slab
    // remains live through terminal readback.
    let (point_ptr, point_len) = unsafe {
        proof_layout.whir_original_evaluation_point_device_mut(proof_slab.as_ptr() as *mut u8)
    };
    assert_eq!(
        point_len,
        base_geometry.message_size_log2(),
        "WHIR point slab differs from preflight geometry"
    );
    let point = unsafe { DeviceSlice::from_raw_parts_mut(point_ptr, point_len) };
    {
        assert_eq!(logical_point.len(), base_geometry.trace_len_log2());
        let (prefix, coordinates) = point.split_at_mut(logical_point.len());
        memory_copy_async(prefix, logical_point, context.get_exec_stream())?;
        if base_geometry.pack_log2() != 0 {
            gpu_hash::blake2s::transcript_squeeze_fresh_e4(
                seed,
                coordinates,
                context.get_exec_stream(),
            )?;
            for kind in [
                gpu_gkr::proof_layout::WhirBaseLayerKind::Memory,
                gpu_gkr::proof_layout::WhirBaseLayerKind::Witness,
                gpu_gkr::proof_layout::WhirBaseLayerKind::Setup,
            ] {
                let (src, src_len) = unsafe {
                    proof_layout
                        .whir_base_logical_evals_device_mut(proof_slab.as_ptr() as *mut u8, kind)
                };
                let (dst, dst_len) = unsafe {
                    proof_layout.whir_base_evals_device_mut(proof_slab.as_ptr() as *mut u8, kind)
                };
                let src = unsafe { DeviceSlice::from_raw_parts(src, src_len) };
                let dst = unsafe { DeviceSlice::from_raw_parts_mut(dst, dst_len) };
                gpu_gkr::packed_merge::launch_merge_claims_e4(
                    src,
                    coordinates,
                    u32::try_from(base_geometry.pack_log2()).expect("packing log2 exceeds u32"),
                    dst,
                    context,
                )?;
            }
        }
    }

    // Draw the WHIR base batching challenge on device from the rolling backward
    // seed. Pow-aware (`draw_random_field_els_with_pow(seed, 1, bits)`): grinds
    // the configured batched-proximity PoW, advances the seed, and honors the
    // skip-first-word convention. The nonce lands in its slab slot.
    // SAFETY: `ProofLayout` computes a live, aligned, non-overlapping E4 region
    // inside `proof_slab`. The draw and every WHIR consumer are ordered on the
    // exec stream, and the slab outlives the scheduled work.
    let (batching_challenge_ptr, batching_challenge_len) =
        unsafe { proof_layout.whir_batching_challenge_device_mut(proof_slab.as_ptr() as *mut u8) };
    assert_eq!(batching_challenge_len, 1);
    let batching_challenge_device =
        unsafe { DeviceSlice::from_raw_parts_mut(batching_challenge_ptr, batching_challenge_len) };
    // SAFETY: `ProofLayout` computes a live, non-overlapping single-`u64` region
    // for the batching pow nonce inside the slab; the kernel write here and the
    // terminal readback are both exec-stream-ordered.
    let (batching_nonce_ptr, _batching_nonce_len) = unsafe {
        proof_layout.batched_proximity_pow_nonce_device_mut(proof_slab.as_ptr() as *mut u8)
    };
    let batching_nonce_dst: &mut era_cudart::slice::DeviceVariable<u64> =
        unsafe { era_cudart::slice::DeviceVariable::from_raw_parts_mut(batching_nonce_ptr) };
    gpu_whir::pow::schedule_draw_e4_challenges_with_pow(
        seed,
        &mut *batching_challenge_device,
        batching_pow_bits,
        batching_nonce_dst,
        context,
    )?;
    Ok(())
}
