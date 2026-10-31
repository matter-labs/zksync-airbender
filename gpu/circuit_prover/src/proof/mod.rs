use gpu_trace::trace::memory::uses_base_commitment_geometry;
pub mod inputs;
pub mod memory_policy;
pub mod merged_commitment;

use memory_policy::ProofMemoryPolicy;
mod orchestration;

#[cfg(test)]
mod tests;

use std::sync::Arc;

use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStreamWaitEventFlags;
use fft::GoodAllocator;

use crate::proof::inputs::GpuGKRProofTransfer;
use crate::upstream::{
    validate_sumcheck_schedule, BaseColumns, BaseCommitmentGeometry, GKRCircuitArtifact,
    PrimeField, ProverConfig, SumcheckScheduleClass,
};
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::context::UnsafeMutAccessor;
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::{BF, E4};
use gpu_gkr::backward::GKRBackwardStageSnapshotSink;
use gpu_gkr::forward::{schedule_forward_pass, ForwardOutputSlabTarget};
use gpu_gkr::GkrPrograms;
use gpu_prover_context::ProverContext;

pub use orchestration::GpuGKRProofJob;
use orchestration::{
    prepare_backward_handoff, prepare_stage1_and_forward_setup, schedule_backward_phase,
    schedule_terminal_proof_assembly, schedule_whir_phase, stage1_forward::BundleDeviceRefs,
    BackwardPhaseResult, ForwardToBackwardHandoff, GpuGKRProofJobKeepalive,
    Stage1AndForwardPreparation, WhirPhaseResult,
};

fn validate_same_size_schedule(gkr_programs: &GkrPrograms, prover_config: &ProverConfig) {
    validated_schedule_class(gkr_programs, prover_config)
        .expect("invalid GKR same-size sumcheck schedule");
}

fn validated_schedule_class(
    gkr_programs: &GkrPrograms,
    prover_config: &ProverConfig,
) -> Option<SumcheckScheduleClass> {
    validate_sumcheck_schedule(
        &prover_config.same_size_sumcheck_schedule,
        main_folding_steps(gkr_programs),
    )
    .ok()
}

fn main_folding_steps(gkr_programs: &GkrPrograms) -> usize {
    gkr_programs.compiled_circuit().trace_len.trailing_zeros() as usize
}

/// One immutable config/geometry/policy bound before transfers. Producer routing,
/// storage representations and actual per-role backend constraints are checked
/// independently of preset selection; execution jobs share the config.
pub struct ProofPreflight<F: PrimeField> {
    dr_tail: gpu_gkr::DrTailProofPlan,
    circuit: Arc<GKRCircuitArtifact<F>>,
    config: ProverConfig,
    geometry: BaseCommitmentGeometry,
    memory_policy: ProofMemoryPolicy,
    batching_pow_bits: u32,
    twiddle_domain_log2: u32,
}

impl<F: PrimeField> ProofPreflight<F> {
    pub fn geometry(&self) -> BaseCommitmentGeometry {
        self.geometry
    }

    pub fn memory_policy(&self) -> ProofMemoryPolicy {
        self.memory_policy
    }

    #[cfg(test)]
    pub(crate) fn batching_pow_bits_for_test(&self) -> u32 {
        self.batching_pow_bits
    }
}

/// Field-free protocol/policy admission. Backend transform checks are separate.
pub(crate) fn validate_base_proof_geometry_policy(
    geometry: &BaseCommitmentGeometry,
    memory_policy: ProofMemoryPolicy,
    main_layers: usize,
) {
    assert!(
        memory_policy.witness.is_valid(),
        "invalid witness memory policy"
    );
    memory_policy.gkr.validate_for_main_layers(main_layers);
    if geometry.commitment_mode() == crate::upstream::CommitmentMode::MergedMemoryAndWitness {
        merged_commitment::validate_merged_packed_geometry(geometry);
    } else {
        gpu_trace::trace::memory::validate_separate_base_commitment_geometry(geometry);
    }
}

/// Validate the representations the BabyBear producers and query readers use.
/// Legacy holders retain their existing transform path; empty roles do no work.
fn validate_baby_bear_base_proof_policy(
    geometry: &BaseCommitmentGeometry,
    policy: ProofMemoryPolicy,
    twiddle_domain_log2: u32,
) {
    use crate::upstream::BaseOracleRole as Role;
    use gpu_trace::trace::holder::{validate_baby_bear_base_opening, TreesCacheMode};
    use memory_policy::{
        OpeningStrategy as Opening, WitnessCommitmentStrategy as Commit, WitnessOpeningStrategy,
        WitnessPostCommitStorage as Store,
    };
    if !uses_base_commitment_geometry(geometry) {
        return;
    }
    // Every base query consumes the partial-tree format, including Memory
    // whose commitment phase carries only a cap into this proof.
    gpu_trace::trace::holder::TraceHolder::<BF>::validate_base_layout(
        geometry,
        TreesCacheMode::CachePartial,
    );
    let validate = |role, opening, trees| {
        if geometry.oracle(role).physical_columns() != 0 {
            validate_baby_bear_base_opening(geometry, opening, trees, twiddle_domain_log2);
        }
    };
    // Setup is transferred with Partial trees; memory carries only its cap.
    validate(Role::Setup, policy.setup, TreesCacheMode::CachePartial);
    validate(Role::Memory, policy.memory, TreesCacheMode::CacheNone);
    // In merged mode the combined nonempty set is Memory; Witness is empty.
    if geometry.oracle(Role::Witness).physical_columns() != 0 {
        let commitment = match policy.witness.commitment {
            Commit::AllCosets if policy.witness.post_commitment != Store::RawAndMonomials => {
                Opening::AllCosets
            }
            Commit::AllCosets | Commit::PerCoset => Opening::PerCoset,
            Commit::InPlace => Opening::InPlace,
        };
        validate(Role::Witness, commitment, TreesCacheMode::CachePartial);
        let opening = match policy.witness.opening {
            WitnessOpeningStrategy::ReuseCosets => Opening::AllCosets,
            WitnessOpeningStrategy::Recompute(opening) => opening,
        };
        validate(Role::Witness, opening, TreesCacheMode::CachePartial);
    }
}

/// Existing BabyBear proof backend's pre-transfer capability boundary. The
/// capacity is supplied by the live context, never inferred from a constant.
pub fn preflight_proof(
    programs: &GkrPrograms,
    config: &ProverConfig,
    final_trace_log: u32,
    device_id: i32,
    memory_policy: ProofMemoryPolicy,
    twiddle_domain_log2: u32,
) -> CudaResult<ProofPreflight<BF>> {
    assert_eq!(
        config.trace_len_log2,
        programs.compiled_circuit().trace_len.trailing_zeros() as usize,
        "proof config trace length differs from compiled circuit"
    );
    assert_eq!(
        final_trace_log as usize, config.sumcheck_explicit_output_size_log_2,
        "GKR final trace size differs from configured explicit output size"
    );
    assert!(
        (final_trace_log as usize) < config.trace_len_log2,
        "GPU forward transcript handoff requires at least one dimension-reduction layer"
    );
    let geometry =
        BaseCommitmentGeometry::from_config(config, BaseColumns::of(programs.compiled_circuit()))
            .expect("invalid base commitment geometry");
    validate_base_proof_geometry_policy(&geometry, memory_policy, programs.main_layers_count());
    validate_baby_bear_base_proof_policy(&geometry, memory_policy, twiddle_domain_log2);
    gpu_whir::validate_baby_bear_recursive_schedule(
        u32::try_from(geometry.message_size_log2()).expect("message log2 exceeds u32"),
        &config.whir_schedule,
        twiddle_domain_log2,
    );
    validate_same_size_schedule(programs, config);
    let batching_pow_bits =
        crate::config::batched_proximity_check_pow_bits_for_geometry(config, &geometry);
    let dr_tail = gpu_gkr::preflight_dr_tail_resources(programs, final_trace_log, device_id)?;
    Ok(ProofPreflight {
        dr_tail,
        circuit: Arc::clone(programs.compiled_circuit()),
        config: config.clone(),
        geometry,
        memory_policy,
        batching_pow_bits,
        twiddle_domain_log2,
    })
}

/// What the DR preflight boundary needs in order to admit a proof request.
///
/// `None` at the boundary means the request is not a proof, so neither the
/// windowed lowering preflight nor DR-tail resource admission applies.
#[derive(Clone, Copy)]
pub struct DrTailPreflightRequest<'a> {
    pub gkr_programs: &'a GkrPrograms,
    pub prover_config: &'a ProverConfig,
    pub final_trace_size_log_2: u32,
    pub device_id: i32,
    pub memory_policy: ProofMemoryPolicy,
    pub twiddle_domain_log2: u32,
}

/// Preflight before constructing transfers so the plan can be owned by them.
pub fn admit_dr_tail_before_transfers<T>(
    request: Option<DrTailPreflightRequest<'_>>,
    construct_transfers: impl FnOnce(Option<ProofPreflight<BF>>) -> T,
) -> CudaResult<T> {
    let Some(request) = request else {
        return Ok(construct_transfers(None));
    };
    let plan = preflight_proof(
        request.gkr_programs,
        request.prover_config,
        request.final_trace_size_log_2,
        request.device_id,
        request.memory_policy,
        request.twiddle_domain_log2,
    )?;
    Ok(construct_transfers(Some(plan)))
}

/// Enqueue a proof with explicit representation choices. Setup and memory
/// always defer materialization until their separate query phases.
pub fn prove<'a, A: GoodAllocator + 'a>(
    gkr_programs: &Arc<GkrPrograms>,
    prover_config: &ProverConfig,
    final_trace_size_log_2: u32,
    inputs: GpuGKRProofTransfer<'a, A>,
    dr_tail_plan: &ProofPreflight<BF>,
    memory_policy: ProofMemoryPolicy,
    context: &ProverContext,
) -> CudaResult<GpuGKRProofJob<'a>> {
    prove_inner(
        gkr_programs,
        prover_config,
        final_trace_size_log_2,
        inputs,
        dr_tail_plan,
        memory_policy,
        None,
        context,
    )
}

#[cfg(test)]
pub(crate) fn prove_stagewise<'a, A: GoodAllocator + 'a>(
    gkr_programs: &Arc<GkrPrograms>,
    prover_config: &ProverConfig,
    final_trace_size_log_2: u32,
    inputs: GpuGKRProofTransfer<'a, A>,
    context: &ProverContext,
) -> CudaResult<GpuGKRProofJob<'a>> {
    let dr_tail_plan = preflight_proof(
        gkr_programs,
        prover_config,
        final_trace_size_log_2,
        era_cudart::device::get_device()?,
        ProofMemoryPolicy::default(),
        context
            .ntt_device_context()
            .whir_leaf_transform_params()
            .omega_log_order,
    )?;
    prove_inner(
        gkr_programs,
        prover_config,
        final_trace_size_log_2,
        inputs,
        &dr_tail_plan,
        ProofMemoryPolicy::default(),
        Some(Box::default()),
        context,
    )
}

fn prove_inner<'a, A: GoodAllocator + 'a>(
    gkr_programs: &Arc<GkrPrograms>,
    prover_config: &ProverConfig,
    final_trace_size_log_2: u32,
    inputs: GpuGKRProofTransfer<'a, A>,
    dr_tail_plan: &ProofPreflight<BF>,
    memory_policy: ProofMemoryPolicy,
    mut stage_snapshots: Option<Box<GKRBackwardStageSnapshotSink>>,
    context: &ProverContext,
) -> CudaResult<GpuGKRProofJob<'a>> {
    assert!(
        Arc::ptr_eq(&dr_tail_plan.circuit, gkr_programs.compiled_circuit()),
        "proof preflight belongs to another circuit artifact"
    );
    assert_eq!(
        &dr_tail_plan.config, prover_config,
        "proof config differs from preflight"
    );
    assert_eq!(
        dr_tail_plan.memory_policy, memory_policy,
        "proof policy differs from preflight"
    );
    assert_eq!(
        dr_tail_plan.twiddle_domain_log2,
        context
            .ntt_device_context()
            .whir_leaf_transform_params()
            .omega_log_order,
        "proof context twiddle capacity differs from preflight"
    );
    dr_tail_plan
        .dr_tail
        .validate_before_enqueue(gkr_programs, final_trace_size_log_2, context);
    let base_geometry = dr_tail_plan.geometry;
    let compiled_circuit = gkr_programs.compiled_circuit().as_ref();
    assert_eq!(
        prover_config
            .base_oracles_values_per_leaf()
            .trailing_zeros() as usize,
        prover_config.whir_schedule.base_folding_log2()
    );
    let whir_schedule = &prover_config.whir_schedule;

    let GpuGKRProofTransfer {
        transfer,
        mut setup,
        decoder,
        inits_and_teardowns,
        tracing_data,
        memory,
        top_bits,
        top_bits_host,
        external_challenges,
    } = inputs;
    memory.host.validate_for_geometry(&base_geometry);
    if let Some(setup_transfer) = setup.as_ref() {
        setup_transfer.host.validate_for_geometry(&base_geometry);
        assert_eq!(
            setup_transfer.trace_holder.log_lde_factor,
            prover_config.lde_factor().trailing_zeros()
        );
        assert_eq!(
            setup_transfer.trace_holder.log_rows_per_leaf,
            prover_config
                .base_oracles_values_per_leaf()
                .trailing_zeros()
        );
        assert_eq!(
            setup_transfer.trace_holder.log_tree_cap_size,
            prover_config.cap_size.trailing_zeros()
        );
    }

    // Single fork/join from h2d_stream → exec_stream covering every pre-prove
    // H2D bundled by `inputs` (setup, decoder, inits_and_teardowns, tracing_data,
    // memory caps, top_bits, external_challenges).
    transfer.ensure_transferred(context)?;

    let stream = context.get_exec_stream();
    let mut callbacks = Callbacks::new();
    let mut proof = Box::new(None);
    let proof_handle = UnsafeMutAccessor::new(proof.as_mut());
    let mut ranges = Vec::new();
    let proof_range = Range::new("gkr.proof")?;
    proof_range.start(stream)?;

    context.reset_used_mem_peak();

    let Stage1AndForwardPreparation {
        mut stage1_output,
        mut synthetic_setup_trace_holder,
        proof_layout,
        proof_slab,
        mut forward_setup,
        d_seed,
    } = prepare_stage1_and_forward_setup::<A>(
        gkr_programs,
        prover_config,
        base_geometry,
        final_trace_size_log_2,
        whir_schedule,
        BundleDeviceRefs {
            setup: setup.as_ref(),
            decoder: decoder.as_ref(),
            inits_and_teardowns: inits_and_teardowns.as_ref(),
            memory: &memory,
            top_bits_device: top_bits.as_ref(),
            external_challenges_device: &external_challenges.device,
        },
        tracing_data.as_ref(),
        memory_policy.witness,
        context,
    )?;
    // Their final device readers are enqueued; Transfer still owns the H2D sources.
    drop(tracing_data);
    drop(inits_and_teardowns);
    drop(decoder);

    let output_evaluations_slab =
        unsafe { proof_layout.output_evaluations_device_mut(proof_slab.as_ptr() as *mut u8) }.map(
            |(ptr, len)| {
                assert_eq!(
                    ptr,
                    proof_slab.as_ptr() as *mut E4,
                    "output_evaluations must be the proof slab prefix for direct forward writes",
                );
                ForwardOutputSlabTarget {
                    backing: Arc::clone(&proof_slab),
                    len,
                }
            },
        );
    let forward_output = schedule_forward_pass(
        setup.as_ref().map(|setup| &setup.trace_holder),
        synthetic_setup_trace_holder.as_ref(),
        &mut stage1_output,
        &mut forward_setup,
        &external_challenges.value,
        &top_bits_host,
        final_trace_size_log_2,
        output_evaluations_slab,
        gkr_programs,
        memory_policy.gkr,
        context,
    )?;
    let ForwardToBackwardHandoff {
        post_forward_handoff_range,
        transcript_handoff,
        backward_state,
        forward_setup_keepalive,
        d_lookup_challenges_for_backward,
        d_seed,
        d_evaluation_point_and_batching,
        top_layer_claim_layout,
        initial_d_claims,
    } = prepare_backward_handoff(
        forward_output,
        forward_setup,
        d_seed,
        final_trace_size_log_2,
        context,
    )?;

    ranges.push(post_forward_handoff_range);

    let BackwardPhaseResult {
        mut backward_scheduled,
    } = schedule_backward_phase(
        backward_state,
        top_bits_host.clone(),
        Arc::clone(gkr_programs),
        &dr_tail_plan.dr_tail,
        external_challenges.device.as_ptr(),
        d_seed,
        d_evaluation_point_and_batching,
        initial_d_claims,
        top_layer_claim_layout,
        d_lookup_challenges_for_backward,
        &proof_slab,
        &proof_layout,
        stage_snapshots.as_deref_mut().map(UnsafeMutAccessor::new),
        &mut callbacks,
        context,
    )?;
    let batching_pow_bits = dr_tail_plan.batching_pow_bits;
    let WhirPhaseResult {
        mut base_layer_claims_scheduled,
        base_layer_claims_shared_state,
        whir_scheduled,
    } = schedule_whir_phase(
        compiled_circuit,
        base_geometry,
        whir_schedule,
        &mut setup,
        &mut synthetic_setup_trace_holder,
        &mut stage1_output,
        &mut backward_scheduled,
        &proof_slab,
        &proof_layout,
        batching_pow_bits,
        memory_policy,
        context,
    )?;

    // `backward_scheduled` itself is the keepalive — the per-layer device
    // handles were already taken by the orchestrator (or remain as `Some`
    // for the proof-lifetime final-seed/claim-point buffers), and the
    // callbacks/tracing/host-staging buffers all ride on this struct.
    let mut backward_keepalive = backward_scheduled;

    let proof_host_mirror = Some(schedule_terminal_proof_assembly(
        &proof_slab,
        &proof_layout,
        proof_handle,
        whir_schedule.clone(),
        base_layer_claims_shared_state,
        external_challenges.value,
        // The ACTUAL per-circuit top bits (all-zero for trivial unified
        // chunks): they land in `GKRProof::inits_and_teardowns_top_bits`,
        // which the full-statement verifier asserts to be zero for the
        // leading (dummy) unified instances.
        top_bits_host.clone(),
        &mut callbacks,
        context,
    )?);
    drop(transcript_handoff);

    {
        let event = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
        event.record(stream)?;
        context
            .get_h2d_stream()
            .wait_event(&event, CudaStreamWaitEventFlags::DEFAULT)?;
    }

    proof_range.end(stream)?;
    ranges.push(proof_range);

    // All device readers are enqueued on exec, so these reservations can be
    // reused by subsequent stream work. Input reservations drop at function
    // exit; the returned job retains host data and callback owners through finish().
    drop(synthetic_setup_trace_holder);
    backward_keepalive.release_device_buffers();
    base_layer_claims_scheduled.release_device_buffers();
    // Proof slab: last scheduled use is the terminal D2H on exec_stream.
    drop(proof_slab);

    let is_finished_event = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
    is_finished_event.record(stream)?;

    let inputs_keepalive = inputs::GpuGKRProofTransferKeepalive {
        _setup_host: setup.as_ref().map(|setup| Arc::clone(&setup.host)),
        _transfer: transfer.into_keepalive(),
    };

    Ok(GpuGKRProofJob {
        is_finished_event,
        callbacks,
        proof,
        ranges,
        stage_snapshots,
        keepalive: GpuGKRProofJobKeepalive {
            _stage1: stage1_output.into_keepalive(),
            _inputs: inputs_keepalive,
            _forward_setup: forward_setup_keepalive,
            _backward: backward_keepalive,
            _base_layer_claims: base_layer_claims_scheduled,
            _whir: whir_scheduled,
            _proof_host_mirror: proof_host_mirror,
        },
    })
}

#[cfg(test)]
pub(crate) use orchestration::schedule_base_commitment_handoff;
