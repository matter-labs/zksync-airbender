//! Test-only whole-proof MAIN A/B measurement driver.
//!
//! This module deliberately does not add a hook to `prove()` or `prove_inner`.
//! It invokes the same production phase functions from a test-only scheduler so
//! the overlapping whole-proof/backward allocator observations can begin and
//! seal at their exact ownership boundaries without changing a production
//! enqueue path.

use super::*;

use gpu_prover_context::{
    DeviceMemoryHighWaterObserver, PoolMemoryHighWaterReport, PoolMemoryHighWaterSnapshot,
};

pub(crate) struct MainAcceptanceScheduledJob<'a, 'context, A: GoodAllocator> {
    job: GpuGKRProofJob<'a, A>,
    backward_observer: DeviceMemoryHighWaterObserver<'context>,
    backward_peak_window: PoolMemoryHighWaterSnapshot,
    operations: Vec<MainAcceptanceOperation>,
}

pub(crate) struct MainAcceptanceFinishedJob {
    pub(crate) proof: crate::upstream::GKRProof<
        gpu_core::primitives::field::BF,
        E4,
        crate::upstream::DefaultTreeConstructor,
    >,
    pub(crate) proof_time_ms: f32,
    pub(crate) backward: PoolMemoryHighWaterReport,
    pub(crate) backward_peak_window: PoolMemoryHighWaterSnapshot,
    pub(crate) operations: Vec<MainAcceptanceOperation>,
}

impl<A: GoodAllocator> MainAcceptanceScheduledJob<'_, '_, A> {
    pub(crate) fn finish(self) -> era_cudart::result::CudaResult<MainAcceptanceFinishedJob> {
        let Self {
            job,
            backward_observer,
            backward_peak_window,
            mut operations,
        } = self;
        let (proof, proof_time_ms) = job.finish()?;
        operations.push(MainAcceptanceOperation::ProofJobFinished);
        let backward = backward_observer.finish();
        operations.push(MainAcceptanceOperation::BackwardObserverFinished);
        Ok(MainAcceptanceFinishedJob {
            proof,
            proof_time_ms,
            backward,
            backward_peak_window,
            operations,
        })
    }
}

/// Test-only twin of `prove_inner` with one scoped observer around the real
/// backward scheduler. Keep this phase sequence mechanically aligned with
/// `prove_inner`; the packet's static oracle compares their load-bearing calls.
pub(crate) fn schedule_main_acceptance_proof<'a, 'context, A: GoodAllocator + 'a>(
    gkr_programs: &Arc<GkrPrograms>,
    prover_config: &ProverConfig,
    final_trace_size_log_2: u32,
    inputs: GpuGKRProofTransfer<'a, A>,
    backward_options: GkrBackwardOptions,
    context: &'context ProverContext,
) -> Result<MainAcceptanceScheduledJob<'a, 'context, A>, GpuProveError> {
    let compiled_circuit = gkr_programs.compiled_circuit().as_ref();
    let backward_strategy =
        resolve_backward_execution_strategy_checked(gkr_programs, prover_config, backward_options)?;
    match backward_strategy {
        BackwardExecutionStrategy::PerRound if backward_options.windowed_r0 => {
            return Err(GpuProveError::MainLayerExecutionPlan {
                error: MainLayerExecutionPlanError::WindowedStrategyUnavailable,
            });
        }
        BackwardExecutionStrategy::WindowedR0 => assert!(
            gkr_programs.window_programs_ready(),
            "the test-only measured scheduler requires windowed preflight"
        ),
        BackwardExecutionStrategy::PerRound => {}
    }
    let _continuation_window_count = main_continuation_window_count(
        backward_options,
        backward_strategy,
        main_folding_steps(gkr_programs),
    )
    .expect("the measured scheduler requires an execution plan accepted by preflight");
    if gpu_gkr::production_main_chain_selected(backward_options, backward_strategy) {
        assert!(gkr_programs.main_continuation_window_programs_ready());
        assert!(gkr_programs.main_tail_programs_ready());
    }
    assert_eq!(
        prover_config.base_oracles_values_per_leaf.trailing_zeros() as usize,
        prover_config.whir_schedule.whir_steps_schedule[0]
    );
    let whir_schedule = &prover_config.whir_schedule;
    let mut operations = Vec::with_capacity(14);

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

    if let Some(setup_transfer) = setup.as_ref() {
        assert_eq!(
            setup_transfer.trace_holder.log_lde_factor,
            prover_config.lde_factor.trailing_zeros()
        );
        assert_eq!(
            setup_transfer.trace_holder.log_rows_per_leaf,
            prover_config.base_oracles_values_per_leaf.trailing_zeros()
        );
        assert_eq!(
            setup_transfer.trace_holder.log_tree_cap_size,
            prover_config.cap_size.trailing_zeros()
        );
    }

    transfer.ensure_transferred(context)?;
    operations.push(MainAcceptanceOperation::InitialInputsTransferEnsured);

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
        final_trace_size_log_2,
        whir_schedule,
        BundleDeviceRefs {
            setup: setup.as_ref(),
            decoder: decoder.as_ref(),
            inits_and_teardowns: inits_and_teardowns.as_ref(),
            memory: &memory,
            top_bits_device: top_bits.as_ref().map(|t| &t.device),
            external_challenges_device: &external_challenges.device,
        },
        tracing_data.as_ref(),
        context,
    )?;
    operations.push(MainAcceptanceOperation::Stage1AndForwardPrepared);

    let output_evaluations_slab =
        unsafe { proof_layout.output_evaluations_device_mut(proof_slab.as_ptr() as *mut u8) }.map(
            |(ptr, len)| {
                assert_eq!(ptr, proof_slab.as_ptr() as *mut E4);
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
        context,
    )?;
    operations.push(MainAcceptanceOperation::ForwardScheduled);

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
    operations.push(MainAcceptanceOperation::BackwardHandoffPrepared);
    ranges.push(post_forward_handoff_range);

    operations.push(MainAcceptanceOperation::BackwardObserverStarted);
    let mut backward_observer = context.observe_device_memory_high_water();
    let BackwardPhaseResult {
        mut backward_scheduled,
    } = schedule_backward_phase(
        backward_state,
        top_bits_host.clone(),
        Arc::clone(gkr_programs),
        backward_options,
        backward_strategy,
        external_challenges.device.as_ptr(),
        d_seed,
        d_evaluation_point_and_batching,
        initial_d_claims,
        top_layer_claim_layout,
        d_lookup_challenges_for_backward,
        &proof_slab,
        &proof_layout,
        None,
        &mut callbacks,
        context,
    )?;
    let backward_peak_window = backward_observer.seal();
    operations.push(MainAcceptanceOperation::BackwardScheduled);
    operations.push(MainAcceptanceOperation::BackwardObserverSealed);

    let batching_pow_bits =
        crate::config::batched_proximity_check_pow_bits(prover_config, compiled_circuit);
    let WhirPhaseResult {
        transition_ranges,
        mut base_layer_claims_scheduled,
        base_layer_claims_shared_state,
        mut whir_scheduled,
    } = schedule_whir_phase(
        compiled_circuit,
        whir_schedule,
        &mut setup,
        &mut synthetic_setup_trace_holder,
        &mut stage1_output,
        &mut backward_scheduled,
        &proof_slab,
        &proof_layout,
        batching_pow_bits,
        context,
    )?;
    operations.push(MainAcceptanceOperation::WhirScheduled);
    ranges.extend(transition_ranges);
    let mut backward_keepalive = backward_scheduled;

    let proof_host_mirror = Some(schedule_terminal_proof_assembly(
        &proof_slab,
        &proof_layout,
        proof_handle,
        whir_schedule.clone(),
        base_layer_claims_shared_state,
        external_challenges.value,
        top_bits_host.clone(),
        &mut callbacks,
        context,
    )?);
    operations.push(MainAcceptanceOperation::FinalSlabD2hAndProofAssemblyScheduled);
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

    drop(synthetic_setup_trace_holder);
    if let Some(setup) = setup.as_mut() {
        setup.trace_holder.release_cosets();
    }
    backward_keepalive.release_device_buffers();
    base_layer_claims_scheduled.release_device_buffers();
    whir_scheduled.release_device_buffers();
    drop(proof_slab);
    operations.push(MainAcceptanceOperation::ProofOwnedDeviceBuffersReleased);

    let is_finished_event = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
    is_finished_event.record(stream)?;
    let inputs_keepalive = GpuGKRProofTransfer {
        transfer,
        setup,
        decoder,
        inits_and_teardowns,
        tracing_data,
        memory,
        top_bits,
        top_bits_host,
        external_challenges,
    }
    .into_keepalive();

    let job = GpuGKRProofJob {
        is_finished_event,
        callbacks,
        proof,
        ranges,
        stage_snapshots: None,
        keepalive: GpuGKRProofJobKeepalive {
            _stage1: stage1_output.into_keepalive(),
            _inputs: inputs_keepalive,
            _forward_setup: forward_setup_keepalive,
            _backward: backward_keepalive,
            _base_layer_claims: base_layer_claims_scheduled,
            _whir: whir_scheduled,
            _proof_host_mirror: proof_host_mirror,
        },
    };
    operations.push(MainAcceptanceOperation::ProofJobReturned);
    Ok(MainAcceptanceScheduledJob {
        job,
        backward_observer,
        backward_peak_window,
        operations,
    })
}
